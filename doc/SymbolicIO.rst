Overview
========

This document describes a high level plan, and proposed concrete syntax, for managing symbolic input and output from the verifier.

Problem Statement
=================

For the most basic one-shot exploits, the verifier needs to support input over various channels (e.g., files and sockets).  These inputs can generally be concrete.  More interesting exploits involve *interaction* where the exploit probes the software system to either fingerprint it or leak secrets (e.g., canary values or addresses to defeat ASLR).  Some of the major challenges in supporting interactive exploits include:

- The verifier must be able to leak symbolic values to the outside world
- Symbolic values may be pointers, which have additional structure within the verifier; this structure must be preserved
- The verifier must be able to re-ingest symbolic values and losslessly reconstruct them
- The verifier can symbolically branch (i.e., explore both control flow paths following a conditional branch on a symbolic value); this means that the "same" output from the program can be produced more than once (and the outside world must be prepared for that)


Note that interactivity is a Phase 2 concern, but we need to plan our strategy now to ensure that we can make progress quickly once Phase 2 starts.

Symbolic I/O Sketch
===================


This section sketches out what interactive symbolic I/O could look like.  It will start with symbolic output and then explain symbolic input in terms of the information available to the outside world (e.g., a pwntools script).


Data Format
-----------

We anticipate using a streaming JSON format where each JSON object in the stream is the result of a single ``write`` (or equivalent) call.  The proposed schema for each write (from the verifier to the outside world) is:

::
   <write> := { "pathCondition": [<symbolicBranchId>*],
                "streamOffset": <Natural>,
                "bytes": [<symbolicByte>*]
              }

   <symbolicBranchId> := <Natural>

   <symbolicByte> := { "type": "concrete",
                       "value": <Word8>
                     }
                  \|  { "type": "symbolic",
                       "symbolicId": <Natural>
                     }


Each write contains a sequence of bytes that can be concrete or symbolic.  The other two fields of the write are crucial for identifying writes on different symbolic branches of the symbolic execution.  The ``pathCondition`` is the sequence of unique identifiers assigned to symbolic branches that are in scope in the verifier when the write occurs.  The ``streamOffset`` is the offset into the logical output stream that the write begins at.  There will be a single logical stream of bytes for each path explored through the program.  The goal is that these two pieces of information should be enough to correlate writes across all symbolic branches.

Note that it may be sufficient for ``pathCondition`` to be a simple unique identifier (another ``Natural``), with the mapping from unique identifiers to path conditions being maintained inside of the solver; this would simplify the external interface, given that we would prefer to not require the symbolic pwntools library to need to reason about path conditions explicitly.  However, that may be aspirational.

For concrete bytes, the ``Word8``  ``value`` is a literal byte representing a concrete value output by the verifier.

For symbolic bytes, the ``Natural``  ``symbolicId`` is an opaque name for a symbolic value inside of the verifier.  In the outside world, the pwntools script should assign this a symbolic value (e.g., using the angr representation of formulas).

The external observer, a symbolic pwntools script, will send responses back to the verifier as an analogous stream of JSON data descriptions.  Each data packet will be described as a ``read`` (from the perspective of the verifier):

::
   <read> := { "pathCondition": [<symbolicBranchId>*],
               "streamOffset": <Natural>,
               "bytes": [<symbolicByte>*]
             }

   <symbolicBranchId> := <Natural>

   <symbolicByte> := { "type": "concrete",
                       "value": <Word8>
                     }
                  \|  { "type": "symbolic",
                       "symbolicValue": <symbolicExpression>
                     }

   <symbolicExpression> := { "type": "symbolicValueRef"
                           , "symbolicId": <Natural>
                           }
                        \|  { "type": "binaryOperator",
                             "operation": "+",
                             "lhs": <symbolicExpression>,
                             "rhs": <symbolicExpression>
                           }
                        \| ...


This is very similar to the output from the verifier, except that symbolic values passed back may have an expression structure to reflect the computations performed in the symbolic pwntools script.  The syntax presented above is a small example; the full expression language will need to be worked out.  Some notes:

- The ``symbolicId`` in the ``symbolicValueRef`` case is a ``symbolicId`` referring to a symbolic value in the verifier that was emitted as part of a previous ``<write>``
- This format suggests a nested formula structure, which could be sub-optimal (i.e., expensive) if there is substantial term sharing; we can introduce observable sharing if necessary
- This formulation assumes that the *lengths* of writes will be concrete. If we need to support symbolic length writes, we will need ``streamOffset`` to be a symbolic expression and will need to support an additional ``condition`` field in the definition of each byte.


Symbolic Pwntools
-----------------

The verifier is currently designed to read from static files, which is likely insufficient for the streaming input/output use case.  We can adapt it to work over local UNIX sockets (or expect streaming file output instead).

There are a few key challenges for the symbolic pwntools interface:

- *Converting symbolic values emitted by the verifier into a format that can be operated on sensibly*: This can likely be accomplished by just maintaining a map from the unique identifiers that are emitted by the verifier to a base symbolic value as supported by whatever symbolic representation angr uses. By virtue of executing, symbolic pwntools will build up *expressions* in terms of those symbolic values.  When symbolic pwntools writes one of the symbolic expressions back to the verifier (by the ``symbolicExpression`` production), it will need to replace references to symbolic values with their corresponding reference numbers from the verifier.
- *Handling branching outputs from the verifier*: The verifier will execute symbolic branches that make it look like a single write may be executed multiple times.  The symbolic pwntools backend will need to be able to account for this and respond multiple times independently.  It is intended that the ``streamOffset`` and ``pathCondition`` will be sufficient to enable symbolic pwntools to synchronize properly, but the crafting of that logic will be non-trivial.

Notable Technical Challenges
============================

Beyond the challenges in implementing symbolic pwntools, there are some additional challenges on the verifier side.  These include:

- *The verifier can both branch and merge*: Path merging is crucial for the scalability of the verifier.  However, merging means that a ``write`` followed by a ``read`` in the program being verified might not cleanly match up. For example, assume that the verifier executes a symbolic branch and issues a ``write`` on each branch.  These are "the same" write, as only one can occur on any given concrete execution.  Additionally, it could be the case that the divergent execution branches are *merged* in the verifier before the next ``read``.  This means that the symbolic pwntools script may produce two responses that need to be merged to be received by the single ``read`` on the merged execution path.  This is not insurmountable, but it will require careful monitoring of the branching and merging structure (and metadata) of the verification.
- *We likely need to track the current path condition in a way that can be easily exported to symbolic pwntools*: This should be possible, though the verifier is not currently set up to do so. We can probably get away with just allocating a fresh nonce at each symbolic branch and maintaining the "current" sequence on each branch.  Tracking merges may be more difficult; we will have to investigate if there are any hooks to allow us to observe merges.
- *We will need a global database of externalized symbolic values*: This should actually be straightforward (though we might never get to garbage collect it, so may want to be careful).  Note that in the current design, we should not need to export any of the formula structure of symbolic values to symbolic pwntools, which is a good design goal to maintain.  Fully reifing all of the symbolic structure would be very expensive, and capturing all of the constraints necessary to interpret it may be impossible (as those mostly live in the SMT solver).
- *Existing verifier assumptions may be optimistic*: There are a few assumptions in the implementations of the networking primitives in the verifier that will likely prevent them from being correct in the presence of symbolic branches around I/O.  These assumptions are mostly marked in the source, but they will need to be corrected.  Some of these will require some work in the core symbolic-io library.

Potential Approaches
====================

This section documents a few concrete proposals that we could investigate for implementing the branching necessary in the symbolic pwntools library.

Call with Current Continuation (call/cc)
----------------------------------------

In this formulation, we could implement ``call/cc`` using Python's bytecode rewriting API.  At a high level, this would introduce a new ``call/cc`` primitive that was able to capture the current continuation and invoke it multiple times.  We could implement the pwntools API on top of this primitive, enabling us to hide all of the necessary logic in the library.

An example of using the bytecode parsing/rewriting interface is here https://github.com/snoack/python-goto, which uses it to implement ``goto`` in Python.

Major challenges include:

- Transforming local state into a data structure that can be passed to each continuation
- Capturing global state safely seems challenging (e.g., figuring out what all of the relevant global state *is*)
- It really needs to be a global transformation, because ``return`` has to be turned into a call to a continuation (that has to be passed in as an argument)

Note that this is a really technically interesting approach, but may be fragile in the presence of Python changes. All of the complexity could be bundled up into a single module, but there is inherent risk.

External Multiplexer
--------------------

Part of the complexity of the ``call/cc`` solution is the (pseudo-)requirement that it have exactly the same interface as a non-symbolic pwntools script.  Adding an external multiplexer to handle all output from the verifier (and to coordinate responses from symbolic pwntools) might simplify the problem substantially.  As a quick sketch of the approach:

1. We would change the verifier output stream to have a single output channel, but where each write would be tagged with the logical channel being written to (e.g., stdout, stderr, or a socket with port information)
2. The multiplexer would read the stream of verifier outputs and spawn a fresh instance of the symbolic pwntools script for each symbolic branch
3. The implementation of symbolic pwntools would have to instrument all of its input and output methods to communicate with the multiplexer, including the ability to *block* until the multiplexer gives it the go-ahead to continue

This approach adds a layer of indirection to manage branching and splitting. That layer means that the script proper can remain largely oblivious to the branching and splitting and merely block until the multiplexer provides it with input. It can produce outputs at its leisure, while the multiplexer can then send responses to the verifier. How much of the branching/merging logic can/should be exposed to the multiplexer is an open question.

When the multiplexer observes that a symbolic branch has occurred, it would need to spawn another copy of the symbolic pwntools script and replay any inputs already received to that script.  It should be possible for the multiplexer to notice a symbolic branch based not only on the path condition (which could be ambiguous), but if it sees that the "same" byte offset has been emitted more than once.  It should not be necessary to replay outputs *up to the point where the divergence is detected*.

Because the multiplexer will probably not be able to observe any merging in the verifier, merging responses from the multiplexer will likely need to be handled within the verifier (if applicable).
