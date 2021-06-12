Design Notes
============

Given the `requirements document <Requirements.rst>`_, this document contains a sketch of the design of the necessary verifier.  It will be based on the macaw and crucible libraries for binary analysis and symbolic execution, with support from the core of the pate verifier.

Note that we cannot symbolically execute the target program from the entry point while proving all of the assertions implied by the requirements provided by users of the tool, as it will not scale to realistic program sizes. Instead, we will build a compositional verifier. In high level terms, the verifier will:

1. Translate requirements into a set of verification conditions (which can be thought of as a set of quantified assertions)
2. Instantiate the requirements for each basic block
3. Verify that the assertions hold

If all of the assertions can be verified, the requirements specified by the user are satisfied by the target binary.  The inputs to the verifier will be user provided requirements, a binary, and an input that triggers (or does not trigger) a Weird Machine in the program.

One of our key requirements is to be able to interact with the environment and external agents that feed input to the program (e.g., to trigger the Weird Machine). To support this, we will need to support whole-program symbolic execution. Note that this seems to be in contrast to our requirement for compositionality. We can support both requirements by using symbolic execution to consume external input and produce output, while deferring verification to a compositional post-processing step.

1. Discover binary code with macaw
   - Will implement future improved heuristics for dealing with stripped binaries
   - Run code discovery on the target executable and its (transitive) shared libraries
2. Lift discovered functions into Crucible
   - Will require building models of some system calls
3. Symbolically execute the program with the concrete input provided to trigger the Weird Machine
   - This will consume input *and* generate output
   - Symbolic branching in this phase would be potentially problematic for managing the state of the input generator (but we *can* split inputs---outputs are trickier)
   - Simulate until we get to the Weird Machine (it may be very useful to have it labeled)
   - Save the state of the input and output channels (environment) at each function entry (granularity to be evaluated)
4. Translate the user-provided requirements into quantified/labeled assertions
   - We can start with some trivial requirements
5. Instantiate each assertion at the necessary program locations (based on label)
   - The boundaries at which we do this are TBD, but would match the granularity of the saved states from step 3
   - Likely something like acyclic superblocks
   - The assertions will become block postconditions to be proved
   - The collected state from step 3 (along with other state information like aliasing information) will be preconditions assumed
   - The other state information should be generated in a top-down and bottom-up traversal of the program that propagates *demand* and the necessary context to satisfy that demand
6. Verify that the postconditions hold (under various environmental configuration options)

Later (hopefully in Phase 2), we can look at the problem of establishing (conditional) behavioral equivalence after the Weird Machine returns. This is a relational verification problem and could be addressed by extending the pate verifier build for AMP.


Major Features to Implement
===========================

Our tools are fairly robust, but need to be extended in various ways to support this project.

- Support for command line argument initialization in symbolic execution (concrete required, symbolic optional)
- Symbolic I/O interaction
  - The major missing feature is adding input that is computed by an external source (which is itself based on processing symbolic output)
  - Ultimately including network
  - Adding environment variables
- Support for printing pointer values to output channels and reading them back in
  - This is required to model interactions that take advantage of pointer disclosure attacks
  - Some pointers are easy to handle because they are constant (e.g., pointers into the data section)
  - Dynamic allocations are harder
  - Observation: some Weird Machines rely on the relative ordering of allocations in order to work. Within a large slab we can guarantee that. Between slabs, it relies on OS behaviors
- Support for (symbolic or virtual) ASLR, which would alter the addresses assigned to instructions (independently for the executable image and shared libraries)
- Lifting shared libraries and dynamically "linking" them (enabling dynamic library functions to be called during symbolic execution)
- Symbolic models (crucible overrides) of system call behavior (arranged into profiles to support multiple operating systems)
  - Note: we will also likely want symbolic overrides for *some* standard library functions to use where possible, but we are likely to need to simulate the entire function in cases where it is involved in a Weird Machine
- Lazy re-analysis to identify gadgets and turn them into executable code
  - It may be the case that we may want to analyze ahead to figure out what the program induced by the Weird Machine is instead of rediscovering it from first-principles
- Windows support in macaw (including win32)
  - This will require some Windows-specific system call overrides
- Better support for stripped binaries in macaw
- User-assisted jump table resolution in macaw
  - Could come from reverse engineers or the testing team (i.e., answering the question "at the jump at PC=0xNNN, what are the observed targets)

Minimum Viable Product
======================

We should start with a simple verifier that ignores the compositional/scalable verification problem. We can start by putting together a whole-program verifier based on macaw and crucible that takes as input:
- The binary (linux/x86)
- Triggering input
- Command line arguments for the binary being verified
Note that our initial requirement can be that the program just doesn't crash when the Weird Machine is triggered. Also note that our first triggering input can be static, but that we will want to quickly implement interaction after that.

Initially, we can target some CTF problems and their solutions (e.g., https://github.com/perribus/mooosl)

Notes
=====

Memory Allocation
-----------------

Memory layouts are key to correctly understanding the execution of Weird Machines.

Dynamic Loading
---------------

While we plan to address dynamic linking by collecting the transitive closure of all libraries accessed by a program, dynamic loading (i.e., via ``dlopen``) is trickier. We would prefer to leave this out of scope, but if we must address it, we can do so by adding a crucible-level override for the ``dlopen`` function that attempts to load the indicated shared library from the provided set of shared libraries. If it does not exist, the verifier can exit with a report on the missing library. As an alternative, it could simply return a failing exit code and emit a diagnostic recording the dynamic loading attempt.
