Tricks for debugging the verifier
=================================

The verifier is a large, complex piece of software. This document serves to
collect various tricks that we have learned to effectively debug issues that
arise when using the verifier.

Profile, profile, profile
=========================

Make sure to use the ``--profile-to`` flag, as the profiler is the best tool we
have for visualizing what is taking up the most time in the verifier.

Log all the things
==================

There is quite a bit of information that can be gleaned from the ``--log-*``
flags that the verifier offers. These include (but are not limited to) the following:

* ``--log-symbolic-branches``: This logs every time the verifier undergoes a
  symbolic control flow branch. If you suspect that there is unwanted symbolic
  information being passed around, this option can be helpful for confirming if
  this is the case.
* ``--log-solver-interactions``: This logs every SMT query that gets sent to an SMT
  solver. This can be helpful if you encounter a problem where the verifier is
  bottlenecked on the output of an SMT solver.
* ``--log-function-cfgs``: This logs the ``macaw`` control-flow graph of each
  function that is called during simulation. ``macaw`` CFGs are at a level of
  abstraction slightly higher than assembly. The CFG will still tell you the
  addresses of each line of assembly in the binary, but the instructions will
  have been lifted to ``macaw`` operations, which describe the steps that the
  simulator performs.
* ``--log-function-calls``: This logs every time a function is called, as well
  as the address to which the function returns. This can be useful not only for
  tracing through the control flow at a high level, but also for seeing the last
  function that gets called before the verifier becomes stuck.

Overrides are your friend
=========================

You can learn a lot about what is going on in the simulator by overriding
frequently invoked functions. We have a variety of debugging mechanisms for use
in overrides:

* ``(println <str>)`` prints a string ``str`` to standard output when
  simulated.
* ``(read-c-string <ptr>)`` reads a concrete string from the memory pointed to
  by ``ptr``. This can be especially handy for functions like ``printf``,
  ``strcmp``, ``strcpy``, or any other function that has a string as an
  argument.
* ``(print-pointer <ptr>)`` pretty-prints the address of ``ptr``.

Trace through the CFG
=====================

If you want to know what is happening during simulation at a very low level,
you can add print statements to the verifier's codebase that follow the
structure of the ``--log-function-cfgs`` output. For instance, here is the
``macaw`` CFG for a ``cmp`` instruction seen in the wild:

```
# 0x40114f cmp    QWORD PTR [rbp-0x8],0x0
r27 := read_mem r26 (bvle8)
r28 := (bv_slt r27 (0x0 :: [64]))
r29 := (eq r27 (0x0 :: [64]))
r30 := (trunc r27 8)
r31 := (even_parity r30)
```

What are these ``read_mem``, ``bv_slt``, etc. things? They are pretty-printed
versions of ``macaw`` operations, and you can see which operations correspond
to which pretty-printed output
[here](https://github.com/GaloisInc/macaw/blob/b813ecda9a4339ce31b6fb4b48f7e0f8d394ca55/base/src/Data/Macaw/CFG/App.hs#L456-L500)
and
[here](https://github.com/GaloisInc/macaw/blob/9d2e1d4b9f163c8947a284c2031000c54a3a9330/base/src/Data/Macaw/CFG/Core.hs#L756-L769)
in ``macaw``. From there, those operations become mapped to ``crucible``
operations
[here](https://github.com/GaloisInc/macaw/blob/9d2e1d4b9f163c8947a284c2031000c54a3a9330/symbolic/src/Data/Macaw/Symbolic/CrucGen.hs#L991-L1223).
Once you know what ``crucible`` operation you want to trace, you can do so by
adding a print statement to the corresponding case in [this ``crucible``
function](https://github.com/GaloisInc/crucible/blob/e1308319eef8e0fcb55ed04df7eb2e9d5e87aac5/crucible/src/Lang/Crucible/Simulator/Evaluation.hs#L261-L1006).

Note that some ``macaw`` operations do not map to ``crucible`` operations, but
instead they map to ``macaw``-specific extensions. For example, note
[here](https://github.com/GaloisInc/macaw/blob/9d2e1d4b9f163c8947a284c2031000c54a3a9330/symbolic/src/Data/Macaw/Symbolic/CrucGen.hs#L1007)
that under certain conditions, an ``eq ... ...`` operation can turn into a
``PtrEq`` extension. These extensions are handled directly in the verifier's
memory model, so to trace them, add print statements to
``evalMacawExprExtension`` or ``execAmbientStmtExtension`` in
``Ambient.Extensions``, depending on what type of extension it is. The full
list of extensions can be found
[here](https://github.com/GaloisInc/macaw/blob/9d2e1d4b9f163c8947a284c2031000c54a3a9330/symbolic/src/Data/Macaw/Symbolic/CrucGen.hs#L199-L459).
