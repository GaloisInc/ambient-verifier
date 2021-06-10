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
3. Symbolically execute the program with the concrete input provided to trigger the weird machine
   - This will consume input *and* generate output
   - Symbolic branching in this phase would be potentially problematic for managing the state of the input generator (but we *can* split inputs---outputs are trickier)
   - Simulate until we get to the weird machine (it may be very useful to have it labeled)
   - Save the state of the input and output channels (environment) at each function entry (granularity to be evaluated)
4. Translate the user-provided requirements into quantified/labeled assertions
   - We can start with some trivial requirements
5. Instantiate each assertion at the necessary program locations (based on label)
   - The boundaries at which we do this are TBD, but would match the granularity of the saved states from step 3
   - Likely something like acyclic superblocks
   - The assertions will become block postconditions to be proved
   - The collected state from step 3 (along with other state information like aliasing information) will be preconditions assumed
   - The other state information should be generated in a top-down and bottom-up traversal of the program that propagates *demand* and the necessary context to satisfy that demand
6. Verify that the postconditions hold

Later (hopefully in Phase 2), we can look at the problem of establishing (conditional) behavioral equivalence after the weird machine returns. This is a relational verification problem and could be addressed by extending the pate verifier build for AMP.



