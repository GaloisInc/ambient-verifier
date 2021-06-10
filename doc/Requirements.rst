Scenario
========

Our work on this project is focused on evaluating the impact of an embedded Weird Machine (WM) on the execution of a program. In particular, we would like to compare the behavior of a program containing a WM (with a corresponding input to trigger it) to the behavior of the same program without that WM (e.g., under a non-triggering input or after a patch has removed the WM).

Requirements
============

The verifier will take three arguments: a set of user-provided requirements, a target binary, and an input that triggers (or does not trigger) the Weird Machine.

- Verify that a program (with or without a Weird Machine) satisfies a set of requirements (provided by users of the tool)
- Reason about the behavior and side effects of Weird Machines embedded in a program
- Support Weird Machines that require interaction with the program to trigger (via multiple I/O sources, environment variables, and more)
- Reason about the behavioral difference between a program with and without a Weird Machine (i.e., it is patched out)
- Support dynamically-linked binaries (with calls into shared libraries fully-executed)
- Support for Windows
- Ensure that the WM can be (or cannot be) triggered under different environmental configurations (e.g., operating system configurations)

Note that neither the format nor scope of requirements has been determined. Simple properties like "does not crash" are certainly in scope.

Team Interactions
=================

- We can (and should) communicate with the dynamic testing team which requirements we cannot verify (and provide any scoping we can to narrow the search space for their approach)
