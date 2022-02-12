Must be built with Coq 8.14 or higher.

You can clone this repository with

    git clone --recursive https://github.com/dijamner/pyrosome

Git submodules are used for some dependencies. If you did not clone with `--recursive`, run

    git submodule update --init --recursive

from inside the repository.

To build the project, run `./build.sh <t>` where `<t>` is the number of threads to use.


Important/representative files:

Metatheory:
Term.v - contains basic term syntax definitions
Rule.v - contains basic rule and language syntax definitions
Core.v - contains judgment forms and monotonicity properties
CompilerDefs.v - contains definitions related to compiler metatheory
Compilers.v - contains the proof of the inductive-implies-semantic theorem

Case Study:
SimpleVSubst.v - the substitution calculus
SimpleVCPS.v - the CPS transformation for STLC
SimpleVCC.v - the core closure conversion pass
SimpleVCPSHeap.v - the CPS transformation for heap operations
CombinedThm.v - The combined corectness result about the full compiler