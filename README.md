# Build

Tested with Coq 8.20, but may work with other versions.

You can clone this repository with

    git clone --recursive https://github.com/dijamner/pyrosome

Git submodules are used for some dependencies. If you did not clone with `--recursive`, run

    make clone_all

from inside the repository.

Once the necessary dependencies are cloned, run `make -jN` to build the project,
where `N` is the number of threads to use. This project benefits substantially from
parallel builds, so higher `N` is likely to build much faster, especially for `N <= 4`.
There are some files that take a while to build, so don't be surprised if building takes
an hour or more the first time, even with high `N`.

# Issues

This project is in active (and early) development, so if you use it you will run into situations
that we either have not yet addressed or have not documented the solutions to.
If you encounter a feature that you want to have or any bugs (including user-facing tactics with
poor error messages), please reach out or just submit an issue on this repository.

# Organization

The source code is split into a `Utils` folder that contains generic library features such
as properties of lists and some useful typeclasses, and a `Pyrosome` folder that contains
all of the code specific to this project. Here's an incomplete outline of the `Pyrosome` directory:

## Theory

- Term.v contains basic term syntax definitions
- Rule.v contains basic rule and language syntax definitions
- Core.v contains judgment forms and monotonicity properties

## Compilers

- CompilerDefs.v contains definitions related to compiler metatheory
- Compilers.v contains the proof of the central inductive-implies-semantic theorem

## Elab

- Elab.v contains an elaboration judgment for use in filling in object-language implicits
- ElabCompilers.v is like Elab.v, but for compiler correctness

## Tools

- Matches.v contains most of the tactics for working with Pyrosome judgments

## Lang
- PolySubst.v contains code that generates simply-typed and polymorphic substitution calculi
- Subst.v contains a dependently-typed substitution calculus
- SimpleVCPS.v contains the CPS transformation for STLC
- SimpleVCC.v contains the core closure conversion pass
- SimpleVCPSHeap.v contains the CPS transformation for heap operations
- CombinedThm.v contains the combined corectness result about the simply-typed case study compiler
- PolyCompilers.v contains the polymorphic extensions and the final theorem about the polymorphic compiler.