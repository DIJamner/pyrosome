# Build / Kick-the-tires

This project has been validated against Rocq 9.1.
There are 2 ways to set up your environment: use an existing Rocq 9.1 install
or use `nix-shell` from the top-level `pyrosome` directory on a system that supports it.
The easiest way to install Rocq is to use `opam` (https://rocq-prover.org/docs/using-opam).
Once you have Rocq available, run `make -jN` in the top-level directory to build the project,
where `N` is the number of threads to use. This project benefits substantially from
parallel builds, so higher `N` is likely to build much faster, especially for `N <= 4`.
There are some files that take a while to build, so don't be surprised if building takes
an hour or more the first time, especially with low `N`.

# Contents

The file [PAPER_MAP.md](PAPER_MAP.md) contains a table mapping definitions and theorems
from the paper to their corresponding code in this artifact.


# Reusability

To demonstrate the reusability of this work, try adding a new feature.
As the simplest possible example, the file `pyrosome/src/Pyrosome/Lang/SimpleVProd.v`
defines a product type with 2 projections. Make a copy of that file and
add an extra component to the tuples, turning it from pairs into triples,
and a corresponding projection. The `compute_wf_lang` tactic uses the
e-graph machinery described in this paper to compute equivalence between types.
We invite the reviewers to test more complex examples, for example additional compilers,
but do not include explicit instructions here as such examples would be more involved.

Note that the above examples are primarily Pyrosome examples. However, as our e-graphs
are now the default automation in Pyrosome, we believe that they still reflect the
reusability of our contributions.