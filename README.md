# Build / Kick-the-tires

This project has been validated against Rocq 9.1.
There are 3 ways to set up your environment: use an existing Rocq 9.1 install,
use `nix-shell` from the top-level `pyrosome` directory on a system that supports it,
or use the included VM image (instructions for which are below).
The easiest way to install Rocq is to use `opam` (https://rocq-prover.org/docs/using-opam).
Once you have Rocq available, run `make -jN` in the top-level directory to build the project,
where `N` is the number of threads to use. This project benefits substantially from
parallel builds, so higher `N` is likely to build much faster, especially for `N <= 4`.
There are some files that take a while to build, so don't be surprised if building takes
an hour or more the first time, especially with low `N`.

# Contents

The file [PAPER_MAP.md](PAPER_MAP.md) contains a table mapping definitions and theorems
from the paper to their corresponding code in this artifact.

# VM

The VM is a QEMU x86_64 NixOS image with Rocq 9.1 and its Stdlib, and a small
Xfce desktop with Emacs and Proof General.
You can install QEMU from your package manager (e.g. homebrew on MacOS)
or from here: https://www.qemu.org/download/.
To launch the VM with recommended settings, run `./artifact/out/run_quemu.sh`.
Note that since this is an x86_64 VM, it may run slowly on ARM devices.

- Login: user `artifact`, password `artifact`. Both the desktop and the
  console log in automatically.
- Resources: allocate at least 8 GB RAM. 4 cores are recommended, but 1 is enough.

To step through a proof interactively, use the terminal that opens on the
desktop at login and run `emacs` on a file, e.g.
`emacs src/Pyrosome/Theory/Core.v &`. Proof General needs the generated
`_CoqProject` and compiled dependencies, so run `make -jN` first.

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