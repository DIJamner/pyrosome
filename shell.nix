{ pkgs ? import <nixpkgs> {},
  native-enabled ? false
}:

with pkgs;mkShell {
  buildInputs = if native-enabled
                then [
                  #Note: must use coq form opam because native_compute doesn't work well with the nix version
                  #coq_8_20
                  linuxPackages.perf
                  opam
                  pkg-config
                  gcc
                  bintools-unwrapped
                  gmp
                ]
                else [ coq_8_20  ];
  shellHook = if native-enabled
              then "eval $(opam env)"
              else "";
}
