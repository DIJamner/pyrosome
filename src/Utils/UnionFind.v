(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.

   based on this paper:
   Sylvain Conchon and Jean-Christophe Filliâtre. A persistent union-find data structure.
   In ACM SIGPLAN Workshop on ML, 37–45. Freiburg, Germany, October 2007. ACM Press.
   URL: https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf.
*)
Require Import Equalities Orders ZArith.

From Utils Require Import Natlike ArrayList.
Import Natlike.Ops ArrayList.Ops.



(* Use typeclasses since passing some instances to functors breaks the VM
   (issue #12519)
 *)
Section UnionFind.
  Context {t : Type}
          {idx_ops : NatlikeOps t}
          {array : Type -> Type}
          {array_ops : ArrayListOps t array}.

  (*TODO: make notations use ops*)
  (*Module Ntns := (ArrayNotations NL AL).
  Import NL AL Ntns.
   *)

  Record union_find :=
    MkUF {
        rank : array t;
        parent : array t;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : t
      }.

  Definition length uf := length uf.(parent).
  
  Definition empty : union_find :=
    MkUF (make zero) (make zero) zero.

  (*TODO: write w/ state monad for clarity?*)
  
  Definition alloc '(MkUF ra pa mr) :=
    let (i,pa) := alloc pa zero in
    (*We don't need to initialize rank since default of 0 is correct*)
    (MkUF ra (set pa i i) mr, i).

  Definition find_aux
    : t -> array t -> t -> array t * t :=
    iter
      (fun f i => (f,i))
      (fun find_aux f i =>         
      let fi := get f i in
      if eqb fi i then
        (f,i)
      else
        let (f, r) := find_aux f fi in
        let f := set f i r in
        (f,r)
      ).

  Definition find '(MkUF ra pa mr) x :=
    let (f,cx) := find_aux mr pa x in
    (MkUF ra f mr, cx).

  
  (*TODO: move to the right place*)
  Definition max (x y : t) :=
    if leb x y then y else x.

  (*TODO: needs to return the root id*)
  Definition union h x y :=
    let (h, cx) := find h x in
    let (h, cy) := find h y in
    if eqb cx cy then (h, cx) else
      let (ra, pa, mr) := h in
      let rx := get ra cx in
      let ry := get ra cy in
      if ltb ry rx then
        (MkUF ra (set pa cy cx) mr, cx)
      else if ltb rx ry then
             (MkUF ra (set pa cx cy) mr, cy)
           else
             (MkUF (set ra cx (succ rx))
                  (set pa cy cx)
                       (max mr (succ rx)), cx).
End UnionFind.

(*TODO*)
Module UnionFindSpec
       (Import NL : Natlike)
       (Import AL : ArrayList NL)
       (Import ALS : ArrayListSpec NL AL).
End UnionFindSpec.


(* All definitions and proofs need to be generic over arraylist implementations.
   Use the following code to test functions with a specific implementation: *)

(*Testing *)
From Utils Require Import PersistentArrayList.
#[local] Existing Instance PArrayList.arraylist_ops.
#[local] Existing Instance Int63Natlike.natlike_ops.

Import Int63.

Time Eval vm_compute in
     let uf :=N.recursion empty
                          (fun _  uf =>
                             let (uf, i) := alloc uf in
                             if ltb i 10 then uf else
                               let (uf,_) := union uf i (sub i 10) in
                               uf)
                          100000 in
     snd (find uf 64828%int63).

  
