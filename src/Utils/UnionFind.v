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

From Utils Require Import Utils Natlike ArrayList.



(* Use typeclasses since passing some instances to functors breaks the VM
   (issue #12519)
 *)
Section UnionFind.
  
  Context {idx : Type}
          `{Natlike idx}
          {array : Type -> Type}
          `{ArrayList idx array}.

  Notation zero := (zero : idx).

  (*TODO: make notations use ops*)
  (*Module Ntns := (ArrayNotations NL AL).
  Import NL AL Ntns.
   *)

  Record union_find :=
    MkUF {
        rank : array idx;
        parent : array idx;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : idx
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
    : idx -> array idx -> idx -> array idx * idx :=
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
  Definition max (x y : idx) :=
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
Class UnionFind_ok := {}.


(* All definitions and proofs need to be generic over arraylist implementations.
   Use the following code to test functions with a specific implementation: *)

(*Testing *)
(*
#[local] Existing Instance PArrayList.arraylist_ops.
#[local] Existing Instance Int63Natlike.natlike_ops.
*)

Module Int63UnionFind.

  Require Import Int63 ZArith.
  From Utils Require Import PersistentArrayList.

  Axiom TODO : forall A, A.
  
  #[refine] Instance int63eqb : Eqb int := { eqb := Int63Natlike.eqb}.
  exact Int63Natlike.eqb_eq.
  apply TODO.  apply TODO.
  exact Int63Natlike.eq_dec.
  Defined.

  Instance natlike_int63 : Natlike int :=
    {
      natlike_eqb := int63eqb;
      ltb := Int63Natlike.ltb;
      leb := Int63Natlike.leb;
      zero := Int63Natlike.zero;
      succ := Int63Natlike.succ;
      is_top := Int63Natlike.is_top;
      iter := @Int63Natlike.iter;
    }.

  Instance arraylist_parraylist : ArrayList int PArrayList.array :=
    {
    make := @PArrayList.make;
    get := @PArrayList.get;
    set := @PArrayList.set;
    length := @PArrayList.length;
    alloc := @PArrayList.alloc;
    }.

  (* takes around 7s
  Time Eval vm_compute in
    let uf :=N.recursion empty
                         (fun _  uf =>
                            let (uf, i) := alloc uf in
                            if ltb i 10 then uf else
                              let (uf,_) := union uf i (sub i 10) in
                              uf)
                         1000000 in
    snd (find uf 604828%int63).
   *)

End Int63UnionFind.
  
