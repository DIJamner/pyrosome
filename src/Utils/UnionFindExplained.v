(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.

   based on this paper:
   Sylvain Conchon and Jean-Christophe Filliâtre. A persistent union-find data structure.
   In ACM SIGPLAN Workshop on ML, 37–45. Freiburg, Germany, October 2007. ACM Press.
   URL: https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf.


TODO: explanation implementation may not be optimal.
Review it next to existing literature:
Robert Nieuwenhuis and Albert Oliveras. Proof-producing congruence closure. 2005.
https://www.cs.upc.edu/~oliveras/rta05.pdf
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
  (* TODO: figure out what features explanations need *)
  Context {expl : Type}
    (*TODO: this doesn't work so well w/ current proof structure
      since reflexivity requires the term as input.
      Fixing this ties into ideas around putting the proof terms in the egraph
     *)
    (refl : expl)
    (symmetry : expl -> expl)
    (transitivity : expl -> expl -> expl).

  Notation zero := (zero : idx).

  (*TODO: make notations use ops*)
  (*Module Ntns := (ArrayNotations NL AL).
  Import NL AL Ntns.
   *)

  Record union_find :=
    MkUF {
        rank : array idx;
        parent : array idx;
        explanation : array expl;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : idx
      }.

  Definition length uf := length uf.(parent).
  
  Definition empty : union_find :=
    MkUF (make zero) (make zero) (make refl) zero.

  (*TODO: write w/ state monad for clarity?*)
  Definition alloc '(MkUF ra pa ea mr) :=
    let (i,pa) := alloc pa zero in
    (*We don't need to initialize rank since default of 0 is correct
      the same goes for explanations
     *)
    (MkUF ra (set pa i i) ea mr, i).
  
  (*TODO: need to modify the explanation*)
  Definition find_aux
    : idx -> array idx -> array expl -> idx -> array idx * array expl * idx :=
    iter
      (fun f e i => (f,e, i))
      (fun find_aux f e i =>         
      let fi := get f i in
      if eqb fi i then
        (f,e, i)
      else
        let '(f, e, r) := find_aux f e fi in
        let f := set f i r in
        let e := set e i (transitivity (get e i) (get e fi)) in
        (f,e,r)
      ).
  

  Definition find '(MkUF ra pa ea mr) x :=
    let '(f,ea,cx) := find_aux mr pa ea x in
    (MkUF ra f ea mr, cx).

  Definition get_expl '(MkUF ra pa ea mr) x :=
    get ea x.
  
  Definition explain uf x y :=
    let '(uf, fx) := find uf x in
    let '(uf, fy) := find uf y in
    if eqb fx fy
    then Some (transitivity (get_expl uf x) (symmetry (get_expl uf y)))
    else None.
  
  
  (*TODO: move to the right place*)
  Definition max (x y : idx) :=
    if leb x y then y else x.

  (*TODO: check explanation works*)
  Definition union h x y expl :=
    let (h, cx) := find h x in
    let (h, cy) := find h y in
    if eqb cx cy then (h, cx) else
      let (ra, pa, ea, mr) := h in
      let rx := get ra cx in
      let ry := get ra cy in
      if ltb ry rx then
        (MkUF ra (set pa cy cx)
           (set ea cy (symmetry expl))
           mr, cx)
      else if ltb rx ry then
             (MkUF ra (set pa cx cy) 
                (set ea cy expl)
                mr, cy)
           else
             (MkUF (set ra cx (succ rx))
                  (set pa cy cx)
                  (set ea cy (symmetry expl))
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
  
