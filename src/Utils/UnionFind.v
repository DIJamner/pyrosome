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


(* All definitions and proofs need to be generic over arraylist implementations.
   Use the following code to test functions with a specific implementation: *)

Module UnionFind
       (* TODO: can't abstract for now due to issue #14849
       (Import NL : Natlike)
       (Import AL : ArrayList NL)*).
  (*Temporary imports*)
  From Utils Require PersistentArrayList.
  Module NL := PersistentArrayList.Int63Natlike.
  Module AL := PersistentArrayList.PArrayList.
  
  Module Ntns := (ArrayNotations NL AL).
  Import NL AL Ntns.

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
    (MkUF ra pa.[i<-i] mr, i).

  Definition find_aux
    : t -> array t -> t -> array t * t :=
    iter
      (fun f i => (f,i))
      (fun find_aux f i =>         
      let fi := f.[i] in
      if eqb fi i then
        (f,i)
      else
        let (f, r) := find_aux f fi in
        let f := f.[i<-r] in
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
      let rx := ra.[cx] in
      let ry := ra.[cy] in
      if ltb ry rx then
        (MkUF ra pa.[cy <- cx] mr, cx)
      else if ltb rx ry then
             (MkUF ra pa.[cx <- cy] mr, cy)
           else
             (MkUF ra.[cx <- succ rx]
                  pa.[cy <- cx]
                       (max mr (succ rx)), cx).
End UnionFind.

(*TODO*)
Module UnionFindSpec
       (Import NL : Natlike)
       (Import AL : ArrayList NL)
       (Import ALS : ArrayListSpec NL AL).
End UnionFindSpec.

(*Testing *)
From Utils Require PersistentArrayList.

Module UF63 := UnionFind.
Import Int63 UF63.
Import UF63.Ntns.


Time Eval vm_compute in
     let uf :=N.recursion empty
                          (fun _  uf =>
                             let (uf, i) := alloc uf in
                             if ltb i 10 then uf else
                               let (uf,_) := union uf i (sub i 10) in
                               uf)
                          100000 in
     snd (find uf 64828%int63).

  
