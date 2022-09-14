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

Require Import List Int63 ZArith.
Import ListNotations.
Open Scope int63.
From Utils Require Import Utils Natlike ArrayList PersistentArrayList.
Import PArrayList (array, length).

(*TODO: move these instances to the right places*)
#[refine] Instance int63eqb : Eqb int := { eqb := Int63Natlike.eqb}.
exact Int63Natlike.eqb_eq.
exact Uint63.eqb_false_spec.
exact Uint63.eqb_refl.
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

Instance arraylist_parraylist : ArrayList int array :=
  {
    make := @PArrayList.make;
    get := @PArrayList.get;
    set := @PArrayList.set;
    length := @PArrayList.length;
    alloc := @PArrayList.alloc;
  }.

Notation make := (make (ArrayList := arraylist_parraylist)).



(* Use typeclasses since passing some instances to functors breaks the VM
   (issue #12519)
 *)
Section UnionFind.

  (*TODO: what to instantiate this with?
    I'm tempted to keep this data in egraph nodes
 
  Context (pf : Type)
    (pf_symmetry : pf -> pf).
   *)
  Definition pf : Set := int + int.
  Definition pf_symmetry (a : pf) :=
    match a with
    | inl i => inr i
    | inr i => inl i
    end.

  Definition expl := list pf.

  Definition refl : expl := [].
  Definition symmetry (e : expl) := rev e.
  Definition transitivity : expl -> expl -> expl := @app _.

  (*TODO: make notations use ops*)
  (*Module Ntns := (ArrayNotations NL AL).
  Import NL AL Ntns.
   *)

  Record union_find :=
    MkUF {
        rank : array int;
        parent : array int;
        explanation : array expl;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : int
      }.

  Definition length uf := length uf.(parent).
  
  Definition empty : union_find :=
    MkUF (make 0) (make 0) (make refl) 0.

  (*TODO: write w/ state monad for clarity?*)
  Definition alloc '(MkUF ra pa ea mr) :=
    let (i,pa) := alloc pa zero in
    (*We don't need to initialize rank since default of 0 is correct
      the same goes for explanations
     *)
    (MkUF ra (set pa i i) ea mr, i).
  
  Definition find_aux
    : int -> array int -> array expl -> int -> array int * array expl * int :=
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
  Definition max (x y : int) :=
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


