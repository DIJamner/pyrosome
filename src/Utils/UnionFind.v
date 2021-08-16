(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.
*)
Require Import Equalities Orders ZArith.

Require Int63 PArray.

Module Type HasT.
  Parameter t : Type.
End HasT.

Module Type ArrayListOps (Idx : HasT).

  Parameter array : Type -> Type.

  (* Since the arrays are dynamically extensible,
     make does not need a size
   *)
  Parameter make : forall {A}, A -> array A.
  
  Parameter get : forall {A}, array A -> Idx.t -> A.

  (* Sets a index to a new value if that index is less than max_length.
     Can extend the array.

     TODO: profile performance of PArray implementation to decide whether
     a non-extending version is worth adding to the interface
   *)
  Parameter set : forall {A}, array A -> Idx.t -> A -> array A.

  Parameter length : forall {A}, array A -> Idx.t.
  
  Parameter alloc : forall {A}, array A -> A -> Idx.t * array A.

End ArrayListOps.

Module Type NatLike (Idx : EqLtLe).

  Include OrderFunctions Idx.

  Parameter zero : Idx.t.
  
  Parameter succ : Idx.t -> Idx.t.

  Parameter isTop : Idx.t -> bool.

  Axiom zero_spec
    : forall a, Idx.le zero a.

  Axiom succ_greater
    : forall a,
      (exists b, Idx.lt a b) ->
      Idx.lt a (succ a).
  
  Axiom succ_least
    : forall a b,
      Idx.lt a b ->
      Idx.le (succ a) b.

  Axiom isTop_spec
    : forall a,
      isTop a = false
      <-> (exists b, Idx.lt a b).

End NatLike.

(*Copied and modified from primitive arrays*)
Module ArrayNotations
       (Idx : EqLtLe)
       (Import IdxFns : NatLike Idx)
       (Import AO : (ArrayListOps Idx)).
  Delimit Scope array_scope with array.
  Notation "t .[ i ]" :=
    (get t i)
      (at level 2, left associativity, format "t .[ i ]").
  Notation "t .[ i <- a ]" :=
    (set t i a)
      (at level 2, left associativity, format "t .[ i <- a ]").
  Notation "'new!' a :: t" :=
    (alloc t a)
      (at level 60, right associativity, format "new! a :: t").
  
  Infix "=?" := eqb (at level 70, no associativity).
  Infix "<?" := ltb (at level 70, no associativity).
  Infix "<=?" := leb (at level 70, no associativity).
  Notation "i .+1" := (succ i) (at level 70, no associativity).
End ArrayNotations.

Module Type ArrayListSpec 
       (Idx : EqLtLe)
       (Import IdxFns : NatLike Idx)
       (Import AO : (ArrayListOps Idx)).

  Module Import N := (ArrayNotations Idx IdxFns AO).

  Axiom get_set_same : forall A t i (a:A), t.[i<-a].[i] = a.
  Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
  
  Axiom get_make : forall A (a:A) i, (make a).[i] = a.

  Axiom get_alloc_same
    : forall A l (a:A) l' i,
      (i,l') = alloc l a ->
      l'.[i] = a.

  Axiom alloc_fresh
    : forall A l (a:A) l' i,
      (i,l') = alloc l a ->
      (exists i', Idx.lt (length l) i') ->
      Idx.lt (length l) i.

  (*TODO: move to the right place*)
  Definition max (x y : Idx.t) :=
    if x <=? y then y else x.

  Axiom length_set :
    forall A t i (a : A),
      length t.[i <- a] = max (length t) (i.+1).

  Axiom length_make : forall A (a:A), length (make a) = zero.

  (*TODO: rest of array axioms as necessary *)
  
End ArrayListSpec.  

Module Int63EqLtLe <: EqLtLe.
  
  Import Int63.
  Definition t := int.
  Definition eq : int -> int -> Prop := @eq int.
  Definition lt x y := BinInt.Z.lt φ (x)%int63 φ (y)%int63.
  Definition le x y := BinInt.Z.le φ (x)%int63 φ (y)%int63.

End Int63EqLtLe.



Import Int63 Lia.

Lemma max_int_greatest
  : forall a, Int63EqLtLe.le a max_int.
Proof.
  unfold Int63EqLtLe.le.
  intro a.
  let x := eval vm_compute in  φ (max_int)%int63 in 
      change ( φ (max_int)%int63) with x.
  pose proof (to_Z_bounded a).
  let x := eval vm_compute in  wB in 
      change wB with x in H.
  lia.
Qed.

Module Int63Fns <: NatLike Int63EqLtLe.

  Import Int63 Int63EqLtLe.
  Definition compare := compare.
  
  Lemma compare_spec :
    forall x y : int, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros.
    rewrite compare_spec.
    unfold eq.
    destruct (BinInt.Z.compare_spec φ (x)%int63 φ (y)%int63); auto using to_Z_inj.
  Qed.

  Definition eqb := eqb.
  Definition ltb := ltb.
  Definition leb := leb.
  
  Definition eqb_eq : forall x y : int, eqb x y = true <-> eq x y := eqb_spec.
  Definition ltb_lt : forall x y : int, ltb x y = true <-> lt x y := ltb_spec.
  Definition leb_le : forall x y : int, leb x y = true <-> le x y := leb_spec.

  Definition zero : int := 0.

  Definition succ : int -> int := succ.

  Definition isTop i :=
    eqb i max_int.

  Lemma zero_spec : forall i, le zero i.
  Proof.
    apply to_Z_bounded.
  Qed.

  Lemma eq_max_int_no_greater
    : forall a,
      a <> max_int
      <-> (exists b, lt a b).
  Proof.
    split; intros.
    {
      exists max_int.
      unfold lt.
      pose proof (fun p => H (to_Z_inj _ _ p)).
      change (?a -> False) with (not a) in H0.
      pose proof (max_int_greatest a).
      unfold le in*.
      lia.
    }
    {
      unfold lt in *.
      firstorder.
      intro.
      subst.
      pose proof (max_int_greatest x).
      unfold le in *.
      lia.
    }
  Qed.
  
  Lemma neq_max_int_lt
    : forall a,
      a <> max_int
      <-> lt a max_int.
  Proof.
    intro a.
    rewrite eq_max_int_no_greater.
    unfold lt; split; [ intros [b H] | exists max_int; auto].
    pose proof (max_int_greatest b).
    unfold le in *.
    lia.
  Qed. 

  Lemma isTop_spec
    : forall a,
      isTop a = false
      <-> (exists b, lt a b).
  Proof.
    intro a.
    rewrite <- eq_max_int_no_greater.
    remember (isTop a) as b.
    unfold isTop in *.
    destruct b; split; try intuition congruence.
    {
      symmetry in Heqb.
      rewrite eqb_eq in Heqb.
      unfold eq in *.
      subst.
      tauto.
    }
    {
      intros _.
      intro Heq; rewrite <- eqb_eq in Heq.
      rewrite Heq in Heqb.
      inversion Heqb.
    }
  Qed.
  
  Lemma succ_greater
    : forall a,
      (exists b, lt a b) ->
      lt a (succ a).
  Proof.
    intro a.
    rewrite <- eq_max_int_no_greater.
    rewrite neq_max_int_lt.
    unfold lt.
    rewrite succ_spec.
    intros.
    rewrite Z.mod_small.
    lia.
    let x := eval vm_compute in  φ (max_int)%int63 in 
        change ( φ (max_int)%int63) with x in H.
    pose proof (to_Z_bounded a).
    let x := eval vm_compute in  wB in 
        change wB with x.
    lia.
  Qed.
  
  Lemma succ_least
    : forall a b,
      lt a b ->
      le (succ a) b.
  Proof.
    unfold lt.
    unfold le.
    unfold succ.
    unfold Int63.succ.
    intros.
    rewrite add_spec.
    pose proof (to_Z_bounded a).
    rewrite to_Z_1.
    pose proof (Z.mod_le (φ (a)%int63 + 1) wB ltac:(lia) wB_pos).
    lia.
  Qed.

End Int63Fns.

(*TODO: right place for this?*)
Import Int63.
Import Int63EqLtLe.
Require Import ZArith.


(*TODO: small inefficiency by going through N.recursion*)
Definition posZrec {A} base rec z : A :=
  let rec' n := rec (Z.of_N n) in
  match z with
  | Zpos p => N.recursion base rec' (Npos p)
  | _ => base
  end.


(* TODO: check the inefficiency due to converting Z to int at each iteration *)
Definition intrec {A} base rec i : A :=
  let rec' z := rec (of_Z z) in
  posZrec base rec' (to_Z i).


Import Int63 PArray.

Compute max_length.
Compute max_int.
Compute (max_int/max_length)%int63.

Module PArrayListOps <: (ArrayListOps Int63EqLtLe).

  Import Int63 PArray.
  
  Record array_rec (A : Type) :=
    MkArr {
        arr : PArray.array A;
        len : int
      }.
  Definition array := array_rec.
  Arguments MkArr {_}.
  Arguments arr {_}.
  Arguments len {_}.

  (* initial size is hardcoded *)
  Definition make {A} default := MkArr (@make A (4)%int63 default) 0.

  Definition get {A} l := @get A l.(arr).

  Definition copyNth {A} l i (l' : PArray.array A) : PArray.array A :=
    l'.[i <- l.[i]].
  
  (* TODO: this one is tricky. Make sure it computes nicely *)
  Definition copyUpTo {A} (l l' : PArray.array A) : int -> PArray.array A :=
    intrec l (copyNth l').

  (*TODO: duplicated; refactor*)
  Definition max (x y : int) :=
    if leb x y then y else x.

  (*TODO: separate order notations so that I can use them here*)
  Definition expandToContain {A} i '(MkArr l len_l) : array A :=
    let backed_len := length l in
    if ltb i backed_len then MkArr l (max i len_l)
    else
      let backed_len' := max (2 * backed_len)%int63 i in
      let default := PArray.get l backed_len in
      MkArr (copyUpTo (PArray.make backed_len' default) l len_l) i.    
  
  (* Dynamically grows the array as necessary *)
  Definition set {A} l i (a : A) :=
    let '(MkArr l len_l) := (expandToContain (i+1) l) in
    MkArr (set l i a) len_l.

  Definition length := @len.
  
  Definition alloc {A} l (a : A) := (l.(len),set l l.(len) a).

End PArrayListOps.

(*Testing*)
Import PArrayListOps.
Module Import N := (ArrayNotations Int63EqLtLe Int63Fns PArrayListOps).

Compute make 4.
Time Compute
  let '(_,l) := (alloc (make 3) 2) in
  let '(_,l) := (alloc l 2) in
  let '(_,l) := (alloc l 2) in
  let '(_,l) := (alloc l 2) in
  let '(_,l) := (alloc l 2) in
  l.
Time Compute (expandToContain 2 (make 4)).[6555 <- 5]%int63.


Compute (make 4).[5 <- 5]%int63.
(*TODO: needs to be instant*)
Compute (make 4).[33 <- 5]%int63.
