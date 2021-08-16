Require Import Orders ZArith Int63 PArray Lia.

From Utils Require Import Natlike ArrayList.

Module Int63Natlike <: Natlike.

  Definition t := int.
  Definition eq : int -> int -> Prop := @eq int.
  Definition lt x y := BinInt.Z.lt φ (x)%int63 φ (y)%int63.
  Definition le x y := BinInt.Z.le φ (x)%int63 φ (y)%int63.
  
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

  
  Lemma max_int_greatest
    : forall a, le a max_int.
  Proof.
    unfold le.
    intro a.
    let x := eval vm_compute in  φ (max_int)%int63 in 
        change ( φ (max_int)%int63) with x.
    pose proof (to_Z_bounded a).
    let x := eval vm_compute in  wB in 
        change wB with x in H.
    lia.
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

End Int63Natlike.


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


Module PArrayList <: (ArrayList Int63Natlike).
  
  Record array_rec (A : Type) :=
    MkArr {
        arr : PArray.array A;
        len : int
      }.

  Arguments MkArr {_}.
  Arguments arr {_}.
  Arguments len {_}.

  Definition array := array_rec.

  (* initial headspace is hardcoded. 
     TODO: profile for best size *)
  Definition make {A} default := MkArr (@make A (32)%int63 default) 0.

  Definition get {A} l := @get A l.(arr).

  Definition copyNth {A} l i (l' : PArray.array A) : PArray.array A :=
    l'.[i <- l.[i]].
  
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

End PArrayList.

(* TODO: prove ArrayList properties *)

(*Testing*)
Import PArrayList.
Module Import N := (ArrayNotations Int63Natlike PArrayList).

Open Scope int63.
Compute make 4.
Time Compute
  let '(_,l) := (alloc (make 3) 2) in
  let '(_,l) := (alloc l 2) in
  let '(_,l) := (alloc l 2) in
  let '(_,l) := (alloc l 2) in
  let '(_,l) := (alloc l 2) in
  l.
Time Compute (make 0).[6555 <- 5]%int63.

