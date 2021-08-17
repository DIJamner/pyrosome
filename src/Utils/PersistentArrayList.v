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

(*TODO: move to Utils.v?*)
Fixpoint lookup_assoc_list {A} (default:A) l i : A :=
  match l with
  | nil => default
  | cons (i',a) l' =>
    if eqb i i' then a else lookup_assoc_list default l' i
  end.


Module PArrayList <: (ArrayList Int63Natlike).

  
  Module Import Notations := (NatlikeNotations Int63Natlike).
  
  Record array_rec (A : Type) :=
    MkArr {
        arr : PArray.array A;
        len : int;
        (* Due to PArray.max_length, we store overflow in an association list.
           This allows us to prove theorems about this structure that do not depend on max_length.
           However, users should expect for performance purposes that this list is unused
           since computing with arraylists of sufficient size will probably trigger a stack overflow currently.
         *)
        extra : list (int * A);
      }.

  Arguments MkArr {_}.
  Arguments arr {_}.
  Arguments len {_}.
  Arguments extra {_}.

  Definition array := array_rec.

  (* initial headspace is hardcoded. 
     TODO: profile for best size *)
  Definition make {A} default := MkArr (@make A (32)%int63 default) 0 nil.

  Definition get {A} l i :=
    if i <? max_length
    then if i <? l.(len) then @get A l.(arr) i else default l.(arr)
    else lookup_assoc_list l.(arr).[i] l.(extra) i.

  Definition copy_nth {A} l i (l' : PArray.array A) : PArray.array A :=
    l'.[i <- l.[i]].
  
  Definition copy_up_to {A} (l l' : PArray.array A) : int -> PArray.array A :=
    intrec l (copy_nth l').

  (*TODO: duplicated; refactor*)
  Definition max (x y : int) :=
    if x <=? y then y else x.

  (* len_l is the length of the initiazed segment of l *)
  Definition expand_to_len_parray {A} l old_len new_len : PArray.array A :=
    let backed_len := length l in
    if new_len <? backed_len then l else
      let backed_len' := max (2 * backed_len)%int63 new_len in
      let default := PArray.get l backed_len in
      (copy_up_to (PArray.make backed_len' default) l old_len).
  
  Definition expand_to_contain {A} i '(MkArr l old_len extra) : array A :=
    let new_len := max (i+1) old_len in
    MkArr (expand_to_len_parray l (length l) new_len) new_len extra.    
  
  (* Dynamically grows the array as necessary *)
  Definition set {A} l i (a : A) :=
    let '(MkArr l len_l extra) := (expand_to_contain i l) in
    MkArr (set l i a) len_l (if i<? max_length  then extra else (i,a)::extra).

  Definition length {A} := @len A.
  
  Definition alloc {A} l (a : A) := (l.(len),set l l.(len) a).

End PArrayList.

(* TODO: prove ArrayList properties *)
Module PArrayListProperties : ArrayListSpec Int63Natlike PArrayList.

  Import PArrayList.
  Import Int63Natlike.
  Open Scope int63.

  Module Import Notations :=
    (NatlikeNotations Int63Natlike)
      <+ (ArrayNotations Int63Natlike PArrayList).

  
  Lemma length_copy_nth A (l l' : PArray.array A) i
    : PArray.length (copy_nth l' i l) = PArray.length l.
  Proof.
    unfold copy_nth.
    apply PArray.length_set.
  Qed.

  Lemma peano_rect_length A (l : PArray.array A) f p
    : (forall p l, PArray.length (f p l) = PArray.length l) ->
      PArray.length (Pos.peano_rect _ l f p) = PArray.length l.
  Proof.
    intros.
    revert l.
    revert dependent f.
    induction p; intros; simpl in *; auto.
    all: rewrite ?H;
      rewrite !IHp;
      [ apply H |];
      intros;
      rewrite !H;
      reflexivity.
  Qed.      
    
    
  Lemma length_copy_up_to A (l l' : PArray.array A) i
    : PArray.length (copy_up_to l l' i) = PArray.length l.
  Proof.
    unfold copy_up_to.
    unfold intrec.
    generalize (to_Z i) as z.
    clear i.
    destruct z; unfold posZrec; simpl; auto.
    revert l l'.
    eapply Pos.peano_rect.
    all: intros; simpl in *; auto.
    rewrite peano_rect_length;
      intros; apply length_set.
  Qed.

  

  (*TODO: move to the same place as max*)
  Definition min (x y : int) :=
    if x <=? y then x else y.

  
  Ltac case_order_fn e :=
    let b := fresh "b" in
    let H := fresh "Heqb" in
    remember e as b eqn:H; destruct b; symmetry in H;
    [| let H' := fresh in
       rename H into H';
       assert (~ e = true) as H by (rewrite H'; auto);
       clear H'
    ];
    first [ rewrite leb_le in H
          | rewrite ltb_lt in H
          | rewrite eqb_eq in H];
    try (unfold lt in *; unfold le in *; lia).

  
  Ltac case_match_order_fn :=
    match goal with
    | [|- context[match ?e with _ => _ end]]
      => case_order_fn e
    end.
  
  (*TODO: going to run into max_length here.
    How should I work around? Refinements probably slow in vm_compute.
   *)
  Lemma expand_to_len_parray_length A (l : PArray.array A) old_len new_len
    : le (min new_len max_length) (PArray.length (expand_to_len_parray l old_len new_len)).
  Proof.
    unfold expand_to_len_parray.
    unfold min.
    case_order_fn (new_len <=? max_length).
    {
      case_order_fn (new_len <? PArray.length l).
      rewrite length_copy_up_to.
      rewrite length_make.
      case_order_fn (max (2 * PArray.length l) new_len <=? max_length).
      unfold max.
      case_order_fn (2 * PArray.length l <=? new_len)%int63.
    }
    {
      case_order_fn (new_len <? PArray.length l).
      rewrite length_copy_up_to.
      rewrite length_make.
      case_order_fn (max (2 * PArray.length l) new_len <=? max_length).
      clear Heqb1.
      unfold max.
      case_order_fn ((2 * PArray.length l)%int63 <=? new_len).
    }
  Qed.  
  
  Lemma get_set_same : forall A t i (a:A), t.[i<-a].[i] = a.
  Proof.
    intros A [] i a.
    unfold set.
    unfold get.
    unfold expand_to_contain.
    simpl.
    unfold max.
    
    case_order_fn (i =? max_int).
    {
      unfold eq in *; subst; simpl.
      case_order_fn (0 <=? len0); simpl; auto.
    }
    unfold eq in *.
    case_match_order_fn.
    case_order_fn (i+1 <=? len0).
    case_match_order_fn.
    {
      apply PArray.get_set_same.
      rewrite ltb_lt.
      pose proof (expand_to_len_parray_length _ arr0 (PArray.length arr0) len0).
      revert H.
      unfold min.
      case_match_order_fn.
    }
    {
      unfold lt in *.
      unfold le in *.
      rewrite add_spec in Heqb1.
      rewrite to_Z_1 in Heqb1.
      pose proof (to_Z_bounded i).   
      rewrite Zmod_small in Heqb1; try lia.
      split; try lia. 
      pose proof (fun pf => Heqb (to_Z_inj i max_int pf)).   
      let x := eval vm_compute in (to_Z max_int) in 
          change (to_Z max_int) with x in *.
      let x := eval vm_compute in wB in 
          change wB with x in *.
      lia.
    }
    {
      assert (i <? i + 1 = true).
      {
        rewrite ltb_lt.
        unfold lt in *.
        unfold le in *.
        rewrite add_spec.
        rewrite to_Z_1.
        pose proof (to_Z_bounded i).   
        rewrite Zmod_small; try lia.
        split; try lia. 
        pose proof (fun pf => Heqb (to_Z_inj i max_int pf)).   
        let x := eval vm_compute in (to_Z max_int) in 
            change (to_Z max_int) with x in *.
        let x := eval vm_compute in wB in 
            change wB with x in *.
        lia.
      }
      rewrite H.
      apply PArray.get_set_same.
      rewrite ltb_lt.
      pose proof (expand_to_len_parray_length _ arr0 (PArray.length arr0) (i+1)).
      revert H0.
      unfold min.
      rewrite ltb_lt in H.
      case_match_order_fn; intro.
    }
    {
      simpl.
      rewrite eqb_refl.
      reflexivity.
    }
  Qed.
  

  Lemma get_copy_nth_other A l_src l i j
    : i <> j -> @PArray.get A (copy_nth l_src i l) j = PArray.get l j.
  Proof.
    intros.
    apply get_set_other; auto.
  Qed.

  
  Lemma copy_nth_comm A (l_src1 l_src2 l : PArray.array A) i j
    : i <> j ->
      (copy_nth l_src1 i (copy_nth l_src2 j l))
      = (copy_nth l_src2 j (copy_nth l_src1 i l)).
  Proof.
    intros; unfold copy_nth.
    apply array_ext.
    rewrite !length_set; reflexivity.
    2: rewrite !default_set; reflexivity.
    {
      rewrite !length_set.
      intros.
      case_order_fn (eqb i0 j).
      {
        unfold eq in *; subst.
        rewrite ?PArray.get_set_same;
        [| rewrite length_set; auto].
        rewrite get_set_other; auto.
        rewrite ?PArray.get_set_same; auto.
      }
      case_order_fn (eqb i0 i).
      {
        unfold eq in *; subst.
        rewrite ?PArray.get_set_same;
        [| rewrite length_set; auto].
        rewrite get_set_other; auto.
        rewrite ?PArray.get_set_same; auto.
      }
      {       
        unfold eq in *; subst.
        rewrite !get_set_other; auto.
      }
    }
  Qed.
  
  Lemma get_copy_up_to_in_bounds A i len l l_src
    : lt i len ->
      PArray.get (copy_up_to l l_src len) i
      = @PArray.get A l_src i.
  Proof.
    unfold copy_up_to.
    unfold intrec.
    unfold lt.
    pose proof (to_Z_bounded len) as H.
    revert H.
    generalize (to_Z len).
    clear len.
    intros.
    unfold posZrec.
    destruct z;
      [pose proof (to_Z_bounded i); lia | | lia].
    unfold N.recursion.
    simpl.
    revert dependent i.
    revert H.
    revert l l_src.
    induction p; intros; simpl in *; auto.
    {
      rewrite get_copy_nth_other.
      rewrite copy_nth_comm.
      (*
      TODO: generalize one of the l_srcs?
      generalize the fn? *)
  Admitted.

  
  Lemma get_copy_up_to_out_of_bounds A i len l l_src
    : ~ lt i len ->
      PArray.get (copy_up_to l l_src len) i
      = @PArray.get A l i.
  Proof.
  Admitted.

  Lemma get_expand_parray A (l : PArray.array A) new_len i
    : PArray.get (expand_to_len_parray l (PArray.length l) new_len) i = PArray.get l i.
  Proof.
    unfold expand_to_len_parray.
    case_order_fn (new_len <? PArray.length l).
    reflexivity.
    case_order_fn (i <? PArray.length l).
    rewrite get_copy_up_to_in_bounds; auto.
    rewrite get_copy_up_to_out_of_bounds; auto.
    rewrite get_make.
    rewrite !get_out_of_bounds; auto.
    admit.
    admit.
Admitted.   

    
  Lemma get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
  Proof.
    intros A [] i j a Hij.
    unfold set.
    unfold get.
    unfold expand_to_contain.
    simpl.
    case_order_fn (j <? max_length).
    {
      rewrite PArray.get_set_other; auto.
      case_order_fn (j <? len0).
      {
        assert (j <? max (i + 1) len0 = true).
        {
          rewrite ltb_lt.
          unfold max.
          case_match_order_fn.
        }
        rewrite H.
        rewrite get_expand_parray; auto.
      }
      {
        case_match_order_fn.
        {
          rewrite get_expand_parray.
          rewrite !get_out_of_bounds; auto.
          admit.
        }
        rewrite default_set.
        admit (*TODO: default lemma*).
      }
    }
    {
      admit (*TODO*).
    }
  Admitted.
          
  
  Lemma get_make : forall A (a:A) i, (make a).[i] = a.
  Proof.
    unfold get.
    unfold make.
    intros.
    repeat (case_match_order_fn; simpl; auto).
    admit (*easy*).
    admit (*easy*).
  Admitted.

  Lemma get_alloc_same
    : forall A l (a:A) l' i,
      (i,l') = alloc l a ->
      l'.[i] = a.
  Proof.
    intros A l a l' i.
    unfold alloc.
    intro H; inversion H; subst.
    apply get_set_same.
  Qed.

  Lemma alloc_fresh
    : forall A l (a:A) l' i,
      (i,l') = alloc l a ->
      (exists i', lt (length l) i') ->
      i = (length l).
  Proof.
    intros A l a l' i.
    unfold alloc.
    intro H; inversion H; subst; clear H.
    destruct l; simpl.
    rewrite <- eq_max_int_no_greater.
    intros.
    unfold max.
    reflexivity.
  Qed.    

  Lemma max_comm a b : max a b = max b a.
  Proof.
    unfold max; repeat case_match_order_fn;
    unfold le in *; apply to_Z_inj; lia.
  Qed.    
  
  Lemma length_set :
    forall A t i (a : A),
      length t.[i <- a] = max (length t) (i.+1).
  Proof.
    intros A [] i a; unfold set; unfold length; simpl.
    apply max_comm.
  Qed.

  
  (*TODO: move to the right place*)
  Definition max (x y : int) :=
    if x <=? y then y else x.


  Lemma length_make : forall A (a:A), length (make a) = zero.
  Proof.
    intros; reflexivity.
  Qed.

  (*
   *
   *
   *
   *
   *
   

  
  (*Testing*)

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
   *)

End PArrayListProperties.
  

