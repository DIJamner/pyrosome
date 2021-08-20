Require Import Orders ZArith Int63 PArray Lia.

From Utils Require Import Natlike ArrayList.

Require Import Ltac2.Ltac2.
Import Ltac2.Message Ltac2.Control.
Set Default Proof Mode "Classic".

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


  
  (*TODO: move to a better location*)

  Ltac2 pose_int_bounds () :=
    let pose_bound_if_int hp :=
        match hp with
        | (i, _, ty) =>
          let ic := hyp i in
          lazy_match! ty with
          | int => ltac1:(ic|- pose proof (to_Z_bounded ic)) (Ltac1.of_constr ic)
          | PArray.array _ =>
            ltac1:(ic|-
                   pose proof (to_Z_bounded (PArray.length ic));
                   let H := fresh "Hlen" in
                   pose proof (leb_length _ ic) as H;
                   rewrite leb_le in H)
                             (Ltac1.of_constr ic)
          | _ => ()
          end
        end in
    List.iter pose_bound_if_int (hyps()).
  
  Ltac rewrite_ops :=
    repeat lazymatch goal with
           | [H : context [to_Z (succ _)]|-_] =>
             rewrite succ_spec in H;
             rewrite Zmod_small in H
           | [H : context [to_Z (_+_)]|-_] =>
             rewrite add_spec in H;
             rewrite Zmod_small in H
           | [H : context [to_Z (_*_)]|-_] =>
             rewrite mul_spec in H;
             rewrite Zmod_small in H
           | [H : context [to_Z 1]|-_] =>
             rewrite to_Z_1 in H
           | [H : context [to_Z 0]|-_] =>
             rewrite to_Z_1 in H
           | [|- context [to_Z (succ _)]] =>
             rewrite succ_spec;
             rewrite Zmod_small
           | [|- context [to_Z (_+_)]] =>
             rewrite add_spec;
             rewrite Zmod_small
           | [|- context [to_Z (_*_)]] =>
             rewrite mul_spec;
             rewrite Zmod_small
           | [|- context [to_Z 1]] =>
             rewrite to_Z_1
           | [|- context [to_Z 0]] =>
             rewrite to_Z_1
           end.

  Ltac eval_const c :=
    let x := eval vm_compute in c in 
        change c with x in *.

  Ltac eval_int_consts :=
    eval_const (to_Z max_int);
    eval_const (to_Z max_length);
    eval_const (to_Z zero);
    eval_const (to_Z 32);
    eval_const (to_Z 2);
    eval_const (to_Z 1);
    eval_const (to_Z 0);
    eval_const wB.

  Ltac coerce_goal :=
    lazymatch goal with
    | [|- Int63.ltb _ _ = true] =>
      rewrite ltb_lt
    | [|- Int63.leb _ _ = true] =>
      rewrite leb_le
    | [|- Int63.eqb _ _ = true] =>
      rewrite eqb_eq
    | [|- Int63.eqb _ _ = false] =>
      rewrite <-Bool.not_true_iff_false;
      rewrite eqb_eq
    | [|- Int63.ltb _ _ = false] =>
      rewrite <-Bool.not_true_iff_false;
      rewrite ltb_lt
    | [|- Int63.leb _ _ = false] =>
      rewrite <-Bool.not_true_iff_false;
      rewrite leb_le
    | [|- (?a = _)] =>
      lazymatch type of a with
      | int => apply to_Z_inj
      | _ => idtac
      end
    | _ => idtac
    end.
    
  Ltac int_lia_prep :=
    coerce_goal;
    unfold t in *;
    ltac2:(enter pose_int_bounds);
    unfold lt in*;
    unfold eq in *;
    unfold le in *;
    (rewrite_ops + idtac);
    eval_int_consts.

  Ltac int_lia := int_lia_prep; lia.
  
  Lemma max_int_greatest
    : forall a, le a max_int.
  Proof.
    intros; int_lia.
  Qed.

  Lemma eq_max_int_no_greater
    : forall a,
      a <> max_int
      <-> (exists b, lt a b).
  Proof.
    split; intros.
    {
      exists max_int.
      pose proof (fun p => H (to_Z_inj _ _ p)).
      int_lia.
    }
    {
      firstorder.
      intro.
      subst.
      int_lia.
    }
  Qed.
  
  Lemma neq_max_int_lt
    : forall a,
      a <> max_int
      <-> lt a max_int.
  Proof.
    intro a.
    rewrite eq_max_int_no_greater.
    split; [ intros [b H] | exists max_int; auto].
    int_lia.
  Qed. 

  Lemma isTop_spec
    : forall a,
      isTop a = false
      <-> (exists b, lt a b).
  Proof.
    intro a.
    rewrite <- eq_max_int_no_greater.
    unfold isTop in *.
    rewrite <-Bool.not_true_iff_false.
    rewrite eqb_eq.
    intuition int_lia.
  Qed.
  
  Lemma succ_greater
    : forall a,
      (exists b, lt a b) ->
      lt a (succ a).
  Proof.
    intro a.
    rewrite <- eq_max_int_no_greater.
    rewrite neq_max_int_lt.
    intros; int_lia.
  Qed.
  
  Lemma succ_least
    : forall a b,
      lt a b ->
      le (succ a) b.
  Proof.
    intros.
    pose proof (Z.mod_le (φ (a)%int63 + 1) wB ltac:(int_lia) wB_pos).
    int_lia.
  Qed.
  
  Lemma natlike_ind
    : forall P : t -> Prop,
      P zero -> (forall n, isTop n = false -> P n -> P (succ n)) -> forall n, P n.
  Proof.
    intros.
    (*TODO: handle in int_lia*)
    unfold isTop in *.
    rewrite <- of_to_Z.
    assert (forall z, (0 <= z < wB - 1)%Z -> P (of_Z z) -> P (of_Z (z+1)))%int63.
    {
      intros.
      (*TODO: handle of_Z in int_lia*)
      replace (of_Z (z+1)) with  (of_Z z + 1)%int63.
      2:{        
        replace z with (z mod wB)%Z at 2.
        rewrite <- of_Z_spec at 1.
        replace (of_Z (φ (of_Z z)%int63 + 1)) with (of_Z (((φ (of_Z z)%int63 + 1) mod wB))).
        rewrite <- to_Z_1.
        rewrite <- add_spec; eauto.
        rewrite of_to_Z; auto.
        {
          rewrite of_Z_spec.
          rewrite <- of_to_Z .
          rewrite of_Z_spec.
          reflexivity.
        }
        rewrite Zmod_small; lia.
      }
      apply H0; auto.
      rewrite <-Bool.not_true_iff_false.
      rewrite eqb_eq.
      int_lia_prep.
      rewrite neq_max_int_lt.
      unfold lt.
      rewrite of_Z_spec.
      rewrite Zmod_small; try int_lia.
    }
    clear H0.
    pose proof (to_Z_bounded n).
    revert H0.
    generalize (to_Z n).
    intros z H0.
    pose proof H0 as H2; revert H2.
    apply Z.right_induction with (z := 0%Z) (n:=z).
    {
      intros x y xeq; subst; reflexivity.
    }
    intros; assumption.
    2:lia.
    {
      clear z H0.
      intros z Hnneg IH H0.
      specialize (H1 z ltac:(lia)).
      apply H1.
      apply IH.
      lia.
    }
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
    (* extra max is in case i =? max_int *)
    let new_len := max i (max (i+1) old_len) in
    MkArr (expand_to_len_parray l old_len new_len) new_len extra.    
  
  (* Dynamically grows the array as necessary *)
  Definition set {A} l i (a : A) :=
    let '(MkArr l len_l extra) := (expand_to_contain i l) in
    MkArr (set l i a) len_l (if i<? max_length  then extra else (i,a)::extra).

  Definition length {A} := @len A.
  
  Definition alloc {A} l (a : A) := (l.(len),set l l.(len) a).

End PArrayList.


(*TODO: move to the right place*)
  Import Int63 Int63Natlike.
  Lemma intrec_succ {A}
    : forall (a : A) (f : int -> A -> A),
      forall n, lt n max_int -> (intrec a f (succ n)) = (f n (intrec a f n)).
  Proof.
    intros a f n.
    unfold intrec.
    unfold posZrec.
    rewrite succ_spec.
    rewrite <- (of_to_Z n) at 1 3.
    pose proof (to_Z_bounded n) as H; revert H.
    generalize (to_Z n).
    clear n.
    destruct z; intros; try solve [lia | simpl in *; auto].
    unfold lt in *.
    replace ((Z.pos p + 1) mod wB)%Z with ((Z.pos p + 1))%Z.
    simpl.
    rewrite Pos.add_1_r; auto.
    rewrite Pos.peano_rect_succ; auto.

    rewrite of_Z_spec in H0.
    let x := eval vm_compute in (to_Z max_int) in 
        change (to_Z max_int) with x in *.
    let x := eval vm_compute in wB in 
        change wB with x in *.
    rewrite Zmod_small in H0; try lia.
    rewrite Zmod_small; lia.
  Qed.

(* TODO: prove ArrayList properties *)
Module PArrayListProperties : ArrayListSpec Int63Natlike PArrayList.

  Import PArrayList.
  Import Int63Natlike.
  Open Scope int63.

  Module Import Notations :=
    (NatlikeNotations Int63Natlike)
      <+ (ArrayNotations Int63Natlike PArrayList).

  Definition well_formed {A} '(MkArr l len_l _ : array A) :=
    (le len_l (PArray.length l) /\ (forall i, le len_l i -> PArray.get l i = default l)) \/
    (lt PArray.max_length len_l).

  
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
    try (int_lia).

  
  Ltac case_match_order_fn :=
    match goal with
    | [|- context[match ?e with _ => _ end]]
      => case_order_fn e
    end.
  
  (*TODO: going to run into max_length here.
    How should I work around? Refinements probably slow in vm_compute.
   *)
  Lemma expand_to_len_parray_length_old A (l : PArray.array A) old_len new_len
    : le (min new_len max_length) (PArray.length (expand_to_len_parray l old_len new_len)).
  Proof.
    unfold expand_to_len_parray.
    unfold min.
    case_order_fn (new_len <=? max_length).
    {
      case_order_fn (new_len <? PArray.length l).
      int_lia_prep.
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

  
  Lemma expand_to_len_parray_length A (l : PArray.array A) old_len new_len
    : (PArray.length (expand_to_len_parray l old_len new_len))
      = let backed_len := PArray.length l in
        if new_len <? backed_len
        then backed_len
        else min (max (2 * backed_len) new_len) max_length.
  Proof.
    unfold expand_to_len_parray.
    unfold min.
    unfold max.
    case_match_order_fn.
    rewrite length_copy_up_to.
    rewrite length_make.
    repeat case_match_order_fn.
  Qed.

  
  Lemma get_set_same : forall A t i (a:A), well_formed t -> t.[i<-a].[i] = a.
  Proof.
    intros A [] i a.
    unfold set.
    unfold get.
    unfold expand_to_contain.
    simpl.
    unfold max; unfold min;
      intuition repeat case_match_order_fn.
    all: try (simpl; rewrite eqb_refl; reflexivity).
    all: try(
      apply PArray.get_set_same;
      rewrite expand_to_len_parray_length;
      unfold max; unfold min;
      intuition repeat case_match_order_fn).
    all: revert Heqb1; repeat case_match_order_fn.  
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


  Lemma default_peano_rect A f p (l : PArray.array A)
    : (forall p l,  default (f p l) = default l) ->
      default (Pos.peano_rect _  l f p) = default l.
  Proof.
    revert f l; induction p; intros; simpl in *; auto;
      rewrite ?H; rewrite IHp; intros; rewrite ?H; auto.
  Qed.


  (* needed to make Qed terminate reasonably*)
  Local Strategy 1 [of_pos].

  (*TODO: use natlike_ind*)
  Lemma get_copy_up_to_in_bounds A i len l l_src
    : default l = default l_src ->
      (forall i, le (PArray.length l) i ->
                 PArray.get l_src i = default l) ->
      lt i len ->
      PArray.get (copy_up_to l l_src len) i
      = @PArray.get A l_src i.
  Proof.
    intros Hdefault_eq Hdefault_len.
    unfold copy_up_to.
    unfold intrec.
    unfold lt.
    pose proof (to_Z_bounded len) as H.
    revert H.
    generalize (to_Z len).
    clear len.
    intros.
    unfold posZrec.
     
    destruct z; try int_lia.

    revert dependent i.
    remember (N.pos p) as n.
    revert dependent p.
    apply N.right_induction with (z:=0%N) (n:= n); try int_lia.
    {
      intros x y Heq; subst.
      reflexivity.
    }
    {
      intros; simpl in *.
      destruct n0; simpl in *.
      {
        enough (i = 0).
        {
          subst.
          unfold copy_nth.
          case_order_fn ((0 <? PArray.length l)).
          rewrite PArray.get_set_same; try rewrite ltb_lt; auto.
          rewrite PArray.get_out_of_bounds.
          {
            case_order_fn ((0 <? PArray.length l_src)).
            rewrite Hdefault_len.
            rewrite default_set.
            reflexivity.
            int_lia.
            rewrite default_set.
            rewrite PArray.get_out_of_bounds; auto.
            rewrite <- ltb_lt in Heqb0.
            apply Bool.not_true_is_false in Heqb0; auto.
          }
          rewrite length_set.
          rewrite <- ltb_lt in Heqb.
          apply Bool.not_true_is_false in Heqb; auto.
        }
        {
          destruct p; inversion Heqn; subst; clear Heqn.
          apply to_Z_inj.
          (*TODO: include in int_lia*)
          rewrite to_Z_0.
          int_lia.
        }
      }
      {
        rewrite Pos.peano_rect_succ.
        inversion Heqn; subst; clear Heqn.
        case_order_fn (eqb i (of_pos p0)).
        {
          unfold eq in *; subst.
          unfold copy_nth.

          (*Need due to possible compute bug*)
          (*TODO: should be okay w/ strategy above*)
          (*remember (of_pos p0) as p0i.*)
          case_order_fn ((of_pos p0 <? PArray.length l)).
          {
            rewrite PArray.get_set_same.
            reflexivity.
            rewrite peano_rect_length.
            rewrite length_set.
            rewrite ltb_lt; auto.
            intros.
            rewrite length_set.
            reflexivity.
          }
          {
            rewrite get_out_of_bounds.
            rewrite default_set.
            {
              rewrite default_peano_rect.
              rewrite default_set.
              rewrite Hdefault_len; eauto.
              int_lia.

              intros.
              rewrite default_set; auto.
            }
            rewrite length_set.
            rewrite peano_rect_length.
            rewrite length_set.            
            rewrite <- ltb_lt in Heqb.
            apply Bool.not_true_is_false in Heqb; auto.
            intros.
            rewrite length_set; auto.
          }
        }
        {
          unfold eq in *.
          unfold copy_nth.
          rewrite PArray.get_set_other; auto.
          erewrite H0.
          eauto.
          2: eauto.
          int_lia.
          pose proof (fun pf => Heqb (to_Z_inj _ _ pf)).          
          change (of_pos p0) with (of_Z (Z.pos p0)) in H3.
          rewrite of_Z_spec in H3.
          rewrite Zmod_small in H3.
          int_lia.
          int_lia.
        } 
      }
    }
  Qed.



  Lemma get_copy_up_to_out_of_bounds A i len l l_src
    : ~ lt i len ->
      PArray.get (copy_up_to l l_src len) i
      = @PArray.get A l i.
  Proof.
    unfold copy_up_to.
    revert i.
    apply Int63Natlike.natlike_ind with (n:= len).
    { intros; reflexivity. }
    {
      intros.
      case_order_fn (n =? max_int); [ unfold eq in *; subst; reflexivity|].
      {
        assert (to_Z n <> to_Z max_int).
        {
          intro Heq; apply Heqb; unfold eq; apply to_Z_inj; auto.
        }
        assert (lt n max_int) by int_lia.
        rewrite intrec_succ; auto.
        unfold copy_nth at 1.
        rewrite PArray.get_set_other.
        rewrite H0; auto.
        int_lia.
        assert (to_Z n <> to_Z i) by int_lia.
        congruence.
      }
    }
  Qed.

  Lemma get_expand_parray A (l : PArray.array A) old_len new_len i
    : lt i old_len ->
      le old_len (PArray.length l) ->
      PArray.get (expand_to_len_parray l old_len new_len) i = PArray.get l i.
  Proof.
    intros.
    unfold expand_to_len_parray.
    case_order_fn (new_len <? PArray.length l).
    reflexivity.
    case_order_fn (i <? PArray.length l).
    {
      rewrite get_copy_up_to_in_bounds; auto.
      rewrite default_make.
      rewrite get_out_of_bounds; auto.
      {
        rewrite <-Bool.not_true_iff_false.
        rewrite ltb_lt.
        int_lia.
      }
      {
        intro i0.
        rewrite !length_make.
        rewrite default_make.
        intro.
        rewrite !get_out_of_bounds; auto.
        {
          rewrite <-Bool.not_true_iff_false.
          rewrite ltb_lt.
          int_lia.
        }
        revert H1.
        unfold max.
        pose proof (leb_length _ l) as Hlen; rewrite leb_le in Hlen.
        case_order_fn (2 * PArray.length l <=? new_len);
          case_match_order_fn;
          intros;
          rewrite <-Bool.not_true_iff_false;
          rewrite ltb_lt;
          int_lia.
      }
    }
  Qed.

  (*
  Lemma get_expand_parray_out_of_bounds A (l : PArray.array A) old_len new_len i
    : ~lt i old_len ->
      le old_len (PArray.length l) ->
      PArray.get (expand_to_len_parray l old_len new_len) i = PArray.default l.
  Proof.
    intros.
    unfold expand_to_len_parray.
    case_order_fn (new_len <? PArray.length l).
    {
      apply get_out_of_bounds.
      int_lia.
    }
    case_order_fn (i <? PArray.length l).
    {
      rewrite get_copy_up_to_in_bounds; auto.
      apply get_out_of_bounds; int_lia.
      rewrite default_make.
      rewrite get_out_of_bounds; auto; int_lia.
      {
        intro i0.
        rewrite !length_make.
        rewrite default_make.
        intro.
        rewrite !get_out_of_bounds; auto; try int_lia.
        revert H1.
        unfold max.
        pose proof (leb_length _ l) as Hlen; rewrite leb_le in Hlen.
        case_order_fn (2 * PArray.length l <=? new_len);
          case_match_order_fn;
          intros;
          rewrite <-Bool.not_true_iff_false;
          rewrite ltb_lt;
          int_lia.
      }
      int_lia.
      repeat case_match_order_fn.
    }
  Qed.
   *)

  
  (*Well-formedness lemmas*)
  Lemma make_well_formed : forall A (a:A), well_formed (make a).
  Proof.
    simpl; intros.
    left.
    rewrite length_make.
    intuition repeat case_match_order_fn; try int_lia.
    rewrite get_make; rewrite default_make; auto.
  Qed.

  
  Lemma default_copy_nth A l l' i
    : @default A (copy_nth l' i l) = default l.
  Proof.
    unfold copy_nth.
    rewrite default_set; auto.
  Qed.
  
  Lemma default_intrec A l f i
    : (forall i l', default (f i l') = default l') ->
      @default A (intrec l f i) = default l.
  Proof.
    revert l f; apply natlike_ind with (n:= i);
      intros.
    cbn; auto.

    unfold isTop in *.
    rewrite <-Bool.not_true_iff_false in H.
    rewrite eqb_eq in H.
    unfold eq in H.
    rewrite neq_max_int_lt in H.
    rewrite intrec_succ; try int_lia.
    rewrite H1.
    rewrite H0; auto.
  Qed.
    
  Lemma default_copy_up_to A l l' len0
    : @default A (copy_up_to l l' len0) = default l.
  Proof.
    revert l l'; apply natlike_ind with (n:= len0);
      intros.
    cbn; auto.
    unfold copy_up_to.
    unfold isTop in *.
    
    rewrite <-Bool.not_true_iff_false in H.
    rewrite eqb_eq in H.
    unfold eq in H.
    rewrite neq_max_int_lt in H.
    rewrite intrec_succ; try int_lia.
    rewrite default_copy_nth.
    rewrite default_intrec; auto.
    {
      intros; apply default_copy_nth.
    }
  Qed.
  
  Lemma set_well_formed : forall A t i (a:A), well_formed t -> well_formed t.[i<-a].
  Proof.
    intros A [] i a; simpl; intros.
    rewrite length_set.
    simpl; intros.
    rewrite expand_to_len_parray_length; simpl.
    unfold min in *; unfold max in *.
    intuition idtac.
    {
      case_order_fn (i+1 <=? len0).
      {
        case_order_fn (i <=? len0).
        {
          left; intuition idtac.
          repeat case_match_order_fn.
          {
            rewrite get_set_other.
            (*TODO: make int_lia work directly*)
            2:assert (to_Z i <> to_Z i0) by int_lia;
              intro H'; apply H2; f_equal; exact H'.
            rewrite default_set.
            unfold expand_to_len_parray.
            case_match_order_fn; eauto.
            rewrite get_copy_up_to_out_of_bounds; try int_lia.
            rewrite default_copy_up_to.
            rewrite get_make.
            rewrite default_make.
            auto.
          }
        }
        {
          case_order_fn (max_int <=? i).
        }
      }
      {
        case_order_fn (max_int <=? i).
        {
          assert (i = max_int) by (apply to_Z_inj; int_lia); subst.
          right; cbn; int_lia.
        }
        {
          repeat (case_match_order_fn;[]).
          case_order_fn (max_length <? i+1).
          left.
          case_match_order_fn.
          {
            split.
            int_lia.
            intros.
            rewrite get_set_other.
            (*TODO: make int_lia work directly*)
            2:assert (to_Z i <> to_Z i0) by int_lia;
              intro H'; apply H2; f_equal; exact H'.
            rewrite default_set.
            unfold expand_to_len_parray.
            case_match_order_fn; eauto.
            apply H1; int_lia.
          }
          {
            split.
            repeat case_match_order_fn.

            intros.
            rewrite get_set_other.
            (*TODO: make int_lia work directly*)
            2:assert (to_Z i <> to_Z i0) by int_lia;
              intro H'; apply H2; f_equal; exact H'.
            rewrite default_set.
            unfold expand_to_len_parray.
            case_match_order_fn; eauto.
            rewrite get_copy_up_to_out_of_bounds; try int_lia.
            rewrite default_copy_up_to.
            rewrite get_make.
            rewrite default_make.
            auto.
          }
        }
      }
    }
    {
      repeat case_match_order_fn;
      case_order_fn (max_length <? i);
      left;
      split; try int_lia; intros.
      all: revert Heqb.
      all: repeat case_match_order_fn.
    }
  Qed.

  Lemma alloc_well_formed
    : forall A t (a:A) i t',
      well_formed t ->
      (i,t') = alloc t a ->
      well_formed t'.
  Proof.
    intros A t a i t'; unfold alloc; simpl.
    intro wft; intro H; inversion H; subst; clear H.
    apply set_well_formed; auto.
  Qed.    

  
  Lemma get_set_other : forall A t i j (a:A), well_formed t -> i <> j -> t.[i<-a].[j] = t.[j].
  Proof.
    unfold well_formed.
    unfold set.
    unfold get.    
    unfold expand_to_contain.
    intros A [] i j a wft Hij.
    simpl; intuition repeat (case_match_order_fn; simpl).
    all: try(rewrite PArray.get_set_other;[| assumption]).
    solve [rewrite get_expand_parray; auto].
    all: rewrite ?default_set.
    {
      unfold expand_to_len_parray.
      repeat case_match_order_fn.
      apply H1; int_lia.
      rewrite get_copy_up_to_out_of_bounds; auto; try int_lia.
      rewrite get_make.
      rewrite get_out_of_bounds; auto; int_lia.
    }
    {
      unfold expand_to_len_parray.
      repeat case_match_order_fn.
      revert Heqb0; revert Heqb2; unfold max;
        repeat case_match_order_fn.
      revert Heqb0; repeat case_match_order_fn.
    }
    {
      unfold expand_to_len_parray.
      revert Heqb0; unfold max;
        repeat case_match_order_fn; auto;
        rewrite default_copy_up_to;
        rewrite default_make;
        intros; rewrite get_out_of_bounds; auto; int_lia.
    }
    {
      f_equal.
      rewrite !get_out_of_bounds.
      {
        unfold expand_to_len_parray.
        repeat case_match_order_fn; auto;
        rewrite default_copy_up_to;
        rewrite default_make;
        intros; rewrite get_out_of_bounds; auto; int_lia.
      }
      int_lia.
      {
        rewrite expand_to_len_parray_length.
        simpl.
        unfold min; unfold max.
        repeat case_match_order_fn; auto.
      }
    }
    {
      unfold eq in *; subst; tauto.
    }
    {
      f_equal.
      rewrite !get_out_of_bounds.
      {
        unfold expand_to_len_parray.
        repeat case_match_order_fn; auto;
        rewrite default_copy_up_to;
        rewrite default_make;
        intros; rewrite get_out_of_bounds; auto; int_lia.
      }
      int_lia.
      {
        rewrite expand_to_len_parray_length.
        simpl.
        unfold min; unfold max.
        repeat case_match_order_fn; auto.
      }
    }
    {
      unfold expand_to_len_parray.
      repeat case_match_order_fn; auto.
      rewrite get_copy_up_to_in_bounds; auto.
      {
        rewrite default_make.
        rewrite get_out_of_bounds; auto; int_lia.
      }
      {
        rewrite length_make.
        rewrite default_make.
        intros.
        rewrite !get_out_of_bounds; auto; try int_lia.
        revert H0; unfold max.
        case_order_fn (i + 1 <=? len0).
        case_order_fn (i <=? len0).
        case_order_fn (2 * PArray.length arr0 <=? len0);
          repeat case_match_order_fn; intros; auto; try int_lia.
        repeat case_match_order_fn; intros; auto; try int_lia.
        repeat case_match_order_fn; intros; auto; try int_lia.
        revert Heqb5; 
          repeat case_match_order_fn; intros; auto.
      }
    }
    {
      exfalso.
      revert Heqb0; unfold max.
      repeat case_match_order_fn; intros; auto.
      revert Heqb0; unfold max.
      repeat case_match_order_fn; intros; auto.
    }
    {
      f_equal.
      rewrite !get_out_of_bounds.
      {
        unfold expand_to_len_parray.
        repeat case_match_order_fn; auto;
        rewrite default_copy_up_to;
        rewrite default_make;
        intros; rewrite get_out_of_bounds; auto; int_lia.
      }
      int_lia.
      {
        rewrite expand_to_len_parray_length.
        simpl.
        unfold min; unfold max.
        repeat case_match_order_fn; auto.
      }
    }
    {
      f_equal.
      rewrite !get_out_of_bounds.
      {
        unfold expand_to_len_parray.
        repeat case_match_order_fn; auto;
        rewrite default_copy_up_to;
        rewrite default_make;
        intros; rewrite get_out_of_bounds; auto; int_lia.
      }
      int_lia.
      {
        rewrite expand_to_len_parray_length.
        simpl.
        unfold min; unfold max.
        repeat case_match_order_fn; auto.
      }
    }
    }
  Qed.
          
  
  Lemma get_make : forall A (a:A) i, (make a).[i] = a.
  Proof.
    unfold get.
    unfold make.
    intros.
    repeat (case_match_order_fn; simpl; auto).
    rewrite get_out_of_bounds.
    apply default_make.
    compute.
    int_lia.
  Qed.

  Lemma get_alloc_same
    : forall A l (a:A) l' i,
      well_formed l ->
      (i,l') = alloc l a ->
      l'.[i] = a.
  Proof.
    intros A l a l' i wfl.
    unfold alloc.
    intro H; inversion H; subst.
    apply get_set_same; auto.
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

  (*TODO: gets broken by max_int. TODO: some prior theorems are a bit too permissive
   and work by happenstance.*)
  Lemma length_set :
    forall A t i (a : A),
      length t.[i <- a] = (max i max (length t) (i.+1).
  Proof.
    intros A [] i a; unfold set; unfold length; simpl.
    TODO: update 
    rewrite <- max_comm.
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
  

