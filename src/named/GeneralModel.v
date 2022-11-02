Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Substable Model.
From Named Require Term.
Require Import Coq.Logic.FunctionalExtensionality.

Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
    {|
      term_substable := _;
      sort_substable := _;
      Model.eq_sort := eq_sort;
      (*TODO: rename the conflict*)
      Model.eq_term := eq_term;
      Model.wf_sort := wf_sort;
      Model.wf_term := wf_term;
    |}.

Section WithExp.

Context {V : Type}
        {V_Eqb : Eqb V}
        {V_default : WithDefault V}
        (exp : Type)
        (default : exp)
        (eq_exp : exp -> exp -> Prop)
        (eq_exp_symm : forall e1 e2, eq_exp e1 e2 -> eq_exp e2 e1)
        (eq_exp_trans : forall e1 e2 e3, eq_exp e1 e2 -> eq_exp e2 e3 -> eq_exp e1 e3)
        (eq_exp_refl : forall e, eq_exp e e)
        (* (eq_srt : Type -> Type -> Prop) *)
        (wf_exp : exp -> Type -> Prop)
        (* (wf_srt : Type -> Prop) *)
.

Print Model.


Notation named_list := (@named_list V).

Definition meta_subst := named_list exp.

Definition term := meta_subst -> exp.

Definition sort := Type.

Definition ctx : Type := named_list sort.

Print In.

(* Fixpoint In_subst (a : V * exp) (l : meta_subst) := *)
(*   match l with *)
(*   | [] => False *)
(*   | (v, b) :: m => ((fst a) = v /\ eq_exp (snd a) b) \/ In_subst a m *)
(*   end. *)


(* Definition incl_subst (l m : meta_subst) := *)
(*   forall a, In_subst a l -> In_subst a m. *)

Notation Substable0 := (Substable0 V).
Notation Substable := (@Substable V).

Definition inj_var (v : V) : term :=
  fun (ms : meta_subst) =>
  named_list_lookup default ms v.


Definition apply_subst (l : named_list term) (t : term) : term :=
  fun (ms' : meta_subst) =>
    t ((named_map (fun x => x ms') l)).

Definition id_args {B} (c : named_list B) :=
  map inj_var (map fst c).

Notation id_subst c := (with_names_from c (id_args c)).

Print wf_subst.
Definition eq_term_sub (c : list V) (e1 e2 : term) :=
  (* wf_subst [] ms c *)
  forall ms, map fst ms = c -> eq_exp (e1 ms) (e2 ms).


Lemma eq_term_sub_refl : forall args e1, eq_term_sub args e1 e1.
Proof.
  unfold eq_term_sub.
  intros.
  apply eq_exp_refl.
Qed.

(* Lemma eq_term_trans : forall args e1 e2 e3, eq_term args e1 e2 -> eq_term args e2 e3 -> eq_term args e1 e3. *)
(* Proof. *)
(*   unfold eq_term. *)
(*   intros. *)
(*   rewrite H; trivial. *)
(*   apply H0; trivial. *)
(* Qed. *)

(* Lemma eq_term_comm : forall c s e1 e2, eq_term c s e1 e2 -> eq_term c s e2 e1. *)
(* Proof. *)
(*   unfold eq_term. *)
(*   intros. *)
(*   apply eq_exp_symm. *)
(*   apply H; trivial. *)
(* Qed. *)

Inductive eq_subst' : meta_subst -> meta_subst -> Prop :=
| eq_subst_nil : eq_subst' [] []
| eq_subst_cons : forall v e1 e2 s1 s2,
    eq_subst' s1 s2 -> eq_exp e1 e2 -> eq_subst' ((v, e1) :: s1) ((v, e2) :: s2)
.

Lemma eq_subst_refl : forall s, eq_subst' s s.
Proof.
  induction s; simpl; trivial.
  apply eq_subst_nil.
  destruct a.
  repeat constructor.
  trivial.
  apply eq_exp_refl.
Qed.

Lemma eq_subst_symm : forall s1 s2, eq_subst' s1 s2 -> eq_subst' s2 s1.
Proof.
  intros.
  induction H. apply eq_subst_nil.
  apply eq_subst_cons.
  apply IHeq_subst'.
  apply eq_exp_symm.
  trivial.
Qed.

Definition ws_term args (e : term) :=
  NoDup args /\
  forall s, map fst s = args -> forall s', eq_subst' s s' -> forall s'', NoDup (map fst s'') -> incl s' s'' -> eq_exp (e s) (e s'').

Definition wf_term (c : ctx) t (srt : sort) :=
  ws_term (map fst c) t /\
    forall s, Forall2
           (fun v_srt v_e =>
              match v_srt, v_e with
              | (v1, srt'), (v2, e) => v1 = v2 /\ wf_exp e srt'
              end)
            c s -> wf_exp (t s) srt.

Instance substable_term : Substable0 term :=
  {
    inj_var := inj_var;
    eq_term0 := eq_term_sub;
    apply_subst0 := apply_subst;
    well_scoped0 := ws_term
  }.

Definition eq_sort {A} (_ : list A) (s1 s2 : sort) :=
  s1 = s2.

Lemma eq_sort_comm : forall (args : list V) e1 e2, eq_sort args e1 e2 -> eq_sort args e2 e1.
Proof.
  unfold eq_sort.
  symmetry.
  apply H; trivial.
Qed.

Instance substable_sort : Substable term sort :=
  {
    apply_subst := fun _ s => s;
    eq_term := eq_sort;
    well_scoped := fun _ _ => True
  }.

Ltac unfold_all :=
  repeat (
      unfold ws_term, apply_subst, inj_var, subst_lookup, pair_map_snd,
      wf_term, Substable.apply_subst, eq_term, eq_sort, eq_term_sub, eq_sort in *;
      simpl in *).

Ltac cases x :=
  case_eq x; intros;
  match goal with
  | [ H : eqb _ _ = true |- _ ] => apply eqb_eq in H; rewrite H
  | [ H : eqb _ _ = false |- _ ] => apply eqb_neq in H
  | _ => idtac
  end.

  Ltac if_refl :=
    match goal with
    | [ H : ?a = ?b |- (if eqb ?a ?b then _ else _) = _ ] => rewrite H
    | [ H : ?b = ?a |- (if eqb ?a ?b then _ else _) = _ ] => rewrite H
    | [ H : ?a <> ?b |- (if eqb ?a ?b then _ else _) = _ ] => rewrite <- eqb_neq in H; rewrite H
    | [ H : ?a = ?b |- _ = (if eqb ?a ?b then _ else _) _ ] => rewrite H
    | [ H : ?b = ?a |- _ = (if eqb ?a ?b then _ else _) _ ] => rewrite H
    | [ H : ?a <> ?b |- _ = (if eqb ?a ?b then _ else _) _ ] => rewrite <- eqb_neq in H; rewrite H
    | _ => idtac
    end;
    match goal with
    | [ |- (if eqb ?a ?a then _ else _) = _ ] => replace (eqb a a) with (true); try (symmetry; apply eqb_refl)
    | [ |- _ = (if eqb ?a ?a then _ else _) _ ] => replace (eqb a a) with (true); try (symmetry; apply eqb_refl)
    | _ => idtac
    end.

  Lemma named_map_fst {A B} : forall (l : named_list A) (f : A -> B), map fst l = map fst (named_map f l).
    Proof.
      intros.
      induction l; simpl; trivial.
      rewrite IHl.
      unfold pair_map_snd; destruct a; simpl.
      trivial.
    Qed.


  Lemma named_map_fst' {A B C} : forall (l1 : named_list A) (l2 : named_list B) (f : B -> C), map fst l1 = map fst l2 -> map fst l1 = map fst (named_map f l2).
    Proof.
      intros.
      rewrite H.
      apply named_map_fst.
    Qed.

Ltac model_crush :=
  repeat
    (intros;
     unfold_all;
     trivial;
     match goal with
     | [x : _ * _ |- _] => destruct x
     | [|- (fun _ => _) = _] => apply functional_extensionality
     | [|- (if ?a then _ else _) = _] => cases a; if_refl
     | [|- _ = (if ?a then _ else _)] => cases a; if_refl
     | [H : False |- _] => inversion H
     | [H : _ /\ _ |- _] => destruct H
     | [H : _ \/ _ |- _] => destruct H
     | [|- _ /\ _] => constructor
     | [|- _ :: _ = _ :: _] => apply invert_eq_cons_cons
     | [|- (_, _) = (_, _)] => apply pair_equal_spec
     | [H : _ :: _ = _ :: _ |- _] => apply invert_eq_cons_cons in H
     | [H : NoDup (_ :: ?a) |- NoDup ?a ] => apply NoDup_cons_iff in H
     | [H : (_, _) = (_, _) |- _] => apply pair_equal_spec in H
     | [H : ws_term _ ?a |- ws_term _ ?a] => apply H
     | [ |- map fst (named_map _ _) = map fst _] => symmetry
     | [ |- incl [] _ ] => apply incl_nil_l
     | [ |- map fst _ = map fst (named_map _ _)] => repeat apply named_map_fst'; trivial
     | [ H : eqb _ _ = false |- _ ] => try apply eqb_neq in H
     | [ H : eqb _ _ = true |- _ ] => try apply eqb_eq in H
     | [ |- eqb _ _ = false ] => try apply eqb_neq
     | [ |- eqb _ _ = true ] => try apply eqb_eq
     | [H : ?a <> ?a |- _] => contradiction
     | [H : ?a = _ |- _] => rewrite H in *
     | _ => idtac
     end;
     try rewrite <- named_map_fst;
     try rewrite map_fst_with_names_from;
     try rewrite map_length;
     if_refl
    ).

  Fixpoint inb {A} `{Eqb A} (a : A) l :=
    match l with
    | [] => false
    | e :: l' => orb (eqb a e) (inb a l')
    end.

  Lemma inb_in {A} `{Eqb A} : forall (a : A) l, inb a l = true -> In a l.
  Proof.
    intros.
    induction l.
    contradict H0; simpl; auto.
    simpl in *.
    cases (eqb a0 a).
    left; trivial.
    right; destruct H0.
    apply not_eq_sym in H1.
    apply eqb_neq in H1.
    rewrite H1 in IHl.
    simpl in IHl.
    apply IHl; trivial.
  Qed.

  Lemma not_or : forall A B, ~ A -> ~B -> ~ (A \/ B).
  Proof.
    intros.
    apply neg_false; constructor; intros; try contradiction.
    destruct H1; contradict H1; assumption.
  Qed.

  Lemma inb_not_in {A} `{Eqb A} : forall (a : A) l, inb a l = false -> (~ In a l).
  Proof.
    intros.
    induction l.
    - apply in_nil.
    - model_crush; apply Bool.orb_false_iff in H0; destruct H0.
      apply not_or.
      apply eqb_neq in H0; auto.
      apply (IHl H1).
  Qed.

  Fixpoint merge_named_lists {A} (l1 l2 : named_list A) :=
    match l1 with
    | [] => l2
    | (v, e) :: l1' =>
        if (inb v (map fst l2))
        then merge_named_lists l1' l2
        else (v, e) :: merge_named_lists l1' l2
    end.

  Lemma merge_named_lists_in_l2 {A} (l1 l2 : named_list A) x :
    In x l2 -> In x (merge_named_lists l1 l2).
  Proof.
    induction l1; model_crush.
    case (inb v0 (map fst l2)); try apply in_cons; try apply H.
    all: apply IHl1; trivial.
  Qed.

  Lemma merge_named_lists_incl (l1 l2 : meta_subst) : 
    incl l2 (merge_named_lists l1 l2).
  Proof.
    induction l1; model_crush.
    apply incl_refl.
    case (inb v (map fst l2)).
    - apply IHl1; trivial.
    - apply incl_tl.
      apply IHl1.
  Qed.

  Lemma named_list_lookup_in : forall l v e, In v (map fst l) -> named_list_lookup default l v = e -> In (v, e) l.
  Proof.
    induction l; model_crush.
    left; rewrite <- H0; model_crush.
    cases (eqb v v0).
    left; rewrite <- H0; model_crush.
    right; apply IHl; try rewrite <- H0; model_crush.
  Qed.

  Lemma named_list_lookup_in' : forall l v e, NoDup (map fst l) -> In (v, e) l -> named_list_lookup default l v = e.
  Proof.
    model_crush.
    induction l.
    model_crush.
    destruct a.
    simpl in H.
    apply NoDup_cons_iff in H.
    destruct H.
    specialize (IHl H1).
    model_crush.
    apply pair_fst_in in H0.
    apply H in H0.
    contradiction.
    apply (IHl H0).
Qed.

  Lemma merge_named_lists_incl_l (l1 l2 : named_list exp) :
    NoDup (map fst l1) ->
    (forall v, In v (map fst l1) -> In v (map fst l2) -> named_list_lookup default l1 v = named_list_lookup default l2 v) ->
    incl l1 (merge_named_lists l1 l2).
  Proof.
    induction l1; model_crush.
    specialize (H0 v (or_introl eq_refl)) as H1.
    assert (eqb v v = true) by apply eqb_refl.
    rewrite H2 in H1; clear H2.
    apply incl_cons; cases (inb v (map fst l2)); model_crush.
    - apply inb_in in H2.
      specialize (H1 H2).
      apply merge_named_lists_in_l2.
      apply named_list_lookup_in; model_crush.
    - apply IHl1; model_crush.
      specialize (H0 v0).
      case_eq (eqb v0 v); intros; rewrite H5 in *.
      + apply NoDup_cons_iff in H.
        destruct H.
        apply eqb_eq in H5.
        rewrite H5 in *.
        apply H in H3; contradiction.
      + apply H0; model_crush.
        right; apply H3.
    - left; trivial.
    - apply incl_tl; apply IHl1; model_crush.
      specialize (H0 v0).
      case_eq (eqb v0 v); intros; rewrite H5 in *.
      + apply NoDup_cons_iff in H.
        destruct H.
        apply eqb_eq in H5.
        rewrite H5 in *.
        apply H in H3; contradiction.
      + apply H0; model_crush.
        right; apply H3.
Qed.

  Lemma merge_named_lists_not_in {A} : forall (l1 l2 : named_list A) a,
    ~ In a l1 -> ~ In a l2 -> ~ In a (merge_named_lists l1 l2).
  Proof.
    intros.
    induction l1; model_crush.
    apply Decidable.not_or in H; destruct H.
    apply IHl1 in H1.
    cases (inb v0 (map fst l2)); model_crush.
    apply not_or; auto.
  Qed.

  Lemma merge_named_lists_not_in_fst {A} : forall (l1 l2 : named_list A) a,
    ~ In a (map fst l1) -> ~ In a (map fst l2) -> ~ In a (map fst (merge_named_lists l1 l2)).
  Proof.
    intros.
    induction l1; model_crush.
    apply Decidable.not_or in H; destruct H.
    apply IHl1 in H1.
    cases (inb v (map fst l2)); model_crush.
    apply not_or; auto.
Qed.

  Lemma NoDup_merged_lists {A} : forall (l1 l2 : named_list A),
    NoDup (map fst l1) -> NoDup (map fst l2) -> NoDup (map fst (merge_named_lists l1 l2)).
  Proof.
    intros.
    induction l1. model_crush. model_crush. apply NoDup_cons_iff in H; destruct H; apply IHl1 in H1.
    cases (inb v (map fst l2)); model_crush.
    apply NoDup_cons.
    apply inb_not_in in H2.
    apply merge_named_lists_not_in_fst; assumption.
    assumption.
  Qed.

  Lemma in_lookup : forall v ms, In v (map fst ms) -> In (v, named_list_lookup default ms v) ms.
 Proof.
    intros.
    induction ms; model_crush.
    left; model_crush; destruct H0; trivial.
    cases (eqb v v0).
    left; trivial.
    right; trivial.
    apply IHms; trivial.
Qed.

  Lemma in_in_fst {A} : forall (c : named_list A) n,
    In n (map fst c) -> exists a, In (n, a) c.
  Proof.
    model_crush.
    induction c; inversion H.
    exists (snd a); model_crush; left; trivial.
    apply IHc in H0.
    simpl.
    case H0.
    intros.
    exists (x).
    right.
    apply H1.
  Qed.

  Lemma in_fst {A} : forall n (e : A) (l : named_list A), In (n, e) l -> In n (map fst l).
  Proof.
    intros.
    induction l; model_crush.
    left; trivial.
    right; trivial.
    apply IHl; trivial.
Qed.
    
    
  Lemma in_fst' {A} : forall n (e : A) (l1 : named_list A) (l2 : list V), map fst l1 = l2 -> In n l2 -> In n (map fst l1).
  Proof.
    model_crush.
Qed.

  Lemma lookup_found_nodup {A} :
    forall (c : named_list A) (n : V) (default : A) (a : A),
      NoDup (map fst c) -> In (n, a) c -> a = named_list_lookup default c n.
    Proof.
      model_crush.
      induction c; model_crush.
      inversion H.
      apply in_fst in H0.
      apply H4 in H0; contradiction.
      apply IHc; model_crush.
    Qed.


  Lemma named_list_lookup_incl : forall s s' n,
      NoDup (map fst s) -> NoDup (map fst s') -> In n (map fst s) -> incl s s' -> named_list_lookup default s n = named_list_lookup default s' n.
  Proof.
    model_crush.
    specialize (in_in_fst s n H1); intros.
    case H3; intros.
    erewrite <- lookup_found_nodup with (c := s).
    apply lookup_found_nodup.
    1, 3: trivial.
    2: apply H4.
    apply (H2 (n, x) H4).
Qed.

  Lemma id_substable {B : Type}: forall e,
  forall (c : named_list B),
    ws_term (map fst c) e
    -> forall args, ws_term args e
              -> eq_term_sub args e (apply_subst (id_subst c) e).
  Proof.
    unfold eq_term_sub.
    model_crush.
    specialize (H3 (named_map (fun x : meta_subst -> exp => x ms) (id_subst c))).
    specialize (H2 ms H1).
    specialize H3 with (s'' := (merge_named_lists (named_map (fun x => x ms) (id_subst c)) ms)); model_crush.
    eapply eq_exp_trans.
    2: { apply eq_exp_symm.
         eapply H3.
         - model_crush.
           unfold id_args; model_crush.
         - apply eq_subst_refl.
         - apply NoDup_merged_lists; model_crush.
           unfold id_args; model_crush.
         - apply merge_named_lists_incl_l; model_crush.
           unfold id_args; model_crush.
           clear H3.
           induction c; model_crush.
           rewrite <- IHc; model_crush.
    }
    eapply H2.
    apply eq_subst_refl.
    apply NoDup_merged_lists; model_crush; unfold id_args; model_crush.
    apply merge_named_lists_incl; model_crush.
Qed.

  Lemma eqb_eq_eqb : forall (H1 H2 : Eqb V) (x y : V), eqb (Eqb:=H1) x y = eqb (Eqb:=H2) x y.
    Proof.
      intros.
      case_eq (eqb x y); model_crush.
Qed.

  Fixpoint rem_dups' {A} (s : named_list A) (l : list V) :=
  match s with
  | [] => []
  | a :: s' => if (inb (fst a) l)
              then rem_dups' s' l
              else a :: rem_dups' s' ((fst a) :: l)
  end.

  Definition rem_dups {A} (s : named_list A) := rem_dups' s [].

  Lemma rem_dups_NoDup' {A} : forall (s : named_list A) l, NoDup (map fst (rem_dups' s l)) /\ (forall v, In v l -> ~In v (map fst (rem_dups' s l))).
  Proof.
    induction s; model_crush.
    apply NoDup_nil.
    unfold not; trivial.
    all: cases (inb v l); model_crush.
    specialize (IHs l).
    destruct IHs.
    apply H0.
    specialize (IHs (v :: l)).
    destruct IHs.
    apply NoDup_cons.
    apply H1.
    apply in_eq.
    trivial.
    specialize (IHs l).
    destruct IHs.
    apply H2; trivial.
    unfold not.
    intros.
    destruct H1.
    model_crush.
    apply inb_not_in in H0.
    apply H0 in H; trivial.
    specialize (IHs (v :: l)).
    destruct IHs.
    apply H3 in H1.
    trivial.
    apply in_cons.
    apply H.
Qed.    

  Lemma rem_dups_NoDup {A} : forall (s : named_list A), NoDup (map fst (rem_dups s)).
    Proof.
      intros.
      specialize (rem_dups_NoDup' s []).
      model_crush.
    Qed.

  Lemma rem_dups_not_In {A} : forall (s : named_list A) l (v : V), In v l -> ~In v (map fst (rem_dups' s l)).
    Proof.
      intros.
      specialize (rem_dups_NoDup' s).
      model_crush.
      apply H0.
      apply H.
    Qed.


  Lemma rem_dups_lookup : forall (s : named_list exp) x l, ~In x l -> eq_exp (named_list_lookup default s x) (named_list_lookup default (rem_dups' s l) x).
    Proof.
    induction s; model_crush.
    cases (eqb x v);
    cases (inb v l).
    rewrite H0 in H.
    apply inb_in in H1.
    apply H in H1; contradiction.
    model_crush.
    cases (eqb v v).
    trivial.
    destruct H2.
    trivial.
    apply IHs.
    trivial.
    model_crush.
    cases (eqb x v).
    model_crush.
    apply IHs.
    unfold not; intros.
    destruct H3; model_crush.
    apply H in H3.
    trivial.
Qed.

  Lemma eqb_eq_lookup : forall (H : Eqb V) x s, named_list_lookup (H := V_Eqb) default s x = named_list_lookup (H := H) default s x.
    Proof.
      induction s; model_crush.
    Qed.

  (* Lemma rem_dups'_change_order {A} : forall (s : named_list A) v1 v2 l, rem_dups' s (v1 :: v2 :: l) = rem_dups' s (v2 :: v1 :: l). *)
  (* Proof. *)
  (*   induction s; model_crush. *)
  (*   Search ((_ || _)%bool). *)
  (*   rewrite Bool.orb_assoc in H. *)
  (*   rewrite Bool.orb_comm with (b1 := eqb v v1) in H. *)
  (*   rewrite <- Bool.orb_assoc in H. *)
  (*   rewrite H in H0. *)
  (*   contradict H0. *)
  (*   apply Bool.diff_true_false. *)
  (*   rewrite Bool.orb_assoc in H. *)
  (*   rewrite Bool.orb_comm with (b1 := eqb v v1) in H. *)
  (*   rewrite <- Bool.orb_assoc in H. *)
  (*   rewrite H in H0. *)
  (*   contradict H0. *)
  (*   apply Bool.diff_false_true. *)



  (* Lemma rem_dups'_append_l {A} : forall (s : named_list A) v, ~In v (map fst s) -> forall l, rem_dups' s l = rem_dups' s (v :: l). *)
  (* Proof. *)
  (*   induction s; model_crush. *)
  (*   apply IHs. *)
  (*   unfold not in *. *)
  (*   intros. *)
  (*   apply H. *)
  (*   right. *)
  (*   apply H2. *)
  (*   contradict H1. *)
  (*   rewrite Bool.orb_true_r. *)
  (*   apply Bool.diff_true_false. *)
  (*   rewrite Bool.orb_false_r in H1. *)
  (*   contradict H. *)
  (*   left. *)
  (*   apply eqb_eq. *)
  (*   trivial. *)
  (*   repeat rewrite <- IHs; model_crush. *)

  Lemma rem_dups_no_add {A} : forall (s : named_list A) l v, ~In v (map fst s) -> ~In v (map fst (rem_dups' s l)).
  Proof.
    induction s; model_crush.
    cases (inb v0 l).
    apply IHs.
    apply Decidable.not_or in H.
    apply H.
    apply Decidable.not_or in H.
    destruct H.
    eapply IHs in H1.
    Search (~ In _ (_ :: _)).
    simpl.
    apply not_in_cons.
    constructor.
    apply not_eq_sym.
    apply H.
    apply H1.
  Qed.

  Lemma not_in_concat' {A} : forall x (l1 : list A), ~In x l1 -> forall l2, ~In x l2 -> ~ In x (l1 ++ l2).
  Proof.
    induction l1; model_crush; try apply Decidable.not_or in H; destruct H.
    apply not_or; model_crush.
    apply IHl1; model_crush.
  Qed.

  Lemma not_in_concat_1 {A} : forall x (l1 l2 : list A), ~ In x (l1 ++ l2) -> ~In x l1.
  Proof.
    induction l2; model_crush.
    rewrite app_nil_r in H.
    apply H.
    apply IHl2.
    clear IHl2.
    induction l1.
    rewrite app_nil_l in H.
    rewrite app_nil_l.
    Search (~ In _ (_ :: _)).
    apply not_in_cons in H.
    apply H.
    Search ((_ :: _) ++ _).
    rewrite <- app_comm_cons.
    apply not_in_cons.
    constructor.
    rewrite <- app_comm_cons in H.
    apply not_in_cons in H.
    apply H.
    rewrite <- app_comm_cons in H.
    apply not_in_cons in H.
    apply IHl1.
    apply H.
Qed.

  Lemma not_in_concat_2 {A} : forall x (l1 l2 : list A), ~ In x (l1 ++ l2) -> ~In x l2.
  Proof.
    induction l1; model_crush.
    apply IHl1.
    apply Decidable.not_or in H.
    apply H.
  Qed.


  Lemma NoDup_order_swap_1 {A} : forall l1 l2 (v: A), NoDup (v :: l1 ++ l2) -> NoDup (l1 ++ v :: l2).
  Proof.
    induction l1; model_crush.
    apply NoDup_cons.
    inversion H; inversion H3.
    apply not_in_concat'.
    apply not_in_concat_1 in H6.
    apply H6.
    apply not_in_concat_2 in H6.
    apply not_in_cons.
    constructor.
    apply not_in_cons in H2.
    apply not_eq_sym.
    apply H2.
    trivial.
    apply IHl1.
    apply NoDup_cons; inversion H.
    apply not_in_cons in H2.
    apply H2.
    inversion H3.
    trivial.
Qed.

  Lemma NoDup_order_swap_2 {A} : forall l1 l2 (v : A), NoDup (l1 ++ v :: l2) -> NoDup (v :: l1 ++ l2).
  Proof.
    induction l1; model_crush.
    inversion H.
    apply IHl1 in H3.
    apply NoDup_cons.
    - apply not_in_cons; constructor; model_crush.
      apply not_in_concat_2 in H2.
      apply not_in_cons in H2.
      apply not_eq_sym.
      apply H2.
      inversion H3.
      apply H6.
    - assert (a :: l1 ++ v :: l2 = (a :: l1) ++ v :: l2) by trivial.
      rewrite H4 in H.
      apply NoDup_remove in H.
      apply H.
  Qed.

  Lemma rem_dups_NoDup_id {A} : forall (s : named_list A) l, NoDup (map fst s ++ l) -> s = rem_dups' s l.
  Proof.
    induction s; model_crush.
    inversion H.
    apply not_in_concat_2 in H3.
    apply inb_in in H0.
    apply H3 in H0.
    contradiction H0.
    apply IHs.
    apply NoDup_order_swap_1.
    apply H.
  Qed.

  Lemma rem_dups_in {A} : forall (l : named_list A) s v a, ~In v s -> NoDup (map fst l) -> In (v, a) l -> In (v, a) (rem_dups' l s).
  Proof.
    induction l; model_crush.
    cases (inb v s); model_crush.
    apply inb_in in H3.
    apply H in H3; contradiction.
    left; trivial.
    cases (inb v0 s).
    apply IHl; model_crush.
    apply in_cons.
    apply IHl; model_crush.
    apply not_or.
    inversion H0.
    apply in_fst in H1.
    unfold not; intros.
    rewrite H7 in *.
    apply H5.
    apply H1.
    trivial.
  Qed.

  Lemma incl_rem_cons {A} : forall (l1 : named_list A) s, NoDup (s ++ (map fst l1)) -> forall l2, NoDup (map fst l2) -> incl l1 l2 -> incl l1 (rem_dups' l2 s).
  Proof.
    induction l1; model_crush.
    apply incl_cons.
    constructor.
    apply incl_cons in H1.
    destruct H1.
    apply rem_dups_in; model_crush.
    apply NoDup_order_swap_2 in H.
    inversion H.
    apply not_in_concat_1 in H5.
    trivial.
    apply IHl1; model_crush.
    apply NoDup_order_swap_2 in H.
    inversion H; trivial.
    apply incl_cons in H1.
    apply H1.
Qed.

Lemma eq_subst_eq_fst : forall s1 s2, eq_subst' s1 s2 -> map fst s1 = map fst s2.
Proof.
  model_crush.
  induction H; model_crush.
Qed.


  Lemma subst_var : forall (H : Eqb V) (s : named_list term) (x : V),
      forall args,
        ws_term (map fst s) (inj_var x) ->
      eq_term_sub args (apply_subst s (inj_var x)) (subst_lookup s x).
  Proof.
    induction s. model_crush.
    specialize H1 with (s := []) (s' := []) (s'' := rem_dups ms); model_crush.
    eapply eq_exp_trans.
    apply H1; model_crush.
    apply eq_subst_nil.
    apply rem_dups_NoDup.
    apply eq_exp_symm.
    apply rem_dups_lookup.
    model_crush; unfold not; trivial.
    model_crush.
    cases (eqb x v); model_crush; cases (eqb (Eqb := V_Eqb) x v); model_crush.
    cases (eqb (Eqb := V_Eqb) v v); model_crush; apply eq_term_sub_refl.
    eapply IHs; model_crush.
    apply eq_exp_trans with (e2 := named_list_lookup (H := V_Eqb) default ((v, default) :: s0) x).
    simpl.
    cases (eqb (Eqb := V_Eqb) x v).
    contradiction.
    trivial.
    apply eq_exp_trans with (e2 := named_list_lookup (H := V_Eqb) default (rem_dups ((v, default) :: s'')) x).
    - apply H2 with (s' := (v, default) :: s'); model_crush.
      apply eq_subst_cons; trivial.
      apply NoDup_cons.
      apply rem_dups_not_In.
      simpl; left; trivial.
      apply rem_dups_NoDup'.
      apply incl_cons.
      constructor.
      model_crush.
      left; model_crush.
      unfold rem_dups; simpl.
      apply incl_tl.
      apply incl_rem_cons; model_crush.
      apply eq_subst_eq_fst in H6.
      model_crush.
    - model_crush.
      cases (eqb (Eqb := V_Eqb) x v); model_crush.
      apply eq_exp_symm.
      apply rem_dups_lookup.
      model_crush.
      apply not_or; model_crush.
      apply not_eq_sym; model_crush.
      auto.
Qed.

  Lemma lookup_found {A} : forall (l1 l2 : named_list A) d1 d2 (e : V), In e (map fst l1) -> named_list_lookup d1 (l1 ++ l2) e = named_list_lookup d2 l1 e.
  Proof.
    model_crush.
    induction l1; model_crush.
    apply IHl1.
    model_crush.
Qed.

  (* Lemma ws_term_append : forall (args : list V) (l1 l2 : named_list exp) (a : term), *)
  (*     ws_term args a -> map fst l1 = args -> a (l1 ++ l2) = a l1. *)
  (* Proof. *)
  (*   model_crush. *)
  (*   apply H; model_crush. *)
  (*   apply lookup_found. *)
  (*   unfold ws_term in H. *)
  (*   rewrite <- H0 in H1; trivial. *)
  (* Qed. *)

  Lemma named_map_cons_eq {A B} : forall l (n : V) (e : A) (f : A -> B),
      named_map f ((n, e) :: l) = (n, f e) :: named_map f l.
  Proof.
    trivial.
  Qed.


   Lemma named_map_cmp {A B C} : forall (f : B -> C) (g : A -> B) h (l : named_list A), (forall x, f (g x) = h x) -> named_map f (named_map g l) = named_map h l.
  Proof.
    model_crush.
    induction l; model_crush.

Qed.

  Lemma subst_assoc0 : forall (s1 s2 : named_list term) (a : term),
      ws_term (map fst s2) a -> forall args,
        eq_term_sub args (apply_subst s1 (apply_subst s2 a)) (apply_subst (subst_cmp s1 s2) a).
  Proof.
    unfold eq_term_sub; model_crush.
    assert ((a
       (named_map
          (fun x : meta_subst -> exp =>
           x (named_map (fun x0 : meta_subst -> exp => x0 ms) s1)) s2)) = 
    (a
       (named_map (fun x : meta_subst -> exp => x ms)
          (named_map
             (fun (t : term) (ms' : meta_subst) =>
              t (named_map (fun x : meta_subst -> exp => x ms') s1)) s2)))).
    f_equal.
    symmetry.
    apply named_map_cmp.
    trivial.
    rewrite H2.
    apply eq_exp_refl.
  Qed.

  Lemma subst_id0 {B} : forall (c : named_list B) (a : term),
      ws_term (map fst c) a -> forall args, ws_term args a -> eq_term_sub args (apply_subst (id_subst c) a) a.
  Proof.
    intros.
    pose proof (id_substable (B := B) (e := a) c) as id_sub.
    unfold eq_term_sub in *.
    intros.
    apply eq_exp_symm.
    eapply id_sub.
    trivial.
    apply H0.
    trivial.
Qed.

  Lemma strengthen_subst0 : forall (s : named_list term) (e a : term) (n : V),
      ws_term (map fst s) a -> fresh n s ->
      forall args,
      eq_term_sub args (apply_subst ((n, e) :: s) a) (apply_subst s a).
  Proof.
    model_crush.
    apply eq_exp_symm.
    eapply H1; model_crush.
    apply eq_subst_refl.
    apply NoDup_cons; model_crush.
    apply incl_tl.
    apply incl_refl.
Qed.

  Lemma fun_app_eq {A B} : forall (f g : A -> B) (a : A), f = g -> f a = g a.
  Proof.
    model_crush.
  Qed.

  Lemma ws_extend : forall (args : list V) (v : V) (t : term),
      ~In v args -> ws_term args t -> ws_term (v :: args) t.
  Proof.
    unfold ws_term in *.
    model_crush.
    apply NoDup_cons; trivial.
    destruct s, s'; try inversion H2; model_crush.
    inversion H3.
    assert (eq_exp (t s) (t s'')).
    apply H1 with (s' := s'); model_crush.
    inversion H3; trivial.
    apply incl_cons in H5; model_crush.
    eapply eq_exp_trans.
    2: apply H9.
    apply eq_exp_symm.
    apply H1 with (s' := s); model_crush.
    apply eq_subst_refl.
    apply NoDup_cons; trivial.
    apply incl_tl.
    apply incl_refl.
Qed.

  Lemma well_scoped_subst0 : forall (args : list V) (s : named_list term) (a : term),
      NoDup args ->
      ws_subst args s ->
      ws_term (map fst s) a ->
      ws_term args (apply_subst s a).
  Proof.
    model_crush.
    eapply H2; model_crush.
    2: apply incl_refl.
    clear H2.
    induction s; model_crush.
    apply eq_subst_nil.
    apply eq_subst_cons.
    apply IHs; model_crush.
    apply H8 with (s' := s'); model_crush.
Qed.

Instance substable_term_ok : Substable0_ok term.
constructor; intros.
- cbv [Substable.inj_var substable_term inj_var subst_lookup apply_subst0 apply_subst].
  apply subst_var; trivial.
- apply subst_assoc0; trivial.
- apply subst_id0; constructor; destruct H, H0; trivial.
- apply strengthen_subst0; trivial.
- apply well_scoped_subst0; trivial.
Qed.

Instance substable_sort_ok : Substable_ok term sort.
Proof.
  constructor; model_crush.
Qed.

Definition wf_sort (_ : named_list sort) (s : sort) := True.

      Print eq_subst'.

Definition eq_term_model (c : ctx) (s : sort) (e1 e2 : term) :=
  forall ms1 ms2, map fst ms1 = map fst c -> eq_subst' ms1 ms2 -> eq_exp (e1 ms1) (e2 ms2).

Lemma eq_term_model_refl : forall c t e, wf_term c e t -> eq_term_model c t e e.
Proof.
  unfold eq_term_model.
  model_crush.
  eapply H3; model_crush.
  apply H1.
  apply eq_subst_eq_fst in H1.
  rewrite <- H1; rewrite H0.
  apply H.
  apply incl_refl.
Qed.

Lemma eq_term_model_symm : forall c t e1 e2, eq_term_model c t e1 e2 -> eq_term_model c t e2 e1.
Proof.
  unfold eq_term_model in *.
  model_crush.
  apply eq_exp_symm.
  apply H.
  apply eq_subst_eq_fst in H1.
  rewrite <- H1; trivial.

  apply eq_subst_symm.
  trivial.
Qed.

Lemma eq_term_model_trans : forall c t e1 e2 e3, eq_term_model c t e1 e2 -> eq_term_model c t e2 e3 -> eq_term_model c t e1 e3.
Proof.
  unfold eq_term_model in *.
  model_crush.
  apply eq_exp_trans with (e2 ms1).
  apply H; trivial.
  apply eq_subst_refl.
  apply H0; trivial.
Qed.

Notation Model := (@Model V term sort).

#[export] Instance model : Model := mut_mod (eq_sort (A := V * sort)) eq_term_model wf_sort wf_term.

  (* Lemma term_subst_id_eq {A} : forall (c : named_list A) n, apply_subst (with_names_from c (map inj_var (map fst c))) (inj_var n) = inj_var n. *)
  (*   Proof. *)
  (*     model_crush. *)
  (*     induction c; model_crush. *)
  (* Qed. *)

  Lemma eq_subst_dom_eq_l : forall c c' s1 s2, eq_subst c c' s1 s2 -> map fst c' = map fst s1.
  Proof.
    induction 1; model_crush.
  Qed.

  Lemma eq_term_subst : forall (c : ctx) (s1 s2 : named_list term)
                      (c' : ctx) (t : sort)
                      (e1 e2 : term),
                    NoDup (map fst c') ->
                    eq_subst c c' s1 s2 ->
                    eq_term_model c' t e1 e2 ->
                    eq_term_model c t [/s2 /] e1 [/s1 /] e2 [/s2 /].
    Proof.
      unfold eq_term_model in *.
      unfold Substable.apply_subst.
      model_crush.
      eapply eq_exp_trans.
      apply H1.
      clear H1; induction H0; model_crush.
      rewrite <- IHeq_subst; model_crush.
      2: apply eq_exp_refl.
      clear H1.
      induction H0; model_crush.
      apply eq_subst_nil.
      apply eq_subst_cons.
      unfold eq_term_model in *.
      apply IHeq_subst; trivial.
      apply NoDup_cons_iff in H; model_crush.
      apply H1; trivial.
Qed.

  Lemma eq_sort_subst : forall (c : ctx) (s1 s2 : subst)
                      (c' : ctx) (t : sort)
                      (e1 e2 : sort),
                    NoDup (map fst c') ->
                    eq_subst c c' s1 s2 ->
                    eq_sort c' e1 e2 ->
                    eq_sort c e1 [/s1 /] e2 [/s2 /].
    Proof.
      model_crush.
Qed.

  Lemma incl_nodup_eq {A} :
    forall (l l' : named_list A) (n : V) (a a' : A),
      incl ((n, a) :: l) ((n, a') :: l') -> NoDup (n :: map fst l') -> a = a'.
      Proof.
        intros.
        induction l; model_crush.
        unfold incl in H.
        specialize (H (n, a)).
        model_crush.
        assert ((n, a) = (n, a) \/ False) by (left; reflexivity).
        apply H in H1.
        model_crush.
        apply in_fst in H1.
        inversion H0.
        apply H4 in H1; contradiction.
        apply IHl.

        apply incl_cons in H; destruct H.
        apply incl_cons in H1; destruct H1.
        apply incl_cons.
        constructor; trivial.
      Qed.

  Lemma in_fst_in {A} : forall (c c' : named_list A) n a,
      In n (map fst c) -> NoDup (n :: map fst c') -> incl c ((n, a) :: c') -> In (n, a) c.
  Proof.
    model_crush.
    induction c, c'.
    - model_crush.
    - model_crush.
    - specialize (H1 a0); simpl in H1.
      destruct H1.
      left; trivial.
      rewrite <- H1.
      apply in_eq.
      contradiction.
    - model_crush.
      left; model_crush.
      eapply incl_nodup_eq.
      apply H1.
      apply H0.
      right; model_crush.
      apply IHc; model_crush.
      apply incl_cons in H1; model_crush.
  Qed.

  Lemma ws_term_var : forall (c : list V) (n : V),
      NoDup c -> In n c -> ws_term c (inj_var n).
  Proof.
    model_crush.
    rewrite <- H1 in *.
    clear H1.
    apply eq_exp_trans with (e2 := (named_list_lookup default s' n)).
    induction H2.
    inversion H0.
    model_crush.
    cases (eqb n n); model_crush.
    cases (eqb n v); model_crush.
    apply IHeq_subst'; model_crush.
    eapply incl_cons.
    apply H4.
    assert (map fst s' = map fst s).
    clear H; clear H0; clear H4.
    induction H2; model_crush.
    assert (named_list_lookup default s' n = named_list_lookup default s'' n).
    apply named_list_lookup_incl; model_crush.
    rewrite H5.
    apply eq_exp_refl.
Qed.


  Lemma wf_term_var : forall (c : ctx) (n : V) (s : sort),
      NoDup (map fst c) -> In (n, s) c -> wf_term c (inj_var n) s.
  Proof.
    intros.
    unfold wf_term.
    constructor.
    + apply ws_term_var.
      induction H; model_crush.
      apply NoDup_nil.
      apply NoDup_cons; model_crush.
      eapply in_fst.
      apply H0.
    + model_crush.
      induction H1; model_crush.
      cases (eqb n n); model_crush.
      cases (eqb n v); model_crush.
      inversion H.
      apply in_fst in H0.
      apply H7 in H0.
      contradiction.
      apply IHForall2.
      inversion H; trivial.
      trivial.
Qed.

Inductive wf_subst' : list V -> subst -> Prop :=
| wf_subst_nil' : forall c, wf_subst' c []
| wf_subst_cons' : forall c s name e, wf_subst' c s ->
                                  ws_term c e ->
                                  wf_subst' c ((name, e) :: s).

  Lemma wf_subst_wf_subst' : forall c s c', wf_subst c s c' -> wf_subst' (map fst c) s.
  Proof.
    model_crush.
    induction H.
    apply wf_subst_nil'.
    apply wf_subst_cons'; model_crush.
  Qed.

  Inductive ws_subst (c : ctx) : subst -> Prop :=
  | ws_subst_nil : ws_subst c []
  | ws_subst_cons : forall s n e, ws_subst c s -> ws_term (map fst c) e -> ws_subst c ((n, e) :: s).

  Lemma wf_subst_ws : forall c s c', wf_subst c s c' -> ws_subst c s.
  Proof.
    intros.
    induction H.
    apply ws_subst_nil.
    apply ws_subst_cons; model_crush.
  Qed.

  Lemma wf_term_subst_monotonicity : forall (c : ctx) (e : term) (t : sort),
      wf_term c e t ->
      wf_ctx c ->
      forall (c'' : ctx) (s : named_list term),
        NoDup (map fst c'') ->
        wf_subst c'' s c ->
        wf_term c'' e[/s/] t [/s/].
  Proof.
    model_crush.
    assert (map fst c = map fst s).
    clear H0; clear H3; clear H4; clear H; induction H2; model_crush.
    - apply H4 with (named_map (fun x : meta_subst -> exp => x s'') s).
      + model_crush.
      + clear H9.
        apply wf_subst_ws in H2.
        induction H2; model_crush.
        apply eq_subst_nil.
        apply eq_subst_cons; model_crush.
        apply H10 with (s'); trivial.
      + model_crush.
      + apply incl_refl.
    - apply H3.
      clear H; clear H0; clear H1; clear H3; clear H4.
      induction H2; model_crush.
      apply Forall2_cons.
      + constructor; model_crush.
        apply H0; apply H5.
      + apply IHwf_subst.
  Qed.

  Lemma wf_ctx_NoDup : forall c, wf_ctx c -> NoDup (map fst c).
  Proof.
    model_crush.
    induction H; model_crush.
    apply NoDup_nil.
    apply NoDup_cons; trivial.
  Qed.

  Instance model_ok : Model_ok model.
 Proof.
    constructor; intros; repeat (unfold eq_sort in *; trivial; simpl in *).
    + apply substable_term_ok.
    + apply substable_sort_ok.
    + rewrite H; trivial.
    + rewrite H; trivial.
    + apply eq_term_subst with (c' := c'); trivial.
      apply wf_ctx_NoDup; trivial.
    + apply eq_term_model_refl; trivial.
    + apply eq_term_model_trans with (e12); trivial.
    + apply eq_term_model_symm; trivial.
    + rewrite <- H0; trivial.
    + apply wf_term_var; trivial.
    + apply wf_term_subst_monotonicity with (c := c); trivial.
    + model_crush.
Qed.

Class Model_from_exp :=
  {
    subst_term := substable_term;
    subst_sort := substable_sort
}.

      End WithExp.


      (* TODO:
         - Update NatModel to use this GeneralModel
         - Write a simple example of a constant folding algorithm
         - Equality within Pyrosome -> compile to this model
         - Bedrock model (how to define equality of bedrock terms)
      *)
