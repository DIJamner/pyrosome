Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Substable Model Compilers.
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
        (default : exp).


Notation named_list := (@named_list V).

Definition meta_subst := named_list exp.

Definition term := meta_subst -> exp.

Definition sort := meta_subst -> Type.

Definition ctx : Type := named_list sort.

  Definition eq_sort (_ : ctx) (s1 s2 : sort) :=
    s1 = s2.

  Definition wf_sort (_ : ctx) (_ : sort) := True.

  Definition eq_term (c : ctx) (_ : sort) (t1 t2 : term) :=
    (* TODO: check if this is the right way around *)
    forall (s : named_list exp), NoDup (map fst s) -> incl (map fst c) (map fst s) -> t1 s = t2 s.

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

(* TODO change to eq_term *)
Definition eq_term0 args (e1 e2 : term) :=
  forall ms, map fst ms = args -> e1 ms = e2 ms.

Lemma eq_term0_refl : forall args e1, eq_term0 args e1 e1.
Proof.
  unfold eq_term0.
  trivial.
Qed.

Lemma eq_term0_trans : forall args e1 e2 e3, eq_term0 args e1 e2 -> eq_term0 args e2 e3 -> eq_term0 args e1 e3.
Proof.
  unfold eq_term0.
  intros.
  rewrite H; trivial.
  apply H0; trivial.
Qed.

Lemma eq_term0_comm : forall args e1 e2, eq_term0 args e1 e2 -> eq_term0 args e2 e1.
Proof.
  unfold eq_term0.
  symmetry.
  apply H; trivial.
Qed.


(* TODO make this simpler? *)
Definition ws_term args (e : term) :=
  NoDup args /\
  forall s, map fst s = args -> forall s', NoDup (map fst s') -> incl s s' -> e s' = e s.

Definition id_substable {B} (e : term) :=
  forall (c : named_list B),
    ws_term (map fst c) e
    -> forall args, ws_term args e
              -> eq_term0 args e (apply_subst (id_subst c) e).

Definition wf_term (c : ctx) t (_ : sort) := ws_term (map fst c) t.

Instance substable_term : Substable0 term :=
  {
    inj_var := inj_var;
    eq_term0 := eq_term0;
    apply_subst0 := apply_subst;
    well_scoped0 := ws_term
  }.

Instance substable_sort : Substable term sort :=
  {
    apply_subst := fun _ B => B;
    eq_term := fun _ => eq;
    well_scoped := fun _ _ => True
  }.

Notation Model := (@Model V term sort).

#[export] Instance model : Model := mut_mod eq_sort eq_term wf_sort wf_term.

Ltac unfold_all :=
  repeat (
      unfold ws_term, apply_subst, inj_var, subst_lookup, pair_map_snd,
      wf_term, Substable.apply_subst, eq_term0 in *;
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
     | [H : ?a, H': ?a -> ?b |- _] => apply H' in H; clear H'
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
  Qed.

  Lemma merge_named_lists_incl {A} (l1 l2 : named_list A) : 
    incl l2 (merge_named_lists l1 l2).
  Proof.
    induction l1; model_crush; try apply incl_refl.
    case (inb v (map fst l2)).
    - apply IHl1.
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
    induction l1; model_crush; apply NoDup_cons_iff in H; destruct H; apply IHl1 in H1.
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
Qed.

  Lemma id_substable_pf {B : Type}: forall e,
    id_substable (B:=B) e.
  Proof.
    unfold id_substable.
    unfold eq_term0.
    model_crush.
    specialize (H3 (named_map (fun x : meta_subst -> exp => x ms) (id_subst c))).
    specialize (H2 ms H1).
    rewrite <- H3 with (s' := (merge_named_lists (named_map (fun x => x ms) (id_subst c)) ms)); model_crush.
    symmetry; apply H2; model_crush.
    all: unfold id_args; model_crush.
    apply NoDup_merged_lists; model_crush.
    apply merge_named_lists_incl; model_crush.
    apply NoDup_merged_lists; model_crush.
    clear H3.
    induction c; model_crush; try apply incl_nil_l.
    apply List.incl_cons; cases (inb v args).
    * apply merge_named_lists_in_l2.
      apply in_lookup.
      rewrite H1.
      apply inb_in; trivial.
    * apply in_eq.
    * apply IHc.
      apply NoDup_cons_iff in H.
      destruct H.
      trivial.
    * apply incl_tl.
      apply IHc.
      apply NoDup_cons_iff in H.
      destruct H.
      trivial.
Qed.


  Lemma eqb_eq_eqb : forall (H1 H2 : Eqb V) (x y : V), eqb (Eqb:=H1) x y = eqb (Eqb:=H2) x y.
    Proof.
      intros.
      case_eq (eqb x y); model_crush.
Qed.

  Lemma subst_var : forall (H : Eqb V) (s : named_list term) (x : V),
      In x (map fst s) ->
      forall args,
      eq_term0 args (apply_subst s (inj_var x)) (subst_lookup s x).
  Proof.
    model_crush.
    induction s; model_crush.
Qed.

  Lemma lookup_found {A} : forall (l1 l2 : named_list A) d1 d2 (e : V), In e (map fst l1) -> named_list_lookup d1 (l1 ++ l2) e = named_list_lookup d2 l1 e.
  Proof.
    model_crush.
    induction l1; model_crush.
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
        eq_term0 args (apply_subst s1 (apply_subst s2 a)) (apply_subst (subst_cmp s1 s2) a).
  Proof.
    model_crush.
    repeat erewrite ws_term_append; model_crush.
    f_equal.
    symmetry.
    apply named_map_cmp.
    trivial.
  Qed.

  Lemma subst_id0 {B} : forall (c : named_list B) (a : term),
      ws_term (map fst c) a -> forall args, ws_term args a -> eq_term0 args (apply_subst (id_subst c) a) a.
  Proof.
    intros.
    pose proof (id_substable_pf (B := B) (e := a) c) as id_sub.
    apply eq_term0_comm.
    apply id_sub; model_crush.
Qed.

  Lemma in_fst {A} : forall n (e : A) (l : named_list A), In (n, e) l -> In n (map fst l).
  Proof.
    intros.
    induction l; model_crush.
    left; trivial.
    right; trivial.
Qed.
    
    
  Lemma in_fst' {A} : forall n (e : A) (l1 : named_list A) (l2 : list V), map fst l1 = l2 -> In n l2 -> In n (map fst l1).
  Proof.
    model_crush.
Qed.

  Lemma strengthen_subst0 : forall (s : named_list term) (e a : term) (n : V),
      ws_term (map fst s) a -> fresh n s ->
      forall args,
      eq_term0 args (apply_subst ((n, e) :: s) a) (apply_subst s a).
  Proof.
    model_crush.
    apply H1; simpl; try rewrite <- named_map_fst in *; simpl; trivial.
    apply NoDup_cons; assumption.
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
    induction s; model_crush.
    inversion H2.
    clear IHs.
    assert (t s' = t s).
    apply H1; model_crush.
    apply incl_cons in H4.
    model_crush.
    rewrite H6.
    symmetry.
    apply H1; model_crush.
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
    f_equal.
    clear H2.
    induction s; model_crush.
    apply H7; model_crush.
Qed.

Instance substable_term_ok : Substable0_ok term.
constructor; intros.
- apply subst_var; trivial.
  admit.
- apply subst_assoc0; trivial.
- apply subst_id0; constructor; destruct H, H0; trivial.
- apply strengthen_subst0; trivial.
- apply well_scoped_subst0; trivial.
  admit.
Admitted.

Instance substable_sort_ok : Substable_ok term sort.
Proof.
  constructor;
  model_crush.
Qed.



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
                    eq_term c' t e1 e2 ->
                    eq_term c t [/s2 /] e1 [/s1 /] e2 [/s2 /].
    Proof.
      unfold eq_term in *.
      unfold Substable.apply_subst.
      model_crush.
      rewrite H1; model_crush.
      f_equal.
      clear H1.
      induction H0; model_crush.
      unfold eq_term in H1.
      apply H1; trivial.
      apply IHeq_subst; trivial.
      apply NoDup_cons_iff in H; model_crush.
      all: erewrite <- eq_subst_dom_eq_l; try apply H0; model_crush.
      apply incl_refl.
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
      apply NoDup_cons_iff in H0; model_crush.
      apply incl_cons in H1; model_crush.
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

  Lemma wf_term_var : forall (c : list V) (n : V),
      NoDup c -> In n c -> ws_term c (inj_var n).
  Proof.
    model_crush.
    rewrite <- H1 in *.
    clear H1.
    symmetry.
    apply named_list_lookup_incl; trivial.
Qed.

      Print wf_subst.
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

  Lemma wf_term_subst_monotonicity : forall (c : ctx) (e : term) (t : sort),
      wf_term c e t ->
      wf_ctx c ->
      forall (c'' : ctx) (s : named_list term),
        NoDup (map fst c'') ->
        wf_subst c'' s c ->
        wf_term c'' e[/s/] t [/s/].
  Proof.
    model_crush.
    f_equal.
    clear H0.
    Print wf_subst.
    apply wf_subst_wf_subst' in H2.
    induction s; model_crush.
    inversion H2; model_crush.
    2: {
      apply IHs.
      inversion H2.
      assumption.
    }
    unfold ws_term in H10; model_crush.
    apply H12; trivial.
  Qed.

  Instance model_ok : Model_ok model.
  Proof.
    constructor; intros; trivial; simpl in *.
    + apply substable_term_ok.
    + apply substable_sort_ok.
    + unfold eq_sort; trivial.
    + unfold eq_sort in *; inversion H; inversion H0; trivial.
    + unfold eq_sort in *; symmetry; trivial.
    + apply eq_term_subst with (c' := c'); trivial.
      admit.
    + unfold eq_term in *; trivial.
    + unfold eq_term in *; intros; rewrite H; trivial; apply H0; model_crush.
    + unfold eq_term in *; symmetry; trivial; apply H; model_crush.
    + apply wf_term_var; trivial.
      admit.
      eapply in_fst; apply H.
    + apply wf_term_subst_monotonicity with (c := c); trivial.
      admit.
Admitted.

Class Model_from_exp :=
  {
    subst_term := substable_term;
    subst_sort := substable_sort
}.
