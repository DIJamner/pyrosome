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

Definition sort := Type.

Notation Substable0 := (Substable0 V).
Notation Substable := (@Substable V).

Definition inj_var (v : V) : term :=
  fun (ms : meta_subst) =>
  named_list_lookup default ms v.


Definition apply_subst (l : named_list term) (t : term) : term :=
  fun (ms' : meta_subst) =>
    t ((named_map (fun x => x ms') l) ++ ms').

Definition id_args {B} (c : named_list B) :=
  map inj_var (map fst c).

Notation id_subst c := (with_names_from c (id_args c)).

Definition id_substable {B} (e : term) :=
  forall (c : named_list B), e = apply_subst (id_subst c) e.

Definition ws_term args (e : term) :=
    (forall s, map fst s = args ->
         forall s', (forall arg, In arg args -> named_list_lookup default s' arg = named_list_lookup default s arg) ->
           e s' = e s)
  /\ forall B, id_substable (B:=B) e.

Instance substable_term : Substable0 term :=
  {
    inj_var := inj_var;
    apply_subst0 := apply_subst;
    well_scoped0 := ws_term
  }.

Instance substable_sort : Substable term sort :=
  {
    apply_subst := fun _ B => B;
    well_scoped := fun _ _ => True
  }.

Definition ctx : Type := named_list sort.

  Definition eq_sort (_ : ctx) (s1 s2 : sort) :=
    s1 = s2.

  Definition wf_sort (_ : ctx) (_ : sort) := True.

  Definition eq_term (_ : ctx) (_ : sort) (t1 t2 : term) :=
    forall (s : named_list exp), t1 s = t2 s.

  Definition wf_term (c : ctx) t (_ : sort) := ws_term (map fst c) t.

Notation Model := (@Model V term sort).

#[export] Instance model : Model := mut_mod eq_sort eq_term wf_sort wf_term.

Ltac unfold_all :=
  repeat (unfold apply_subst, inj_var, subst_lookup, pair_map_snd, wf_term, Substable.apply_subst in *; simpl in *).

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
     | [H : (_, _) = (_, _) |- _] => apply pair_equal_spec in H
     | [H : _ = _ |- _] => try rewrite H
     | [H : ws_term _ ?a |- ws_term _ ?a] => apply H
     | [ |- map fst (named_map _ _) = map fst _] => symmetry
     | [ |- map fst _ = map fst (named_map _ _)] => repeat apply named_map_fst'; trivial
     | _ => idtac
     end;
     try rewrite <- named_map_fst;
     if_refl
    ).


  Lemma eqb_eq_eqb : forall (H1 H2 : Eqb V) (x y : V), eqb (Eqb:=H1) x y = eqb (Eqb:=H2) x y.
    Proof.
      intros.
      case_eq (eqb x y); intros.
      apply eqb_eq in H.
      apply eqb_eq.
      trivial.
      apply eqb_neq in H.
      apply eqb_neq.
      trivial.
Qed.

  Lemma subst_var : forall (H : Eqb V) (s : named_list term) (x : V),
      apply_subst s (inj_var x) = subst_lookup s x.
  Proof.
    model_crush.
    induction s; model_crush.
Qed.

  Lemma lookup_found {A} : forall (l1 l2 : named_list A) d1 d2 (e : V), In e (map fst l1) -> named_list_lookup d1 (l1 ++ l2) e = named_list_lookup d2 l1 e.
  Proof.
    model_crush.
    induction l1; model_crush.
    rewrite H in H0; contradict H0; apply eq_refl.
Qed.

  Lemma ws_term_append : forall (args : list V) (l1 l2 : named_list exp) (a : term),
      ws_term args a -> map fst l1 = args -> a (l1 ++ l2) = a l1.
  Proof.
    model_crush.
    apply H; model_crush.
    apply lookup_found.
    unfold ws_term in H.
    rewrite <- H0 in H1; trivial.
  Qed.

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
      ws_term (map fst s2) a -> apply_subst s1 (apply_subst s2 a) = apply_subst (subst_cmp s1 s2) a.
  Proof.
    model_crush.
    repeat erewrite ws_term_append; model_crush.
    f_equal.
    symmetry.
    apply named_map_cmp.
    trivial.
  Qed.

  Lemma subst_id0 {B} : forall (c : named_list B) (a : term),
      ws_term (map fst c) a -> apply_subst (id_subst c) a = a.
  Proof.
    intros.
    destruct H.
    unfold id_substable in H0.
    specialize (H0 B c).
    auto.
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
      apply_subst ((n, e) :: s) a = apply_subst s a.
  Proof.
    intros.
    unfold apply_subst.
    apply functional_extensionality; intros.
    symmetry; erewrite ws_term_append at 1.
    remember (fun t => t x) as f.
    pose proof (named_map_fst s f (A := (meta_subst -> exp))) as nmf.
    symmetry in nmf.
    destruct H.
    specialize (H (named_map f s) nmf (named_map f ((n, e) :: s) ++ x)).
    symmetry; apply H.
    intros.
    unfold fresh in H0.
    rewrite named_map_cons_eq.
    case_eq (eqb arg n); intros.
    apply eqb_eq in H3.
    rewrite H3 in H2.
    apply H0 in H2; contradiction.
    simpl.
    rewrite H3.
    apply lookup_found.
    rewrite nmf; trivial.
    all: model_crush.
Qed.

  Lemma fun_app_eq {A B} : forall (f g : A -> B) (a : A), f = g -> f a = g a.
  Proof.
    model_crush.
  Qed.

  Lemma well_scoped_subst0 : forall (args : list V) (s : named_list term) (a : term),
      ws_subst args s ->
      ws_term (map fst s) a ->
      ws_term args (apply_subst s a).
  Proof.
    model_crush.
    constructor; model_crush.
    + repeat erewrite ws_term_append; model_crush; model_crush.
      f_equal.
      clear H0.
      induction s.
      trivial.
      destruct a0.
      repeat rewrite named_map_cons_eq.
      destruct H.
      destruct H0.
      destruct H0.
      specialize (H0 s0 H1 s' H2).
      rewrite H0.
      rewrite IHs; trivial.
    + unfold id_substable.
      model_crush.
      repeat erewrite ws_term_append; model_crush; model_crush.
      clear H0.
      f_equal.
      induction s.
      model_crush.
      unfold ws_subst in H.
      destruct a0.
      destruct H.
      destruct H0.
      destruct H0.
      unfold id_substable in H2.
      specialize (H2 B c).
      apply fun_app_eq with (a := x) in H2.
      model_crush.
Qed.

Instance substable_term_ok : Substable0_ok term.
constructor; intros.
- apply subst_var.
- apply subst_assoc0; trivial.
- apply subst_id0; trivial.
- apply strengthen_subst0; trivial.
- apply well_scoped_subst0; trivial.
Qed.

Instance substable_sort_ok : Substable_ok term sort.
Proof.
  constructor;
  model_crush.
Qed.



  Lemma term_subst_id_eq {A} : forall (c : named_list A) n, apply_subst (with_names_from c (map inj_var (map fst c))) (inj_var n) = inj_var n.
    Proof.
      model_crush.
      induction c; model_crush.
  Qed.

  Lemma eq_term_subst : forall (c : ctx) (s1 s2 : named_list term)
                      (c' : ctx) (t : sort) 
                      (e1 e2 : term),
                    eq_subst c c' s1 s2 ->
                    eq_term c' t e1 e2 ->
                    eq_term c t [/s2 /] e1 [/s1 /] e2 [/s2 /].
    Proof.
      unfold eq_term in *.
      unfold Substable.apply_subst.
      model_crush.
      rewrite H0.
      f_equal.
      apply app_inv_tail_iff.
      induction H; model_crush.
    Qed.

  Lemma wf_term_var : forall (c : list V) (n : V),
                  In n c -> ws_term c (inj_var n).
  Proof.
    model_crush.
    constructor; model_crush.
    - apply H1; trivial.
    - unfold id_substable; model_crush.
      induction c0; model_crush.
  Qed.

  Lemma wf_subst_same_name : forall c' s c, wf_subst c' s c -> map fst c = map fst s.
  Proof.
    model_crush.
    induction H; model_crush.
  Qed.


  Lemma wf_term_subst_monotonicity : forall (c : ctx) (e : term) (t : sort),
      wf_term c e t ->
      wf_ctx c ->
      forall (c'' : ctx) (s : named_list term),
        wf_subst c'' s c ->
        wf_term c'' e[/s/] t [/s/].
  Proof.
    constructor; unfold Substable.apply_subst; model_crush.
    + repeat erewrite ws_term_append; model_crush; model_crush.
      clear H.
      f_equal.
      induction H1.
      trivial.
      inversion H0.
      simpl.
      rewrite IHwf_subst.
      inversion H.
      specialize (H10 s0 H2 s' H3).
      rewrite H10.
      trivial.
      trivial.
      all: erewrite <- wf_subst_same_name; eauto.
    + unfold id_substable.
      model_crush.
      apply wf_subst_same_name in H1 as Hs.
      repeat erewrite ws_term_append; model_crush; model_crush.
      f_equal.
      clear H.
      induction H1; trivial.
      simpl.
      inversion H0.
      rewrite IHwf_subst; trivial.
      inversion H.
      unfold id_substable in H9.
      specialize (H9 B c0).
      apply fun_app_eq with (a := x) in H9.
      rewrite H9.
      trivial.
      apply wf_subst_same_name in H1.
      trivial.
      all: erewrite <- wf_subst_same_name; eauto.
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
    + unfold eq_term in *; trivial.
    + unfold eq_term in *; intros; rewrite H; trivial.
    + unfold eq_term in *; symmetry; trivial.
    + apply wf_term_var; trivial; eapply in_fst; apply H.
    + apply wf_term_subst_monotonicity with (c := c); trivial.
Qed.

Class Model_from_exp :=
  {
    subst_term := substable_term;
    subst_sort := substable_sort
  }.


End WithExp.
