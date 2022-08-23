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


Context {V : Type}.

Locate named_list.
Notation named_list := (@named_list V).
Notation Substable0 := (Substable0 V).
Notation Substable := (@Substable V).

Definition sort := Type.

Definition term' : sort := named_list nat -> nat.

Notation Model' := (@Model V term' sort).
Definition subst' : Type := named_list term'.
Definition ctx : Type := named_list sort.

Section WithEqb.
  Context {V_Eqb : Eqb V}.

  Definition term_subst' (s : subst') e : term' :=
    fun (s' : named_list nat) =>
      e ((named_map (fun (t : term') => t s') s) ++ s').

  Definition var' (default : term') (n : V) : term' :=
    fun (s : named_list nat) =>
      named_list_lookup (default s) s n.

  Definition val' (v : nat) : term' :=
    fun _ => v.

  Definition bin_op (op : nat -> nat -> nat) (t1 t2 : term') : term' :=
    fun (s : named_list nat) =>
      op (t1 s) (t2 s).

  Definition inj_var' := var' (val' 0).
  Definition id_args' {B} (c : named_list B) :=
      map inj_var' (map fst c).

  Notation id_subst c := (with_names_from c (id_args' c)).

  Definition id_substable (e : term') :=
    forall (c c' : named_list nat), (forall x, named_list_lookup 0 c x = named_list_lookup 0 c' x) -> e c = e c'.

  Definition term := { x : term' | id_substable x}.

  Definition val (v : nat) : term.
    apply exist with (x := val' v).
    unfold id_substable, val'.
    trivial.
  Qed.

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
    | _ => idtac
    end;
    match goal with
    | [ |- (if eqb ?a ?a then _ else _) = _ ] => replace (eqb a a) with (true); try (symmetry; apply eqb_refl)
    | _ => idtac
    end.

  Lemma fun_app_eq {A B} : forall (f g : A -> B) (a : A), f = g -> f a = g a.
  Proof.
    intros.
    rewrite H.
    trivial.
  Qed.

  Lemma inj_var_ok : forall (v : V), id_substable (inj_var' v).
    intros.
    unfold id_substable.
    intros.
    unfold inj_var, var', val', term_subst'.
    apply H.
  Qed.

  Definition inj_var (v : V) : term :=
    exist _ (inj_var' v) (inj_var_ok v).

  Definition subst : Type := named_list term.

  Lemma term_subst_ok : forall (s : subst) (e : term), id_substable
    (term_subst' (named_map (fun t : term => proj1_sig t) s) (proj1_sig e)).
  Proof.
    intros.
    destruct e.
    simpl.
    unfold term_subst'.
    unfold id_substable, term_subst' in *.
    intros.
    apply i.
    intros.
    induction s.
    trivial.
    simpl.
    destruct a; simpl.
    case (eqb x0 v); trivial.
    unfold proj1_sig.
    destruct t.
    unfold id_substable in i0.
    apply i0.
    trivial.
Defined.
  
  Definition term_subst (s : subst) (e : term) : term :=
    exist (fun x : term' => id_substable x)
          (term_subst' (named_map (fun t : term => proj1_sig t) s) (proj1_sig e))
          (term_subst_ok s e).

  Definition ws_term args (e : term) :=
    forall s, map fst s = args ->
         forall s', (forall arg, In arg args -> named_list_lookup 0 s arg = named_list_lookup 0 s' arg)
               -> (proj1_sig e) s = (proj1_sig e) s'.

  Instance substable_term : Substable0 term :=
    {
      inj_var := inj_var;
      apply_subst0 := term_subst;
      well_scoped0 := ws_term
    }.

  Instance substable_sort : Substable term sort :=
    {
      apply_subst := fun _ B => B;
      well_scoped := fun _ _ => True
    }.

  Ltac unfold_defs :=
    try unfold inj_var, var', val', apply_subst, term_subst, ws_term, id_substable in *.

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
      term_subst s (inj_var x) = subst_lookup s x.
  Proof.
    intros.
    unfold term_subst.
    unfold subst_lookup.
    simpl.
    unfold inj_var.
    induction s; simpl.
    f_equal.
    unfold pair_map_snd.
    destruct a.
    case (eqb x v); trivial.
    destruct t.
    simpl.
    unfold term_subst'.
    unfold inj_var'.
    (* apply functional_extensionality. *)
    (* intros. *)
    (* simpl. *)
    (* f_equal. *)
    (* assert (eqb (Eqb:=V_Eqb) x v = eqb (Eqb:=H) x v)by apply eqb_eq_eqb. *)
    Admitted.

  Lemma lookup_found {A} : forall (l1 l2 : named_list A) d1 d2 (e : V), In e (map fst l1) -> named_list_lookup d1 (l1 ++ l2) e = named_list_lookup d2 l1 e.
  Proof.
    intros.
    induction l1.
    inversion H.
    simpl in *.
    destruct H; destruct a; simpl in *.
    rewrite H.
    assert (eqb e e = true).
    apply eqb_eq.
    trivial.
    rewrite H0; simpl.
    trivial.
    case (eqb e v).
    trivial.
    apply IHl1.
    apply H.
Qed.

  Lemma named_map_cons_eq {A B} : forall l (n : V) (e : A) (f : A -> B),
      named_map f ((n, e) :: l) = (n, f e) :: named_map f l.
  Proof.
    trivial.
  Qed.

   Lemma named_map_cmp {A B C} : forall (f : B -> C) (g : A -> B) h (l : named_list A), (forall x, f (g x) = h x) -> named_map f (named_map g l) = named_map h l.
  Proof.
    intros.
    induction l.
    trivial.
    destruct a.
    repeat rewrite named_map_cons_eq.
    apply invert_eq_cons_cons.
    constructor.
    rewrite H; trivial.
    trivial.
Qed.

  Lemma ws_term_append : forall (args : list V) (l1 l2 : named_list nat) (a : term),
      ws_term args a -> args = map fst l1 -> (proj1_sig a) (l1 ++ l2) = (proj1_sig a) l1.
  Proof.
    intros.
    unfold ws_term in  H.
    symmetry in H0.
    specialize (H l1 H0 (l1 ++ l2)).
    symmetry.
    apply H.
    intros.
    symmetry.
    apply lookup_found.
    rewrite <- H0 in H1; trivial.
  Qed.

  Lemma named_map_fst {A B} : forall (l : named_list A) (f : A -> B), map fst l = map fst (named_map f l).
    Proof.
      intros.
      induction l.
      trivial.
      destruct a.
      rewrite named_map_cons_eq.
      repeat rewrite map_cons.
      simpl.
      apply invert_eq_cons_cons.
      constructor; trivial.
    Qed.


  Lemma named_map_fst' {A B C} : forall (l1 : named_list A) (l2 : named_list B) (f : B -> C), map fst l1 = map fst l2 -> map fst l1 = map fst (named_map f l2).
    Proof.
      intros; rewrite H.
      apply named_map_fst.
    Qed.

  Ltac cleanup_ws_append :=
    match goal with
    | [H : ws_term _ ?a |- ws_term _ ?a] => apply H
    | [ |- map fst _ = map fst (named_map _ _)] => repeat apply named_map_fst'; trivial
    | _ => idtac
    end.

  Lemma subst_assoc0 : forall (s1 s2 : named_list term) (a : term),
      ws_term (map fst s2) a -> term_subst s1 (term_subst s2 a) = term_subst (subst_cmp s1 s2) a.
  Proof.
    intros.
    unfold subst_cmp.
    simpl.
    unfold term_subst in *.
    apply functional_extensionality; intros.
    repeat erewrite ws_term_append; cleanup_ws_append.
    f_equal.
    symmetry.
    apply named_map_cmp.
    trivial.
Qed.

  Lemma subst_id0 {B} : forall (c : named_list B) (a : term),
      ws_term (map fst c) a -> term_subst (id_subst c) a = a.
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
    induction l.
    trivial.
    inversion H; rewrite map_cons; simpl.
    left.
    rewrite H0.
    trivial.
    apply IHl in H0.
    right.
    trivial.
Qed.
    
    
  Lemma in_fst' {A} : forall n (e : A) (l1 : named_list A) (l2 : list V), map fst l1 = l2 -> In n l2 -> In n (map fst l1).
  Proof.
    intros.
    rewrite H.
    trivial.
Qed.

  Lemma strengthen_subst0 : forall (s : named_list term) (e a : term) (n : V),
      ws_term (map fst s) a -> fresh n s ->
      term_subst ((n, e) :: s) a = term_subst s a.
  Proof.
    intros.
    unfold term_subst.
    apply functional_extensionality; intros.
    symmetry; erewrite ws_term_append at 1; cleanup_ws_append.
    remember (fun t : term => t x) as f.
    pose proof (named_map_fst s f) as nmf.
    symmetry in nmf.
    destruct H.
    specialize (H (named_map f s) nmf (named_map f ((n, e) :: s) ++ x)).
    apply H.
    intros.
    unfold fresh in H0.
    rewrite named_map_cons_eq.
    case_eq (eqb arg n); intros.
    apply eqb_eq in H3.
    rewrite H3 in H2.
    apply H0 in H2; contradiction.
    simpl.
    rewrite H3.
    symmetry; apply lookup_found.
    rewrite nmf; trivial.
Qed.

  Lemma well_scoped_subst0 : forall (args : list V) (s : subst) (a : term),
      ws_subst args s ->
      ws_term (map fst s) a ->
      ws_term args (term_subst s a).
  Proof.
    constructor; intros.
    + unfold term_subst.
      repeat erewrite ws_term_append; cleanup_ws_append.
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
      intros.
      unfold term_subst.
      apply functional_extensionality; intros.
      repeat erewrite ws_term_append; cleanup_ws_append.
      clear H0.
      f_equal.
      induction s.
      trivial.
      destruct a0.
      repeat rewrite named_map_cons_eq.
      destruct H.
      destruct H0.
      destruct H0.
      unfold id_substable in H2.
      specialize (H2 B c).
      unfold term_subst in H2.
      apply fun_app_eq with (a := x) in H2.
      rewrite H2.
      rewrite IHs; trivial.
Qed.

  Instance substable_term_ok : Substable0_ok term.
  Proof.
    constructor; intros.
    + apply subst_var.
    + apply subst_assoc0; trivial.
    + apply subst_id0; trivial.
    + apply strengthen_subst0; trivial.
    + apply well_scoped_subst0; trivial.
Qed.

  Instance substable_sort_ok : Substable_ok term sort.
  Proof.
    constructor; intros; trivial.
  Qed.

  Definition eq_sort (_ : ctx) (s1 s2 : sort) :=
    s1 = s2.

  Definition wf_sort (_ : ctx) (_ : sort) := True.

  Definition eq_term (_ : ctx) (_ : sort) (t1 t2 : term) :=
    forall (s : named_list nat), t1 s = t2 s.

  Definition wf_term (c : ctx) t (_ : sort) := ws_term (map fst c) t.

  #[export] Instance model : Model := mut_mod eq_sort eq_term wf_sort wf_term.


  Lemma term_subst_id_eq {A} : forall (c : named_list A) n, term_subst (with_names_from c (map inj_var (map fst c))) (var (val 0) n) = var (val 0) n.
    Proof.
    intros.
    unfold term_subst in *.
    apply functional_extensionality.
    intros.
    unfold inj_var in *.
    unfold var in *.
    unfold val in *.
    induction c.
    trivial.
    destruct a.
    simpl.
    case_eq (eqb n v); intros.
    apply eqb_eq in H.
    rewrite H; trivial.
    apply IHc.
  Qed.

  Print Model_ok.

  Lemma eq_term_subst : forall (c : ctx) (s1 s2 : subst)
                      (c' : ctx) (t : sort) 
                      (e1 e2 : term),
                    eq_subst c c' s1 s2 ->
                    eq_term c' t e1 e2 ->
                    eq_term c t [/s2 /] e1 [/s1 /] e2 [/s2 /].
    Proof.
      unfold eq_term in *.
      intros.
      unfold apply_subst.
      simpl.
      unfold term_subst.
      rewrite H0.
      f_equal.
      apply app_inv_tail_iff.
      induction H.
      trivial.
      repeat rewrite named_map_cons_eq.
      apply invert_eq_cons_cons; constructor.
      simpl in H1.
      unfold eq_term in H1.
      rewrite H1.
      trivial.
      apply IHeq_subst.
    Qed.

  Lemma wf_term_var : forall (c : list V) (n : V),
                  In n c -> ws_term c (inj_var n).
  Proof.
    unfold_defs.
    constructor; intros; simpl.
    - apply H1; trivial.
    - apply functional_extensionality.
      intros.
      induction c0.
      trivial.
      destruct a.
      unfold term_subst.
      simpl in *.
      case_eq (eqb n v); intros.
      apply eqb_eq in H0.
      rewrite H0.
      trivial.
      apply IHc0.
  Qed.

Print Model_ok.

  Lemma wf_subst_same_name : forall c' s c, wf_subst c' s c -> map fst c = map fst s.
  Proof.
    intros.
    induction H; trivial.
    simpl.
    rewrite IHwf_subst.
    trivial.
  Qed.


  Lemma wf_term_subst_monotonicity : forall (c : ctx) (e : term) (t : sort),
      wf_term c e t ->
      wf_ctx c ->
      forall (c'' : ctx) (s : subst),
        wf_subst c'' s c ->
        wf_term c'' e[/s/] t [/s/].
  Proof.
    constructor; intros.
    + unfold_defs.
      unfold wf_term in H.
      apply wf_subst_same_name in H1 as Hs.
      repeat erewrite ws_term_append; cleanup_ws_append.
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
      eapply wf_subst_same_name; apply H1.
    + unfold_defs.
      unfold wf_term in H.
      intros.
      apply wf_subst_same_name in H1 as Hs.
      apply functional_extensionality; intros.
      unfold term_subst.
      repeat erewrite ws_term_append; cleanup_ws_append.
      f_equal.
      clear H.
      induction H1; trivial.
      simpl.
      inversion H0.
      rewrite IHwf_subst; trivial.
      inversion H.
      unfold id_substable in H9.
      specialize (H9 B c0).
      unfold term_subst in H9.
      apply fun_app_eq with (a := x) in H9.
      rewrite H9.
      trivial.
      apply wf_subst_same_name in H1.
      trivial.
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


  Inductive iterm : Type :=
  | ival : nat -> iterm
  | ivar : V -> iterm
  | ibinop : (nat -> nat -> nat) -> iterm -> iterm -> iterm
  .

  Fixpoint iterm_to_term (i : iterm) :=
    match i with
    | ival n => val n
    | ivar n => inj_var n
    | ibinop op i1 i2 => bin_op op (iterm_to_term i1) (iterm_to_term i2)
    end.

  Fixpoint scope (i : iterm) :=
    match i with
    | ival n => []
    | ivar n => [n]
    | ibinop op i1 i2 => scope i1 ++ scope i2
    end.



  Lemma ws_iterm_to_term : forall i, ws_term (scope i) (iterm_to_term i).
  Proof.
    induction i; constructor; intros; simpl; trivial.
    - unfold_defs; trivial.
    - apply H0; left; trivial.
    - unfold id_substable.
      intros.
      unfold_defs.
      apply functional_extensionality; intros.
      induction c; trivial.
      destruct a.
      simpl.
      cases (eqb v v0).
      trivial.
      apply IHc.
    - unfold bin_op.
      f_equal.
      + destruct IHi1.
        clear H2.
        clear IHi2.
        remember (map (fun x => (x, named_list_lookup 0 s x)) (scope i1)) as s1.
        specialize (H1 s1).
        rewrite <- H1.
        2: {
          rewrite Heqs1.
          rewrite map_map.
          simpl.
          apply map_id.
        }
        2: {
          intros.
          clear H1.
          rewrite Heqs1.
          clear Heqs1.
          induction (scope i1); destruct H2.
          { 
            simpl.
            if_refl.
            trivial.
          } 
          {
            simpl.
            cases (eqb arg a); trivial.
            apply IHl; trivial.
          }
        }
        apply H1.
        rewrite Heqs1.
        rewrite map_map.
        simpl.
        apply map_id.
        intros.
        clear H1.
        rewrite Heqs1.
        clear Heqs1.
        simpl in *.
        clear H.
        induction (scope i1).
        destruct H2.
        destruct H2.
        simpl.
        if_refl.
        apply H0.
        simpl; left.
        trivial.
        simpl.
        cases (eqb arg a).
        apply H0.
        simpl; left;trivial.
        apply IHl.
        intros.
        apply H0.
        simpl; right; trivial.
        trivial.
      + destruct IHi2.
        clear H2.
        clear IHi1.
        remember (map (fun x => (x, named_list_lookup 0 s x)) (scope i2)) as s2.
        specialize (H1 s2).
        rewrite <- H1.
        2: {
          rewrite Heqs2.
          rewrite map_map.
          simpl.
          apply map_id.
        }
        2: {
          intros.
          clear H1.
          rewrite Heqs2.
          clear Heqs2.
          induction (scope i2); destruct H2.
          { 
            simpl.
            if_refl.
            trivial.
          } 
          {
            simpl.
            cases (eqb arg a); trivial.
            apply IHl; trivial.
          }
        }
        apply H1.
        rewrite Heqs2.
        rewrite map_map.
        simpl.
        apply map_id.
        intros.
        clear H1.
        rewrite Heqs2.
        clear Heqs2.
        simpl in *.
        clear H.
        induction (scope i2).
        destruct H2.
        destruct H2.
        simpl.
        if_refl.
        apply H0.
        Search (In _ (_ ++ _)).
        apply in_or_app; right.
        simpl; left; trivial.
        simpl.
        cases (eqb arg a).
        apply H0.
        apply in_or_app; right.
        simpl; left;trivial.
        apply IHl.
        intros.
        apply H0.
        apply in_or_app.
        apply in_app_or in H2.
        assert (In arg0 l -> In arg0 (scope i1) \/ In arg0 (a :: l)).
        intros.
        simpl; right; right; trivial.
        assert (In arg0 (scope i1) -> In arg0 (scope i1) \/ In arg0 (a :: l)).
        intros.
        simpl; left; trivial.
        apply (or_ind H4 H3 H2).
        trivial.
    - unfold id_substable.
      intros.
      unfold bin_op.
      apply functional_extensionality.
      intros.
      unfold term_subst.
      f_equal.
      destruct IHi1.
      unfold id_substable in H0.
      unfold term_subst in H0.
      specialize (H0 B c).
      eapply fun_app_eq in H0.
      apply H0.
      destruct IHi2.
      unfold id_substable in H0.
      unfold term_subst in H0.
      specialize (H0 B c).
      eapply fun_app_eq in H0.
      apply H0.
Qed.


     End Eqb.



        








      

      













