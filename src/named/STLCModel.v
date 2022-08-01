Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Substable Model GeneralModel Compilers.
From Named Require Term.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive out_ty :=
| ty : Type -> out_ty
| arr : out_ty -> out_ty -> out_ty.

Definition env_ty := list out_ty.


Fixpoint out (t : out_ty) :=
  match t with
  | ty t' => t'
  | arr t1 t2 => (out t1) -> (out t2)
  end.

Definition env (t : env_ty) := fold_right prod unit (map out t).

Definition exp G A := env G -> out A.

Definition subst G G' := env G -> env G'.

Definition emp : env_ty := [].
Definition ext (G : env_ty) (A : out_ty) : env_ty := A :: G.
Arguments ext G A : clear implicits.

Definition wkn {G} {A} : subst (ext G A) G := snd.

Definition hd {G A} : exp (ext G A) A := fst.

Definition term_subst {G G' A} (g : subst G G') (e : exp G' A) :=
  fun x => e (g x).

Definition ty_subst {G G'} (g : subst G G') (t : env G' -> Type) :=
  fun x => t (g x).

Definition forget {G} : subst G emp := fun _ => tt.

Definition snoc {G G' A} (g : subst G G') (e : exp G' A) : subst G (ext G' A) :=
  fun x => let x' := g x in (e x', x').

(* TODO : ws lemmas for each def *)
Definition lam G A B (e : exp (ext G A) B) : exp G (arr A B) :=
  fun g a => e (a, g).

Definition app G A B (e1 : exp G (arr A B)) (e2 : exp G A) : exp G B :=
  fun g => e1 g (e2 g).

Lemma beta G A B (e : exp (ext G A) B) (e' : exp G A)
  : app (lam e) e' = term_subst (snoc id e') e.
  unfold exp, ext, ty_subst, snoc, id, app, lam in *.
  intuition.
Qed. 

Definition gexp := {G & {A & exp G A}}.

Context {V : Type}
        {V_Eqb : Eqb V}
        {V_default : WithDefault V}.

Notation named_list := (@named_list V).
Notation Substable0 := (Substable0 V).
Notation Substable := (@Substable V).
Notation term := (@GeneralModel.term V gexp).
Notation meta_subst := (@GeneralModel.meta_subst V gexp).

Definition term_lam (e : term) : term :=
  fun ms : meta_subst =>
    let e_ms := e ms in
    let (G, p) := e_ms in
    let (B, e') := p in
    match G as g return (G = g -> gexp) with
    | [] => fun _ => e ms
    | A :: G' =>
        (fun H =>
           let e' := eq_rect G (fun G1 => exp G1 B) e' (A :: G') H in
           existT _ G' (existT _ (arr A B) (lam e')))
    end eq_refl.

Definition default_emp : gexp :=
  existT _ emp
  (existT (fun A => exp emp A) (ty unit)
     (fun _ => tt)).

Fixpoint out_ty_eq (t1 t2 : out_ty) :=
  match t1, t2 with
  | ty t1, ty t2 => t1 = t2
  | arr t11 t12, arr t21 t22 => (out_ty_eq t11 t21) /\ (out_ty_eq t12 t22)
  | _, _ => True
  end.

Definition term_env_ty (e : term) (ms : meta_subst) : env_ty :=
  let e_ms := e ms in
  let (G, p) := e_ms in G.

Definition term_out_ty (e : term) (ms : meta_subst) : out_ty :=
  let e_ms := e ms in
  let (G, p) := e_ms in
  let (A, _) := p in A.


Definition term_app
           (e1 e2 : term)
           (pf : forall ms, term_env_ty e1 ms = term_env_ty e2 ms)
           (pf' : forall ms, term_out_ty e1 ms = arr A )
  : term.
unfold term in *.
intros.
specialize (pf X).
unfold term_env_ty in pf.
unfold gexp.
remember (e1 X) as e1'.
remember (e2 X) as e2'.
clear Heqe1'.
clear Heqe2'.
clear e1.
clear e2.
unfold gexp in e1', e2'.
destruct e1', e2'.
rename x into G.
rename x0 into G'.
inversion s; clear s.
rename x into T1.
rename X0 into e1.
inversion s0; clear s0.
rename x into T2.
rename X0 into e2.
destruct T1.
apply default_emp.
rewrite <- pf in *.

apply (app e1 e2).


Search (Eqb _).
repeat econstructor.

Definition term_app (e1 : term) (e2 : term) : term :=
  fun ms : meta_subst =>
    let e1_ms := e1 ms in
    let e2_ms := e2 ms in
    let (G1, p1) := e1_ms in
    let (T1, e1') := p1 in
    let (G2, p2) := e2_ms in
    let (T2, e2') := p2 in
    match T1 as t1 return (T1 = t1 -> gexp) with
    | ty t1' => default_emp
    | arr A B =>
        (fun H =>
           let e' := eq_rect G (fun G1 => exp G1 B) e' (A :: G') H in
           existT _ G (existT _ (arr A B) (lam e')))
    end eq_refl.


Notation id_substable := (GeneralModel.id_substable (exp := gexp) default_emp).
Print GeneralModel.id_substable.
Check id_substable.

Lemma lam_id_substable {G A B} : forall e, id_substable (existT _ (ext G A) (existT _ B e)) -> id_substable (lam e).



Definition model := (GeneralModel.model).



Notation Substable0 := (Substable0 V).
Notation Substable := (@Substable V).

Definition var (default : gexp) (v : V) : term :=
  fun (ms : meta_subst) =>
  named_list_lookup default ms v.


Definition apply_subst (l : named_list term) (t : term) : term :=
  fun (ms' : meta_subst) =>
    t ((named_map (fun x => x ms') l) ++ ms').


Definition default_emp : gexp :=
  existT (fun G => {A & exp G A}) unit
  (existT (fun A => exp unit A) unit
     (fun _ => tt)).


Definition inj_var (v : V) : term :=
  var default_emp v.

Instance model : Model term := GeneralModel.mut_mod.

Definition id_args {B} (c : named_list B) :=
  map inj_var (map fst c).

Notation id_subst c := (with_names_from c (id_args c)).

Definition id_substable {B} (e : term) :=
  forall (c : named_list B), e = apply_subst (id_subst c) e.

Definition ws_term args (e : term) :=
    (forall s, map fst s = args ->
         forall s', (forall arg, In arg args -> named_list_lookup default_emp s arg = named_list_lookup default_emp s' arg) ->
           e s = e s')
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


Ltac unfold_all :=
  repeat (unfold apply_subst, inj_var, subst_lookup, var; simpl).

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
    intros.
    unfold_all.
    induction s; simpl; trivial.
    unfold pair_map_snd.
    destruct a.
    assert (eqb (Eqb:=V_Eqb) x v = eqb (Eqb:=H) x v)by apply eqb_eq_eqb.
    rewrite H0.
    case (eqb x v); trivial.
Qed.

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

  Lemma ws_term_append : forall (args : list V) (l1 l2 : named_list gexp) (a : term),
      ws_term args a -> args = map fst l1 -> a (l1 ++ l2) = a l1.
  Proof.
    intros.
    unfold ws_term in  H.
    symmetry in H0.
    destruct H.
    specialize (H l1 H0 (l1 ++ l2)).
    symmetry.
    apply H.
    intros.
    symmetry.
    apply lookup_found.
    rewrite <- H0 in H2; trivial.
  Qed.

  Lemma named_map_cons_eq {A B} : forall l (n : V) (e : A) (f : A -> B),
      named_map f ((n, e) :: l) = (n, f e) :: named_map f l.
  Proof.
    trivial.
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

  Ltac cleanup_ws_append :=
    match goal with
    | [H : ws_term _ ?a |- ws_term _ ?a] => apply H
    | [ |- map fst _ = map fst (named_map _ _)] => repeat apply named_map_fst'; trivial
    | _ => idtac
    end.

  Lemma subst_assoc0 : forall (s1 s2 : named_list term) (a : term),
      ws_term (map fst s2) a -> apply_subst s1 (apply_subst s2 a) = apply_subst (subst_cmp s1 s2) a.
  Proof.
    intros.
    unfold subst_cmp.
    simpl.
    unfold apply_subst in *.
    apply functional_extensionality; intros.
    repeat erewrite ws_term_append; cleanup_ws_append.
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
      apply_subst ((n, e) :: s) a = apply_subst s a.
  Proof.
    intros.
    unfold apply_subst.
    apply functional_extensionality; intros.
    symmetry; erewrite ws_term_append at 1; cleanup_ws_append.
    remember (fun t => t x) as f.
    pose proof (named_map_fst s f (A := (meta_subst -> gexp))) as nmf.
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

  Lemma fun_app_eq {A B} : forall (f g : A -> B) (a : A), f = g -> f a = g a.
  Proof.
    intros.
    rewrite H.
    trivial.
  Qed.

  Lemma well_scoped_subst0 : forall (args : list V) (s : named_list term) (a : term),
      ws_subst args s ->
      ws_term (map fst s) a ->
      ws_term args (apply_subst s a).
  Proof.
    constructor; intros.
    + unfold apply_subst.
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
      unfold apply_subst.
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
      apply fun_app_eq with (a := x) in H2.
      rewrite H2.
      rewrite IHs; trivial.
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
  constructor; intros; trivial.
Qed.

Definition ctx : Type := named_list sort.

  Definition eq_sort (_ : ctx) (s1 s2 : sort) :=
    s1 = s2.

  Definition wf_sort (_ : ctx) (_ : sort) := True.

  Definition eq_term (_ : ctx) (_ : sort) (t1 t2 : term) :=
    forall (s : named_list gexp), t1 s = t2 s.

  Definition wf_term (c : ctx) t (_ : sort) := ws_term (map fst c) t.

Notation Model := (@Model V term sort).

#[export] Instance model : Model := mut_mod eq_sort eq_term wf_sort wf_term.


  Lemma term_subst_id_eq {A} : forall (c : named_list A) n, apply_subst (with_names_from c (map inj_var (map fst c))) (var default_emp n) = var default_emp n.
    Proof.
    intros.
    unfold apply_subst in *.
    apply functional_extensionality.
    intros.
    unfold inj_var in *.
    unfold var in *.
    induction c.
    trivial.
    destruct a.
    simpl.
    case_eq (eqb n v); intros.
    apply eqb_eq in H.
    rewrite H; trivial.
    apply IHc.
  Qed.

  Lemma eq_term_subst : forall (c : ctx) (s1 s2 : named_list term)
                      (c' : ctx) (t : sort) 
                      (e1 e2 : term),
                    eq_subst c c' s1 s2 ->
                    eq_term c' t e1 e2 ->
                    eq_term c t [/s2 /] e1 [/s1 /] e2 [/s2 /].
    Proof.
      unfold eq_term in *.
      intros.
      unfold Substable.apply_subst.
      simpl.
      unfold apply_subst.
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
    unfold_all.
    constructor; intros; simpl.
    - apply H1; trivial.
    - unfold id_substable; intros.
      apply functional_extensionality.
      intros.
      induction c0.
      trivial.
      destruct a.
      unfold apply_subst.
      simpl in *.
      case_eq (eqb n v); intros.
      apply eqb_eq in H0.
      rewrite H0.
      trivial.
      apply IHc0.
  Qed.

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
      forall (c'' : ctx) (s : named_list term),
        wf_subst c'' s c ->
        wf_term c'' e[/s/] t [/s/].
  Proof.
    constructor; intros.
    + unfold Substable.apply_subst.
      unfold_all.
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
    + unfold id_substable.
      unfold Substable.apply_subst.
      unfold_all.
      unfold wf_term in H.
      intros.
      apply wf_subst_same_name in H1 as Hs.
      apply functional_extensionality; intros.
      unfold apply_subst.
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
