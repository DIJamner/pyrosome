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

Definition term : sort := named_list nat -> nat.

Notation Model := (@Model V term sort).
Definition subst : Type := named_list term.

Section WithEqb.
  Context {V_Eqb : Eqb V}.

  Print named_list_lookup.
  Definition var (default : term) (n : V) : term :=
    fun (s : named_list nat) =>
      named_list_lookup (default s) s n.

  Definition val (v : nat) : term :=
    fun _ => v.

  Definition bin_op (op : nat -> nat -> nat) (t1 t2 : term) : term :=
    fun (s : named_list nat) =>
      op (t1 s) (t2 s).

  Definition term_subst (s : subst) e : term :=
    fun (s' : named_list nat) =>
      e ((named_map (fun (t : term) => t s') (filter (fun (t : term) => negb (existsb (fun y => eqb (fst t) (fst y)) s')) s)) ++ map (fun (n : nat) => if (existsb (fun y => eqb (fst 
      e ((named_map (fun (t : term) => t s') s) ++ filter (fun x => negb (existsb (fun y => eqb (fst x) (fst y)) s)) s').


  Definition ws_term (args : list V) (e : term) : Prop :=
    forall (s : list (V * nat)),
      map (fun x => fst x) s = args
      -> forall (s' : list (V * nat)),
        e s = e (s ++ s').

  Instance substable_term : Substable0 term :=
    {
      inj_var := var (val 0);
      apply_subst0 := term_subst;
      well_scoped0 := ws_term
    }.

  Instance substable_sort : Substable term sort :=
    {
      apply_subst := fun _ _ => term;
      well_scoped := fun _ _ => True
    }.

  (* Lemma subst_var : forall s x, apply_subst0 s (inj_var x) = subst_lookup s x. *)
  (* Proof. *)
  (*   intros; simpl. *)
  (*   unfold term_subst. *)
  (*   unfold subst_lookup. *)
  (*   unfold var. *)
  (*   simpl. *)
  (*   induction s; simpl. *)
  (*   trivial. *)
  (*   unfold pair_map_snd. *)
  (*   destruct a. *)
  (*   case (eqb x v); trivial. *)
  (* Qed. *)

  Lemma map_cmp {A B C} :
    forall (l : list A) (f : A -> B) (g : B -> C) (h : A -> C),
      (forall (a : A), g (f a) = h a)
      -> map h l = map g (map f l).
  Proof.
    intros.
    induction l.
    trivial.
    repeat rewrite map_cons.
    apply invert_eq_cons_cons.
    constructor.
    symmetry.
    apply (H a).
    trivial.
  Qed.

  (* Lemma named_map_cons {A B} : forall (l : named_list A) (f : A -> B) (x : V * A), *)
  (*     named_map f (x :: l) = pair_map_snd f x :: named_map f l. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold named_map. *)
  (*   rewrite map_cons. *)


  Lemma map_fst_name_eq' {A B} : forall (l : named_list A) (f : A -> B),
      map fst l = map fst (named_map f l).
  Proof.
    intros.
    induction l.
    trivial.
    unfold named_map.
    repeat rewrite map_cons.
    apply invert_eq_cons_cons.
    constructor.
    destruct a.
    trivial.
    trivial.
  Qed.

  Lemma map_fst_name_eq {A B} : forall (l1 l2 : named_list A) (f : A -> B),
      map fst l1 = map fst l2 ->
      map fst l1 = map fst (named_map f l2).
  Proof.
    intros.
    rewrite H.
    apply map_fst_name_eq'.
    Qed.

  Print Substable0_ok.

  Print subst_cmp.

  Instance substable_term_ok : Substable0_ok term.
  Proof.
    constructor; intros; simpl.
    + admit.
    + unfold term_subst.
      apply functional_extensionality.
      simpl in  H.
      unfold ws_term in H.
      intros.
      symmetry in H.
      erewrite H.
      erewrite H.
      f_equal.
      apply map_cmp.
      destruct a0.
      trivial.
      all: symmetry;
        repeat apply map_fst_name_eq;
        trivial.
    + unfold term_subst.
      apply functional_extensionality.
      intros.
      f_equal.
      unfold named_map.
      unfold id_subst.

    
    



    intros.
    simpl.
    unfold subst_lookup.
    simpl.
    unfold term_subst.
    unfold var.
    induction s.
    simpl.
    trivial.
    simpl.
    unfold pair_map_snd.
    destruct a.
    remember (eqb x v) as e.
    assert (
  (if eqb x v
   then t
   else
    named_list_lookup
      (fun s0 : named_list nat => named_list_lookup (val 0 s0) s0 x) s x) =

  (if e
   then t
   else
    named_list_lookup
      (fun s0 : named_list nat => named_list_lookup (val 0 s0) s0 x) s x)).
    rewrite Heqe.

    admit.









  Definition ctx := named_list sort.

  Inductive eq_sort : ctx -> sort -> sort -> Prop :=
  | eq_sort_natural : forall c, eq_sort c natural natural.

  Inductive wf_sort : ctx -> sort -> Prop :=
  | wf_sort_natural : forall c, wf_sort c natural.

  Inductive eq_term : ctx -> sort -> term -> term -> Prop :=
  | eq_term_val_val : forall c s n, eq_term c s (val n) (val n).

  Inductive wf_term : ctx -> term -> sort -> Prop :=
  | wf_term_all : forall c s t, wf_term c s t.

  #[export] Instance model : Model := mut_mod eq_sort eq_term wf_sort wf_term.
