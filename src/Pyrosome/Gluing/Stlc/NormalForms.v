Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab.
From Pyrosome.Gluing.Stlc Require Import Model Normalization.
From Pyrosome.Gluing.Stlc Require Export Eqns.
Import Core.Notations.

Notation term := (@term string).
Notation sort := (@sort string).
Notation ctx := (@ctx string).

(* ------------------------------------------------------------------ *)
(* Tactic glue                                                          *)
(* ------------------------------------------------------------------ *)

(* Normalize the subject/sort of a [wf_term] goal (they are typically
   presented as [t[/with_names_from c' s/]] by [wf_term_by']); the language
   itself is deliberately left alone. *)
Ltac norm_wf_goal :=
  match goal with
  | [|- wf_term ?l ?c ?e ?t] =>
      let c' := eval vm_compute in c in
      let e' := eval vm_compute in e in
      let t' := eval vm_compute in t in
      change_no_check (wf_term l c' e' t')
  end.

Ltac wf_args_solve :=
  repeat first
    [ simple apply wf_args_nil
    | simple eapply wf_args_cons
    | progress cbn [Model.wf_term core_model]
    | progress norm_wf_goal
    | eassumption ].

(* [wf_by name] : close a [wf_term stlc_unit [] (con name s) t] goal by the
   language's rule for [name], leaving the argument obligations. *)
Ltac wf_by name :=
  eapply wf_term_by' with (n := name);
  [ solve_in | wf_args_solve | left; vm_compute; reflexivity ].

(* ------------------------------------------------------------------ *)
(* Typing of the index syntax                                           *)
(* ------------------------------------------------------------------ *)

Lemma wf_Unit : wf_term stlc_unit [] Unit Sty.
Proof. wf_by "unit". Qed.

Lemma wf_Arr A B
  : wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] (Arr A B) Sty.
Proof. intros; wf_by "->". Qed.

Lemma wf_Emp : wf_term stlc_unit [] Emp Senv.
Proof. wf_by "emp". Qed.

Lemma wf_Ext G A
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] (Ext G A) Senv.
Proof. intros; wf_by "ext". Qed.

Lemma TyOk_wf A : TyOk A -> wf_term stlc_unit [] A Sty.
Proof.
  induction 1.
  - apply wf_Unit.
  - apply wf_Arr; assumption.
Qed.

Lemma EnvOk_wf G : EnvOk G -> wf_term stlc_unit [] G Senv.
Proof.
  induction 1.
  - apply wf_Emp.
  - apply wf_Ext; auto using TyOk_wf.
Qed.

#[local] Hint Resolve TyOk_wf EnvOk_wf : stlc_nf.

(* ------------------------------------------------------------------ *)
(* Typing of the remaining term formers                                 *)
(* ------------------------------------------------------------------ *)

Lemma wf_Id G
  : wf_term stlc_unit [] G Senv -> wf_term stlc_unit [] (Id G) (Ssub G G).
Proof. intros; wf_by "id". Qed.

Lemma wf_Forget G
  : wf_term stlc_unit [] G Senv -> wf_term stlc_unit [] (Forget G) (Ssub G Emp).
Proof. intros; wf_by "forget". Qed.

Lemma wf_Wkn G A
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] (Wkn G A) (Ssub (Ext G A) G).
Proof. intros; wf_by "wkn". Qed.

Lemma wf_Hd G A
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] (Hd G A) (Sval (Ext G A) A).
Proof. intros; wf_by "hd". Qed.

Lemma wf_Cmp G1 G2 G3 f g
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] (Cmp G1 G2 G3 f g) (Ssub G1 G3).
Proof. intros; wf_by "cmp". Qed.

Lemma wf_Snoc G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    wf_term stlc_unit [] (Snoc G G' g A v) (Ssub G (Ext G' A)).
Proof. intros; wf_by "snoc". Qed.

Lemma wf_ValSubst G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G' A) ->
    wf_term stlc_unit [] (ValSubst G G' g A v) (Sval G A).
Proof. intros; wf_by "val_subst". Qed.

Lemma wf_ExpSubst G G' g A e
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] e (Sexp G' A) ->
    wf_term stlc_unit [] (ExpSubst G G' g A e) (Sexp G A).
Proof. intros; wf_by "exp_subst". Qed.

Lemma wf_Ret G A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    wf_term stlc_unit [] (Ret G A v) (Sexp G A).
Proof. intros; wf_by "ret". Qed.

Lemma wf_Tt G
  : wf_term stlc_unit [] G Senv -> wf_term stlc_unit [] (Tt G) (Sval G Unit).
Proof. intros; wf_by "tt". Qed.

Lemma wf_Lam G A B e
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp (Ext G A) B) ->
    wf_term stlc_unit [] (Lam G A B e) (Sval G (Arr A B)).
Proof. intros; wf_by "lambda". Qed.

Lemma wf_App G A B e e'
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp G (Arr A B)) ->
    wf_term stlc_unit [] e' (Sexp G A) ->
    wf_term stlc_unit [] (App G A B e e') (Sexp G B).
Proof. intros; wf_by "app". Qed.

#[local] Hint Resolve wf_Unit wf_Arr wf_Emp wf_Ext wf_Id wf_Forget wf_Wkn wf_Hd
  wf_Cmp wf_Snoc wf_ValSubst wf_ExpSubst wf_Ret wf_Tt wf_Lam wf_App : stlc_nf.

Local Notation wft := (wf_term stlc_unit []).
Local Notation eqt := (eq_term stlc_unit []).

(* ------------------------------------------------------------------ *)
(* Sort inversion                                                       *)
(* ------------------------------------------------------------------ *)

(* Every sort former ([sub]/[val]/[exp]) determines its own indices by a
   SINGLE rule of the language, so inverting [wf_sort] on a concrete sort
   recovers plain well-formedness of those indices with no further
   hypotheses -- in particular no [EnvOk]/[TyOk] on the indices themselves.
   This is what [RSub_wf]/[RSub_eq] (Gluing/Stlc/RSub.v) and [RV_eq]
   (Gluing/Stlc/LogRel.v) lean on to stay side-condition-free: given an
   equation at [sub G G']/[val G A]/[exp G A], inverting the SORT of either
   side is enough to reconstruct [wft G Senv]/[wft A Sty], without ever
   needing [EnvOk]/[TyOk] for [G]/[A] themselves. *)

Lemma eqt_wf_sort t e1 e2 : eqt t e1 e2 -> wf_sort stlc_unit [] t.
Proof.
  intro H; eapply eq_term_wf_sort; try typeclasses eauto;
    [ exact stlc_unit_wf | constructor | exact H ].
Qed.

Lemma wft_wf_sort e t : wft e t -> wf_sort stlc_unit [] t.
Proof. intro H; eapply eqt_wf_sort; apply eq_term_refl; exact H. Qed.

Ltac sort_inv H :=
  inversion H; subst;
  match goal with
  | [ Hin : In _ stlc_unit |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
         | [ Ha : wf_args _ (_::_) _ |- _ ] => inversion Ha; subst; clear Ha
         end;
  cbn [Model.wf_term core_model] in *;
  split; assumption.

Lemma wf_sort_sub_inv G G' : wf_sort stlc_unit [] (Ssub G G') -> wft G Senv /\ wft G' Senv.
Proof. unfold Ssub; intro H; sort_inv H. Qed.

Lemma wf_sort_val_inv G A : wf_sort stlc_unit [] (Sval G A) -> wft G Senv /\ wft A Sty.
Proof. unfold Sval; intro H; sort_inv H. Qed.

Lemma wf_sort_exp_inv G A : wf_sort stlc_unit [] (Sexp G A) -> wft G Senv /\ wft A Sty.
Proof. unfold Sexp; intro H; sort_inv H. Qed.

Lemma wft_sub_inv G G' g : wft g (Ssub G G') -> wft G Senv /\ wft G' Senv.
Proof. intro H; apply wf_sort_sub_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_val_inv G A v : wft v (Sval G A) -> wft G Senv /\ wft A Sty.
Proof. intro H; apply wf_sort_val_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_exp_inv G A e : wft e (Sexp G A) -> wft G Senv /\ wft A Sty.
Proof. intro H; apply wf_sort_exp_inv; eapply wft_wf_sort; exact H. Qed.

(* ------------------------------------------------------------------ *)
(* Congruence for the term formers                                      *)
(* ------------------------------------------------------------------ *)

(* The 18 equation lemmas ([eq_val_subst_id], [eq_wkn_snoc], ...) and the
   [stlc_unit_cong_inst]-based congruence toolkit live in Gluing/Stlc/Eqns.v;
   this file only needs the specializations below, whose statements pin the
   congruence rules' left- and right-hand sides together (the general form in
   Eqns.v keeps them independent, which is more than the canonical-forms
   development ever needs). *)

Lemma cong_Cmp G1 G2 G3 f f' g g'
  : wft G1 Senv -> wft G2 Senv -> wft G3 Senv ->
    eqt (Ssub G1 G2) f f' -> eqt (Ssub G2 G3) g g' ->
    eqt (Ssub G1 G3) (Cmp G1 G2 G3 f g) (Cmp G1 G2 G3 f' g').
Proof. intros; apply Cmp_cong; auto using eq_term_refl. Qed.

Lemma cong_Snoc G G' g g' A v v'
  : wft G Senv -> wft G' Senv -> wft A Sty ->
    eqt (Ssub G G') g g' -> eqt (Sval G A) v v' ->
    eqt (Ssub G (Ext G' A)) (Snoc G G' g A v) (Snoc G G' g' A v').
Proof. intros; apply Snoc_cong; auto using eq_term_refl. Qed.

Lemma cong_ValSubst G G' g g' A v v'
  : wft G Senv -> wft G' Senv -> wft A Sty ->
    eqt (Ssub G G') g g' -> eqt (Sval G' A) v v' ->
    eqt (Sval G A) (ValSubst G G' g A v) (ValSubst G G' g' A v').
Proof. intros; apply ValSubst_cong; auto using eq_term_refl. Qed.

Lemma cong_ExpSubst G G' g g' A e e'
  : wft G Senv -> wft G' Senv -> wft A Sty ->
    eqt (Ssub G G') g g' -> eqt (Sexp G' A) e e' ->
    eqt (Sexp G A) (ExpSubst G G' g A e) (ExpSubst G G' g' A e').
Proof. intros; apply ExpSubst_cong; auto using eq_term_refl. Qed.

Lemma cong_Ret G A v v'
  : wft G Senv -> wft A Sty -> eqt (Sval G A) v v' ->
    eqt (Sexp G A) (Ret G A v) (Ret G A v').
Proof. intros; apply Ret_cong; auto using eq_term_refl. Qed.

Lemma cong_Lam G A B e e'
  : wft G Senv -> wft A Sty -> wft B Sty ->
    eqt (Sexp (Ext G A) B) e e' ->
    eqt (Sval G (Arr A B)) (Lam G A B e) (Lam G A B e').
Proof. intros; apply Lam_cong; auto using eq_term_refl. Qed.

Lemma cong_App G A B e e' n n'
  : wft G Senv -> wft A Sty -> wft B Sty ->
    eqt (Sexp G (Arr A B)) e e' -> eqt (Sexp G A) n n' ->
    eqt (Sexp G B) (App G A B e n) (App G A B e' n').
Proof. intros; apply App_cong; auto using eq_term_refl. Qed.

(* ================================================================== *)
(* LAYER 1: canonical forms and weakenings                             *)
(* ================================================================== *)

(* ---- object-level variables (untyped: indices are just carried) ---- *)
Inductive Var : term -> Prop :=
| var_hd : forall G A, Var (Hd G A)
| var_wkn : forall G A B x, Var x -> Var (ValSubst (Ext G B) G (Wkn G B) A x).

(* ---- canonical values / expressions and neutral expressions ---- *)
Inductive NfV : term -> Prop :=
| nfv_var : forall v, Var v -> NfV v
| nfv_tt : forall G, NfV (Tt G)
| nfv_lam : forall G A B e, NfE e -> NfV (Lam G A B e)
with NfE : term -> Prop :=
| nfe_ret : forall G A v, NfV v -> NfE (Ret G A v)
| nfe_ne : forall e, NeE e -> NfE e
with NeE : term -> Prop :=
| nee_varapp : forall G A B x n,
    Var x -> NfE n -> NeE (App G A B (Ret G (Arr A B) x) n)
| nee_app : forall G A B e n, NeE e -> NfE n -> NeE (App G A B e n)
(* A normal function VALUE applied to a NEUTRAL argument is stuck: in this
   CBV presentation [STLC-beta] fires only when BOTH sides are [ret]s, so
   [app (ret (lambda A e)) n] with [n] neutral reduces to nothing.  Without
   this clause the grammar is incomplete and the normalization theorem is
   false.  The clause is stated for an ARBITRARY normal function value (not
   just a lambda), which subsumes the lambda case and keeps [nee_varapp]
   coherent; the two overlap exactly when [v] is a variable and [n] is
   neutral.  [nee_varapp] is NOT subsumed: it allows a NON-neutral (normal)
   argument, which is stuck only because the function is a variable. *)
| nee_lamapp : forall G A B v n,
    NfV v -> NeE n -> NeE (App G A B (Ret G (Arr A B) v) n).

(* ---- weakenings ----

   [Wk D G w] says the substitution [w : sub D G] is a weakening.  This is a
   purely SYNTACTIC class: no clause mentions reducibility, which is what keeps
   the Layer-2 recursion (on the type) well founded.

   DEVIATION FROM THE DESIGN DOC.  The doc lists only [wk_id] and [wk_ext]
   ("drop the most recent variable").  That class is NOT closed under going
   under a binder: the [val_subst lambda] equation rewrites
   [w[lambda A e]] to [lambda A (e[<w o wkn, hd>])], and the lifted
   substitution [<w o wkn, hd> : sub (ext D A) (ext G A)] is a snoc, not a
   wkn-composite.  Without a lift clause the [nfv_lam] case of normal-form
   stability under weakening is simply false as stated, so [wk_lift] is added
   here; the class is exactly the order-preserving embeddings.  It is still
   syntactic, so the well-foundedness argument is unaffected. *)
Inductive Wk : term -> term -> term -> Prop :=
| wk_id : forall G, Wk G G (Id G)
| wk_ext : forall D G A w,
    Wk D G w -> Wk (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) w)
| wk_lift : forall D G A w,
    Wk D G w ->
    Wk (Ext D A) (Ext G A)
      (Snoc (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) w) A (Hd D A)).

(* ---- typed refinements ----

   The untyped predicates above are the ones the normalization statement is
   phrased with, but they admit NO typing lemma: [Var] does not force the
   index arguments of an inner [val_subst] to agree with the ones the outer
   [wkn] shift carries.  For instance
     [Var (ValSubst (Ext G B) G (Wkn G B) A (Hd G' A))]
   holds for every [G'], and is ill-typed unless [G' = G].  The typed
   refinements below carry the indices in the judgement, admit the expected
   typing lemmas, and erase onto the untyped ones. *)
Inductive VarT : term -> term -> term -> Prop :=
| vart_hd : forall G A, VarT (Ext G A) A (Hd G A)
| vart_wkn : forall G A B x,
    VarT G A x -> VarT (Ext G B) A (ValSubst (Ext G B) G (Wkn G B) A x).

Inductive NfVT : term -> term -> term -> Prop :=
| nfvt_var : forall G A v, VarT G A v -> NfVT G A v
| nfvt_tt : forall G, NfVT G Unit (Tt G)
| nfvt_lam : forall G A B e, NfET (Ext G A) B e -> NfVT G (Arr A B) (Lam G A B e)
with NfET : term -> term -> term -> Prop :=
| nfet_ret : forall G A v, NfVT G A v -> NfET G A (Ret G A v)
| nfet_ne : forall G A e, NeET G A e -> NfET G A e
with NeET : term -> term -> term -> Prop :=
| neet_varapp : forall G A B x n,
    VarT G (Arr A B) x -> NfET G A n ->
    NeET G B (App G A B (Ret G (Arr A B) x) n)
| neet_app : forall G A B e n,
    NeET G (Arr A B) e -> NfET G A n -> NeET G B (App G A B e n)
(* The typed form of [nee_lamapp] (see the comment there).
   The [TyOk B] premise is REQUIRED and cannot be dropped: without it
   [NeET_TyOk] is FALSE.  [TyOk A] is recovered from the [NeET G A n]
   premise by [NeET_TyOk] itself, but the codomain [B] is only visible
   through [NfVT G (Arr A B) v], and [NfVT] admits no type-formation lemma
   ([nfvt_lam] can bind an arbitrary, even ill-formed, domain type). *)
| neet_lamapp : forall G A B v n,
    NfVT G (Arr A B) v -> NeET G A n -> TyOk B ->
    NeET G B (App G A B (Ret G (Arr A B) v) n).

Scheme NfVT_min := Minimality for NfVT Sort Prop
  with NfET_min := Minimality for NfET Sort Prop
  with NeET_min := Minimality for NeET Sort Prop.
Combined Scheme NfT_mutind from NfVT_min, NfET_min, NeET_min.

Scheme NfV_min := Minimality for NfV Sort Prop
  with NfE_min := Minimality for NfE Sort Prop
  with NeE_min := Minimality for NeE Sort Prop.
Combined Scheme Nf_mutind from NfV_min, NfE_min, NeE_min.

(* ---- erasure of the typed judgements onto the untyped ones ---- *)
Lemma VarT_Var G A x : VarT G A x -> Var x.
Proof. induction 1; econstructor; eauto. Qed.

Lemma NfT_Nf
  : (forall G A v, NfVT G A v -> NfV v)
    /\ (forall G A e, NfET G A e -> NfE e)
    /\ (forall G A e, NeET G A e -> NeE e).
Proof.
  apply NfT_mutind; intros;
    eauto using NfV, NfE, NeE, VarT_Var.
Qed.

Definition NfET_NfE := proj1 (proj2 NfT_Nf).

(* ------------------------------------------------------------------ *)
(* Inversion helpers for the index predicates                           *)
(* ------------------------------------------------------------------ *)

Lemma TyOk_Arr_inv A B : TyOk (Arr A B) -> TyOk A /\ TyOk B.
Proof.
  intro H; remember (Arr A B) as X eqn:HX; destruct H.
  - unfold Unit, Arr in HX; congruence.
  - unfold Arr in HX; inversion HX; subst; auto.
Qed.

Lemma EnvOk_Ext_inv G A : EnvOk (Ext G A) -> EnvOk G /\ TyOk A.
Proof.
  intro H; remember (Ext G A) as X eqn:HX; destruct H.
  - unfold Emp, Ext in HX; congruence.
  - unfold Ext in HX; inversion HX; subst; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Weakenings: typing                                                   *)
(* ------------------------------------------------------------------ *)

(* A weakening out of a well-formed environment lands in a well-formed one. *)
Lemma Wk_dom D G w : Wk D G w -> EnvOk D -> EnvOk G.
Proof.
  induction 1; intro HD; auto.
  - apply EnvOk_Ext_inv in HD as [HD0 HA]; auto.
  - apply EnvOk_Ext_inv in HD as [HD0 HA]; constructor; auto.
Qed.

Lemma Wk_wf D G w : Wk D G w -> EnvOk D -> EnvOk G -> wft w (Ssub D G).
Proof.
  induction 1; intros HD HG.
  - apply wf_Id; auto using EnvOk_wf.
  - apply EnvOk_Ext_inv in HD as [HD0 HA].
    apply wf_Cmp; auto using EnvOk_wf, TyOk_wf, wf_Ext.
    apply wf_Wkn; auto using EnvOk_wf, TyOk_wf.
  - apply EnvOk_Ext_inv in HD as [HD0 HA].
    apply EnvOk_Ext_inv in HG as [HG0 HA'].
    apply wf_Snoc; auto using EnvOk_wf, TyOk_wf, wf_Ext.
    + apply wf_Cmp; auto using EnvOk_wf, TyOk_wf, wf_Ext.
      apply wf_Wkn; auto using EnvOk_wf, TyOk_wf.
    + apply wf_Hd; auto using EnvOk_wf, TyOk_wf.
Qed.

(* ------------------------------------------------------------------ *)
(* Typing of the (typed) canonical forms                                *)
(* ------------------------------------------------------------------ *)

Lemma VarT_TyOk G A x : VarT G A x -> EnvOk G -> TyOk A.
Proof.
  induction 1; intro HG; apply EnvOk_Ext_inv in HG as [HG0 HA]; auto.
Qed.

Lemma VarT_wf G A x : VarT G A x -> EnvOk G -> wft x (Sval G A).
Proof.
  induction 1; intro HG; apply EnvOk_Ext_inv in HG as [HG0 HA].
  - apply wf_Hd; auto using EnvOk_wf, TyOk_wf.
  - apply wf_ValSubst; auto using EnvOk_wf, TyOk_wf, wf_Ext.
    + apply wf_Wkn; auto using EnvOk_wf, TyOk_wf.
    + apply TyOk_wf; eapply VarT_TyOk; eauto.
Qed.

Lemma NeET_TyOk G T e : NeET G T e -> EnvOk G -> TyOk T.
Proof.
  induction 1; intro HG.
  - apply (VarT_TyOk H) in HG; apply TyOk_Arr_inv in HG; tauto.
  - apply IHNeET in HG; apply TyOk_Arr_inv in HG; tauto.
  - (* neet_lamapp: exactly what the [TyOk B] premise is there for *)
    assumption.
Qed.

Lemma NfT_wf
  : (forall G A v, NfVT G A v -> EnvOk G -> TyOk A -> wft v (Sval G A))
    /\ (forall G A e, NfET G A e -> EnvOk G -> TyOk A -> wft e (Sexp G A))
    /\ (forall G A e, NeET G A e -> EnvOk G -> TyOk A -> wft e (Sexp G A)).
Proof.
  apply NfT_mutind; intros.
  - eauto using VarT_wf.
  - apply wf_Tt; auto using EnvOk_wf.
  - apply TyOk_Arr_inv in H2 as [HA HB].
    apply wf_Lam; auto using EnvOk_wf, TyOk_wf.
    apply H0; auto; constructor; auto.
  - apply wf_Ret; auto using EnvOk_wf, TyOk_wf.
  - auto.
  - assert (TyOk (Arr A B)) as HAB by eauto using VarT_TyOk.
    apply TyOk_Arr_inv in HAB as [HA HB].
    apply wf_App; auto using EnvOk_wf, TyOk_wf.
    apply wf_Ret; auto using EnvOk_wf, TyOk_wf, wf_Arr, VarT_wf.
  - assert (TyOk (Arr A B)) as HAB by eauto using NeET_TyOk.
    apply TyOk_Arr_inv in HAB as [HA HB].
    apply wf_App; auto using EnvOk_wf, TyOk_wf.
    apply H0; [ auto | constructor; auto ].
  - (* neet_lamapp *)
    assert (TyOk A) as HA by (eapply NeET_TyOk; eassumption).
    assert (wft n (Sexp G A)) as Hn by auto.
    assert (wft v (Sval G (Arr A B))) as Hv
        by (apply H0; [ auto | constructor; auto ]).
    apply wf_App; auto using EnvOk_wf, TyOk_wf, wf_Ret, wf_Arr.
Qed.

Definition NfVT_wf := proj1 NfT_wf.
Definition NfET_wf := proj1 (proj2 NfT_wf).
Definition NeET_wf := proj2 (proj2 NfT_wf).

(* ------------------------------------------------------------------ *)
(* Composition of weakenings                                            *)
(* ------------------------------------------------------------------ *)

(* A syntax-directed well-formedness solver.  Every [wf_term] goal arising
   below has a [con]-headed subject whose head symbol picks exactly one
   introduction lemma, so plain [repeat first [...]] (no backtracking) is
   both complete enough and fast. *)
Ltac wfa :=
  repeat first
    [ eassumption
    | simple apply wf_Emp | simple apply wf_Unit
    | simple apply wf_Ext | simple apply wf_Arr
    | simple apply wf_Id | simple apply wf_Forget
    | simple apply wf_Wkn | simple apply wf_Hd | simple apply wf_Cmp
    | simple apply wf_Snoc | simple apply wf_ValSubst | simple apply wf_ExpSubst
    | simple apply wf_Ret | simple apply wf_Tt | simple apply wf_Lam
    | simple apply wf_App
    | simple apply envok_emp | simple apply envok_ext
    | simple apply tyok_unit | simple apply tyok_arr
    | simple apply EnvOk_wf | simple apply TyOk_wf
    | solve [ eapply Wk_wf; wfa ]
    | solve [ eapply VarT_wf; wfa ]
    | solve [ eapply NfVT_wf; wfa ]
    | solve [ eapply NfET_wf; wfa ]
    | solve [ eapply NeET_wf; wfa ]
    | solve [ eapply VarT_TyOk; wfa ]
    | solve [ eapply NeET_TyOk; wfa ] ].

(* [lift_cmp_wkn] -- the workhorse for both non-identity cases of [Wk_cmp]'s
   lift branch, post-composing a lifted weakening with a [wkn] drop -- is a
   DERIVED RULE and lives in Gluing/Stlc/Eqns.v, alongside [eq_lift_inst] and
   [eq_beta_lift]; [wfa] below discharges its [EnvOk]/[TyOk]-derived [wft]
   premises exactly as it would for a hand-proved lemma. *)

Lemma Ext_inj G A G' A' : Ext G A = Ext G' A' -> G = G' /\ A = A'.
Proof. unfold Ext; intro H; inversion H; auto. Qed.

(* Weakenings compose: the composite of two weakenings is provably equal to a
   weakening.  (It is not SYNTACTICALLY a weakening -- [Wk] has no clause for
   [cmp] of two general weakenings -- so the statement is up to [eq_term],
   which is all Layer 2 needs.) *)
Lemma Wk_cmp D G w1
  : Wk D G w1 ->
    forall G' w2, Wk G G' w2 -> EnvOk D ->
      exists w, Wk D G' w /\ eqt (Ssub D G') (Cmp D G G' w1 w2) w.
Proof.
  induction 1 as [G0 | D0 G0 A w0 Hw IH | D0 G0 A w0 Hw IH];
    intros G' w2 H2 HD.
  - (* wk_id *)
    assert (EnvOk G') as HG' by (eapply Wk_dom; eassumption).
    exists w2; split; [ assumption | apply eq_id_left; wfa ].
  - (* wk_ext *)
    apply EnvOk_Ext_inv in HD as [HD0 HA].
    assert (EnvOk G0) as HG0 by (eapply Wk_dom; eassumption).
    assert (EnvOk G') as HG' by (eapply Wk_dom; eassumption).
    destruct (IH _ _ H2 HD0) as [w' [Hw' Heq']].
    exists (Cmp (Ext D0 A) D0 G' (Wkn D0 A) w'); split.
    + apply wk_ext; assumption.
    + eapply eq_term_trans;
        [ apply eq_term_sym; apply eq_cmp_assoc; wfa | ].
      apply cong_Cmp;
        [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq' ].
  - (* wk_lift *)
    apply EnvOk_Ext_inv in HD as [HD0 HA].
    assert (EnvOk G0) as HG0 by (eapply Wk_dom; eassumption).
    remember (Ext G0 A) as GG eqn:HGG.
    destruct H2 as [ G1 | D1 G1 A1 u H2 | D1 G1 A1 u H2 ].
    + (* w2 = id *)
      subst G1.
      exists (Snoc (Ext D0 A) G0 (Cmp (Ext D0 A) D0 G0 (Wkn D0 A) w0) A (Hd D0 A)).
      split; [ apply wk_lift; assumption | apply eq_id_right; wfa ].
    + (* w2 = wkn-drop *)
      apply Ext_inj in HGG as [? ?]; subst D1 A1.
      assert (EnvOk G1) as HG1 by (eapply Wk_dom; eassumption).
      destruct (IH _ _ H2 HD0) as [w' [Hw' Heq']].
      exists (Cmp (Ext D0 A) D0 G1 (Wkn D0 A) w'); split.
      * apply wk_ext; assumption.
      * eapply eq_term_trans; [ apply lift_cmp_wkn; wfa | ].
        apply cong_Cmp;
          [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq' ].
    + (* w2 = lift *)
      apply Ext_inj in HGG as [? ?]; subst D1 A1.
      assert (EnvOk G1) as HG1 by (eapply Wk_dom; eassumption).
      destruct (IH _ _ H2 HD0) as [w' [Hw' Heq']].
      exists (Snoc (Ext D0 A) G1 (Cmp (Ext D0 A) D0 G1 (Wkn D0 A) w') A (Hd D0 A));
        split.
      * apply wk_lift; assumption.
      * eapply eq_term_trans; [ apply eq_cmp_snoc; wfa | ].
        apply cong_Snoc; [ wfa | wfa | wfa | | ].
        -- eapply eq_term_trans; [ apply lift_cmp_wkn; wfa | ].
           apply cong_Cmp;
             [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq' ].
        -- apply eq_snoc_hd; wfa.
Qed.

(* ------------------------------------------------------------------ *)
(* Stability under weakening                                            *)
(* ------------------------------------------------------------------ *)

Lemma VarT_Ext_inv G C A x
  : VarT (Ext G C) A x ->
    (A = C /\ x = Hd G C)
    \/ (exists x0, VarT G A x0 /\ x = ValSubst (Ext G C) G (Wkn G C) A x0).
Proof.
  intro H; remember (Ext G C) as GG eqn:HGG; destruct H;
    apply Ext_inj in HGG as [? ?]; subst; eauto.
Qed.

(* Normal forms are NOT syntactically closed under weakening: [w[x]] is a
   [val_subst] redex, not a variable.  The right statement is closure up to
   provable equality -- which is exactly what the [ceq_term] gluing of the
   design doc consumes. *)
Lemma VarT_wk D G w
  : Wk D G w -> EnvOk D ->
    forall A x, VarT G A x ->
      exists x', VarT D A x' /\ eqt (Sval D A) (ValSubst D G w A x) x'.
Proof.
  induction 1 as [G0 | D0 G0 C w0 Hw IH | D0 G0 C w0 Hw IH]; intros HD A x Hx.
  - (* wk_id *)
    exists x; split; [ assumption | apply eq_val_subst_id; wfa ].
  - (* wk_ext *)
    apply EnvOk_Ext_inv in HD as [HD0 HC].
    assert (EnvOk G0) as HG0 by (eapply Wk_dom; eassumption).
    destruct (IH HD0 _ _ Hx) as [x0 [Hx0 Heq0]].
    exists (ValSubst (Ext D0 C) D0 (Wkn D0 C) A x0); split.
    + apply vart_wkn; assumption.
    + eapply eq_term_trans;
        [ apply eq_term_sym; apply eq_val_subst_cmp; wfa | ].
      apply cong_ValSubst;
        [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq0 ].
  - (* wk_lift *)
    apply EnvOk_Ext_inv in HD as [HD0 HC].
    assert (EnvOk G0) as HG0 by (eapply Wk_dom; eassumption).
    apply VarT_Ext_inv in Hx as [[HA Hxe] | [x1 [Hx1 Hxe]]]; subst.
    + exists (Hd D0 C); split; [ apply vart_hd | apply eq_snoc_hd; wfa ].
    + destruct (IH HD0 _ _ Hx1) as [x0 [Hx0 Heq0]].
      exists (ValSubst (Ext D0 C) D0 (Wkn D0 C) A x0); split.
      * apply vart_wkn; assumption.
      * eapply eq_term_trans; [ apply eq_val_subst_cmp; wfa | ].
        eapply eq_term_trans;
          [ apply cong_ValSubst;
            [ wfa | wfa | wfa | apply eq_wkn_snoc; wfa | apply eq_term_refl; wfa ]
          | ].
        eapply eq_term_trans;
          [ apply eq_term_sym; apply eq_val_subst_cmp; wfa | ].
        apply cong_ValSubst;
          [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq0 ].
Qed.

Lemma NfT_wk
  : (forall G A v, NfVT G A v ->
       forall D w, Wk D G w -> EnvOk D -> EnvOk G -> TyOk A ->
         exists n, NfVT D A n /\ eqt (Sval D A) (ValSubst D G w A v) n)
    /\ (forall G A e, NfET G A e ->
       forall D w, Wk D G w -> EnvOk D -> EnvOk G -> TyOk A ->
         exists n, NfET D A n /\ eqt (Sexp D A) (ExpSubst D G w A e) n)
    /\ (forall G A e, NeET G A e ->
       forall D w, Wk D G w -> EnvOk D -> EnvOk G -> TyOk A ->
         exists n, NeET D A n /\ eqt (Sexp D A) (ExpSubst D G w A e) n).
Proof.
  apply NfT_mutind; intros.
  - (* nfvt_var *)
    edestruct VarT_wk as [x' [Hx' Heq]]; try eassumption.
    exists x'; split; [ apply nfvt_var | ]; assumption.
  - (* nfvt_tt *)
    exists (Tt D); split; [ apply nfvt_tt | apply eq_val_subst_tt; wfa ].
  - (* nfvt_lam *)
    destruct (TyOk_Arr_inv H4) as [HA HB].
    edestruct H0 as [n0 [Hn0 Heq0]];
      [ apply wk_lift; eassumption
      | constructor; assumption
      | constructor; assumption
      | assumption | ].
    exists (Lam D A B n0); split; [ apply nfvt_lam; assumption | ].
    eapply eq_term_trans; [ apply eq_val_subst_lambda; wfa | ].
    apply cong_Lam; [ wfa | wfa | wfa | exact Heq0 ].
  - (* nfet_ret *)
    edestruct H0 as [n0 [Hn0 Heq0]]; try eassumption.
    exists (Ret D A n0); split; [ apply nfet_ret; assumption | ].
    eapply eq_term_trans; [ apply eq_exp_subst_ret; wfa | ].
    apply cong_Ret; [ wfa | wfa | exact Heq0 ].
  - (* nfet_ne *)
    edestruct H0 as [n0 [Hn0 Heq0]]; try eassumption.
    exists n0; split; [ apply nfet_ne | ]; assumption.
  - (* neet_varapp *)
    assert (TyOk (Arr A B)) as HAB by (eapply VarT_TyOk; eassumption).
    destruct (TyOk_Arr_inv HAB) as [HA HB].
    edestruct VarT_wk as [x' [Hx' Heqx]]; try eassumption.
    edestruct H1 as [n' [Hn' Heqn]]; try eassumption.
    exists (App D A B (Ret D (Arr A B) x') n'); split.
    + apply neet_varapp; assumption.
    + eapply eq_term_trans; [ apply eq_exp_subst_app; wfa | ].
      apply cong_App; [ wfa | wfa | wfa | | exact Heqn ].
      eapply eq_term_trans; [ apply eq_exp_subst_ret; wfa | ].
      apply cong_Ret; [ wfa | wfa | exact Heqx ].
  - (* neet_app *)
    assert (TyOk (Arr A B)) as HAB by (eapply NeET_TyOk; eassumption).
    destruct (TyOk_Arr_inv HAB) as [HA HB].
    edestruct H0 as [e' [He' Heqe]]; try eassumption.
    edestruct H2 as [n' [Hn' Heqn]]; try eassumption.
    exists (App D A B e' n'); split; [ apply neet_app; assumption | ].
    eapply eq_term_trans; [ apply eq_exp_subst_app; wfa | ].
    apply cong_App; [ wfa | wfa | wfa | exact Heqe | exact Heqn ].
  - (* neet_lamapp *)
    assert (TyOk A) as HA by (eapply NeET_TyOk; eassumption).
    edestruct H0 as [v' [Hv' Heqv]];
      [ eassumption | eassumption | eassumption | constructor; assumption | ].
    edestruct H2 as [n' [Hn' Heqn]]; try eassumption.
    exists (App D A B (Ret D (Arr A B) v') n'); split.
    + apply neet_lamapp; assumption.
    + eapply eq_term_trans; [ apply eq_exp_subst_app; wfa | ].
      apply cong_App; [ wfa | wfa | wfa | | exact Heqn ].
      eapply eq_term_trans; [ apply eq_exp_subst_ret; wfa | ].
      apply cong_Ret; [ wfa | wfa | exact Heqv ].
Qed.

Definition NfVT_wk := proj1 NfT_wk.
Definition NfET_wk := proj1 (proj2 NfT_wk).
Definition NeET_wk := proj2 (proj2 NfT_wk).
