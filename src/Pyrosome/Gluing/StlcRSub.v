Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab.
From Pyrosome.Gluing Require Import StlcModel StlcNormalization StlcEqns
  StlcNormalForms StlcLogRel.
Import Core.Notations.

(* ================================================================== *)
(* LAYER 3: reducible substitutions, by recursion on the CONTEXT       *)
(* ================================================================== *)

(* [RSub D G g] : the substitution [g : sub D G] is reducible.

   The recursion is on the CODOMAIN environment [G] alone, and the relation is
   defined AFTER [RV] (Layer 2), which is itself defined by recursion on the
   type; so there is no circularity.

   As everywhere in this development the clauses are stated up to [eq_term],
   which makes [RSub] simultaneously the CANONICAL-FORM statement for
   substitutions: a reducible substitution is provably equal to a [snoc]-chain
   whose spine is [forget] and whose entries are reducible values.  That is why
   [sub] needs no separate normal-form development in Layer 1. *)

Local Notation wft := (wf_term stlc_unit []).
Local Notation eqt := (eq_term stlc_unit []).

Fixpoint RSub (D G g : term) {struct G} : Prop :=
  match G with
  | con "emp" [] => eqt (Ssub D Emp) g (Forget D)
  | con "ext" [A; G0] =>
      exists g0 v,
        eqt (Ssub D (Ext G0 A)) g (Snoc D G0 g0 A v)
        /\ RSub D G0 g0
        /\ RV D A v
  | _ => False
  end.

(* The catch-all clause is [False]: [emp] and [ext] are the only environment
   formers, so every environment the development ever meets ([EnvOk]) is
   covered, and the junk cases are ruled out rather than trivially satisfied. *)

(* ------------------------------------------------------------------ *)
(* The intended reading of the two clauses                              *)
(* ------------------------------------------------------------------ *)

Lemma RSub_emp_intro D g : eqt (Ssub D Emp) g (Forget D) -> RSub D Emp g.
Proof. unfold Emp; cbn [RSub]; intro H; exact H. Qed.

Lemma RSub_emp_elim D g : RSub D Emp g -> eqt (Ssub D Emp) g (Forget D).
Proof. unfold Emp; cbn [RSub]; intro H; exact H. Qed.

Lemma RSub_ext_intro D G A g
  : (exists g0 v, eqt (Ssub D (Ext G A)) g (Snoc D G g0 A v)
                  /\ RSub D G g0 /\ RV D A v) ->
    RSub D (Ext G A) g.
Proof. unfold Ext; cbn [RSub]; intro H; exact H. Qed.

Lemma RSub_ext_elim D G A g
  : RSub D (Ext G A) g ->
    exists g0 v, eqt (Ssub D (Ext G A)) g (Snoc D G g0 A v)
                 /\ RSub D G g0 /\ RV D A v.
Proof. unfold Ext; cbn [RSub]; intro H; exact H. Qed.

Corollary RSub_emp_iff D g
  : RSub D Emp g <-> eqt (Ssub D Emp) g (Forget D).
Proof. split; [ apply RSub_emp_elim | apply RSub_emp_intro ]. Qed.

Corollary RSub_ext_iff D G A g
  : RSub D (Ext G A) g
    <-> exists g0 v, eqt (Ssub D (Ext G A)) g (Snoc D G g0 A v)
                     /\ RSub D G g0 /\ RV D A v.
Proof. split; [ apply RSub_ext_elim | apply RSub_ext_intro ]. Qed.

(* ------------------------------------------------------------------ *)
(* Reducible substitutions are well typed                               *)
(* ------------------------------------------------------------------ *)

(* Both clauses hand back an equation whose left-hand side is [g] itself, at
   the sort [sub D G]; so well-typedness needs no induction. *)
Lemma RSub_wf D G g : RSub D G g -> EnvOk G -> wft g (Ssub D G).
Proof.
  intros Hg HG.
  destruct HG as [ | G0 A HG0 HA ].
  - apply RSub_emp_elim in Hg; eapply eqt_wf_l; eassumption.
  - apply RSub_ext_elim in Hg as [g0 [v [Heq _]]]; eapply eqt_wf_l; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Closure under provable equality                                      *)
(* ------------------------------------------------------------------ *)

Lemma RSub_eq D G g g'
  : RSub D G g -> eqt (Ssub D G) g g' -> EnvOk G -> RSub D G g'.
Proof.
  intros Hg Heq HG.
  destruct HG as [ | G0 A HG0 HA ].
  - apply RSub_emp_elim in Hg; apply RSub_emp_intro.
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact Hg ].
  - apply RSub_ext_elim in Hg as [g0 [v [Heqg [Hg0 Hv]]]].
    apply RSub_ext_intro; exists g0, v; split; [ | split; assumption ].
    eapply eq_term_trans; [ apply eq_term_sym; exact Heq | exact Heqg ].
Qed.

Corollary RSub_eq_iff D G g g'
  : eqt (Ssub D G) g g' -> EnvOk G -> (RSub D G g <-> RSub D G g').
Proof.
  intros Heq HG; split; intro H; eapply RSub_eq;
    try eassumption; apply eq_term_sym; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Extension                                                            *)
(* ------------------------------------------------------------------ *)

Lemma RSub_ext D G A g v
  : RSub D G g -> RV D A v -> EnvOk D -> EnvOk G -> TyOk A ->
    RSub D (Ext G A) (Snoc D G g A v).
Proof.
  intros Hg Hv HD HG HA.
  assert (wft g (Ssub D G)) as Hwg by (eapply RSub_wf; eassumption).
  assert (wft v (Sval D A)) as Hwv by (eapply RV_wf; eassumption).
  apply RSub_ext_intro; exists g, v; split; [ | split; assumption ].
  apply eq_term_refl; wfa.
Qed.

(* ------------------------------------------------------------------ *)
(* Eliminators at an extended context: projection and head              *)
(* ------------------------------------------------------------------ *)

(* Post-composing with [wkn] drops the last entry. *)
Lemma RSub_proj D G A h
  : RSub D (Ext G A) h -> EnvOk D -> EnvOk G -> TyOk A ->
    RSub D G (Cmp D (Ext G A) G h (Wkn G A)).
Proof.
  intros Hh HD HG HA.
  assert (wft h (Ssub D (Ext G A))) as Hwh
    by (eapply RSub_wf; [ eassumption | constructor; assumption ]).
  apply RSub_ext_elim in Hh as [g0 [v [Heq [Hg0 Hv]]]].
  assert (wft g0 (Ssub D G)) as Hwg0 by (eapply RSub_wf; eassumption).
  assert (wft v (Sval D A)) as Hwv by (eapply RV_wf; eassumption).
  eapply RSub_eq; [ exact Hg0 | | assumption ].
  apply eq_term_sym.
  eapply eq_term_trans;
    [ apply cong_Cmp;
      [ wfa | wfa | wfa | exact Heq | apply eq_term_refl; wfa ]
    | apply eq_wkn_snoc; wfa ].
Qed.

(* Substituting into [hd] reads the last entry, which is reducible. *)
Lemma RSub_hd D G A h
  : RSub D (Ext G A) h -> EnvOk D -> EnvOk G -> TyOk A ->
    RV D A (ValSubst D (Ext G A) h A (Hd G A)).
Proof.
  intros Hh HD HG HA.
  assert (wft h (Ssub D (Ext G A))) as Hwh
    by (eapply RSub_wf; [ eassumption | constructor; assumption ]).
  apply RSub_ext_elim in Hh as [g0 [v [Heq [Hg0 Hv]]]].
  assert (wft g0 (Ssub D G)) as Hwg0 by (eapply RSub_wf; eassumption).
  assert (wft v (Sval D A)) as Hwv by (eapply RV_wf; eassumption).
  eapply RV_eq; [ eassumption | eassumption | exact Hv | ].
  apply eq_term_sym.
  eapply eq_term_trans;
    [ apply cong_ValSubst;
      [ wfa | wfa | wfa | exact Heq | apply eq_term_refl; wfa ]
    | apply eq_snoc_hd; wfa ].
Qed.

(* ------------------------------------------------------------------ *)
(* Stability under weakening                                            *)
(* ------------------------------------------------------------------ *)

(* This is the only place the layer needs Layer 2's [RV_wk]: the entries of
   the snoc-chain have to be shifted one at a time. *)
Lemma RSub_wk D G g D' w
  : RSub D G g -> Wk D' D w -> EnvOk D' -> EnvOk D -> EnvOk G ->
    RSub D' G (Cmp D' D G w g).
Proof.
  intros Hg Hw HD' HD HG.
  assert (wft w (Ssub D' D)) as Hww by (eapply Wk_wf; eassumption).
  revert g Hg.
  induction HG as [ | G0 A HG0 IH HA ]; intros g Hg.
  - (* G = emp: [w o forget = forget] *)
    apply RSub_emp_elim in Hg.
    apply RSub_emp_intro.
    eapply eq_term_trans;
      [ apply cong_Cmp;
        [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Hg ]
      | apply eq_cmp_forget; wfa ].
  - (* G = ext G0 A: [w o <g0, v> = <w o g0, w[v]>] *)
    apply RSub_ext_elim in Hg as [g0 [v [Heq [Hg0 Hv]]]].
    assert (wft g0 (Ssub D G0)) as Hwg0 by (eapply RSub_wf; eassumption).
    assert (wft v (Sval D A)) as Hwv by (eapply RV_wf; eassumption).
    apply RSub_ext_intro.
    exists (Cmp D' D G0 w g0), (ValSubst D' D w A v).
    split; [ | split ].
    + eapply eq_term_trans;
        [ apply cong_Cmp;
          [ wfa | wfa | wfa | apply eq_term_refl; wfa | exact Heq ]
        | apply eq_cmp_snoc; wfa ].
    + apply IH; exact Hg0.
    + eapply RV_wk; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The identity substitution is reducible -- the crux of the layer      *)
(* ------------------------------------------------------------------ *)

(* At [ext G A] the identity is exposed as the snoc [<wkn, hd>] by
   [snoc_wkn_hd]; [hd] is reducible because it is a VARIABLE
   ([CR_reflect_V]), and the tail [wkn] is the induction hypothesis
   [RSub G G id] pushed along the weakening [wkn o id] by [RSub_wk]. *)
Lemma RSub_id G : EnvOk G -> RSub G G (Id G).
Proof.
  induction 1 as [ | G0 A HG0 IH HA ].
  - apply RSub_emp_intro; apply eq_id_emp_forget.
  - assert (EnvOk (Ext G0 A)) as HGA by (constructor; assumption).
    (* the tail: [wkn : sub (ext G0 A) G0] is reducible *)
    assert (RSub (Ext G0 A) G0 (Wkn G0 A)) as Hwkn.
    { eapply RSub_eq; [ | | assumption ].
      - eapply RSub_wk;
          [ exact IH
          | apply wk_ext; apply wk_id
          | assumption | assumption | assumption ].
      - eapply eq_term_trans; [ apply eq_id_right; wfa | ].
        apply eq_id_right; wfa. }
    apply RSub_ext_intro.
    exists (Wkn G0 A), (Hd G0 A).
    split; [ | split ].
    + apply eq_term_sym; apply eq_snoc_wkn_hd; wfa.
    + exact Hwkn.
    + apply CR_reflect_V; [ apply vart_hd | exact HGA ].
Qed.

(* ------------------------------------------------------------------ *)
(* Consequences                                                         *)
(* ------------------------------------------------------------------ *)

(* Every weakening is a reducible substitution. *)
Corollary Wk_RSub D G w : Wk D G w -> EnvOk D -> RSub D G w.
Proof.
  intros Hw HD.
  assert (EnvOk G) as HG by (eapply Wk_dom; eassumption).
  assert (wft w (Ssub D G)) as Hww by (eapply Wk_wf; eassumption).
  eapply RSub_eq; [ | | eassumption ].
  - eapply RSub_wk;
      [ apply RSub_id; eassumption | eassumption | eassumption
      | eassumption | eassumption ].
  - apply eq_id_right; wfa.
Qed.

(* The lifted substitution [<g o wkn, hd> : sub (ext D A) (ext G A)] -- the
   form produced by the [val_subst lambda] equation, hence the one Layer 4's
   [lambda] congruence consumes. *)
Lemma RSub_lift D G g A
  : RSub D G g -> EnvOk D -> EnvOk G -> TyOk A ->
    RSub (Ext D A) (Ext G A)
      (Snoc (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) g) A (Hd D A)).
Proof.
  intros Hg HD HG HA.
  assert (EnvOk (Ext D A)) as HDA by (constructor; assumption).
  assert (wft g (Ssub D G)) as Hwg by (eapply RSub_wf; eassumption).
  apply RSub_ext.
  - eapply RSub_eq; [ | | eassumption ].
    + eapply RSub_wk;
        [ exact Hg
        | apply wk_ext; apply wk_id
        | assumption | assumption | assumption ].
    + apply cong_Cmp;
        [ wfa | wfa | wfa | apply eq_id_right; wfa | apply eq_term_refl; wfa ].
  - apply CR_reflect_V; [ apply vart_hd | exact HDA ].
  - assumption.
  - assumption.
  - assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* NOT PROVABLE AT THIS LAYER: composition with an arbitrary reducible  *)
(* substitution                                                         *)
(* ------------------------------------------------------------------ *)

(* One would like
     [RSub_cmp : RSub D G g -> RSub D' D h -> ... -> RSub D' G (Cmp D' D G h g)],
   generalizing [RSub_wk].  Following the proof of [RSub_wk] reduces it, at the
   [ext] clause, to
     [RV D A v -> RSub D' D h -> RV D' A (ValSubst D' D h A v)],
   i.e. closure of REDUCIBILITY under reducible substitution.  That statement is
   TRUE, but it is not available here:

   * Layer 2's [RV] is Kripke over WEAKENINGS only -- the arrow clause
     quantifies over [Wk D G w], never over reducible substitutions (that
     restriction is exactly what makes the recursion on the type well founded).
     So from [RV G (Arr A B) v] one can shift [v] along a weakening, but there
     is no clause to appeal to for a general [h].

   * Nor can it be obtained syntactically: normal forms are NOT closed under
     substitution by reducible values.  If [n = app (ret x) m] is neutral with
     [x] a variable of arrow type, and [h] maps [x] to a [lambda], then [h[n]]
     is a beta-redex, not a normal form.  Recovering reducibility there is
     precisely a beta step, i.e. the content of the fundamental theorem.

   Closure under reducible substitution is therefore Layer 4's business: it is
   built into [ceq_term], whose clauses at [sub]/[val]/[exp] quantify over
   reducible substitutions.  Layer 4 does not need [RSub_cmp] either -- the
   [cmp] congruence obtains
     [RSub D G3 (Cmp D G1 G3 h (Cmp G1 G2 G3 f g))]
   by [cmp_assoc] plus the two [ceq_term] hypotheses in sequence (the first
   turns [h] into a reducible [sub D G2], the second consumes it), never by
   composing two bare [RSub]s.  [RSub_wk], [RSub_ext], [RSub_lift], [RSub_id],
   [RSub_proj] and [RSub_hd] above are what it needs. *)
