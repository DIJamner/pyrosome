Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac.
From Pyrosome Require Import Theory.Core Tools.Matches.
From Pyrosome.Tools.EGraph Require Import Automation ComputeWf.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleUnit.
From Pyrosome.Gluing.Stlc Require Import Syntax Normalization NormalForms Eqns.
Import Core.Notations.

(* PROTOTYPE for the "derived rule" mechanism.

   A DERIVED RULE is an [eq_term stlc_unit c _ _ _] over OBJECT-LEVEL variables,
   proved once by the e-graph.  [dstep] then instantiates it at meta-level terms
   exactly as [eredex_steps_with] instantiates a primitive rule -- inferring the
   substitution by unification rather than taking it as an argument.

   This is what lets a multi-step equational chain be replaced by a single
   e-graph call without reintroducing hand-written substitutions. *)

Local Notation wft := (wf_term stlc_unit []).
Local Notation eqt := (eq_term stlc_unit []).

(* ---- proving a derived rule ---- *)

Ltac egraph_eq :=
  pose proof stlc_unit_wf;
  apply (egraph_sound 100 100 100 100 filter_rules
           (fun _ : string * Rule.rule string => true) empty_inj_rules);
  [ exact stlc_unit_wf | solve_wf_ctx | compute_term_wf | compute_term_wf
  | flagged_exact I ].

(* ---- instantiating a derived rule ---- *)

Ltac wf_subst_solve' :=
  repeat first [ simple apply wf_subst_nil
               | simple eapply wf_subst_cons
               | progress cbn [combine map fst]
               | progress cbn [Model.wf_term core_model]
               | eassumption ].

Ltac dstep lem :=
  let ty := type of lem in
  lazymatch ty with
  | @eq_term ?V _ ?l ?cr ?tp ?e1p ?e2p =>
      lazymatch goal with
      | [|- @eq_term ?V' _ ?l' ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_ : @NamedList.named_list V (Term.term V)) in
          first [ unify_var_names V s cr | fail 2 "could not unify var names" ];
          first [ replace (@eq_term V' _ l' c' t e1 e2)
                    with (@eq_term V _ l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [ | f_equal; vm_compute; reflexivity ]
                | fail 2 "could not replace with subst" ];
          eapply (@eq_term_subst V _ l c' s s cr);
          [ exact lem
          | apply eq_subst_refl; try unfold cr; wf_subst_solve'
          | ]
      end
  end.

(* ================================================================== *)
(* Worked example: the lam-beta chain                                  *)
(* ================================================================== *)

Definition Dv := var "D".
Definition Gv := var "G".
Definition Av := var "A".
Definition Bv := var "B".
Definition gv := var "g".
Definition uv := var "u".
Definition ev := var "e".

Definition c_beta_lift : ctx :=
  [("e", Sexp (Ext Gv Av) Bv); ("u", Sval Dv Av); ("g", Ssub Dv Gv);
   ("B", Sty); ("A", Sty); ("G", Senv); ("D", Senv)].

Lemma d_beta_lift
  : eq_term stlc_unit c_beta_lift (Sexp Dv Bv)
      (App Dv Av Bv
         (Ret Dv (Arr Av Bv) (ValSubst Dv Gv gv (Arr Av Bv) (Lam Gv Av Bv ev)))
         (Ret Dv Av uv))
      (ExpSubst Dv (Ext Gv Av) (Snoc Dv Gv gv Av uv) Bv ev).
Proof.
  unfold c_beta_lift, Dv, Gv, Av, Bv, gv, uv, ev,
    Ssub, Sval, Sexp, Senv, Sty, Cmp, Snoc, Wkn, Ext, Hd, Id,
    App, Ret, ValSubst, ExpSubst, Lam, Arr.
  egraph_eq.
Qed.

Lemma wf_ctx_c_beta_lift : wf_ctx (Model := core_model stlc_unit) c_beta_lift.
Proof.
  pose proof stlc_unit_wf.
  unfold c_beta_lift, Dv, Gv, Av, Bv, gv, uv, ev,
    Ssub, Sval, Sexp, Senv, Sty, Ext, Arr.
  solve_wf_ctx.
Qed.

(* The consumer-facing form: same statement as the hand-proved
   [Stlc/ModelEq.eq_beta_lift], obtained by instantiating the derived rule. *)
Lemma eq_beta_lift' D G g A B u e
  : wft D Senv -> wft G Senv -> wft A Sty -> wft B Sty ->
    wft g (Ssub D G) -> wft u (Sval D A) -> wft e (Sexp (Ext G A) B) ->
    eqt (Sexp D B)
      (App D A B (Ret D (Arr A B) (ValSubst D G g (Arr A B) (Lam G A B e)))
         (Ret D A u))
      (ExpSubst D (Ext G A) (Snoc D G g A u) B e).
Proof.
  intros.
  dstep d_beta_lift.
  exact wf_ctx_c_beta_lift.
Qed.

Print Assumptions eq_beta_lift'.
