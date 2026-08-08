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
From Pyrosome.Gluing.Stlc Require Import Syntax Normalization NormalForms.
Import Core.Notations.

(* Evidence for the review of the STLC normalization proof: the two pieces of
   existing Pyrosome tooling that the Gluing development currently reimplements
   by hand both work on [stlc_unit]. *)

Local Notation wft := (wf_term stlc_unit []).
Local Notation eqt := (eq_term stlc_unit []).

(* ================================================================== *)
(* 1.  [eredex_steps_with] INFERS the rule instance                    *)
(* ================================================================== *)

(* Replaces [eq_step nm sl] (Stlc/NormalForms.v) and
   [stlc_unit_eq_inst in_X (s := [...])] (Stlc/Eqns.v): no rule shape, no
   [r_*]/[in_*] scaffolding, no hand-written argument list. *)
Ltac estep nm :=
  eredex_steps_with stlc_unit nm;
  [ repeat first [ simple apply wf_subst_nil
                 | simple eapply wf_subst_cons
                 | progress cbn [combine map fst]
                 | progress cbn [Model.wf_term core_model]
                 | eassumption ]
  | shelve ].

Lemma probe_wkn_snoc G G' g A v
  : wft G Senv -> wft G' Senv -> wft g (Ssub G G') ->
    wft A Sty -> wft v (Sval G A) ->
    eqt (Ssub G G') (Cmp G (Ext G' A) G' (Snoc G G' g A v) (Wkn G' A)) g.
Proof. intros; estep "wkn_snoc". Unshelve. all: admit. Admitted.

Lemma probe_val_subst_lambda G G' g A B e
  : wft G Senv -> wft G' Senv -> wft g (Ssub G' G) ->
    wft A Sty -> wft B Sty -> wft e (Sexp (Ext G A) B) ->
    eqt (Sval G' (Arr A B))
      (ValSubst G' G g (Arr A B) (Lam G A B e))
      (Lam G' A B
         (ExpSubst (Ext G' A) (Ext G A)
            (Snoc (Ext G' A) G (Cmp (Ext G' A) G' G (Wkn G' A) g) A (Hd G' A))
            B e)).
Proof. intros; estep "val_subst lambda". Unshelve. all: admit. Admitted.

(* ================================================================== *)
(* 2.  The E-GRAPH proves the DERIVED equations                        *)
(* ================================================================== *)

Ltac egraph_eq :=
  apply (egraph_sound 100 100 100 100 filter_rules
           (fun _ : string * Rule.rule string => true) empty_inj_rules);
  [ exact stlc_unit_wf | solve_wf_ctx | compute_term_wf | compute_term_wf
  | flagged_exact I ].

Definition D_ := var "D".
Definition G_ := var "G".
Definition A_ := var "A".
Definition B_ := var "B".
Definition g_ := var "g".
Definition u_ := var "u".
Definition e_ := var "e".

Definition cbeta : ctx :=
  [("e", Sexp (Ext G_ A_) B_); ("u", Sval D_ A_); ("g", Ssub D_ G_);
   ("B", Sty); ("A", Sty); ("G", Senv); ("D", Senv)].

(* This is Stlc/ModelEq.eq_beta_lift = Stlc/ModelCong.eq_lam_beta, each ~10
   hand-written [eq_term_trans]/congruence steps resting on
   [eq_lift_inst]/[eq_beta_lift] (another ~8 steps, also duplicated).
   The e-graph does the whole chain, axiom-free, in ~6s. *)
Lemma probe_beta_lift
  : wf_lang stlc_unit ->
    eq_term stlc_unit cbeta (Sexp D_ B_)
      (App D_ A_ B_
         (Ret D_ (Arr A_ B_) (ValSubst D_ G_ g_ (Arr A_ B_) (Lam G_ A_ B_ e_)))
         (Ret D_ A_ u_))
      (ExpSubst D_ (Ext G_ A_) (Snoc D_ G_ g_ A_ u_) B_ e_).
Proof.
  intro.
  unfold cbeta, D_, G_, A_, B_, g_, u_, e_,
    Ssub, Sval, Sexp, Senv, Sty, Cmp, Snoc, Wkn, Ext, Hd, Id,
    App, Ret, ValSubst, ExpSubst, Lam, Arr.
  egraph_eq.
Qed.

Print Assumptions probe_beta_lift.
