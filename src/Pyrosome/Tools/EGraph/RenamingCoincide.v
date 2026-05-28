(* The egraph code (EGraph/Defs.v) and the closing metatheory (ClosedCore.v)
   independently define the open->closed maps [var_to_con]/[sort_var_to_con]/
   [ctx_to_rules] (Defs) vs [vtr]/[svtr]/[ctx_to_rules] (ClosedCore).  They
   coincide; these lemmas let the egraph-soundness assembly rewrite between
   them.  Imports order: ClosedCore then Defs, so the bare [ctx_to_rules] is
   Defs's and ClosedCore's is qualified. *)

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ClosedCore.
From Pyrosome.Tools.EGraph Require Import Defs.

Section Coincide.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Lemma var_to_con_is_vtr (e : Term.term V) : var_to_con e = vtr e.
  Proof.
    induction e; basic_term_crush.
    cbn [var_to_con vtr term_var_map]; f_equal; revert H;
      induction l; basic_goal_prep; basic_utils_crush.
  Qed.

  Lemma sort_var_to_con_is_svtr (t : Term.sort V) : sort_var_to_con t = svtr t.
  Proof.
    destruct t; cbn [sort_var_to_con svtr]; f_equal;
      apply map_ext; intro; apply var_to_con_is_vtr.
  Qed.

  Lemma ctx_to_rules_coincide (c : Term.ctx V) :
    ctx_to_rules c = ClosedCore.ctx_to_rules c.
  Proof.
    unfold ctx_to_rules, ClosedCore.ctx_to_rules, ClosedCore.sort_to_var_rule.
    induction c; basic_goal_prep; basic_utils_crush.
    rewrite sort_var_to_con_is_svtr, IHc; reflexivity.
  Qed.

End Coincide.
