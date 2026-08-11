Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.LogRelCand Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.Ceq
  Pyrosome.Gluing.Dtt.ModelStruct Pyrosome.Gluing.Dtt.ModelGlue.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: the [cterm_by] obligation for "proof
   irrelevance" ([ott_proofirr_el], src/Pyrosome/Lang/OTT/ProofIrr.v),
   the fifth and last rule fragment.

   THE RULE IS ONE EQUATION AND NO CONGRUENCE (there is no former to be
   congruent over -- irrelevance is a fact about the two ARGUMENTS "t"
   and "u" of the rule, not about a constructor applied to them), so this
   file needs only [pi_by_obligation]'s machinery and none of the rest of
   ModelPi.v's apparatus.

   IT IS THE CHEAPEST CASE IN THE WHOLE LAYER.  [Ceq_term]'s semantic
   conjunct (src/Pyrosome/Gluing/Dtt/Ceq.v's [ceq_exp]) constrains only
   the LEFT term of a clause; the equation to discharge here has for its
   two sides the rule's own arguments "t" and "u", each of which ALREADY
   carries a [Ceq_term] clause (handed in by [ceq_args]).  So the syntactic
   half of the goal is [dtt_eqt_by]'s free [eq_term] conjunct, and the
   semantic half is not a new fact at all -- it is exactly the LEFT half
   of the "t" argument's own clause, read off with [Ceq_exp_e].  No
   reducibility argument, and in particular no use of "u"'s clause, is
   needed: the whole proof is one [ceq_exp] application. *)

Local Notation eqt := (eq_term ott_dtt []).

Lemma proofirr_by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    (name = "proof irrelevance") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hname Hargs.
  pose proof (dtt_eqt_by Hin Hargs) as Heq.
  subst name; rule_pin.
  apply ceq_exp; [ exact Heq | ].
  (* The remaining semantic obligation is exactly the LEFT half of the
     "t" argument's own clause; [Ceq_exp_e]'s [exact] does the reduction
     that identifies the two substitution instances, so it is enough to
     try every [exp]-sorted argument clause in context and let the kernel
     pick the one whose left term matches ([match] backtracks over
     hypotheses on tactic failure). *)
  match goal with
  | [ Ht : Ceq_term _ _ _ |- _ ] => exact (proj2 (Ceq_exp_e Ht))
  end.
Qed.
