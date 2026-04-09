Require Import Datatypes.String Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference
  Elab.PreTerm Elab.PreRule.

Lemma wf_lang_snoc
  : forall (V : Type) (V_Eqb : Eqb V) (l_pre : Rule.lang V)
           (l : list (V * Rule.rule V)) (nr : V * Rule.rule V),
    fresh (fst nr) l_pre ->
    wf_lang l_pre ->
    (wf_lang (nr::l_pre) -> wf_lang_ext (nr::l_pre) l) ->
    wf_rule l_pre (snd nr) -> wf_lang_ext l_pre (l++[nr]).
Proof.
  intros.
  autorewrite with lang_core in *.
  destruct nr.
  rewrite invert_wf_lang_cons in *.
  autorewrite with utils in *.
  rewrite fresh_nil in *.
  intuition auto.
  induction H3; basic_goal_prep; eauto with lang_core.
  constructor;
    basic_core_crush.
  rewrite <- app_assoc; cbn; eauto.
Qed.


Ltac update_lang_assumption :=
  lazymatch goal with
  | H : wf_lang _ |- _ =>
      clear H; intro H
  end.


Ltac push_rule' named_rule do_compute :=
    eapply wf_lang_snoc with (nr:=named_rule);
    [solve_fresh | assumption | update_lang_assumption
    | try (do_compute; compute_wf_rule)].

Ltac push_rule_no_compute named_rule :=
  push_rule' named_rule fail.

Ltac push_rule named_rule :=
  push_rule' named_rule idtac.



Ltac elab_rule' named_rule injective do_compute :=
  let base := lazymatch goal with
                |- wf_lang_ext ?base _ => base
              end in
  let named_rule' := eval vm_compute in
    (fst named_rule, infer_rule base injective (snd named_rule))
  in
  push_rule' named_rule' do_compute.


Ltac elab_rule named_rule injective :=
  elab_rule' named_rule injective idtac.


Ltac setup_lang_interactive :=
  lazymatch goal with
    |- wf_lang_ext ?base ?l =>
      (* So that l is fully evaluated *)
      let l' := open_constr:(_ : lang _) in
      replace l with l';[|shelve];
      assert (wf_lang base) by prove_from_known_elabs
  end.
