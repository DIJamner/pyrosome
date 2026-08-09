Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel.
Require Import WIP.DttSyntax WIP.DttWf WIP.DttEqns WIP.DttNf WIP.DttNfWf
  WIP.DttLR WIP.DttLRBasics WIP.DttLRCand WIP.DttLRCore WIP.DttLRFun
  WIP.DttRSub WIP.DttCeq WIP.DttModelStruct.
Import Core.Notations.

Ltac pi_pin :=
  match goal with
  | [ Hin : In _ ott_dtt |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
         | [ H : ceq_args (_::_) _ _ |- _ ] => inversion H; subst; clear H
         | [ H : ceq_args [] _ _ |- _ ] => inversion H; subst; clear H
         end;
  cbn [ceq_term ceq_sort DttCM] in *.

Lemma probe_cong
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    (name = "Emptyrec" \/ name = "Pi_rel" \/ name = "Pi_irr"
     \/ name = "lam_rel" \/ name = "lam_irr"
     \/ name = "app_rel" \/ name = "app_irr") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; pi_pin.
  Show 1. Show 2. Show 3. Show 4. Show 5. Show 6. Show 7.
Abort.

Lemma probe_by
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    (name = "Pi_rel subst" \/ name = "Pi_irr subst"
     \/ name = "lam_rel subst" \/ name = "lam_irr subst"
     \/ name = "app_rel subst" \/ name = "app_irr subst"
     \/ name = "Emptyrec subst"
     \/ name = "Pi_rel beta" \/ name = "Pi_irr beta" \/ name = "Pi_rel eta") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; pi_pin.
  Show 1. Show 2. Show 3. Show 4. Show 5. Show 6. Show 7. Show 8. Show 9. Show 10.
Abort.
