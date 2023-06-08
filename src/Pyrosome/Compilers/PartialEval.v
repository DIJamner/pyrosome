Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Tools Require Import Matches.
From Pyrosome.Proof Require Import TreeProofs.
Import Core.Notations.


Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).


  (* TODO: move to utils?*)
  Fixpoint all_uniqueb {A} `{Eqb A} (l : list A) : bool :=
      match l with
      | [] => true
      | x::l' => (negb (inb x l')) && (all_uniqueb l')
      end.


  Definition rule_affine {V} (p : V * _) : bool :=
    match snd p with
    (* don't consider these for now *)
    | sort_eq_rule _ _ _ => false
    | term_eq_rule _ e1 e2 _ =>
        all_uniqueb (fv e2)
    (* Not rewrites, so therefore safe *)
    | _ => true
    end.
  
(*TODO: I could auto-generate the sort if I wanted *)
(* l' should be a subset of the ambient language with desired rewrite rules *)
Definition partial_eval (l : lang) c t fuel e : term :=
  let pf := step_term_V (filter rule_affine l) c fuel e t in
  match check_proof l c pf with
  | Some (e1, e2, t') =>
      if (eqb e e1)
      then e2
      else e
  | None => e
  end.


Lemma partial_eval_correct l c e t fuel
  : wf_lang l ->
    wf_ctx l c ->
    wf_term l c e t ->
    eq_term l c t e (partial_eval l c t fuel e).
Proof.
  unfold partial_eval.
  set (filter _ _) as l'.
  assert (incl l' l) as H' by apply incl_filter.
  revert H'.
  generalize l'; clear l'; intros.
  case_match; eauto with lang_core.
  basic_goal_prep.
  case_match; basic_core_crush.
  symmetry in HeqH2.
  eapply pf_checker_sound in HeqH2; eauto.
  eapply eq_term_conv; eauto.
  eapply term_sorts_eq;
    eauto.
  basic_core_crush.
Qed.

End WithVar.
