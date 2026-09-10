From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Tools Require Import Matches.
From Pyrosome.Proof Require Import TreeProofs.
Import Core.Notations.

(* ---- file-local speedup tactics ----
   `autorewrite ... in *` spends most of its time attempting rewrites inside
   function-typed hypotheses, which are never usefully rewritten, so this
   variant rewrites in the goal and the non-arrow hypotheses only.  And the
   shared `generic_crush` is a `repeat`, so it always pays one extra
   no-progress round; `core_crush1` does a single round. *)
Ltac ar_core_flat :=
  autorewrite with bool rw_prop inversion utils term lang_core model;
  repeat match goal with
         | H : ?T |- _ =>
             lazymatch T with
             | forall _ : _, _ => fail
             | _ => progress autorewrite with bool rw_prop inversion utils term lang_core model in H
             end
         end.
Ltac core_crush1 :=
  intuition break; subst; ar_core_flat;
  intuition unshelve (eauto 7 with utils term lang_core model).


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
  case_match.
  (* the `else` branch is just reflexivity *)
  all: try (solve [eapply eq_term_refl; eassumption]).
  core_crush1.
  subst.
  eapply pf_checker_sound in case_match_eqn; eauto.
  eapply eq_term_conv; eauto.
  eapply term_sorts_eq;
    eauto.
  (* wf_term l c t0 s follows from the checked proof's equation *)
  eapply eq_term_wf_l; eassumption.
Qed.

End WithVar.
