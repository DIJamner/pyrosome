Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Tools Require Import Resolution.
From Pyrosome.Gluing Require Import CutTModel.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Determinism Model ApplyLemmas SortInj Typing Preservation.
From Pyrosome.Lang.OTT Require Import Base Nat.
Import Core.Notations.

(* [fo_lang] is defined in Model.v (where [norm_ceq_term] references it). *)

Lemma fo_lang_all_fresh : all_fresh fo_lang.
Proof. compute_all_fresh. Qed.

Lemma fo_wf_lang : wf_lang fo_lang.
Proof. unfold fo_lang. prove_by_lang_db. Qed.

(* names-only collapses for the fast Type-safe rule split *)
Lemma sort_rules {name c' args}
  : In (name, sort_rule c' args) fo_lang ->
    In name ["exp";"ty";"sub";"env";"tyinfo";"tlvl";"ltl";"lvl";"relevance"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Lemma term_rules_names {name c' args t}
  : In (name, term_rule c' args t) fo_lang ->
    In name ["Emptyrec";"Empty";"suc";"zero";"Nat";"El";"U";"hd";"wkn";"snoc";
             "ext";"forget";"emp";"exp_subst";"ty_subst";"cmp";"id";"info";"next";
             "inf";"iota";"L0<L1";"L1";"L0";"irr";"rel"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Lemma term_eq_rules_names {name c' e1 e2 t}
  : In (name, term_eq_rule c' e1 e2 t) fo_lang ->
    In name ["Empty subst";"suc subst";"zero subst";"Nat subst";"El subst";
             "U subst";"snoc_wkn_hd";"cmp_snoc";"snoc_hd";"wkn_snoc";"id_emp_forget";
             "cmp_forget";"exp_subst_cmp";"exp_subst_id";"ty_subst_cmp";"ty_subst_id";
             "cmp_assoc";"id_left";"id_right";"next1";"next0";"ltl_irr"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

(* ================================================================== *)
(* apply / length lemmas for the env-free evaluator                    *)
(* ================================================================== *)

(* a normalized object environment has one type per [ext] *)
Lemma eval_env_length : forall G Genv, eval_env G Genv -> length Genv = ctx_len G.
Proof.
  induction 1 as [ | A i G Genv S HG IH HA ]; cbn.
  - reflexivity.
  - rewrite length_map. rewrite IH. reflexivity.
Qed.

(* The CutTModel argument relation over Norm projects onto Core's eq_args
   (the first/eq_term component of each per-argument [ceq_term]). *)
Lemma norm_ceq_args_eq_args : forall c' s1 s2,
    ceq_args (CM := Norm) c' s1 s2 ->
    eq_args (Model := core_model fo_lang) [] c' s1 s2.
Proof.
  induction 1 as [ | c0 es1 es2 H IH nm t e1 e2 Ht ].
  - constructor.
  - unfold ceq_term, Norm, norm_ceq_term in Ht. destruct Ht as [Heq _].
    constructor; eauto.
Qed.

(* ================================================================== *)
(* cterm_var : vacuous (ambient context [])                            *)
(* ================================================================== *)

Lemma Norm_cterm_var : forall (n : string) (t : @sort string),
    In (n, t) [] -> ceq_term (CutTModel := Norm) t (var n) (var n).
Proof. intros n t []. Qed.

(* ================================================================== *)
(* cterm_trans / cterm_sym  (eq_term_trans/sym + glue via determinism) *)
(* ================================================================== *)

Lemma Norm_cterm_trans : forall (t : @sort string) e1 e12 e2,
    ceq_term (CutTModel := Norm) t e1 e12 ->
    ceq_term (CutTModel := Norm) t e12 e2 ->
    ceq_term (CutTModel := Norm) t e1 e2.
Proof.
  intros t e1 e12 e2 H1 H2.
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct H1 as [Heq1 G1], H2 as [Heq2 G2].
  split.
  - exact (eq_term_trans Heq1 Heq2).
  - (* GLUE (typed eval): both glues mention the SAME sort [t]; invert them and
       merge the two derivations of the middle term [e12] via determinism. *)
    inversion G1; subst; inversion G2; subst;
      first
        [ (* cross/spurious cases (contradictory sort-head names) *)
          exfalso; congruence
        | (* exp *) match goal with
            Ha : eval_rel _ e12 _ _, Hb : eval_rel _ e12 _ _ |- _ =>
              destruct (eval_rel_det Ha Hb) as [[? ?] ?]; subst end;
          econstructor; eassumption
        | (* ty *) match goal with
            Ha : eval_ty _ e12 _, Hb : eval_ty _ e12 _ |- _ =>
              destruct (eval_ty_det Ha Hb) as [? ?]; subst end;
          econstructor; eassumption
        | (* sub *) match goal with
            Ha : eval_sub _ _ e12 _, Hb : eval_sub _ _ e12 _ |- _ =>
              destruct (eval_sub_det Ha Hb) as [[? ?] ?]; subst end;
          econstructor; eassumption
        | (* env *) match goal with
            Ha : eval_env e12 _, Hb : eval_env e12 _ |- _ =>
              pose proof (eval_env_det Ha Hb); subst end;
          econstructor; eassumption
        | (* info: nf_info transitivity; ltl: trivial *)
          econstructor; solve [ congruence | assumption ] ].
Qed.

Lemma Norm_cterm_sym : forall (t : @sort string) e1 e2,
    ceq_term (CutTModel := Norm) t e1 e2 -> ceq_term (CutTModel := Norm) t e2 e1.
Proof.
  intros t e1 e2 H.
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct H as [Heq Hg].
  split.
  - exact (eq_term_sym Heq).
  - (* GLUE (typed eval): swap the two evals (resp. flip the nf_info equality). *)
    inversion Hg; subst;
      econstructor; solve [ eassumption | congruence | assumption ].
Qed.

(* ================================================================== *)
(* glue_term symmetry / transitivity, and env-retargeting of [ty] glue. *)
(* These are the building blocks for the (now inductive) [glue_sort]    *)
(* congruence / transitivity / symmetry below: a sort's glue is just     *)
(* [glue_term] on its subterms, so the sort ops reduce to these.         *)
(* ================================================================== *)

Lemma glue_term_sym : forall t e1 e2,
    glue_term t e1 e2 -> glue_term t e2 e1.
Proof.
  intros t e1 e2 H; inversion H; subst;
    econstructor; solve [ eassumption | congruence | assumption ].
Qed.

Lemma glue_term_trans : forall t e1 e12 e2,
    glue_term t e1 e12 -> glue_term t e12 e2 -> glue_term t e1 e2.
Proof.
  intros t e1 e12 e2 G1 G2.
  inversion G1; subst; inversion G2; subst;
    first
      [ exfalso; congruence
      | match goal with
          Ha : eval_rel _ e12 _ _, Hb : eval_rel _ e12 _ _ |- _ =>
            destruct (eval_rel_det Ha Hb) as [[? ?] ?]; subst end;
        econstructor; eassumption
      | match goal with
          Ha : eval_ty _ e12 _, Hb : eval_ty _ e12 _ |- _ =>
            destruct (eval_ty_det Ha Hb) as [? ?]; subst end;
        econstructor; eassumption
      | match goal with
          Ha : eval_sub _ _ e12 _, Hb : eval_sub _ _ e12 _ |- _ =>
            destruct (eval_sub_det Ha Hb) as [[? ?] ?]; subst end;
        econstructor; eassumption
      | match goal with
          Ha : eval_env e12 _, Hb : eval_env e12 _ |- _ =>
            pose proof (eval_env_det Ha Hb); subst end;
        econstructor; eassumption
      | econstructor; solve [ congruence | assumption ] ].
Qed.

(* A [ty]-sorted glue only reads the evaluated env of its context arg; since
   glued envs evaluate to the SAME [senv], the glue transfers across them. The
   [tyinfo] index is irrelevant to [glue_ty], so it may change freely. *)
Lemma glue_ty_retarget : forall i i' G G' A1 A2,
    glue_term (scon "env" []) G G' ->
    glue_term (scon "ty" [i; G]) A1 A2 ->
    glue_term (scon "ty" [i'; G']) A1 A2.
Proof.
  intros i i' G G' A1 A2 He Ht.
  inversion He; subst. inversion Ht; subst.
  match goal with
    Ha : eval_env G ?genv, Hb : eval_env G ?ge |- _ =>
      pose proof (eval_env_det Ha Hb); subst end.
  econstructor; eassumption.
Qed.

(* [cterm_conv] is proved below (just before [cterm_cong]); it reuses the
   typed-glue reconciliation machinery defined in that section. *)

(* ================================================================== *)
(* sort ops : eq_sort_* for the eq component, head+arity for the glue  *)
(* ================================================================== *)

(* Resolve the (now concrete) sort rule's context from [Hin], invert [ceq_args]
   into one [norm_ceq_term] per argument, and expose the per-argument
   [glue_term] witnesses (the [glue_sort] constructors consume exactly these). *)
Ltac peel_sort_args :=
  match goal with Hin : In _ fo_lang |- _ =>
    apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ fo_lang_all_fresh)) in Hin;
    vm_compute in Hin; injection Hin; clear Hin; intros; subst end;
  repeat match goal with H : ceq_args (_ :: _) _ _ |- _ => inversion H; subst; clear H end;
  try match goal with H : ceq_args [] _ _ |- _ => inversion H; subst; clear H end;
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with H : @prod _ _ |- _ => destruct H end.

(* [concretize_subst] / [finish_absurd] mirror the like-named tactics used in
   the [cterm] dispatch below; they are repeated here (Ltac is re-definable) so
   the sort dispatch can run before that section.  The glue goal lives in [Type],
   so dispatch goes through the boolean [eqb] (no [Prop]-into-[Type] elimination
   of the [In] membership). *)
Ltac concretize_subst_s :=
  match goal with
  | E : eqb ?nm ?s = true |- _ =>
      let Eq := fresh in
      pose proof (proj1 (eqb_prop_iff _ nm s) ltac:(rewrite E; exact I)) as Eq;
      clear E; subst nm
  end.

Ltac finish_absurd_s Hmem names :=
  exfalso;
  let Hex := fresh "Hex" in
  assert (Hex : existsb (eqb _) names = true)
    by (apply (proj2 (existsb_exists _ _)); eexists; split;
        [ exact Hmem | apply (@eqb_refl_true string _ string_Eqb_ok) ]);
  cbn in Hex;
  repeat match goal with E : eqb _ _ = false |- _ => rewrite E in Hex end;
  cbn in Hex; discriminate Hex.

Ltac disp_sort_cong nm tac :=
  let E := fresh "Eqn" in
  match goal with
  | |- glue_sort (scon ?name _) _ =>
      destruct (eqb name nm) eqn:E;
      [ concretize_subst_s; peel_sort_args; tac | ]
  end.

Lemma Norm_csort_cong : forall (c' : @ctx string) (name : string) (args : list string) s1 s2,
    In (name, sort_rule c' args) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_sort (CutTModel := Norm) (scon name s1) (scon name s2).
Proof.
  intros c' name args s1 s2 Hin Hargs.
  pose proof fo_wf_lang as wfl.
  unfold ceq_sort, Norm, norm_ceq_sort. split.
  - pose proof (norm_ceq_args_eq_args Hargs) as Heqa.
    eapply sort_con_congruence; try exact _; try eassumption.
  - (* glue: dispatch on the sort name (the only sorts), peel its arguments,
       and rebuild the matching [glue_sort] constructor from the per-argument
       [glue_term]s.  The [exp] type argument is glued at the right side's
       index/env [i2;G2]; retarget it to the left's [i1;G1] (their envs glue). *)
    pose proof (sort_rules Hin) as Hmem.
    disp_sort_cong "exp"
      ltac:(eapply glue_sort_exp;
              [ eapply glue_ty_retarget; [ apply glue_term_sym; eassumption | eassumption ]
              | eassumption | eassumption ]).
    disp_sort_cong "ty" ltac:(eapply glue_sort_ty; eassumption).
    disp_sort_cong "sub" ltac:(eapply glue_sort_sub; eassumption).
    disp_sort_cong "env" ltac:(constructor).
    disp_sort_cong "tyinfo" ltac:(constructor).
    disp_sort_cong "tlvl" ltac:(constructor).
    disp_sort_cong "ltl" ltac:(eapply glue_sort_ltl; eassumption).
    disp_sort_cong "lvl" ltac:(constructor).
    disp_sort_cong "relevance" ltac:(constructor).
    finish_absurd_s Hmem ["exp";"ty";"sub";"env";"tyinfo";"tlvl";"ltl";"lvl";"relevance"].
Qed.

Lemma Norm_csort_by : forall (c' : @ctx string) (name : string) t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_sort (CutTModel := Norm) t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c' name t1 t2 s1 s2 Hin _.
  exfalso.
  assert (Hb : forallb (fun p => match snd p with sort_eq_rule _ _ _ => false | _ => true end)
                       fo_lang = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Hb in Hin; cbn in Hin; discriminate Hin.
Qed.

Lemma Norm_csort_trans : forall t1 t12 t2,
    ceq_sort (CutTModel := Norm) t1 t12 -> ceq_sort (CutTModel := Norm) t12 t2 ->
    ceq_sort (CutTModel := Norm) t1 t2.
Proof.
  intros t1 t12 t2 H1 H2.
  unfold ceq_sort, Norm, norm_ceq_sort in *.
  destruct H1 as [Heq1 Gs1], H2 as [Heq2 Gs2].
  split.
  - exact (eq_sort_trans Heq1 Heq2).
  - (* both glues share the middle sort [t12]; inverting them lines up the
       per-subterm glues, which compose by [glue_term_trans] (retargeting the
       [exp] type argument's [ty] glue across the two glued envs). *)
    inversion Gs1; subst; inversion Gs2; subst;
      first
        [ exfalso; congruence
        | eapply glue_sort_exp;
            [ eapply glue_term_trans;
                [ eassumption
                | eapply glue_ty_retarget; [ apply glue_term_sym; eassumption | eassumption ] ]
            | eapply glue_term_trans; eassumption
            | eapply glue_term_trans; eassumption ]
        | eapply glue_sort_ty; eapply glue_term_trans; eassumption
        | eapply glue_sort_sub; eapply glue_term_trans; eassumption
        | eapply glue_sort_ltl; eapply glue_term_trans; eassumption
        | constructor ].
Qed.

Lemma Norm_csort_sym : forall t1 t2,
    ceq_sort (CutTModel := Norm) t1 t2 -> ceq_sort (CutTModel := Norm) t2 t1.
Proof.
  intros t1 t2 H. unfold ceq_sort, Norm, norm_ceq_sort in *.
  destruct H as [Heq Gs].
  split.
  - exact (eq_sort_sym Heq).
  - (* invert the glue and swap each per-subterm glue ([glue_term_sym]),
       retargeting the [exp] type argument's [ty] glue across the glued envs. *)
    inversion Gs; subst;
      first
        [ eapply glue_sort_exp;
            [ eapply glue_ty_retarget; [ eassumption | apply glue_term_sym; eassumption ]
            | apply glue_term_sym; eassumption | apply glue_term_sym; eassumption ]
        | eapply glue_sort_ty; apply glue_term_sym; eassumption
        | eapply glue_sort_sub; apply glue_term_sym; eassumption
        | eapply glue_sort_ltl; apply glue_term_sym; eassumption
        | constructor ].
Qed.

(* ================================================================== *)
(* Type-safe name dispatch (shared by cterm_cong / cterm_by glue parts)*)
(* ================================================================== *)

Ltac concretize_subst :=
  match goal with
  | E : eqb ?nm ?s = true |- _ =>
      let Eq := fresh in
      pose proof (proj1 (eqb_prop_iff _ nm s) ltac:(rewrite E; exact I)) as Eq;
      clear E; subst nm
  end.

Ltac recover_peel :=
  match goal with Hin : In _ _ |- _ =>
    apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ fo_lang_all_fresh)) in Hin;
    vm_compute in Hin; injection Hin; clear Hin; intros; subst end;
  repeat match goal with H : ceq_args (_ :: _) _ _ |- _ => inversion H; subst; clear H end;
  try match goal with H : ceq_args [] _ _ |- _ => inversion H; subst; clear H end.

(* ------------------------------------------------------------------ *)
(* Typed-glue congruence solver.                                        *)
(*                                                                      *)
(* After [recover_peel], the per-argument [ceq_term] hyps are [eq_term  *)
(* * glue_term] pairs.  The TERM arguments [e1_i]/[e2_i] are bare        *)
(* variables (introduced by the [ceq_args] inversion); the SORT indices *)
(* threaded by the glue (contexts/types) are CONCRETE [con]-headed       *)
(* formers built from those variables.  The solver:                      *)
(*   1. [arg_glue_prep]  : split the pairs and invert each per-arg       *)
(*      [glue_term], exposing its typed eval witnesses;                  *)
(*   2. [eval_indices]   : fully evaluate the con-headed type/context    *)
(*      index witnesses (NEVER the bare-variable term-arg evals), so an  *)
(*      opaque exp-argument type [T] is revealed as a concrete [dU]/[dEl]*)
(*      and its [nf_info] annotations surface as rewritable equalities;  *)
(*   3. [merge_dets]     : equate the shared semantic indices that arise *)
(*      from different arguments' glues, via the [eval_*_det] lemmas;    *)
(*   4. [build_eval]     : pick the result [glue_*] constructor and the  *)
(*      matching [ev_*] evaluator constructors, closing the eval         *)
(*      premises from the (now reconciled) hypotheses, rewriting         *)
(*      [nf_info] equalities to align universe annotations.              *)
(* The two eliminators ([El]/[Emptyrec]) fall out of the same recipe;    *)
(* [Emptyrec] additionally needs its scrutinee value to be a neutral,    *)
(* supplied by [canonical_empty] on the preservation of its eval.        *)
(* ------------------------------------------------------------------ *)

Ltac arg_glue_prep :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with H : @prod _ _ |- _ => destruct H end;
  repeat match goal with H : glue_term _ _ _ |- _ => inversion H; subst; clear H end.

(* Invert ONLY con-headed eval witnesses (the sort's type/context indices);
   leave the bare-variable term-argument evals untouched (inverting those would
   case-split on an opaque variable). *)
Ltac eval_indices :=
  repeat match goal with
    | H : eval_ty  _ (con _ _) _   |- _ => inversion H; subst; clear H
    | H : eval_rel _ (con _ _) _ _ |- _ => inversion H; subst; clear H
    | H : eval_sub _ _ (con _ _) _ |- _ => inversion H; subst; clear H
  end.

(* Equate duplicate semantic indices coming from distinct arguments' glues.
   Determinism keys only on the SUBJECT term, so two evals of the same term —
   even with not-yet-unified context/type indices — get fully reconciled. *)
Ltac merge_dets :=
  repeat first
    [ match goal with Ha : eval_env ?G _, Hb : eval_env ?G _ |- _ =>
        assert_fails (constr_eq Ha Hb);
        pose proof (eval_env_det Ha Hb); subst; clear Hb end
    | match goal with Ha : eval_ty _ ?A _, Hb : eval_ty _ ?A _ |- _ =>
        assert_fails (constr_eq Ha Hb);
        destruct (eval_ty_det Ha Hb) as [? ?]; subst; clear Hb end
    | match goal with Ha : eval_rel _ ?e _ _, Hb : eval_rel _ ?e _ _ |- _ =>
        assert_fails (constr_eq Ha Hb);
        destruct (eval_rel_det Ha Hb) as [[? ?] ?]; subst; clear Hb end
    | match goal with Ha : eval_sub _ _ ?g _, Hb : eval_sub _ _ ?g _ |- _ =>
        assert_fails (constr_eq Ha Hb);
        destruct (eval_sub_det Ha Hb) as [[? ?] ?]; subst; clear Hb end ].

(* Build the result glue from the evaluator: the result [glue_*] constructor
   (chosen by the concrete result-sort head) leaves eval premises with concrete
   heads, so [econstructor] picks the unique [ev_*] and [eassumption] discharges
   them; [nf_info] equalities realign universe annotations when needed. *)
Ltac build_eval :=
  solve [ repeat first
            [ eassumption
            | match goal with H : @eq (@term string) _ _ |- _ => rewrite H end
            | econstructor ] ].

(* Info / [ltl] result: the result glue is an [nf_info] equality (or trivial).
   Expose the (possibly stuck) [nf_info] match with [cbn], then rewrite the
   per-arg [nf_info] equalities into the now-visible scrutinees. *)
Ltac solve_info :=
  solve [ econstructor; cbn in *;
          repeat match goal with H : @eq (@term string) _ _ |- _ => rewrite H end;
          first [ reflexivity | congruence ] ].

Ltac solve_cong :=
  arg_glue_prep; eval_indices; merge_dets;
  first
    [ build_eval
    | solve_info
    | solve [ econstructor ] ].

Ltac disp nm :=
  let E := fresh "Eqn" in
  match goal with
  | |- glue_term _ (con ?name _) _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; solve_cong | ]
  end.

Ltac dispA nm :=
  let E := fresh "Eqn" in
  match goal with
  | |- glue_term _ (con ?name _) _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; admit | ]
  end.

(* ------------------------------------------------------------------ *)
(* The two eliminators need a per-rule step beyond the generic recipe.  *)
(* ------------------------------------------------------------------ *)

(* A [Type]-valued canonical-forms lemma for [El Empty]: a value of that type is
   a neutral.  [canonical_empty] (Typing.v) returns a [Prop] [exists], which
   cannot be eliminated into the [Type]-valued glue goal; casing on the VALUE
   (in [Type]) and refuting the non-neutral shapes from typing avoids that. *)
Lemma canonical_empty_sig : forall Ge v,
    has_svalty Ge v (dEl vEmpty) -> { n | v = vNe n }.
Proof.
  intros Ge v H; destruct v;
    solve [ eexists; reflexivity | exfalso; inversion H ].
Qed.

(* [Emptyrec] : its [El Empty] scrutinee value is a NEUTRAL by canonical
   forms (preservation), which [ev_Emptyrec] requires. *)
Ltac solve_emptyrec :=
  arg_glue_prep; eval_indices; merge_dets;
  match goal with H : eval_rel _ _ (dEl vEmpty) ?v |- _ =>
    destruct (canonical_empty_sig (eval_rel_preserves_typing H)) as [? ?]; subst v end;
  build_eval.

(* [hd] : its result type [ty_subst wkn A] evaluates to [apply_ty (wkn_list n) S],
   while [ev_hd] hands back [shift_ty 1 S]; bridge them with [apply_wkn_eq_shift]
   (the type [S] is scoped because it is a well-formed semantic type). *)
Ltac hd_retype :=
  match goal with
  | H : eval_ty ?ge ?A ?S |- eval_rel _ _ (apply_ty (wkn_list (length ?ge)) ?S) _ =>
      rewrite (fst apply_wkn_eq_shift S (length ge)
                 (wf_svalty_scoped (snd (snd (fst (fst eval_sound)) _ _ _ H))))
  end.
Ltac solve_hd :=
  arg_glue_prep; eval_indices; merge_dets;
  eapply glue_exp;
  [ solve [ repeat first [ eassumption | econstructor ] ]
  | eapply ev_ty_subst; [ eapply ev_wkn; eassumption | eassumption ]
  | hd_retype; eapply ev_hd; eassumption
  | hd_retype; eapply ev_hd; eassumption ].

Ltac disp_emptyrec :=
  let E := fresh "Eqn" in
  match goal with
  | |- glue_term _ (con ?name _) _ =>
      destruct (eqb name "Emptyrec") eqn:E;
      [ concretize_subst; recover_peel; solve_emptyrec | ]
  end.

Ltac disp_hd :=
  let E := fresh "Eqn" in
  match goal with
  | |- glue_term _ (con ?name _) _ =>
      destruct (eqb name "hd") eqn:E;
      [ concretize_subst; recover_peel; solve_hd | ]
  end.

(* close the fall-through (no name matched): [name] is in [names] (Hmem), yet every
   [eqb name "X" = false] hypothesis excludes it — via [existsb], no Prop elimination. *)
Ltac finish_absurd Hmem names :=
  exfalso;
  let Hex := fresh "Hex" in
  assert (Hex : existsb (eqb _) names = true)
    by (apply (proj2 (existsb_exists _ _)); eexists; split;
        [ exact Hmem | apply (@eqb_refl_true string _ string_Eqb_ok) ]);
  cbn in Hex;
  repeat match goal with E : eqb _ _ = false |- _ => rewrite E in Hex end;
  cbn in Hex; discriminate Hex.

(* ================================================================== *)
(* cterm_conv : eq_term_conv + glue carries over the glued sorts       *)
(* ================================================================== *)

(* The glue threads the sort's context/type indices; across [eq_sort]-glued
   sorts those indices evaluate IDENTICALLY (the [glue_sort] component), so the
   term glue transfers: invert the sort glue (its per-index sub-glues) and the
   term glue at [t1], reconcile the shared eval indices, and rebuild at [t2]. *)
Lemma Norm_cterm_conv : forall t1 t2 e1 e2,
    ceq_sort (CutTModel := Norm) t1 t2 ->
    ceq_term (CutTModel := Norm) t1 e1 e2 ->
    ceq_term (CutTModel := Norm) t2 e1 e2.
Proof.
  intros t1 t2 e1 e2 Hs Ht.
  unfold ceq_sort, Norm, norm_ceq_sort in Hs; destruct Hs as [Heqs Gs].
  unfold ceq_term, Norm, norm_ceq_term in *; destruct Ht as [Heqt Gt].
  split.
  - exact (eq_term_conv Heqt Heqs).
  - inversion Gs; subst; inversion Gt; subst;
      repeat match goal with H : glue_term _ _ _ |- _ => inversion H; subst; clear H end;
      eval_indices; merge_dets;
      solve [ build_eval | econstructor; solve [ eassumption | congruence ] ].
Qed.

(* ================================================================== *)
(* cterm_cong                                                          *)
(* ================================================================== *)

(* The well-formedness (eq_term) component is uniform (term_con_congruence); the
   eval GLUE is built for ALL 26 formers from the typed evaluator (see
   [solve_cong]), with [hd] and [Emptyrec] handled by [solve_hd]/[solve_emptyrec]
   (their result type/scrutinee need [apply_wkn_eq_shift] / canonical forms). *)
Lemma Norm_cterm_cong : forall (c' : @ctx string) (name : string) (args : list string)
    (t : @sort string) s1 s2,
    In (name, term_rule c' args t) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_term (CutTModel := Norm) t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hargs.
  pose proof fo_wf_lang as wfl.
  unfold ceq_term, Norm, norm_ceq_term. split.
  - (* well-formedness component (= SyntacticModel cterm_cong) *)
    pose proof (norm_ceq_args_eq_args Hargs) as Heqa.
    eapply term_con_congruence; try exact _; try (right; reflexivity); try eassumption.
  - (* eval glue (typed): dispatch on the (only) term former, peel its arguments
       into per-arg glue witnesses, and rebuild the result [glue_*] from the
       typed evaluator constructors (see [solve_cong]). *)
    pose proof (term_rules_names Hin) as Hmem.
    disp "rel".
    disp "irr".
    disp "L0".
    disp "L1".
    disp "L0<L1".
    disp "inf".
    disp "iota".
    disp "next".
    disp "info".
    disp "emp".
    disp "ext".
    disp "forget".
    disp "id".
    disp "wkn".
    disp "cmp".
    disp "snoc".
    disp "Nat".
    disp "zero".
    disp "Empty".
    disp "U".
    disp "suc".
    disp "exp_subst".
    disp "ty_subst".
    disp_hd.
    disp "El".
    disp_emptyrec.
    finish_absurd Hmem ["Emptyrec";"Empty";"suc";"zero";"Nat";"El";"U";"hd";"wkn";"snoc";
      "ext";"forget";"emp";"exp_subst";"ty_subst";"cmp";"id";"info";"next";"inf";"iota";
      "L0<L1";"L1";"L0";"irr";"rel"].
Qed.

(* ================================================================== *)
(* cterm_by                                                            *)
(* ================================================================== *)

Ltac solve_by :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with H : @prod _ _ |- _ => destruct H end;
  first [ exact tt | reflexivity | solve [congruence] ].

Ltac dispby nm :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; solve_by | ]
  end.

Ltac dispbyA nm :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; admit | ]
  end.

Ltac build := repeat first [ eassumption | econstructor ].

Ltac rhs_finish :=
  cbn [apply_val apply_ty apply_ne nth_default nth_error map ctx_len id_list wkn_list seq] in *;
  repeat match goal with H : @eq (@term string) ?a ?b |- _ => first [ rewrite H | idtac ]; clear H end;
  rewrite ?apply_id_val, ?apply_id_ty, ?apply_id_map, ?snoc_wkn_hd_list;
  cbn [apply_val apply_ty apply_ne nth_default nth_error map ctx_len id_list wkn_list seq];
  build.

Ltac solve_by2 :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with
         | H : @sigT _ _ |- _ => destruct H as [? [? ?]]
         | H : @prod _ _ |- _ => destruct H
         end;
  first
    [ exact tt
    | reflexivity
    | solve [ eexists; split; [ build | rhs_finish ] ]
    | solve [ congruence ] ].

Ltac dispbyB nm :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; solve_by2 | ]
  end.

(* Bespoke tactic for snoc_wkn_hd: needs eval_env_length to equate ctx_len of
   the two G sides (s1 vs s2 substitutions both have the same env witness). *)
Ltac solve_snoc_wkn_hd :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with
         | H : @sigT _ _ |- _ => destruct H as [? [? ?]]
         | H : @prod _ _ |- _ => destruct H
         end;
  match goal with Ha : eval_env ?G1 ?gv, Hb : eval_env ?G2 ?gv |- _ =>
    let Hlen := fresh in
    pose proof (eq_trans (eq_sym (eval_env_length Ha)) (eval_env_length Hb)) as Hlen;
    eexists; split;
    [ build
    | rewrite snoc_wkn_hd_list, Hlen; build ]
  end.

Ltac dispbyB_snoc_wkn_hd :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name "snoc_wkn_hd") eqn:E;
      [ concretize_subst; recover_peel; solve_snoc_wkn_hd | ]
  end.

(* ================================================================== *)
(* cterm_by Tier-C composition rules [id_right] / [wkn_snoc]           *)
(*                                                                     *)
(* Both are [cmp]s whose [g]-slot is an [id]/[wkn] over a context that *)
(* is the codomain of the [f]-slot; the [ev_cmp] output collapses via  *)
(* [map_apply_id_list] / [map_apply_wkn_list] once we know the         *)
(* substitution's length, which the carried [eq_term] (well-formedness)*)
(* supplies through [eval_sub_len] (SortInj) — the codomain         *)
(* [ctx_len] then matches the inner [id]/[wkn]'s context via the env    *)
(* glue ([eval_env_length]).                                           *)
(* ================================================================== *)

Ltac expose_glue :=
  unfold ceq_term, Norm, norm_ceq_term in *;
  cbn in *;
  repeat match goal with H : @prod _ _ |- _ => destruct H end;
  repeat match goal with H : @sigT _ _ |- _ => destruct H as [? [? ?]] end.

(* Goal [length w = ctx_len G]: the [sub]-sorted argument that evaluates to [w]
   has codomain [cod] (first internal arg of its [sub] sort, from the carried
   [eq_term]/wf), and [cod] glues to [G] as environments. *)
Ltac prove_sub_len w G :=
  match goal with
  | Hev : eval_sub ?a w, Heq : eq_term _ [] ?t ?a _ |- _ =>
      lazymatch eval cbn in t with
      | scon "sub" [?cod; _] =>
          let HL := fresh "HL" in
          pose proof (eval_sub_len Hev
                        (eq_term_wf_l fo_wf_lang ltac:(constructor) Heq)) as HL;
          match goal with
          | Ha : eval_env G ?ex, Hb : eval_env cod ?ex |- _ =>
              rewrite HL, <- (eval_env_length Hb), <- (eval_env_length Ha);
              reflexivity
          end
      end
  end.

(* [cmp f id = f] *)
Ltac solve_id_right :=
  expose_glue;
  eexists; split; [ | solve [ eassumption ] ];
  match goal with
  | |- eval_sub (con _ [con _ [?Ge]; _; _; _; _]) ?w =>
      let Hmap := fresh in
      assert (Hmap : map (apply_val w) (id_list (ctx_len Ge)) = w)
        by (apply map_apply_id_list; prove_sub_len w Ge);
      rewrite <- Hmap; econstructor; [ eassumption | econstructor ]
  end.

(* [cmp (snoc g v) wkn = g] *)
Ltac solve_wkn_snoc :=
  expose_glue;
  eexists; split; [ | solve [ eassumption ] ];
  match goal with
  | |- eval_sub (con _ [con _ [_; _; ?Gw]; con _ [?v; ?g; _; _; _; _]; _; _; _]) ?w =>
      match goal with
      | Hg : eval_sub g w, Hv : eval_rel v ?vv |- _ =>
          let Hmap := fresh in
          assert (Hmap : map (apply_val (vv :: w)) (wkn_list (ctx_len Gw)) = w)
            by (apply map_apply_wkn_list; prove_sub_len w Gw);
          rewrite <- Hmap;
          econstructor; [ econstructor; [ exact Hg | exact Hv ] | econstructor ]
      end
  end.

Ltac dispby_id_right :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name "id_right") eqn:E;
      [ concretize_subst; recover_peel; solve_id_right | ]
  end.

Ltac dispby_wkn_snoc :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name "wkn_snoc") eqn:E;
      [ concretize_subst; recover_peel; solve_wkn_snoc | ]
  end.

(* Typed by-solver: reuse the cong front-end (expose per-arg glues, evaluate
   con-headed indices, reconcile via determinism), canonicalize any [El Empty]
   scrutinee, then build the result glue, normalizing the structural-substitution
   redexes ([apply_ty (id_list _)] etc.) so both sides reach the same value. *)
Ltac by_normalize :=
  cbn [apply_val apply_ty apply_ne nth_default nth_error map ctx_len id_list wkn_list seq] in *;
  rewrite ?apply_id_val, ?apply_id_ty, ?apply_id_map, ?snoc_wkn_hd_list in *.

Ltac solve_byT :=
  arg_glue_prep; eval_indices; merge_dets;
  try (match goal with H : eval_rel _ _ (dEl vEmpty) ?v |- _ =>
         destruct (canonical_empty_sig (eval_rel_preserves_typing H)) as [? ?]; subst v end;
       eval_indices; merge_dets);
  first
    [ solve [ econstructor; cbn; repeat match goal with
               H : @eq (@term string) _ _ |- _ => rewrite H end;
              first [ reflexivity | congruence ] ]
    | solve [ econstructor;
              repeat first
                [ eassumption
                | match goal with H : @eq (@term string) _ _ |- _ => rewrite H end
                | progress by_normalize
                | econstructor ] ] ].

(* [solve_byT] discharges 16/22 equation axioms (the structural/composition
   laws); the 6 substitution-pushing laws for data constructors
   ([Empty/Nat/zero/suc/El subst]) and [snoc_wkn_hd] still [admit] (they need the
   evaluator to compute [apply_val] under [vSuc]/codes and through [snoc]/[wkn]).
   The [admit] fallback keeps the dispatch robust; hence [Norm_cterm_by] is still
   [Admitted]. *)
Ltac dispbyT nm :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name nm) eqn:E;
      [ concretize_subst; recover_peel; first [ solve_byT | admit ] | ]
  end.

Lemma Norm_cterm_by : forall (c' : @ctx string) (name : string) e1r e2r tr s1 s2,
    In (name, term_eq_rule c' e1r e2r tr) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_term (CutTModel := Norm) tr[/with_names_from c' s2/]
             e1r[/with_names_from c' s1/] e2r[/with_names_from c' s2/].
Proof.
  intros c' name e1r e2r tr s1 s2 Hin Hargs.
  pose proof fo_wf_lang as wfl.
  unfold ceq_term, Norm, norm_ceq_term. split.
  - (* well-formedness component (= SyntacticModel cterm_by) *)
    pose proof (norm_ceq_args_eq_args Hargs) as Heqa.
    eapply eq_term_subst.
    + eapply eq_term_by; exact Hin.
    + apply eq_args_implies_eq_subst; exact Heqa.
    + eapply rule_in_ctx_wf; [ exact fo_wf_lang | exact Hin | reflexivity ].
  - (* eval glue (typed): both sides of each equation rule evaluate (in the
       eval'd context, at the eval'd type) to the SAME typed value. *)
    pose proof (term_eq_rules_names Hin) as Hmem.
    dispbyT "Empty subst".
    dispbyT "suc subst".
    dispbyT "zero subst".
    dispbyT "Nat subst".
    dispbyT "El subst".
    dispbyT "U subst".
    dispbyT "snoc_wkn_hd".
    dispbyT "cmp_snoc".
    dispbyT "snoc_hd".
    dispbyT "wkn_snoc".
    dispbyT "id_emp_forget".
    dispbyT "cmp_forget".
    dispbyT "exp_subst_cmp".
    dispbyT "exp_subst_id".
    dispbyT "ty_subst_cmp".
    dispbyT "ty_subst_id".
    dispbyT "cmp_assoc".
    dispbyT "id_left".
    dispbyT "id_right".
    dispbyT "next1".
    dispbyT "next0".
    dispbyT "ltl_irr".
    finish_absurd Hmem ["Empty subst";"suc subst";"zero subst";"Nat subst";"El subst";
      "U subst";"snoc_wkn_hd";"cmp_snoc";"snoc_hd";"wkn_snoc";"id_emp_forget";
      "cmp_forget";"exp_subst_cmp";"exp_subst_id";"ty_subst_cmp";"ty_subst_id";
      "cmp_assoc";"id_left";"id_right";"next1";"next0";"ltl_irr"].
Admitted.

(* ================================================================== *)
(* Final Instance                                                      *)
(* ================================================================== *)

#[export] Instance Norm_ok : CutTModel_ok (CM := Norm) fo_lang [].
Proof.
  constructor.
  - exact Norm_cterm_var.
  - exact Norm_cterm_cong.
  - exact Norm_cterm_by.
  - exact Norm_cterm_trans.
  - exact Norm_cterm_sym.
  - exact Norm_cterm_conv.
  - exact Norm_csort_cong.
  - exact Norm_csort_by.
  - exact Norm_csort_trans.
  - exact Norm_csort_sym.
Defined.
