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
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Determinism Model ApplyLemmas SortInj.
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
(* cterm_conv : eq_term_conv + glue carries over (head is preserved)   *)
(* ================================================================== *)

Lemma Norm_cterm_conv : forall t1 t2 e1 e2,
    ceq_sort (CutTModel := Norm) t1 t2 ->
    ceq_term (CutTModel := Norm) t1 e1 e2 ->
    ceq_term (CutTModel := Norm) t2 e1 e2.
Proof.
  intros [n1 a1] [n2 a2] e1 e2 Hs Ht.
  unfold ceq_sort, Norm, norm_ceq_sort in Hs.
  destruct Hs as [Heqs Gs]. unfold glue_sort in Gs. destruct Gs as [Hn Hlen].
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct Ht as [Heqt Gt].
  split.
  - exact (eq_term_conv Heqt Heqs).
  - (* GLUE (typed eval): the glue now depends on the sort's context/type
       args; transferring it across eq_sort-related sorts needs eval/eq_term
       coherence.  Admitted pending the typed-glue gluing soundness. *)
    admit.
Admitted.

(* ================================================================== *)
(* sort ops : eq_sort_* for the eq component, head+arity for the glue  *)
(* ================================================================== *)

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
  - unfold glue_sort. split.
    + apply (@eqb_refl_true string _ string_Eqb_ok).
    + clear Hin. induction Hargs; cbn; congruence.
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
  intros [n1 a1] [n12 a12] [n2 a2] H1 H2.
  unfold ceq_sort, Norm, norm_ceq_sort in *.
  destruct H1 as [Heq1 Gs1], H2 as [Heq2 Gs2].
  unfold glue_sort in *. destruct Gs1 as [Hn1 HL1], Gs2 as [Hn2 HL2].
  split.
  - exact (eq_sort_trans Heq1 Heq2).
  - split.
    + pose proof (proj1 (eqb_prop_iff _ n1 n12) ltac:(rewrite Hn1; exact I)).
      pose proof (proj1 (eqb_prop_iff _ n12 n2) ltac:(rewrite Hn2; exact I)). subst.
      apply (@eqb_refl_true string _ string_Eqb_ok).
    + congruence.
Qed.

Lemma Norm_csort_sym : forall t1 t2,
    ceq_sort (CutTModel := Norm) t1 t2 -> ceq_sort (CutTModel := Norm) t2 t1.
Proof.
  intros [n1 a1] [n2 a2] H. unfold ceq_sort, Norm, norm_ceq_sort in *.
  destruct H as [Heq Gs]. unfold glue_sort in *. destruct Gs as [Hn HL].
  split.
  - exact (eq_sort_sym Heq).
  - split.
    + pose proof (proj1 (eqb_prop_iff _ n1 n2) ltac:(rewrite Hn; exact I)); subst.
      apply (@eqb_refl_true string _ string_Eqb_ok).
    + auto.
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

(* env-free congruence solver, operating on the GLUE goal/hyps (the per-arg
   [ceq_term] hyps are now [eq_term * glue] pairs; split them, then build the
   value with the eval constructors). *)
Ltac solve_cong :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with
         | H : @sigT _ _ |- _ => destruct H as [? [? ?]]
         | H : @prod _ _ |- _ => destruct H
         end;
  first
    [ exact tt
    | solve [ eexists; split; econstructor; solve [eassumption | eauto] ]
    | solve [ eexists; split;
              [ econstructor; solve [eassumption | eauto]
              | repeat match goal with H : @eq (@term string) _ _ |- _ => rewrite H end;
                econstructor; solve [eassumption | eauto] ] ]
    | (* id/wkn: their value depends on [ctx_len], equal by eval_env_length *)
      solve [ match goal with Ha : eval_env ?G1 ?gv, Hb : eval_env ?G2 ?gv |- _ =>
                let Hlen := fresh in
                pose proof (eq_trans (eq_sym (eval_env_length Ha)) (eval_env_length Hb)) as Hlen;
                eexists; split; [ econstructor | rewrite Hlen; econstructor ] end ]
    | solve [ repeat match goal with H : @eq (@term string) _ _ |- _ => rewrite H; clear H end;
              reflexivity ]
    | solve [ congruence ] ].

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
(* cterm_cong                                                          *)
(* ================================================================== *)

(* The well-formedness (eq_term) component is uniform (term_con_congruence);
   the eval GLUE is PROVEN for 24/26 formers, all but the eliminators El and
   Emptyrec, whose congruence needs the scrutinee/code's semantic SHAPE (Tier C,
   to be discharged from the now-available well-formedness). *)
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
  - (* eval glue (typed): build the TYPED eval witnesses for con name s1/s2 at
       the eval'd context/type from the per-arg glue.  Admitted pending the
       typed-glue gluing soundness (the old env-free [disp] tactics no longer
       apply since the glue now threads contexts/types). *)
    admit.
Admitted.

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
       eval'd context, at the eval'd type) to the SAME typed value.  Admitted
       pending the typed-glue gluing soundness (old env-free [dispby] tactics
       no longer apply). *)
    admit.
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
