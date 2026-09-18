(* Stage G'': preservation of the value-restricted polymorphic source.

   [PolyBoundaries.v] proves that [poly_multilang_compiler] preserves
   [boundaries_parameterized] (13 equations) into [target_multilanguage].
   This file lifts that theorem to the polymorphic target
   [poly_target_multilanguage] and extends it along the four remaining
   equations of the polymorphic source [poly_source_boundaries]:

   - ["exp_ty_subst dtt"], ["exp_ty_subst ttd"]  (of [boundaries_ty_subst]),
   - ["dtt forall"], ["ttd forall"]              (of [poly_boundaries]).

   The compiler itself is UNCHANGED: the new source rules are all equations,
   so they add no compiler case.

   Two proof techniques are used, and the split is forced by the shapes of
   the terms involved.

   - The [#"All"] case of the boundary recursor (["typerec All"]) is the one
     rule that is not usable by Theory/RigidRewrite.v: its LHS is a
     [#"typerec"] whose stated sort is not the root-fitting one, so it fails
     [rewrite_rule_ok].  Its single application is therefore done with the
     e-graph, under a rule filter that admits ONLY that rule; the e-graph
     then has one rewrite to find and terminates quickly.  (With the whole
     rule set the same goal exhausts 7GB: ["typerec All"] and ["bAll def"]
     both grow the term, and the forward-only reducer restarts from the
     smallest extracted representative each round.)

   - Everything else is discharged by RigidRewrite.v's reflective bottom-up
     rewriter, which is sound by construction ([rewrite_n_sound]).  Both
     sides are normalized by the same three passes and the results are
     compared by [vm_compute].  The middle pass is the crucial one: it folds
     every boundary [#"typerec"] into the compact constant [#"btrec"]
     (["typerec to btrec"]), which keeps the [#"bfunc"]-laden recursor from
     being traversed by the reduction pass at all.                         *)

Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac.

(* imports for compilers *)
From Pyrosome Require Import Compilers.Compilers Compilers.CompilerFacts
  Elab.ElabCompilers.
Import CompilerDefs.Notations.

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
From Pyrosome.Theory Require Import PatternRigidity RigidRewrite.
Import Core.Notations.

From Stdlib Require derive.Derive.

From Pyrosome.Lang Require Import SimpleVSTLC UTLC BoolType SimpleVProd.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers.
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Import PolySource PolyTrecTerms.

Local Notation compiler := (compiler string).
Local Notation preserving_compiler_ext tgt cmp_pre cmp src :=
  (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

(* ------------------------------------------------------------------ *)
(* Step 1: lift the 13 equations and the two term cases of
   [poly_multilang_compiler_preserving] from [target_multilanguage] to
   [poly_target_multilanguage].  [target_multilanguage] is a syntactic
   suffix of the latter, so [preserving_compiler_embed] applies and none of
   those proofs is re-run.                                                *)
Lemma poly_multilang_compiler_preserving_ptml
  : preserving_compiler_ext poly_target_multilanguage
      polymorphic_interoperating_langs_compiler poly_multilang_compiler
      boundaries_parameterized.
Proof.
  eapply preserving_compiler_embed.
  1: apply poly_multilang_compiler_preserving.
  compute_incl.
Qed.

(* ------------------------------------------------------------------ *)
(* The compiled form of an equation of [poly_source_boundaries], with the
   same [PCMP] used in PolyBoundaries.v.                                  *)
Definition psrule (n:string) :=
  named_list_lookup (Rule.sort_rule [] []) poly_source_boundaries n.
Definition qgctx n :=
  match psrule n with Rule.term_eq_rule c _ _ _ => compile_ctx PCMP c | _ => [] end.
Definition qgsrt n :=
  match psrule n with Rule.term_eq_rule _ _ _ t => compile_sort PCMP t | _ => default end.
Definition qglhs n :=
  match psrule n with Rule.term_eq_rule _ e _ _ => compile PCMP e | _ => default end.
Definition qgrhs n :=
  match psrule n with Rule.term_eq_rule _ _ e _ => compile PCMP e | _ => default end.

Definition qc_ets_dtt := Eval vm_compute in qgctx "exp_ty_subst dtt".
Definition qs_ets_dtt := Eval vm_compute in qgsrt "exp_ty_subst dtt".
Definition ql_ets_dtt := Eval vm_compute in qglhs "exp_ty_subst dtt".
Definition qr_ets_dtt := Eval vm_compute in qgrhs "exp_ty_subst dtt".

Definition qc_ets_ttd := Eval vm_compute in qgctx "exp_ty_subst ttd".
Definition qs_ets_ttd := Eval vm_compute in qgsrt "exp_ty_subst ttd".
Definition ql_ets_ttd := Eval vm_compute in qglhs "exp_ty_subst ttd".
Definition qr_ets_ttd := Eval vm_compute in qgrhs "exp_ty_subst ttd".

Definition qc_dtt_forall := Eval vm_compute in qgctx "dtt forall".
Definition qs_dtt_forall := Eval vm_compute in qgsrt "dtt forall".
Definition ql_dtt_forall := Eval vm_compute in qglhs "dtt forall".
Definition qr_dtt_forall := Eval vm_compute in qgrhs "dtt forall".

Definition qc_ttd_forall := Eval vm_compute in qgctx "ttd forall".
Definition qs_ttd_forall := Eval vm_compute in qgsrt "ttd forall".
Definition ql_ttd_forall := Eval vm_compute in qglhs "ttd forall".
Definition qr_ttd_forall := Eval vm_compute in qgrhs "ttd forall".

(* ------------------------------------------------------------------ *)
(* The reflective rewriter, instantiated at the polymorphic target.       *)

Definition RW ns f e := RigidRewrite.rewrite_n (V:=string) poly_target_multilanguage ns f e.

Definition ball_names : list string := ["bAll def"].
Definition fold_names : list string := ["typerec to btrec"].

(* Every rule of the target that RigidRewrite accepts, minus the ones that
   grow a term or undo the [#"btrec"] folding.  The three [#"typerec"] case
   rules are dropped along with them: after folding there is no boundary
   [#"typerec"] left for them to fire on, and keeping them would unfold the
   recursor again. *)
Definition red_excluded : list string :=
  ["typerec to btrec"; "btrec def"; "bAll def"; "bfunc def"; "bbool def";
   "bstar def"; "typerec func"; "typerec bool"; "typerec star";
   "prod_eta"; "ret_pair"; "Lam-eta"; "typerec All"].

Definition red_names : list string := Eval vm_compute in
  filter (fun n => andb (RigidRewrite.rewrite_rule_ok (V:=string) poly_target_multilanguage n)
                        (negb (existsb (String.eqb n) red_excluded)))
    (map fst poly_target_multilanguage).

Definition Norm e := RW red_names 20 (RW fold_names 50 (RW ball_names 1 e)).

Lemma ball_names_ok
  : forallb (RigidRewrite.rewrite_rule_ok (V:=string) poly_target_multilanguage)
      ball_names = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fold_names_ok
  : forallb (RigidRewrite.rewrite_rule_ok (V:=string) poly_target_multilanguage)
      fold_names = true.
Proof. vm_compute. reflexivity. Qed.

Lemma red_names_ok
  : forallb (RigidRewrite.rewrite_rule_ok (V:=string) poly_target_multilanguage)
      red_names = true.
Proof. vm_compute. reflexivity. Qed.

Lemma RW_sound ns f c t e
  : forallb (RigidRewrite.rewrite_rule_ok (V:=string) poly_target_multilanguage) ns = true ->
    wf_ctx (Model:=core_model poly_target_multilanguage) c ->
    wf_term poly_target_multilanguage c e t ->
    eq_term poly_target_multilanguage c t e (RW ns f e).
Proof.
  intros; eapply RigidRewrite.rewrite_n_sound; try typeclasses eauto;
    eauto using poly_target_multilanguage_wf.
Qed.

Lemma RW_wf ns f c t e
  : forallb (RigidRewrite.rewrite_rule_ok (V:=string) poly_target_multilanguage) ns = true ->
    wf_ctx (Model:=core_model poly_target_multilanguage) c ->
    wf_term poly_target_multilanguage c e t ->
    wf_term poly_target_multilanguage c (RW ns f e) t.
Proof.
  intros; eapply RigidRewrite.rewrite_n_wf; try typeclasses eauto;
    eauto using poly_target_multilanguage_wf.
Qed.

Lemma Norm_sound c t e
  : wf_ctx (Model:=core_model poly_target_multilanguage) c ->
    wf_term poly_target_multilanguage c e t ->
    eq_term poly_target_multilanguage c t e (Norm e).
Proof.
  intros Hc He; unfold Norm.
  assert (W1 : wf_term poly_target_multilanguage c (RW ball_names 1 e) t)
    by (apply RW_wf; auto using ball_names_ok).
  assert (W2 : wf_term poly_target_multilanguage c
                 (RW fold_names 50 (RW ball_names 1 e)) t)
    by (apply RW_wf; auto using fold_names_ok).
  assert (S1 : eq_term poly_target_multilanguage c t e (RW ball_names 1 e))
    by (apply RW_sound; auto using ball_names_ok).
  assert (S2 : eq_term poly_target_multilanguage c t (RW ball_names 1 e)
                 (RW fold_names 50 (RW ball_names 1 e)))
    by (apply RW_sound; auto using fold_names_ok).
  assert (S3 : eq_term poly_target_multilanguage c t
                 (RW fold_names 50 (RW ball_names 1 e))
                 (RW red_names 20 (RW fold_names 50 (RW ball_names 1 e))))
    by (apply RW_sound; auto using red_names_ok).
  eapply eq_term_trans; [ exact S1 |].
  eapply eq_term_trans; [ exact S2 |].
  exact S3.
Qed.

(* Two terms with a common RigidRewrite normal form are equal. *)
Lemma norm_eq c t e1 e2
  : wf_ctx (Model:=core_model poly_target_multilanguage) c ->
    wf_term poly_target_multilanguage c e1 t ->
    wf_term poly_target_multilanguage c e2 t ->
    Norm e1 = Norm e2 ->
    eq_term poly_target_multilanguage c t e1 e2.
Proof.
  intros Hc H1 H2 Hn.
  eapply eq_term_trans; [ apply Norm_sound; assumption |].
  rewrite Hn.
  apply eq_term_sym; apply Norm_sound; assumption.
Qed.

Ltac close_by_norm :=
  pose proof poly_target_multilanguage_wf;
  apply norm_eq;
  [ solve_wf_ctx | compute_term_wf | compute_term_wf | vm_compute; reflexivity ].

(* ------------------------------------------------------------------ *)
(* The two [boundaries_ty_subst] equations.                              *)

Lemma qeq_ets_dtt
  : eq_term poly_target_multilanguage qc_ets_dtt qs_ets_dtt ql_ets_dtt qr_ets_dtt.
Proof.
  unfold qc_ets_dtt, qs_ets_dtt, ql_ets_dtt, qr_ets_dtt. close_by_norm.
Qed.

Lemma qeq_ets_ttd
  : eq_term poly_target_multilanguage qc_ets_ttd qs_ets_ttd ql_ets_ttd qr_ets_ttd.
Proof.
  unfold qc_ets_ttd, qs_ets_ttd, ql_ets_ttd, qr_ets_ttd. close_by_norm.
Qed.

(* ------------------------------------------------------------------ *)
(* The two quantifier equations, in two hops: one ["typerec All"] rewrite
   by the e-graph, then normalization.                                    *)

Definition only_names (ns : list string) : string * Rule.rule string -> bool :=
  fun p => andb (Automation.filter_rules p) (existsb (String.eqb (fst p)) ns).

Ltac by_reduction_names ns :=
  pose proof poly_target_multilanguage_wf;
  apply (Automation.egraph_sound 100 100 100 100 (only_names ns) norev
           Automation.empty_inj_rules);
  [ prove_by_lang_db | solve_wf_ctx | compute_term_wf | compute_term_wf
  | flagged_exact I ].

Definition trec_All_names : list string := ["typerec All"].

Definition QI1 := Eval vm_compute in RW trec_All_names 1 ql_dtt_forall.
Definition QJ1 := Eval vm_compute in RW trec_All_names 1 ql_ttd_forall.

Lemma qeq_dtt_forall_hop1
  : eq_term poly_target_multilanguage qc_dtt_forall qs_dtt_forall ql_dtt_forall QI1.
Proof.
  unfold qc_dtt_forall, qs_dtt_forall, ql_dtt_forall, QI1.
  by_reduction_names trec_All_names.
Qed.

Lemma qeq_dtt_forall_hop2
  : eq_term poly_target_multilanguage qc_dtt_forall qs_dtt_forall QI1 qr_dtt_forall.
Proof.
  unfold qc_dtt_forall, qs_dtt_forall, QI1, qr_dtt_forall. close_by_norm.
Qed.

Lemma qeq_dtt_forall
  : eq_term poly_target_multilanguage qc_dtt_forall qs_dtt_forall
      ql_dtt_forall qr_dtt_forall.
Proof.
  eapply eq_term_trans; [apply qeq_dtt_forall_hop1 | apply qeq_dtt_forall_hop2].
Qed.

Lemma qeq_ttd_forall_hop1
  : eq_term poly_target_multilanguage qc_ttd_forall qs_ttd_forall ql_ttd_forall QJ1.
Proof.
  unfold qc_ttd_forall, qs_ttd_forall, ql_ttd_forall, QJ1.
  by_reduction_names trec_All_names.
Qed.

Lemma qeq_ttd_forall_hop2
  : eq_term poly_target_multilanguage qc_ttd_forall qs_ttd_forall QJ1 qr_ttd_forall.
Proof.
  unfold qc_ttd_forall, qs_ttd_forall, QJ1, qr_ttd_forall. close_by_norm.
Qed.

Lemma qeq_ttd_forall
  : eq_term poly_target_multilanguage qc_ttd_forall qs_ttd_forall
      ql_ttd_forall qr_ttd_forall.
Proof.
  eapply eq_term_trans; [apply qeq_ttd_forall_hop1 | apply qeq_ttd_forall_hop2].
Qed.

(* ------------------------------------------------------------------ *)
(* Assembly.  [poly_source_boundaries] is a computed term, so force its
   four new rules to a literal first; the tail is [boundaries_parameterized],
   which the lifted theorem covers.                                        *)
Definition poly_source_new_lit := Eval vm_compute in
  (poly_boundaries ++ boundaries_ty_subst).

Lemma poly_source_boundaries_split
  : poly_source_boundaries = poly_source_new_lit ++ boundaries_parameterized.
Proof. vm_compute. reflexivity. Qed.

Theorem poly_multilang_compiler_preserving_full
  : preserving_compiler_ext poly_target_multilanguage
      polymorphic_interoperating_langs_compiler poly_multilang_compiler
      poly_source_boundaries.
Proof.
  rewrite poly_source_boundaries_split.
  unfold poly_source_new_lit; cbn [app].
  constructor; [| exact qeq_ttd_forall ].
  constructor; [| exact qeq_dtt_forall ].
  constructor; [| exact qeq_ets_dtt ].
  constructor; [| exact qeq_ets_ttd ].
  exact poly_multilang_compiler_preserving_ptml.
Qed.

(* The same theorem with the prefix folded in. *)
Theorem poly_source_multilanguage_compiler_preserving
  : preserving_compiler_ext poly_target_multilanguage []
      (poly_multilang_compiler ++ polymorphic_interoperating_langs_compiler)
      poly_source_multilanguage.
Proof.
  unfold poly_source_multilanguage.
  eapply elab_compiler_prefix_implies_elab;
    [ | apply poly_multilang_compiler_preserving_full ].
  eapply preserving_compiler_embed;
    [ apply polymorphic_interoperating_langs_compiler_preserving | compute_incl ].
Qed.
