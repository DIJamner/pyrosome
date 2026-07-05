From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core 
  Theory.Renaming Compilers.SemanticsPreservingDef
  Compilers.Compilers Compilers.Parameterizer Compilers.CompilerFacts
  Elab.Elab Elab.ElabCompilers
  Tools.CompilerTools Compilers.CompilerTransitivity
  Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import PolySubst
  SimpleVSubst SimpleVCPS SimpleEvalCtx Let
  SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC
  SimpleVCCHeap SimpleVFix CombinedThm PolyCompilerLangs PolyCompilersCPS.
From Pyrosome.Tools Require Import InjRuleGen.
From Pyrosome.Tools Require Import UnElab.
From Pyrosome.Compilers Require Import CompilerTransitivity.
Import Core.Notations.
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.
Local Open Scope lang_scope.

Definition tgt_parameterized :=
  let ps := (elab_param "D" (tgt_ext ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps tgt_ext.

Local Definition bvp'' :=
  let ps := (elab_param "D" (tgt_ext
                               ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (block_subst ++ value_subst).

Lemma tgt_parameterized_wf
  : wf_lang_ext ((block_parameterized++
                       val_parameterized)
                       ++ty_env_lang)
      tgt_parameterized.
Proof.
  change (block_parameterized++val_parameterized) with bvp''.
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | try now prove_by_lang_db..
    | Ltac.flagged_exact I].
Qed.
#[local] Definition tgt_parameterized_entry :=
  lang_entry tgt_parameterized_wf.
#[export] Hint Resolve tgt_parameterized_entry : wf_lang_db.

Definition cc_full :=
  (fix_cc ++ heap_cc ++ heap_id' ++ cc ++ prod_cc_compile ++ subst_cc ++ []).

Definition cc_parameterized :=
    let pir :=  (elab_param "D" (ir_ext ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
    let ptgt :=  (elab_param "D" (tgt_ext ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
    parameterize_compiler "D"
      ptgt pir cc_full.

(* TODO: duplicated from PolyCompilerLangs. Should the definition be non-local?*)
Local Definition bvp' :=
  let ps := (elab_param "D" (ir_ext
                               ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (block_subst ++ value_subst).

Lemma cc_parameterized_correct
  : preserving_compiler_ext
      (tgt_Model:=core_model ((tgt_parameterized
                                ++ (block_parameterized++
                                      val_parameterized))
                                ++ty_env_lang))
      ty_env_cmp
      cc_parameterized
      (ir_parameterized
         ++ (block_parameterized++
               val_parameterized)).
Proof.
  change (block_parameterized++val_parameterized) with bvp' at 2.
  unfold ty_env_cmp, cc_parameterized,
    ir_parameterized, bvp'.
  unfold parameterize_lang.
  rewrite <- map_app.
  match goal with
  | |- context[core_model ?l] =>
      let y := type of l in
      let x := open_constr:(_:y) in
      replace (core_model l) with (core_model x)
  end.
  1:eapply parameterize_compiler_preserving.
  all: try typeclasses eauto.
  1,2:repeat t'; try constructor.
  1: eapply use_compute_all_fresh; vm_compute; exact I.
  2:{
    unfold ir_ext; rewrite <- !app_assoc.
    replace (block_subst ++ value_subst)
    with ((block_subst ++ value_subst)++[])
      by basic_utils_crush.
    eapply full_cc_compiler_preserving.
  }
  1: prove_by_lang_db.
  1: prove_by_lang_db.
  2: reflexivity.
  1: vm_cast_no_check I.
Qed.
#[local] Definition cc_parameterized_entry :=
  cmp_entry cc_parameterized_correct.
#[export] Hint Resolve cc_parameterized_entry : preserving_db.

Definition exists_cc_def : compiler :=
  match # from exists_block_lang with
  | {{e #"Exists" "D" "A"}} =>
      {{e #"Exists" "A" }}
  | {{e #"pack" "D" "G" "A" "B" "v"}} =>
        {{e #"pack" "A" "v" }}
  | {{e #"unpack" "D" "G" "B" "v" "e'" }} =>
      {{e #"unpack" "v" (#"blk_subst" (#"snoc" #"forget" (#"pair" {ovar 1} #"hd")) "e")  }}
  end.

Definition tgt_param_substs_def :=
  Eval compute in
    let deps := (block_param_substs
                                 ++ val_param_substs
                                 ++ block_ty_subst
                                 ++ env_ty_subst
                                 ++ ty_subst_lang
                                 ++ block_parameterized
                                 ++ val_parameterized
                                 ++ ty_env_lang) in
    eqn_rules type_subst_mode deps
    (hide_lang_implicits (tgt_parameterized++deps) tgt_parameterized).

Derive tgt_param_substs
  in (elab_lang_ext (tgt_parameterized
                             ++block_param_substs
                             ++val_param_substs
                             ++block_ty_subst
                             ++env_ty_subst
                             ++block_parameterized
                             ++ty_subst_lang
                             ++val_parameterized
                             ++ty_env_lang)
              tgt_param_substs_def
              tgt_param_substs)
  as tgt_param_substs_wf.
Proof. auto_elab. Qed.
#[local] Definition tgt_param_substs_entry :=
  lang_entry (elab_lang_implies_wf tgt_param_substs_wf).
#[export] Hint Resolve tgt_param_substs_entry : wf_lang_db.

#[local] Definition cmp'' := Eval compute in cc_parameterized.

Definition block_ty_subst_cc_def : compiler :=
  match # from (block_param_substs
                  ++val_param_substs ++ block_ty_subst
                  ++env_ty_subst) with
  | {{e #"env_ty_subst" "D" "D'" "g" "G"}} =>
      {{e #"ty_subst" "g" "G"}}
  | {{e #"val_ty_subst" "D" "D'" "g" "G" "A" "v"}} =>
      {{e #"val_ty_subst" "g" "v"}}
  | {{e #"sub_ty_subst" "D" "D'" "d" "G" "G'" "g"}} =>
      {{e #"val_ty_subst" "d" "g"}}
  | {{e #"blk_ty_subst" "D" "D'" "g" "G" "e"}} =>
      {{e #"blk_ty_subst" "g" "e"}}
  end.

Derive block_ty_subst_cc
  in (elab_preserving_compiler
              (id_compiler (ty_subst_lang)
                 ++ cc_parameterized++ty_env_cmp)
              (tgt_param_substs
                 ++ tgt_parameterized (*TODO: only include conts*)
                 ++ block_param_substs
                 ++ val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ty_subst_lang
                 ++block_parameterized++val_parameterized
                 ++ty_env_lang)
              block_ty_subst_cc_def
              block_ty_subst_cc
              (block_param_substs ++ val_param_substs
                 ++ block_ty_subst++env_ty_subst))
  as block_ty_subst_cc_preserving.
Proof. Automation.auto_elab_compiler. Qed.
#[local] Definition block_ty_subst_cc_entry :=
  cmp_entry (elab_compiler_implies_preserving block_ty_subst_cc_preserving).
#[export] Hint Resolve block_ty_subst_cc_entry : preserving_db.

Derive exists_cc
  in (elab_preserving_compiler
              (block_ty_subst_cc ++id_compiler (ty_subst_lang)
                 ++ cc_parameterized++ty_env_cmp)
              (exists_block_lang
                 
                 ++ tgt_param_substs
                 ++ tgt_parameterized
                 
                 ++ block_param_substs
                 ++ val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ty_subst_lang
                 ++block_parameterized++val_parameterized
                 ++ty_env_lang)
              exists_cc_def
              exists_cc
              exists_block_lang)
  as exists_cc_preserving.
Proof.
  ElabCompilers.auto_elab_compiler.
   {
     compute_eq_compilation.
     reduce.
     hide_implicits.
     intermediate_term constr:({{e #"blk_subst" (#"snoc" #"id" "v")
                                   (#"blk_subst" (#"snoc" #"forget" (#"pair" {ovar 1} #"hd")) "e") }}).
     { repeat Matches.t. }
     2: Automation.by_reduction; Matches.t'.
     hide_implicits.
     eapply eq_term_trans; cycle 1.
     { eredex_steps_with exists_block_lang "unpack-eta". }
     compute_eq_compilation.
     Matches.by_reduction.
   }
  {
    compute_eq_compilation.
    reduce.
    hide_implicits.
    term_cong;
      compute_eq_compilation.
    all: try term_refl.
    compute_eq_compilation.
    hide_implicits.
    term_cong.
    1: left.
    all:compute_eq_compilation.
    1: sort_cong.
    all: try term_refl.
    all:compute_eq_compilation.
    1:by_reduction; t'.
    hide_implicits.
    term_cong.
    all:compute_eq_compilation.
    all: try term_refl.
    all:compute_eq_compilation.
    hide_implicits.
    term_cong.
    all:compute_eq_compilation.
    all: try term_refl.
    all:compute_eq_compilation.
    reduce.
    hide_implicits.
    term_cong.
    all:compute_eq_compilation.
    all: try term_refl.
    all:compute_eq_compilation.
    hide_implicits.
    (*Time 1:Automation.by_reduction; Matches.t'. 8min+ *)
    (* TODO: This is a hard one to make work.*)
    intermediate_term constr:({{e #"cmp" #"wkn" (#"snoc" #"forget" #"hd")}}).
    { repeat Matches.t. }
    all: Automation.by_reduction; Matches.t'.
  }
  Unshelve.
  all:repeat Matches.t'.
Qed.
#[local] Definition exists_cc_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving exists_cc_preserving).
#[export] Hint Resolve exists_cc_cmp_entry : preserving_db.


  Local Notation preserving_compiler_ext' tgt cmp_pre cmp src :=
    (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).
  
    Lemma id_cmp_app (l l_pre : lang)
      : id_compiler l ++ id_compiler l_pre = id_compiler (l ++ l_pre).
    Proof.
      unfold id_compiler.
      rewrite flat_map_app.
      auto.
    Qed.
    
Lemma id_compiler_preserving'  (l_pre l l' : lang)
  : wf_lang l_pre ->
    wf_lang_ext l_pre l -> incl l l' ->
    preserving_compiler_ext' (l'++l_pre) (id_compiler l_pre) (id_compiler l) l.
Proof.
  intro wfl_pre.
    induction l;
      basic_goal_prep;
      basic_core_crush.
    destruct r;
      basic_goal_prep;
      constructor;
      basic_utils_crush.
    all: try use_rule_in_wf.
    all: rewrite ?id_cmp_app.
    all: rewrite id_compiler_identity_ctx; 
      basic_core_crush.
    { eapply wf_sort_by; basic_core_crush.
      eapply id_args_wf; basic_utils_crush.
      typeclasses eauto.
    }
    all: try typeclasses eauto.
    {
      replace (compile_sort (id_compiler (l ++ l_pre)) s0)
        with s0[/with_names_from n (map var (map fst n))/].
      { eapply wf_term_by; basic_core_crush.
      eapply id_args_wf; basic_utils_crush.
      typeclasses eauto.
      }
      {
        etransitivity.
        { apply sort_subst_id; eauto.
          typeclasses eauto.
        }
        {
          symmetry.
          eapply id_compiler_identity; eauto.
          1:typeclasses eauto.
          basic_core_crush.
        }
      }
    }
    {
      assert (wf_lang (l ++ l_pre)) as H' by basic_core_crush.
      erewrite !(proj1 (id_compiler_identity H')); eauto.
      eapply eq_sort_by; eauto.
      basic_utils_crush.
    }
    {
      assert (wf_lang (l ++ l_pre)) as H' by basic_core_crush.
      erewrite !(proj1 (id_compiler_identity H')); eauto.
      erewrite !(proj1 (proj2 (id_compiler_identity H'))); eauto.
      eapply eq_term_by; eauto.
      basic_utils_crush.
    }
  Qed.

  Lemma id_compiler_preserving (l l_pre : lang)
    : wf_lang l_pre ->
      wf_lang_ext l_pre l ->
      preserving_compiler_ext' (l++l_pre) (id_compiler l_pre) (id_compiler l) l.
  Proof.
    intros; apply id_compiler_preserving'; basic_utils_crush.
  Qed.

  
  Definition hide_cmp_implicits (l:lang) : compiler -> compiler :=
    NamedList.named_map (hide_ccase_implicits l).
  
  #[local] Definition id_cps_def :=
        Eval compute in
        hide_cmp_implicits
          (((val_param_substs
                      ++ val_ty_subst
                      ++env_ty_subst
                      ++ty_subst_lang)++ val_parameterized ++ ty_env_lang))
          (id_compiler (val_param_substs
                      ++ val_ty_subst
                      ++env_ty_subst
                      ++ty_subst_lang)).
  
Lemma ty_subst_lang_id_ext
  : preserving_compiler_ext
      (cps_parameterized ++ ty_env_cmp)
      (tgt_Model := core_model ((val_param_substs
                      ++ val_ty_subst
                      ++env_ty_subst
                      ++ty_subst_lang)
                                  ++ ir_parameterized ++ block_parameterized
                                  ++ val_parameterized ++ ty_env_lang))
      (id_compiler (val_param_substs
                      ++ val_ty_subst
                      ++env_ty_subst
                      ++ty_subst_lang))
         (val_param_substs
            ++ val_ty_subst
            ++env_ty_subst
            ++ty_subst_lang).
Proof.
   compute_preserving_compiler
         (src_parameterized ++ exp_parameterized
            ++ val_parameterized ++ ty_env_lang).
Qed.
#[local] Definition ty_subst_lang_id_ext_entry := cmp_entry ty_subst_lang_id_ext.
#[export] Hint Resolve ty_subst_lang_id_ext_entry : preserving_db.

#[local] Definition id_cc_def :=
        Eval compute in
        hide_cmp_implicits
          (ty_subst_lang++ val_parameterized ++ ty_env_lang)
          (id_compiler ty_subst_lang).

Lemma ty_subst_lang_id_ext_cc
  : preserving_compiler_ext
      (cc_parameterized ++ty_env_cmp)
      (tgt_Model := core_model ((val_param_substs
                      ++ val_ty_subst
                      ++env_ty_subst
                      ++ty_subst_lang)
                                  ++ tgt_parameterized ++ block_parameterized
                                  ++ val_parameterized ++ ty_env_lang))
      (id_compiler ty_subst_lang)
      (ty_subst_lang).
Proof.
  compute_preserving_compiler (ir_parameterized ++ block_parameterized
                                 ++ val_parameterized ++ ty_env_lang).
Qed.
#[local] Definition ty_subst_lang_id_ext_cc_entry :=
  cmp_entry ty_subst_lang_id_ext_cc.
#[export] Hint Resolve ty_subst_lang_id_ext_cc_entry : preserving_db.

Lemma ir_param_substs_preserving
  : preserving_compiler_ext
     (block_ty_subst_cc ++ id_compiler ty_subst_lang ++ cc_parameterized ++ ty_env_cmp)
     (tgt_Model := core_model (tgt_param_substs ++
        tgt_parameterized ++
        block_param_substs ++
        val_param_substs ++
        block_ty_subst ++
        env_ty_subst ++ ty_subst_lang ++ block_parameterized
        ++ val_parameterized ++ ty_env_lang))
     []
     ir_param_substs.
Proof.
  compute_preserving_compiler
    ((block_param_substs ++ val_param_substs ++ block_ty_subst ++ env_ty_subst)
       ++ ty_subst_lang ++
       (ir_parameterized ++ block_parameterized ++ val_parameterized)
       ++ ty_env_lang).
Qed.
#[local] Definition ir_param_substs_cmp_entry :=
  cmp_entry ir_param_substs_preserving.
#[export] Hint Resolve ir_param_substs_cmp_entry : preserving_db.

Definition poly_tgt :=
  (exists_block_lang ++
     tgt_param_substs ++
     tgt_parameterized ++
     block_param_substs ++
     val_param_substs ++
     block_ty_subst ++
     env_ty_subst ++ ty_subst_lang ++ block_parameterized ++ val_parameterized ++ ty_env_lang).

Definition poly_ir :=
  (exists_block_lang ++
     ir_param_substs ++
     block_param_substs ++
     val_param_substs ++
     block_ty_subst ++
     env_ty_subst ++ ty_subst_lang ++ 
     (ir_parameterized ++ block_parameterized ++ val_parameterized) ++ ty_env_lang).

Definition poly_src :=
  exists_lang
    ++ poly
    ++ (exp_param_substs ++ exp_ty_subst)
    ++ (val_param_substs ++ val_ty_subst ++ env_ty_subst ++ ty_subst_lang)
    ++ (src_parameterized ++ exp_parameterized ++ val_parameterized)
    ++ ty_env_lang.

Definition pcps :=
  exists_cps
    ++ poly_cps
    ++ (exp_ty_subst_cps
          ++ id_compiler (val_param_substs ++ val_ty_subst ++ env_ty_subst ++ ty_subst_lang)
          ++ cps_parameterized ++ ty_env_cmp).

Definition pcc :=
  exists_cc
    ++ []
    ++ block_ty_subst_cc
    ++ id_compiler ty_subst_lang ++ cc_parameterized ++ ty_env_cmp.


Theorem combined_poly
  :  preserving_compiler_ext
      (tgt_Model := core_model poly_tgt)
      []
      (compile_cmp pcc pcps)
      poly_src.
Proof.
  apply preservation_transitivity
    with (ir:=poly_ir).
  all: try typeclasses eauto; try reflexivity.
  1-3:[>prove_by_lang_db..].
  1-2:[>prove_by_cmp_db..].
Qed.
