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
  SimpleVCCHeap SimpleVFix CombinedThm.
From Pyrosome.Tools Require Import InjRuleGen.
Import Core.Notations.
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.

Definition stlc_parameterized :=
    let ps := (elab_param "D" (stlc ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps stlc.

Local Definition evp' := 
    let ps := (elab_param "D" (stlc ++exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base ++ value_subst).

Lemma stlc_parameterized_wf
  : wf_lang_ext ((exp_parameterized++val_parameterized)
                       ++ty_env_lang)
      stlc_parameterized.
Proof.
  change (exp_parameterized++val_parameterized) with evp'.
  (*TODO: phrase exp_and_val_parameterized as parameterized in definition*)
  (*TODO: need to strengthen parameterization pl w/ add'l language?
    Currently cheating.
   *)
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_by_lang_db..
    | vm_compute; exact I].
Qed.
#[local] Definition stlc_parameterized_entry :=
  lang_entry stlc_parameterized_wf.
#[export] Hint Resolve stlc_parameterized_entry : wf_lang_db.

Definition src_parameterized :=
    let ps := (elab_param "D" (let_lang ++ src_ext ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (let_lang ++ src_ext).

Local Definition evp'' := 
    let ps := (elab_param "D" (let_lang ++ src_ext ++exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_subst ++ value_subst).

(*TODO: move to Core.v*)
Lemma wf_lang_concat' (l_pre l1 l2 : lang)
  : wf_lang_ext l_pre l1 ->
    wf_lang_ext (l1++l_pre) l2 ->
    wf_lang_ext l_pre (l2 ++ l1).
Proof.
  induction 2; basic_goal_prep; basic_core_firstorder_crush.
  rewrite <- app_assoc; eauto.
Qed.

Lemma src_parameterized_wf
  : wf_lang_ext ((exp_parameterized++val_parameterized)
                       ++ty_env_lang)
      src_parameterized.
Proof.
  change (exp_parameterized++val_parameterized) with evp''.
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | try now prove_by_lang_db..
    | vm_compute; exact I].
Qed.
#[local] Definition src_parameterized_entry :=
  lang_entry src_parameterized_wf.
#[export] Hint Resolve src_parameterized_entry : wf_lang_db.





Definition ir_parameterized :=
  let ps := (elab_param "D" (ir_ext ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps ir_ext.

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

Lemma ir_parameterized_wf
  : wf_lang_ext ((block_parameterized++
                       val_parameterized)
                       ++ty_env_lang)
      ir_parameterized.
Proof.
  change (block_parameterized++val_parameterized) with bvp'.
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | try now  prove_by_lang_db..
    | vm_compute; exact I].
Qed.
#[local] Definition ir_parameterized_entry :=
  lang_entry ir_parameterized_wf.
#[export] Hint Resolve ir_parameterized_entry : wf_lang_db.

Definition exists_def : lang :=
  {[l (*l/subst TODO: psubst*)
  [:| "D" : #"ty_env", "A" : #"ty" (#"ty_ext" "D")
      -----------------------------------------------
      #"Exists" "A" : #"ty" "D"
  ];
    (*TODO:autogenerate*)
  [:= "D" : #"ty_env",
      "A" : #"ty" (#"ty_ext" "D"),
      "D'" : #"ty_env",
      "d" : #"ty_sub" "D'" "D"
      ----------------------------------------------- ("ty_subst Exists")
      #"ty_subst" "d" (#"Exists" "A")
      = #"Exists" (#"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" "d") #"ty_hd") "A")
      : #"ty" "D'"
   ];
    [:| "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" "D",
       "B" :  #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "A") "B")
       -----------------------------------------------
       #"pack_val" "A" "v" : #"val" "D" "G" (#"Exists" "B")
  ];
    [:| "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" "D",
       "B" :  #"ty" (#"ty_ext" "D"),
       "e" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "A") "B")
       -----------------------------------------------
       #"pack" "A" "e" : #"exp" "D" "G" (#"Exists" "B")
  ];
  [:| "D" : #"ty_env",
      "G" : #"env" "D",
      "B" : #"ty" (#"ty_ext" "D"),
      "e" : #"exp" "D" "G" (#"Exists" "B"),
      "C" : #"ty" "D",
      "e'" : #"exp" (#"ty_ext" "D") (#"ext" (#"env_ty_subst" #"ty_wkn" "G") "B")
               (#"ty_subst" #"ty_wkn" "C")
       -----------------------------------------------
       #"unpack" "e" "e'" : #"exp" "D" "G" "C"
  ];
  [:=  "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" "D",
       "B" :  #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "A") "B"),
      "C" : #"ty" "D",
      "e'" : #"exp" (#"ty_ext" "D") (#"ext" (#"env_ty_subst" #"ty_wkn" "G") "B")
               (#"ty_subst" #"ty_wkn" "C")
      ----------------------------------------------- ("unpack-beta")
      #"unpack" (#"ret" (#"pack_val" "A" "v")) "e'"
      = #"exp_subst" (#"snoc" #"id" "v") (#"exp_ty_subst" (#"ty_snoc" #"ty_id" "A") "e'")
      : #"exp" "D" "G" "C"
  ]
  ]}.

#[local] Definition Exists_inst_for_db := inst_for_db "Exists".
#[export] Hint Resolve Exists_inst_for_db : injective_con.

Definition exists_lang :=
  Eval vm_compute in
    (infer_lang_ext_simple_incr 10 100
       (exp_param_substs
          ++ exp_ty_subst
          ++ val_param_substs
          ++ val_ty_subst
          ++env_ty_subst
          ++ty_subst_lang
          ++exp_parameterized++val_parameterized
          ++ty_env_lang) exists_def).


Lemma exists_lang_wf : wf_lang_ext (exp_param_substs
                             ++ exp_ty_subst
                             ++ val_param_substs
                             ++ val_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
                               exists_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition exists_lang_entry :=
  lang_entry exists_lang_wf.
#[export] Hint Resolve exists_lang_entry : wf_lang_db.

Definition exists_block_def : lang :=
  {[l (*l/subst TODO: psubst*)
  [:| "D" : #"ty_env", "A" : #"ty" (#"ty_ext" "D")
      -----------------------------------------------
      #"Exists" "A" : #"ty" "D"
  ];
    [:= "D" : #"ty_env",
              "A" : #"ty" (#"ty_ext" "D"),
              "D'" : #"ty_env",
              "d" : #"ty_sub" "D'" "D"
              ----------------------------------------------- ("ty_subst Exists")
              #"ty_subst" "d" (#"Exists" "A")
               = #"Exists" (#"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" "d") #"ty_hd") "A")
               : #"ty" "D'"
          ];
    [:| "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" "D",
       "B" :  #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "A") "B")
       -----------------------------------------------
       #"pack" "A" "v" : #"val" "D" "G" (#"Exists" "B")
  ];
  [:| "D" : #"ty_env",
      "G" : #"env" "D",
      "B" : #"ty" (#"ty_ext" "D"),
      "v" : #"val" "D" "G" (#"Exists" "B"),
      "e" : #"blk" (#"ty_ext" "D") (#"ext" (#"env_ty_subst" #"ty_wkn" "G") "B")
       -----------------------------------------------
       #"unpack" "v" "e" : #"blk" "D" "G"
  ];
  [:=  "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" "D",
       "B" :  #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "A") "B"),
      "e" : #"blk" (#"ty_ext" "D") (#"ext" (#"env_ty_subst" #"ty_wkn" "G") "B")
      ----------------------------------------------- ("unpack-beta")
      #"unpack" (#"pack" "A" "v") "e"
      = #"blk_subst" (#"snoc" #"id" "v") (#"blk_ty_subst" (#"ty_snoc" #"ty_id" "A")"e")
      : #"blk" "D" "G"
  ];
  [:= "D" : #"ty_env",
      "G" : #"env" "D",
      "B" : #"ty" (#"ty_ext" "D"),
      "v" : #"val" "D" "G" (#"Exists" "B"),
      "e" : #"blk" "D" (#"ext" "G" (#"Exists" "B"))
       ----------------------------------------------- ("unpack-eta")
       #"unpack" "v" (#"blk_subst" (#"snoc" #"wkn" (#"pack" #"ty_hd" #"hd"))
                        (#"blk_ty_subst" #"ty_wkn" "e"))
       = #"blk_subst" (#"snoc" #"id" "v") "e"
       : #"blk" "D" "G"
  ];
   [:= "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" "D",
       "B" :  #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "A") "B"),
      "G'" : #"env" "D",
      "g" : #"sub" "D" "G'" "G"
       ----------------------------------------------- ("blk_subst pack")
       #"val_subst" "g" (#"pack" "A" "v")
       = #"pack" "A" (#"val_subst" "g" "v")
       : #"val" "D" "G'" (#"Exists" "B")
  ];
  [:= "D" : #"ty_env",
      "G" : #"env" "D",
      "B" : #"ty" (#"ty_ext" "D"),
      "v" : #"val" "D" "G" (#"Exists" "B"),
      "e" : #"blk" (#"ty_ext" "D") (#"ext" (#"env_ty_subst" #"ty_wkn" "G") "B"),
      "G'" : #"env" "D",
      "g" : #"sub" "D" "G'" "G"
       ----------------------------------------------- ("blk_subst unpack")
       #"blk_subst" "g" (#"unpack" "v" "e")
       = #"unpack" (#"val_subst" "g" "v")
           (#"blk_subst" { under {{e #"sub_ty_subst" #"ty_wkn" "g" }} } "e")
       : #"blk" "D" "G'"
  ]
  ]}.


Definition exists_block_lang' :=
  Eval vm_compute in
    (infer_lang_ext_simple_incr 10 100
       (block_param_substs
          ++val_param_substs
          ++ block_ty_subst
          ++env_ty_subst
          ++ty_subst_lang
          ++block_parameterized++val_parameterized
          ++ty_env_lang)
       exists_block_def).

(*TODO: too slow. Why? should replace the derive below.
Lemma exists_block_lang_wf
  : wf_lang_ext (block_param_substs
                   ++val_param_substs
                   ++ block_ty_subst
                   ++env_ty_subst
                   ++ty_subst_lang
                   ++block_parameterized++val_parameterized
                   ++ty_env_lang)
      exists_block_lang.
Proof. compute_wf_lang. Qed.
*)

Derive exists_block_lang
  in (elab_lang_ext (block_param_substs
                             ++val_param_substs
                             ++ block_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++block_parameterized++val_parameterized
                             ++ty_env_lang)
              exists_block_def exists_block_lang)
       as exists_block_lang_wf.
Proof. auto_elab. Qed.
#[local] Definition exists_block_lang_entry :=
  lang_entry (elab_lang_implies_wf exists_block_lang_wf).
#[export] Hint Resolve exists_block_lang_entry : wf_lang_db.
