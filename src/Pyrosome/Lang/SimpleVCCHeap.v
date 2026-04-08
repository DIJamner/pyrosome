Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS
     SimpleUnit NatHeap SimpleVCPSHeap SimpleVCC.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

(*TODO: make this divide more sensible*)
Definition heap_id'_def : compiler :=
  match # from (unit_lang ++ heap ++ nat_exp++ nat_lang) with
  | {{s #"heap"}} => {{s#"heap"}}
  end.

Derive heap_id'
       in (elab_preserving_compiler subst_cc
                                          (heap_cps_ops (*TODO: remove via lemma*)
                                             ++ cc_lang (*TODO: remove via lemma*)
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ unit_lang
                                             ++ heap
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          heap_id'_def
                                          heap_id'
                                          (unit_lang ++ heap ++ nat_exp++ nat_lang))
       as heap_id'_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition heap_id'_entry :=
  cmp_entry (elab_compiler_implies_preserving heap_id'_preserving).
#[export] Hint Resolve heap_id'_entry : preserving_db.

(*TODO: move to value_subst? could conflict w/ cmp_forget
  not currently used
TODO: variant of one in SimpleVCC.v
*)
(*TODO: generalize? reverse for tactics?*)
Definition forget_eq_wkn'_def : lang :=
  {[l
      [:= "G" : #"env", "A" : #"ty"
         ----------------------------------------------- ("forget_eq_wkn")
         #"cmp" #"wkn" #"forget" = #"forget"
         : #"sub" (#"ext" "G" "A") #"emp"
      ]
  ]}.
Derive forget_eq_wkn'
       SuchThat (elab_lang_ext value_subst
                               forget_eq_wkn'_def
                               forget_eq_wkn')
       As forget_eq_wkn'_wf.
Proof. auto_elab. Qed.
#[local] Definition forget_eq_wkn'_entry :=
  lang_entry (elab_lang_implies_wf forget_eq_wkn'_wf).
#[export] Hint Resolve forget_eq_wkn'_entry : wf_lang_db.

Definition heap_cc_def : compiler :=
  match # from heap_cps_ops with
  | {{s #"configuration" "G"}} =>
    {{s #"configuration" (#"ext" #"emp" "G")}}
  | {{e #"config" "H" "G" "A" "e"}} =>
    {{e #"config" "H" "e"}}
  | {{e #"get" "G" "v" "e"}} =>
    {{e #"get" "v" (#"blk_subst" (#"snoc" #"forget" (#"pair" {ovar 1} #"hd")) "e")}}
  | {{e #"set" "G" "v" "v'" "e" }} =>
    {{e #"set" "v" "v'" "e" }} 
  end.

(*TODO: make proof brief*)
Derive heap_cc
       in (elab_preserving_compiler (heap_id'++subst_cc)
                                          (heap_cps_ops
                                             ++ cc_lang
                                             ++ prod_cc
                                             ++ forget_eq_wkn'
                                             ++ cps_prod_lang
                                             ++ unit_lang
                                             ++ heap
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          heap_cc_def
                                          heap_cc
                                          heap_cps_ops)
       as heap_cc_preserving.
Proof.
  auto_elab_compiler' (rule_named_in cc_bidirectional_rules) empty_inj_rules.
Qed.
#[local] Definition heap_cc_entry :=
  cmp_entry (elab_compiler_implies_preserving heap_cc_preserving).
#[export] Hint Resolve heap_cc_entry : preserving_db.
