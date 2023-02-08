Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS
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
       SuchThat (elab_preserving_compiler subst_cc
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
       As heap_id'_preserving.
Proof.
  auto_elab_compiler.
  - cleanup_elab_after eredex_steps_with heap "heap_comm".
  - cleanup_elab_after eredex_steps_with heap "lookup_miss".
  - cleanup_elab_after eredex_steps_with heap "lookup_empty".
Qed.
#[export] Hint Resolve heap_id'_preserving : elab_pfs.


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
#[export] Hint Resolve forget_eq_wkn'_wf : elab_pfs.

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
       SuchThat (elab_preserving_compiler (heap_id'++subst_cc)
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
       As heap_cc_preserving.
Proof.
  auto_elab_compiler.
  {
    reduce.
    repeat (term_cong; unfold Model.eq_term; try term_refl; compute_eq_compilation).
    eapply eq_term_trans; cycle 1.
    {
      term_cong; unfold Model.eq_term.
      - term_refl.
      - term_refl.
      - term_refl.
      - compute_eq_compilation.        
        estep_under forget_eq_wkn' "forget_eq_wkn".
      - term_refl.
    }
    compute_eq_compilation.
    eapply eq_term_trans; cycle 1.
    1:estep_under value_subst "cmp_snoc".
    compute_eq_compilation.
    eapply eq_term_trans; cycle 1.
    {
      term_cong; unfold Model.eq_term.
      - term_refl.
      - term_refl.
      - term_refl.
      - term_refl.
      - compute_eq_compilation.
        eapply eq_term_trans; cycle 1.
        {
          term_cong; unfold Model.eq_term.
          - term_refl.
          - term_refl.
          - term_refl.
          - 
            eapply eq_term_trans; cycle 1.
            {
              compute_eq_compilation.
              eredex_steps_with forget_eq_wkn' "forget_eq_wkn".
            }
            compute_eq_compilation.
            {
              term_cong; unfold Model.eq_term.
              - term_refl.
              - term_refl.
              - term_refl.
              - term_refl.
              - compute_eq_compilation.
                eredex_steps_with value_subst "id_emp_forget".
            }
          - term_refl.
        }
        compute_eq_compilation.
        eapply eq_term_trans; cycle 1.
        {
          term_cong; unfold Model.eq_term.
          - term_refl.
          - term_refl.
          - term_refl.
          - eapply eq_term_sym.
            eredex_steps_with value_subst "id_right".
          - term_refl.
        }
        compute_eq_compilation.
        by_reduction.
    }
    eapply eq_term_trans; cycle 1.
    {
      eapply eq_term_sym.
      eredex_steps_with value_subst "id_right".
    }
    compute_eq_compilation.
    term_refl.
  }
  {
    compute_eq_compilation.
    eapply eq_term_trans.
    {
      eredex_steps_with heap_cps_ops "eval get".
    }
    compute_eq_compilation.
    reduce.
    term_cong; try term_refl; unfold Model.eq_term; compute_eq_compilation.
    term_cong; try term_refl; unfold Model.eq_term; compute_eq_compilation.
    term_cong; try term_refl; unfold Model.eq_term; compute_eq_compilation.
    eapply eq_term_trans.
    {      
      eapply eq_term_sym.
      eredex_steps_with forget_eq_wkn' "forget_eq_wkn".
    }      
    compute_eq_compilation.
    eapply eq_term_trans; cycle 1.
    {
      eredex_steps_with value_subst "id_right".
    }
    compute_eq_compilation.
    term_cong; try term_refl; unfold Model.eq_term; compute_eq_compilation.
    by_reduction.
  }
Unshelve.
  all: repeat t'.
Qed.
#[export] Hint Resolve heap_cc_preserving : elab_pfs.
