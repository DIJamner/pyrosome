Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Theory.Renaming
  Tools.Matches Compilers.Parameterizer Compilers.Compilers.
From Pyrosome.Lang Require Import PolySubst
  SimpleVSubst SimpleVCPS SimpleEvalCtx
  SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC
  SimpleVCCHeap SimpleVFix PolyCompilers.
Import Core.Notations.

Require Coq.derive.Derive.



Definition tgt_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (tgt_ext ++ block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps tgt_ext.


Definition tgt_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (tgt_parameterized++
                       block_and_val_parameterized
                       ++ty_subst_lang)
                    tgt_parameterized.


Lemma tgt_parameterized_wf
  : elab_lang_ext (block_and_val_parameterized
                       ++ty_subst_lang)
      tgt_parameterized_def
      tgt_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve tgt_parameterized_wf : elab_pfs.


Compute (map fst ir_parameterized).
Compute (map fst (heap_cc ++fix_cc++cc++ heap_id'++prod_cc_compile++subst_cc++[])).
(*= ["if zero"; "if nonzero"; "blk_subst if0"; "if0"; "eval set"; "eval get"; "config"; "configuration";
       "blk_subst get"; "get"; "blk_subst set"; "set"; "fix_beta"; "val_subst fix"; "fix"; "cont_eta"; "jmp_beta";
       "blk_subst jmp"; "jmp"; "val_subst cont"; "cont"; "neg"; "prod_eta"; "eval pm_pair"; "blk_subst pm_pair";
       "pm_pair"; "val_subst pair"; "pair"; "prod"; "val_subst tt"; "tt"; "unit"; "lookup_empty"; "lookup_miss";
       "lookup_found"; "lookup"; "heap_comm"; "heap_shadow"; "hset"; "hempty"; "heap"; "val_subst nv"; "nv";
       "nat"; "neq_1+"; "neq_0_r"; "neq_0_l"; "neq"; "1+"; "0"; "natural"]
     : list string*)

(*TODO: get the order right*)
Definition cc_full := (heap_cc++fix_cc++cc++ prod_cc_compile++heap_id'++subst_cc++[]).
(* Compute (length cc_full). 42 *)


Definition cc_parameterized :=
  Eval compute in
     let pir :=  (elab_param "D" (ir_ext ++ block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
     
     let ptgt :=  (elab_param "D" (tgt_ext ++ block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
    parameterize_compiler "D"
      (*firstn 41 skips the rule for ty*)
      ptgt pir (firstn 41 cc_full).


Definition cc_parameterized_def :=
  Eval compute in hide_compiler
                    (tgt_parameterized++
                       block_and_val_parameterized
                       ++ty_subst_lang)
                    cc_parameterized.


From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.ElabCompilers.
Lemma cc_parameterized_correct
  : elab_preserving_compiler ty_subst_cmp
      (tgt_parameterized
         ++ block_and_val_parameterized
         ++ty_subst_lang)
      cc_parameterized_def
      cc_parameterized
      
      (ir_parameterized
         ++ block_and_val_parameterized).
Proof.
  auto_elab_compiler.
  {
    cleanup_elab_after
      (reduce; eredex_steps_with (tgt_parameterized) "unit eta").
  }
  { cleanup_elab_after eredex_steps_with heap "heap_comm". }
  { cleanup_elab_after eredex_steps_with heap "lookup_miss". }
  { cleanup_elab_after eredex_steps_with heap "lookup_empty". }
  { reduce.
    repeat (term_cong; unfold Model.eq_term; try term_refl; compute_eq_compilation). TODO: false goal
    eapply eq_term_trans; cycle 1.
    {
      term_cong; unfold Model.eq_term.
      - term_refl.
      - term_refl.
      - compute_eq_compilation.        
        estep_under forget_eq_wkn' "forget_eq_wkn".
      - term_refl.
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
          - term_refl.
        }
        compute_eq_compilation.
        eapply eq_term_trans; cycle 1.
        {
          term_cong; unfold Model.eq_term.
          - term_refl.
          - term_refl.
          - eapply eq_term_sym.
            eredex_steps_with value_subst "id_right".
          - term_refl.
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
  - cleanup_elab_after
      (reduce;
       eapply eq_term_trans;  
       [eapply eq_term_sym;
        eredex_steps_with tgt_parameterized "clo_eta"|];
       by_reduction).
  cleanup_elab_after
  (reduce;
   eapply eq_term_trans;  
   [eapply eq_term_sym;
   eredex_steps_with cc_lang "clo_eta"|];
   by_reduction).
    
    reduce.
    
  Optimize Heap.
  cleanup_elab_after setup_elab_compiler.
    match goal with
  | |- elab_preserving_compiler _ ?tgt ?cmp ?ecmp ?src =>
        rewrite (as_nth_tail cmp); rewrite (as_nth_tail ecmp); rewrite (as_nth_tail src);
         assert (wf_lang tgt) by prove_from_known_elabs
    end.
    repeat elab_compiler_cons; try reflexivity.
    {
      cbv.
      TODO: tt before fix
    (elab_compiler_cons; try reflexivity; [ break_preserving | .. ]) ||
    (compute; apply elab_preserving_compiler_nil)
    break_preserving.
  Compute (map fst cc_parameterized_def).
  
  Compute(map fst (ir_parameterized
         ++ block_and_val_parameterized
         ++ty_subst_lang)).
  ["fix"; "if0"; "config"; "configuration"; "get"; "set"; "tt"; "unit"; "lookup"; "hset"; "hempty"; "heap";
       "nv"; "nat"; "neq_1+"; "neq_0_r"; "neq_0_l"; "neq"; "1+"; "0"; "natural"; "jmp"; "cont"; "neg"; "pm_pair";
       "pair"; "prod"; "blk_subst"; "blk"; "hd"; "wkn"; "snoc"; "ext"; "forget"; "emp"; "val_subst"; "val"; "cmp";
       "id"; "sub"; "env"]
  
  cleanup_elab_after setup_elab_compiler.
  repeat Matches.t; cleanup_elab_after try (solve [ by_reduction ])

  auto_elab_compiler.
    Optimize Heap.

  - cleanup_elab_after eredex_steps_with ir_parameterized "heap_comm".
  - cleanup_elab_after eredex_steps_with ir_parameterized "lookup_miss".
  - cleanup_elab_after eredex_steps_with ir_parameterized "lookup_empty".
  - cleanup_elab_after
    (reduce;
    eapply eq_term_trans;
    [eredex_steps_with ir_parameterized "eval get"|];
    by_reduction).
  - cleanup_elab_after
    (reduce;
     eapply eq_term_trans;
     [eredex_steps_with ir_parameterized "eval get"|];
     by_reduction).
Qed.
#[export] Hint Resolve cps_parameterized_correct : elab_pfs.


(* Total obligations (pre-polymorphism) *)
Compute (length (src_parameterized
                   ++exp_and_val_parameterized)).
Compute (length ((fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                      ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[]))).
(*total: 80,79 | Non-automatic: 5 (CPS) + 4*)

Lemma full_cc_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (fix_cc_lang ++
     heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                      ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                      forget_eq_wkn'++
                                      cps_prod_lang ++ block_subst ++ value_subst))
      []
                        (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                        (fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                            ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[]).
Proof. build_compiler. Qed.



(*
Definition rule_to_param_spec (x : string) r :=
  match r with
  | sort_rule c args 
  | term_rule c args _ =>
      (idx_of x (map fst c, inb x args)
  | sort_eq_rule c _ _
  | term_eq_rule c _ _ _ => (idx_of c, false)
  end. *)

(*
src = src_parameterized
         ++exp_and_val_parameterized*)

Definition cps_parameterized :=
  Eval compute in
    (*TODO: elab_param seems to do the right thing, why is
      parameterize_compiler doing the wrong thing with it?
     *)
    let ps := (elab_param "D" (src_ext ++ exp_ret ++ exp_subst_base
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
    let pir :=  (elab_param "D" (ir_ext ++ block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
    parameterize_compiler "D"
      (*firstn 44 skips the rule for ty*)
    pir ps (firstn 44 cps_full).


Lemma cc_parameterized_correct
  : elab_preserving_compiler ty_subst_cmp
      (ir_parameterized
         ++ block_and_val_parameterized
         ++ty_subst_lang)
      cc_parameterized_def
      cc_parameterized
      
      (src_parameterized
         ++exp_and_val_parameterized).
Proof. auto_elab_compiler.
  - cleanup_elab_after eredex_steps_with ir_parameterized "heap_comm".
  - cleanup_elab_after eredex_steps_with ir_parameterized "lookup_miss".
  - cleanup_elab_after eredex_steps_with ir_parameterized "lookup_empty".
  - cleanup_elab_after
    (reduce;
    eapply eq_term_trans;
    [eredex_steps_with ir_parameterized "eval get"|];
    by_reduction).
  - cleanup_elab_after
    (reduce;
     eapply eq_term_trans;
     [eredex_steps_with ir_parameterized "eval get"|];
     by_reduction).
Qed.
#[export] Hint Resolve cc_parameterized_correct : elab_pfs.



Definition tgt_ext :=
  fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang (* ++ block_subst ++ value_subst*).
