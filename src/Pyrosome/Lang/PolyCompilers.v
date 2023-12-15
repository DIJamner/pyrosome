Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
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
  SimpleVCCHeap SimpleVFix.
Import Core.Notations.

Require Coq.derive.Derive.

Definition src_ext := (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang))(*++(exp_subst ++ value_subst)++[]).*).

Definition ir_ext := heap_cps_ops
         ++ fix_cps_lang
         ++ cps_lang
         ++ cps_prod_lang
         ++ unit_lang
         ++ heap
         ++ nat_exp
         ++ nat_lang (*
         ++ block_subst
         ++ value_subst.*) .

Definition tgt_ext :=
  fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang (* ++ block_subst ++ value_subst*).

Definition stlc_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (stlc ++ exp_ret ++ exp_subst_base
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps stlc.

Definition stlc_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (stlc_parameterized++
                       exp_and_val_parameterized
                       ++ty_subst_lang)
                    stlc_parameterized.

Lemma stlc_parameterized_wf
  : elab_lang_ext (exp_and_val_parameterized
                       ++ty_subst_lang)
      stlc_parameterized_def
      stlc_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_parameterized_wf : elab_pfs.


Definition src_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (src_ext ++ exp_ret ++ exp_subst_base
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps src_ext.

Definition src_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (src_parameterized++
                       exp_and_val_parameterized
                       ++ty_subst_lang)
                    src_parameterized.


Lemma src_parameterized_wf
  : elab_lang_ext (exp_and_val_parameterized
                       ++ty_subst_lang)
      src_parameterized_def
      src_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve src_parameterized_wf : elab_pfs.


(*TODO: move to a better place*)
Definition hide_ccase_implicits {V} `{Eqb V} `{WithDefault V}
  (tgt : Rule.lang V) (cc: compiler_case V) :=
  match cc with
  | sort_case args t =>
      sort_case args (Rule.hide_sort_implicits tgt t)
  | term_case args e =>
      term_case args (Rule.hide_term_implicits tgt e)
  end.

Definition hide_compiler {V} `{Eqb V} `{WithDefault V} (l : Rule.lang V)
  : CompilerDefs.compiler V -> _:=
  NamedList.named_map (hide_ccase_implicits l).

                        
Definition block_and_val_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (block_subst ++ val_subst).


Definition block_and_val_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (block_and_val_parameterized
                       ++ty_subst_lang)
                    block_and_val_parameterized.

Lemma block_and_val_parameterized_wf
  : elab_lang_ext ty_subst_lang
      block_and_val_parameterized_def
      block_and_val_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_and_val_parameterized_wf : elab_pfs.
(*TODO: recompile & remove above*)

Definition cps_full := (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]).

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


Definition ir_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (ir_ext ++ block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps ir_ext.

Definition ir_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (ir_parameterized++
                       block_and_val_parameterized
                       ++ty_subst_lang)
                    ir_parameterized.


Lemma ir_parameterized_wf
  : elab_lang_ext (block_and_val_parameterized
                       ++ty_subst_lang)
      ir_parameterized_def
      ir_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve ir_parameterized_wf : elab_pfs.

Definition cps_parameterized_def :=
  Eval compute in hide_compiler
                    (ir_parameterized++
                       block_and_val_parameterized
                       ++ty_subst_lang)
                    cps_parameterized.


Definition id_ccase '(n,r) : list (string * compiler_case string) :=
  match r with
  | sort_rule c _ => [(n,sort_case (map fst c) (scon n (map var (map fst c))))]
  | term_rule c _ _ => [(n,term_case (map fst c) (con n (map var (map fst c))))]
  |_ => []
  end.
  
Definition id_compiler : lang -> compiler :=
  flat_map id_ccase.

(*
Lemma id_compiler_preserving (l l' : lang)
  : incl l l' -> preserving_compiler_ext (tgt_Model:=core_model l') [] (id_compiler l) l.
Proof.
  induction l;
    basic_goal_prep;
    basic_core_crush.
  destruct r;
    constructor;
    basic_goal_prep;
    basic_core_crush.
  1: exact IHl.
  1:auto.
 *)

Definition ty_subst_cmp := id_compiler ty_subst_lang.
Definition ty_subst_cmp_def :=
  Eval compute in hide_compiler ty_subst_lang ty_subst_cmp.

From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.ElabCompilers.
Lemma ty_subst_id_compiler_correct
  : (elab_preserving_compiler []
       ty_subst_lang
       ty_subst_cmp_def
       ty_subst_cmp
       ty_subst_lang).
Proof.
  auto_elab_compiler.
Qed.
#[export] Hint Resolve ty_subst_id_compiler_correct : elab_pfs.
     

Lemma cps_parameterized_correct
  : elab_preserving_compiler ty_subst_cmp
      (ir_parameterized
         ++ block_and_val_parameterized
         ++ty_subst_lang)
      cps_parameterized_def
      cps_parameterized
      
      (src_parameterized
         ++exp_and_val_parameterized).
Proof.
  Optimize Heap.
  auto_elab_compiler.
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
