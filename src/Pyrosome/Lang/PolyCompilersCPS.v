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
  SimpleVCCHeap SimpleVFix CombinedThm PolyCompilerLangs.
From Pyrosome.Tools Require Import InjRuleGen.
From Pyrosome.Tools Require Import UnElab.
From Pyrosome.Compilers Require Import CompilerTransitivity.
Import Core.Notations.
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.
Local Open Scope lang_scope.

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

Definition cps_full := (let_cps++fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]).

Definition cps_parameterized :=
    (*TODO: elab_param seems to do the right thing, why is
      parameterize_compiler doing the wrong thing with it?
     *)
    let ps := (elab_param "D" (let_lang ++ src_ext ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
    let pir :=  (elab_param "D" (ir_ext ++ block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
    parameterize_compiler "D"
      (*firstn 44 skips the rule for ty. TODO: still necessary?*)
      pir ps cps_full.

Definition ty_env_cmp := id_compiler ty_env_lang.

(*TODO: prove the more general version*)
Lemma ty_subst_id_compiler_correct
  : (preserving_compiler_ext
       (tgt_Model:=core_model ty_env_lang)
       []
       ty_env_cmp
       ty_env_lang).
Proof.
  apply id_compiler_preserving; try typeclasses eauto.
  prove_by_lang_db.
Qed.
#[local] Definition ty_subst_id_entry :=
  cmp_entry ty_subst_id_compiler_correct.
#[export] Hint Resolve ty_subst_id_entry : preserving_db.

(* TODO: duplicated from PolyCompilerLangs. Make non-local?*)
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

Lemma cps_parameterized_correct
  : preserving_compiler_ext
      (tgt_Model:=core_model ((ir_parameterized
                                ++ (block_parameterized++
                                      val_parameterized))
                                ++ty_env_lang))
      ty_env_cmp
      cps_parameterized
      (src_parameterized
         ++ (exp_parameterized++
               val_parameterized)).
Proof.
  change (exp_parameterized++val_parameterized) with evp''.
  unfold ty_env_cmp, cps_parameterized,
    src_parameterized, evp''.
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
  2:rewrite <- app_assoc; eapply full_cps_compiler_preserving.
  1:prove_by_lang_db.
  1:prove_by_lang_db.
  2: reflexivity.
  1: vm_cast_no_check I.
Qed.
#[local] Definition cps_parameterized_entry :=
  cmp_entry cps_parameterized_correct.
#[export] Hint Resolve cps_parameterized_entry : preserving_db.


Definition exp_ty_subst_cps_def : compiler :=
  match # from (exp_param_substs ++ exp_ty_subst) with
  | {{e #"exp_ty_subst" "D" "D'" "g" "G" "A" "e"}} =>
      {{e #"blk_ty_subst" "g" "e"}}
  end.


Definition ir_param_substs_def :=
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
    (hide_lang_implicits (ir_parameterized++deps) ir_parameterized).

(*TODO: this takes too long. Why?
Definition ir_param_substs :=
  Eval vm_compute in
    (infer_lang_ext_simple_incr 10 100
       (block_param_substs
          ++ val_param_substs
          ++ block_ty_subst
          ++ env_ty_subst
          ++ ty_subst_lang
          ++ block_parameterized
          ++ val_parameterized
          ++ ty_env_lang)
       ir_param_substs_def).
*)

Derive ir_param_substs
  in (elab_lang_ext (ir_parameterized
                             ++block_param_substs
                             ++val_param_substs
                             ++block_ty_subst
                             ++env_ty_subst
                             ++block_parameterized
                             ++ty_subst_lang
                             ++val_parameterized
                             ++ty_env_lang)
              ir_param_substs_def
              ir_param_substs)
  as ir_param_substs_wf.
Proof. auto_elab. Qed.
#[local] Definition ir_param_substs_entry :=
  lang_entry (elab_lang_implies_wf ir_param_substs_wf).
#[export] Hint Resolve ir_param_substs_entry : wf_lang_db.

Definition exp_ty_subst_cps' :=
  Eval vm_compute in
    (infer_compiler_simple_autoinj 7
       (ir_param_substs
                 ++ ir_parameterized (*TODO: only include conts*)
                 ++ block_param_substs
                 ++ val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ty_subst_lang
                 ++block_parameterized++val_parameterized
                 ++ty_env_lang)
       (id_compiler (val_param_substs
                             ++ val_ty_subst
                              ++env_ty_subst
                              ++ty_subst_lang)
                 ++ cps_parameterized++ty_env_cmp)
       exp_ty_subst_cps_def
       (exp_param_substs ++ exp_ty_subst)).

(* TODO: Qed/e-graph fails. Why?
Lemma cps_preserving
  : preserving_compiler_ext
      (id_compiler (val_param_substs
                      ++ val_ty_subst
                      ++env_ty_subst
                      ++ty_subst_lang)
         ++ cps_parameterized++ty_env_cmp)
      (tgt_Model:= core_model
                     (ir_param_substs
                        ++ ir_parameterized (*TODO: only include conts*)
                        ++ block_param_substs
                        ++ val_param_substs
                        ++ block_ty_subst
                        ++env_ty_subst
                        ++ty_subst_lang
                        ++block_parameterized++val_parameterized
                        ++ty_env_lang))
      exp_ty_subst_cps
      (exp_param_substs ++ exp_ty_subst).
Proof.
  compute_preserving_compiler
    ((val_param_substs
        ++ val_ty_subst
        ++env_ty_subst
        ++ty_subst_lang)
       ++(src_parameterized ++ exp_parameterized ++ val_parameterized)
       ++ty_env_lang).
Qed.
*)

Derive exp_ty_subst_cps
  in (elab_preserving_compiler
              (id_compiler (val_param_substs
                             ++ val_ty_subst
                              ++env_ty_subst
                              ++ty_subst_lang)
                 ++ cps_parameterized++ty_env_cmp)
              (ir_param_substs
                 ++ ir_parameterized (*TODO: only include conts*)
                 ++ block_param_substs
                 ++ val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ty_subst_lang
                 ++block_parameterized++val_parameterized
                 ++ty_env_lang)
              exp_ty_subst_cps_def
              exp_ty_subst_cps
              (exp_param_substs ++ exp_ty_subst))
  as exp_ty_subst_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition exp_ty_subst_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving exp_ty_subst_cps_preserving).
#[export] Hint Resolve exp_ty_subst_cps_entry : preserving_db.

Definition poly_cps_def : compiler :=
  match # from poly with
  | {{e #"All" "D" "A"}} =>
    {{e #"neg" (#"Exists" (#"neg" "A")) }}
  | {{e #"Lam" "D" "G" "A" "e"}} =>
      {{e #"cont" (#"Exists" (#"neg" "A"))
          (#"unpack" #"hd" (#"blk_subst" (#"snoc" (#"cmp" #"wkn" #"wkn") #"hd") "e")) }}
  | {{e #"@" "D" "G" "A" "e" "B"}} =>      
    bind_k 1 (var "e") {{e #"neg" (#"Exists" (#"neg" "A")) }}
    {{e #"jmp" {ovar 0} (#"pack" "B" {ovar 1}) }}
  end.

(*TODO: move somewhere*)
Definition count_constr_implicits (l:lang) n :=
  match named_list_lookup_err l n with
  | Some (sort_rule c args)
  | Some (term_rule c args _) => length c - length args
  | _ => 0
  end.

Fixpoint count_implicits l e :=
  match e with
  | var _ => 0
  | con n s =>
      fold_left Nat.add (map (count_implicits l) s) (count_constr_implicits l n)
  end.
Import Monad.
Import StateMonad.

Definition ask_evar : state (list term) term :=
  fun l => (hd default l, tl l).


Ltac intermediate_term e :=      
  match goal with
    |- eq_term ?l' ?c ?t ?e1 ?e2 =>
      let e' := open_constr:(_:term) in
      assert (elab_term l' c e e' t) as H';
      [| eapply eq_term_trans with (e12:=e');
         clear H']
  end.

(* Temporary until I restore the proof*)
Axiom (TODO : forall {A}, A).
Derive poly_cps
  in (elab_preserving_compiler
              (exp_ty_subst_cps
                 ++ id_compiler (val_param_substs
                                   ++ val_ty_subst
                                   ++env_ty_subst
                                   ++ty_subst_lang)
                 ++ cps_parameterized++ty_env_cmp)
              (exists_block_lang
                 ++ ir_param_substs
                 ++ ir_parameterized (*TODO: only include conts*)
                 ++ block_param_substs
                 ++ val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ty_subst_lang
                 ++block_parameterized++val_parameterized
                 ++ty_env_lang)
              poly_cps_def
              poly_cps
              poly)
  as poly_cps_preserving.
Proof.
  ElabCompilers.auto_elab_compiler.
  {  apply TODO (*Automation.by_reduction; t'.*). }
  (*Automation.auto_elab_compiler.
12:57-1:46+; too long
   *)
Qed.
#[local] Definition poly_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving poly_cps_preserving).
#[export] Hint Resolve poly_cps_entry : preserving_db.

Local Definition unpack_swap :=
  {{e #"snoc" (#"snoc" (#"cmp" (#"cmp" #"wkn" #"wkn") #"wkn") #"hd") {ovar 2} }}.

Definition exists_cps_def : compiler :=
  match # from exists_lang with
  | {{e #"Exists" "D" "A"}} =>
      {{e #"Exists" "A" }}
  | {{e #"pack_val" "D" "G" "A" "B" "v"}} =>
      {{e #"pack" "A" "v" }}
  | {{e #"pack" "D" "G" "A" "B" "e"}} =>
      bind_k 1 (var "e") {{e #"ty_subst" (#"ty_snoc" #"ty_id" "A") "B" }}
        {{e #"jmp" {ovar 1} (#"pack" "A" #"hd") }}
  | {{e #"unpack" "D" "G" "B" "e" "C" "e'" }} =>
    bind_k 1 (var "e") {{e #"Exists" "B" }}
      {{e #"unpack" #"hd" (#"blk_subst" {unpack_swap} "e'")  }}
  end.

Derive exists_cps
  in (elab_preserving_compiler
              (exp_ty_subst_cps
                 ++ id_compiler (val_param_substs
                                   ++ val_ty_subst
                                   ++env_ty_subst
                                   ++ty_subst_lang)
                 ++ cps_parameterized++ty_env_cmp)
              (exists_block_lang
                 ++ ir_param_substs
                 ++ ir_parameterized (*TODO: only include conts*)
                 ++ block_param_substs
                 ++ val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ty_subst_lang
                 ++block_parameterized++val_parameterized
                 ++ty_env_lang)
              exists_cps_def
              exists_cps
              exists_lang)
  as exists_cps_preserving.
Proof.
  (*TODO: takes much longer than legacy auto_elab_compiler (has not terminated). Why?
    Time  1:Automation.auto_elab_compiler.
    Legacy: ~50s
   *)
  ElabCompilers.auto_elab_compiler.
Qed.
#[local] Definition exists_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving exists_cps_preserving).
#[export] Hint Resolve exists_cps_entry : preserving_db.
