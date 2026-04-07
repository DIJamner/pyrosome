Require Import Datatypes.String Lists.List.
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
Import Core.Notations.
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

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
    | now prove_from_known_elabs..
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
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.ElabCompilers.
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

Local Open Scope lang_scope.
Definition exists_def : lang _ :=
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

Derive exists_lang
  in (elab_lang_ext (exp_param_substs
                             ++ exp_ty_subst
                             ++ val_param_substs
                             ++ val_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
              exists_def exists_lang)
       as exists_lang_wf.
Proof. auto_elab. Qed.
#[local] Definition exists_lang_entry :=
  lang_entry (elab_lang_implies_wf exists_lang_wf).
#[export] Hint Resolve exists_lang_entry : wf_lang_db.

Definition exists_block_def : lang _ :=
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

Derive exists_block_lang
  SuchThat (elab_lang_ext (block_param_substs
                             ++val_param_substs
                             ++ block_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++block_parameterized++val_parameterized
                             ++ty_env_lang)
              exists_block_def exists_block_lang)
       As exists_block_lang_wf.
Proof. auto_elab. Qed.
#[local] Definition exists_block_lang_entry :=
  lang_entry (elab_lang_implies_wf exists_block_lang_wf).
#[export] Hint Resolve exists_block_lang_entry : wf_lang_db.

Definition exp_ty_subst_cps_def : compiler string :=
  match # from (exp_param_substs ++ exp_ty_subst) with
  | {{e #"exp_ty_subst" "D" "D'" "g" "G" "A" "e"}} =>
      {{e #"blk_ty_subst" "g" "e"}}
  end.

Require Import Tools.UnElab.

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

Derive ir_param_substs
  SuchThat (elab_lang_ext (ir_parameterized
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
  As ir_param_substs_wf.
Proof. auto_elab. Qed.
#[local] Definition ir_param_substs_entry :=
  lang_entry (elab_lang_implies_wf ir_param_substs_wf).
#[export] Hint Resolve ir_param_substs_entry : wf_lang_db.

#[local] Definition cmp' := Eval compute in cps_parameterized.
Derive exp_ty_subst_cps
  SuchThat (elab_preserving_compiler
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
  As exp_ty_subst_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition exp_ty_subst_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving exp_ty_subst_cps_preserving).
#[export] Hint Resolve exp_ty_subst_cps_entry : preserving_db.

Definition poly_cps_def : compiler string :=
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
Definition count_constr_implicits (l:lang string) n :=
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

Local Notation ctx := (ctx string).
Local Notation term := (term string).
Local Notation lang := (lang string).
Definition ask_evar : state (list term) term :=
  fun l => (hd default l, tl l).

(*TODO: no fuel*)
Section __.
  Context (insert_implicits : term -> state (list term) term).

  Fixpoint insert_implicits_args (fuel : nat)
    (c:ctx) args s {struct fuel} : state (list term) (list term) :=
    match fuel with
    | S fuel =>
        match c, args, s with
        | [], [], [] => Mret []
        | (x,_)::c', [], [] =>
            @! let x_evar <- ask_evar in
              let s' <- insert_implicits_args fuel c' [] [] in
              ret x_evar::s'
        | (x,_)::c', y::args', e::s' =>
            if eqb x y then
              @! let s'' <- insert_implicits_args fuel c' args' s' in
                let e' <- insert_implicits e in
                ret e':: s''
            else
              @! let x_evar <- ask_evar in
                let s'' <- insert_implicits_args fuel c' args s in
                ret x_evar::s''
        | _, _, _ => Mret default
        end
    | O => Mret default
    end.
End __.
(*really want a reader monad, but I don't have that *)
Fixpoint insert_implicits fuel l e {struct fuel} : state (list term) term :=
  match fuel with
  | S fuel =>
      match e with
      | var x => Mret (var x)
      | con n s =>
          match  (named_list_lookup_err l n) with
          | Some (term_rule c args _) =>
              @! let s' <- insert_implicits_args (insert_implicits fuel l) fuel c args s in
                ret con n s'
          | _ => Mret default
          end
      end
  | O => Mret default
  end.

Ltac mk_evar_list c :=
  lazymatch c with
  | S ?c' =>
      let x := open_constr:(_:term) in
      let l' := mk_evar_list c' in
      constr:(x::l')
  | O => constr:([])
  end.

Ltac insert_implicits l e :=
  let c := eval compute in (count_implicits l e) in
    let evar_list := mk_evar_list c in
    let e' := eval compute in (snd (insert_implicits 100 l e evar_list)) in
      idtac e'.


Ltac intermediate_term e :=      
  match goal with
    |- eq_term ?l' ?c ?t ?e1 ?e2 =>
      let e' := open_constr:(_:term) in
      assert (elab_term l' c e e' t) as H';
      [| eapply eq_term_trans with (e12:=e');
         clear H']
  end.

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
  auto_elab_compiler.
  { Automation.by_reduction; t'. }
  (*Automation.auto_elab_compiler.
12:57-1:46+; too long
   *)  
Qed.
#[local] Definition poly_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving poly_cps_preserving).
#[export] Hint Resolve poly_cps_entry : preserving_db.

Local Definition unpack_swap :=
  {{e #"snoc" (#"snoc" (#"cmp" (#"cmp" #"wkn" #"wkn") #"wkn") #"hd") {ovar 2} }}.

Definition exists_cps_def : compiler string :=
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
  SuchThat (elab_preserving_compiler
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
  As exists_cps_preserving.
Proof.
  (*TODO: takes much longer than legacy auto_elab_compiler (has not terminated). Why?
    Time  1:Automation.auto_elab_compiler.
    Legacy: ~50s
   *)
  auto_elab_compiler.
Qed.
#[local] Definition exists_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving exists_cps_preserving).
#[export] Hint Resolve exists_cps_entry : preserving_db.

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

Definition exists_cc_def : compiler string :=
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
  SuchThat (elab_lang_ext (tgt_parameterized
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
  As tgt_param_substs_wf.
Proof. auto_elab. Qed.
#[local] Definition tgt_param_substs_entry :=
  lang_entry (elab_lang_implies_wf tgt_param_substs_wf).
#[export] Hint Resolve tgt_param_substs_entry : wf_lang_db.

#[local] Definition cmp'' := Eval compute in cc_parameterized.

Definition block_ty_subst_cc_def : compiler string :=
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
  SuchThat (elab_preserving_compiler
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
  As block_ty_subst_cc_preserving.
Proof. Automation.auto_elab_compiler. Qed.
#[local] Definition block_ty_subst_cc_entry :=
  cmp_entry (elab_compiler_implies_preserving block_ty_subst_cc_preserving).
#[export] Hint Resolve block_ty_subst_cc_entry : preserving_db.

Derive exists_cc
  SuchThat (elab_preserving_compiler
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
  As exists_cc_preserving.
Proof.
  auto_elab_compiler.
  { Automation.by_reduction; Matches.t'. }
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

Require Import Pyrosome.Compilers.CompilerTransitivity.

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

  
  Definition hide_cmp_implicits (l:lang) : compiler string -> compiler string :=
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
