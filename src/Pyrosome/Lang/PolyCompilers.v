Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Theory.Renaming
  Tools.Matches Compilers.Parameterizer Compilers.Compilers Compilers.CompilerFacts.
From Pyrosome.Lang Require Import PolySubst
  SimpleVSubst SimpleVCPS SimpleEvalCtx
  SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC
  SimpleVCCHeap SimpleVFix CombinedThm.
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
    let ps := (elab_param "D" (stlc ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps stlc.

(*
Definition stlc_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (stlc_parameterized++
                       exp_and_val_parameterized
                       ++ty_subst_lang)
                    stlc_parameterized.
 *)

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
#[export] Hint Resolve stlc_parameterized_wf : elab_pfs.


Definition src_parameterized :=
    let ps := (elab_param "D" (src_ext ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps src_ext.


Local Definition evp'' := 
    let ps := (elab_param "D" (src_ext ++exp_ret ++ exp_subst_base
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

Ltac prove_from_known_elabs ::=
  rewrite <- ?as_nth_tail;
   repeat
    lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat'
    | |- wf_lang_ext _ [] => apply wf_lang_nil
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => compute_all_fresh
    | |- incl _ _ => compute_incl
    end.


Lemma src_parameterized_wf
  : wf_lang_ext ((exp_parameterized++val_parameterized)
                       ++ty_env_lang)
      src_parameterized.
Proof.
  change (exp_parameterized++val_parameterized) with evp''.
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | try now prove_from_known_elabs..
    | vm_compute; exact I].
  {
    unfold src_ext.
    prove_from_known_elabs.
  }
Qed.
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
    | try now prove_from_known_elabs..
    | vm_compute; exact I].
  {
    unfold ir_ext.
    prove_from_known_elabs.
  }
Qed.
#[export] Hint Resolve ir_parameterized_wf : elab_pfs.


Definition cps_parameterized :=
    (*TODO: elab_param seems to do the right thing, why is
      parameterize_compiler doing the wrong thing with it?
     *)
    let ps := (elab_param "D" (src_ext ++ exp_ret ++ exp_subst_base
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
(*
Definition id_ccase '(n,r) : list (string * compiler_case string) :=
  match r with
  | sort_rule c _ => [(n,sort_case (map fst c) (scon n (map var (map fst c))))]
  | term_rule c _ _ => [(n,term_case (map fst c) (con n (map var (map fst c))))]
  |_ => []
  end.
  
Definition id_compiler : lang -> compiler :=
  flat_map id_ccase.*)

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
  prove_from_known_elabs.
Qed.
#[export] Hint Resolve ty_subst_id_compiler_correct : elab_pfs.
     

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
  2:eapply full_cps_compiler_preserving.
  1:prove_from_known_elabs.
  1:unfold src_ext;prove_from_known_elabs.
  2: reflexivity.
  1: vm_compute; exact I.
Qed.
#[export] Hint Resolve cps_parameterized_correct : elab_pfs.


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

#[export] Hint Resolve (inst_for_db "Exists") : injective_con.

(*TODO: add in*)
  Eval compute in
    eqn_rules type_subst_mode (exp_ty_subst++val_ty_subst
                                 ++env_ty_subst++exp_parameterized
                                 ++val_parameterized ++ty_subst_lang)
    exists_def.

Derive exists_lang
  SuchThat (elab_lang_ext (exp_param_substs
                             ++ exp_ty_subst
                             ++ val_param_substs
                             ++ val_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
              exists_def exists_lang)
       As exists_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exists_lang_wf : elab_pfs. 


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
  ]
  ]}.

(*TODO: add in*)
  Eval compute in
    eqn_rules type_subst_mode (block_ty_subst++val_ty_subst
                                 ++env_ty_subst++block_parameterized
                                 ++val_parameterized ++ty_subst_lang)
    exists_block_def.

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
#[export] Hint Resolve exists_block_lang_wf : elab_pfs. 

Import CompilerDefs.Notations.



Definition exp_ty_subst_cps_def : compiler string :=
  match # from (exp_param_substs ++ exp_ty_subst) with
  | {{e #"exp_ty_subst" "D" "D'" "g" "G" "A" "e"}} =>
      {{e #"blk_ty_subst" "g" "e"}}
  end.

(*TODO: upstream*)
Ltac auto_elab_compiler :=
  cleanup_elab_after setup_elab_compiler;
  repeat ([> repeat Matches.t;cleanup_elab_after try (solve [ by_reduction ]) |..]).

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
#[export] Hint Resolve ir_param_substs_wf : elab_pfs.

Let cmp' := Eval compute in cps_parameterized.
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
Proof.
  auto_elab_compiler.
  {
    right.

    compute_eq_compilation.
    sort_cong.
    all: try term_refl.
    compute_eq_compilation.
    by_reduction. (*TODO: fix auto_elab_compiler to handle*)
  }
  Unshelve.
  repeat Matches.t'.
Qed.


  (*TODO: upstream*)
  Ltac eredex_steps_with' lang name' :=
    let V := string in
    let mr := eval vm_compute in (named_list_lookup_err lang name') in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
          lazymatch goal with
          | |- eq_term ?l ?c' ?t ?e1 ?e2 =>
              let s1 := open_constr:((_ : subst V)) in
              let s2 := open_constr:((_ : subst V)) in
              let s3 := open_constr:((_ : subst V)) in
              (first [ unify_var_names V s1 c; unify_var_names V s2 c; unify_var_names V s3 c
                     | fail 2 "could not unify var names" ]);
              (first [ eapply (eq_term_conv (t:= tp [/s1 /]));
                       [eapply (eq_term_trans (l:=l) (c:=c') (e1:=e1) (e12:= e1p [/s2 /]));
                        [ try term_refl
                        | eapply (eq_term_trans (l:=l) (c:=c') (e12:= e2p [/s3 /]));
                          [eapply eq_term_subst;
                           [eapply eq_term_by with (name:=name'); solve_in
                           |repeat apply  eq_subst_cons; try apply  eq_subst_nil;
                            process_eq_term
                           |try (solve [ cleanup_auto_elab ])]
                          |try term_refl]]
                       | sort_cong; repeat process_eq_term]
                         
                     | fail 2 "could not replace with subst" ])
          end
      | None => fail 100 "rule not found in lang"
      end.

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


TODO: not id on exp_param_substs ++
        exp_ty_subst, need compiler for them
                           (map exp subst to blk subst)
                           
Let cmp' := Eval compute in cps_parameterized.
Derive poly_cps
  SuchThat (elab_preserving_compiler
              (id_compiler (val_param_substs
                              ++env_ty_subst
                              ++ty_subst_lang)
                 ++ cps_parameterized++ty_env_cmp)
              (exists_block_lang
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
  As poly_cps_preserving.
Proof.
  change cps_parameterized with cmp'.
  cleanup_elab_after setup_elab_compiler.
  (*  TODO: why are there unshelved terms? *)
  1-3: shelve.
  {
    repeat Matches.t.
  }
  {
    repeat Matches.t;cleanup_elab_after
                       try (solve [ by_reduction ]).
    right; sort_cong; try now term_refl.
    cleanup_elab_after try (solve [ by_reduction ]).
  }
  {
    repeat Matches.t;cleanup_elab_after
                       try (solve [ by_reduction ]).
    right; sort_cong; try now term_refl.
    compute_eq_compilation.
    reduce.
    TODO: don't have rule for ty_subst on neg.
    Finish substitutions and should be good to go.
    cleanup_elab_after try (solve [ by_reduction ]).
    cleanup_elab_after try (solve [ by_reduction ]).
  }
    right.
    repeat Matches.t.
    sort_cong.
    1: now term_refl.
    compute_eq_compilation.
    by_reduction.
    reduce.
    cleanup_elab_after
   try (solve [ by_reduction ]).
    
    left.
    cbn.
    by_reduction.
    (#"snoc" (#"cmp" #"wkn" #"wkn") #"hd")
    G,ExA,A => G,A
    something like this?
    (#"subst" (#"snoc" (under #"wkn") #"hd") "e")
    Lam case.
    TODO:issue: e doesn't have the right subst.
    Need to replace old hd w/ new hd?
    repeat Matches.t.
    {
      left.
      cbn.
      TODO: val d G on one side, val d ext on the other.
      ret type (#"Exists" "D" (#"neg" (#"ty_ext" "D") "A"))
    apply named_list_lookup_err_in; compute.
    TODO: missing "env_ty_subst"
    repeat f_equal.
    ; reflexivity.
  }
    left.
    match goal with
      |- ?x = ?y =>
        let x' := eval compute in x in
          change (x' = y)
    end.
    TODO: is the issue that I don't have the id compiler for a part of the ext?
             ty_subst_lang maybe?
             (exp_and_val_param_substs ++
     exp_ty_subst ++
     env_ty_subst ++ ty_subst_lang ++ exp_parameterized ++ val_parameterized ++ ty_env_lang)
    case for All:
      - ex -[""] A
    TODO: issue: "" in the substitution lining up w/ D
    cbn [fst].
    cleanup_elab_after
      try (solve [ by_reduction ])
          Ltac auto_elab_compiler :=
  cleanup_elab_after setup_elab_compiler; repeat Matches.t; cleanup_elab_after
   try (solve [ by_reduction ])

  auto_elab_compiler.
  {
    cbn [fst] in *.
    TODO: compiler linted? and still "" appears.

  Import Tools.Linter.

    Definition lint_ccase (src tgt : lang string) '(n,c) :=
      match named_list_lookup_err src n, c with
      (* rule disagreements *)
      | None, (term_case args e) =>
          [ccase_constr_unbound_in_lang n c] ++ (lint_term tgt args e)
      | None, (sort_case args t) =>
          [ccase_constr_unbound_in_lang n c] ++ (lint_sort tgt args t)
      | Some (sort_rule _ _), (term_case args e) =>
          [ccase_sort_give_term_case n e] ++ (lint_term tgt args e)
      | Some (term_rule _ _ _), (sort_case args t)=>
          [ccase_term_give_sort_case n t] ++ (lint_sort tgt args t)
      | Some (sort_eq_rule _ _ _), (sort_case args t) 
      | Some (term_eq_rule _ _ _ _), (sort_case args t) =>
          [ccase_eqn_give_sort_case n t] ++ (lint_sort tgt args t)
      | Some (sort_eq_rule _ _ _), (term_case args e)
      | Some (term_eq_rule _ _ _ _), (term_case args e) =>
          [ccase_eqn_give_term_case n e] ++ (lint_term tgt args e)
      (* rule-matching cases *)
      | Some (sort_rule c _), sort_case args t =>
          (lint_ccase_args args c) ++ (lint_sort tgt args t)
      | Some (term_rule c _ t), term_case args e =>
          (lint_ccase_args args c) ++ (lint_term tgt args e)
      end.

  (*TODO: make more precise wrt comparing to l *)
  Definition lint_cmp_ext src tgt cmp :=
    flat_map (lint_ccase src tgt) cmp.
    
Ltac lint_compiler src tgt cmp :=
  let lint_res := (eval vm_compute in (lint_cmp_ext src tgt cmp)) in
  lazymatch lint_res with
  | [] => idtac
  (* TODO: print all errors *)
  | ?e::_ => print_linting_err e
  end.

  match goal with
  | |- elab_preserving_compiler _ ?tgt ?cmp ?ecmp ?src =>
      lint_compiler src tgt cmp
  end.
  break_preserving
  lint_compiler l cmp
                  
    TODO:  add lint to auto_elab_compiler
  auto_elab_compiler. (*
  16:{
   (* TODO: compiler linter
                   Linter .lint_lang_ex
      auto_elab_compiler.
    Goal: show "A" : "ty_env" (oops)in env D : "", A : ty ""*)
  fail fail.
  all: try lazymatch goal with
  | |- string => shelve
  | |- SimpleVSubst.sort => shelve
         end.
  4:{
    TODO:default strings appearing, what case did I miss?.
  all: try apply default.
  (*To long.., maybe because langs aren't computed*)
  TODO
*)
Qed.
#[export] Hint Resolve poly_cps_preserving : elab_pfs.


Derive poly_cps
  SuchThat (elab_lang_ext (exp_and_val_param_substs
                             ++ exp_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
              poly_def poly)
       As poly_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve poly_wf : elab_pfs. 

(*
Definition poly_cps : compiler  :=
*)
