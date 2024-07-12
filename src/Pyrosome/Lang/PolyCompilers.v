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
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve exp_ty_subst_cps_preserving : elab_pfs.

(*
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
  *)

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

Derive poly_cps
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
              poly_cps_def
              poly_cps
              poly)
  As poly_cps_preserving.
Proof.
  change cps_parameterized with cmp'.
  auto_elab_compiler.
  {
    compute_eq_compilation.
    reduce.
    hide_implicits.

      (*TODO: upstream when done*)
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
              let H1 := fresh in
              let H2 := fresh in
              assert (eq_subst (Model:=core_model l) c' c s1 s2) as H1;
              [|clear H1; assert (eq_subst (Model:=core_model l) c' c s2 s3) as H2;
              [| clear H2;
              (first [ eapply (eq_term_conv (t:= tp [/s1 /]));
                       [eapply (eq_term_trans (l:=l) (c:=c') (e1:=e1) (e12:= e1p [/s2 /]));
                        [ try term_refl
                        | eapply (eq_term_trans (l:=l) (c:=c') (e12:= e2p [/s3 /]));
                          [eapply eq_term_subst;
                           [eapply eq_term_by with (name:=name'); solve_in
                           |repeat apply  eq_subst_cons; try apply  eq_subst_nil;
                            process_eq_term
                           |try (solve [ cleanup_auto_elab ])]
                          |try term_refl ] ]
                       | sort_cong; repeat process_eq_term]
                         
                     | fail 2 "could not replace with subst using rule" mr ]) ] ];
              [repeat eapply eq_subst_cons; try eapply eq_subst_nil; try term_refl..|]
          end
      | None => fail 100 "rule not found in lang"
      end.
  
  Ltac eredex_steps_with'' lang name :=
    let V := string in
  let mr := eval vm_compute in (named_list_lookup_err lang name) in
  lazymatch mr with
  | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
      lazymatch goal with
      | |- eq_term ?l ?c' ?t ?e1 ?e2 =>
              let s1 := open_constr:((_ : subst V)) in
              let s2 := open_constr:((_ : subst V)) in
              let s3 := open_constr:((_ : subst V)) in
              
              (first [ unify_var_names V s1 c; unify_var_names V s2 c; unify_var_names V s3 c
                     | fail 2 "could not unify var names" ]);
              let H1 := fresh in
              let H2 := fresh in
              assert (eq_subst (Model:=core_model l) c' c s1 s2) as H1;
              [|(*clear H1;*) assert (eq_subst (Model:=core_model l) c' c s2 s3) as H2;
              [| (*clear H2;*)

                 (first
             [ replace (eq_term l c' t e1 e2) with (eq_term l c' tp [/s1 /] e1p [/s2 /] e2p [/s3 /]);
                [  | f_equal; vm_compute; try reflexivity ]
             | fail 2 "could not replace with subst" ])(*;
             eapply eq_term_conv;
             [eapply (eq_term_subst (l:=l) (c:=c') (s1:=s1) (s2:=s2) (c':=c));
             [ eapply (eq_term_by l c name tp e1p e2p); try (solve [ cleanup_auto_elab ])
             | eapply eq_subst_refl; try (solve [ cleanup_auto_elab ])
             | try (solve [ cleanup_auto_elab ]) ] | ] *) ] ] 
      end
  | None => fail 100 "rule not found in lang"
  end.
  eapply eq_term_trans; cycle 1.
  {
    eredex_steps_with ir_parameterized "cont_eta".
  }
  all: compute_eq_compilation.
  term_cong.
  all: compute_eq_compilation.
  all: try term_refl.
  reduce.
  hide_implicits.

  
  match goal with
  |- eq_term ?l' ?c ?t ?e1 ?e2 =>
    let e := constr:({{e #"blk_subst" (#"snoc" #"id" #"hd") (#"jmp" (#"val_subst" (#"cmp" #"wkn" #"wkn") "v") #"hd") }})
      in
      let e' := open_constr:(_:term) in
      assert (elab_term l' c e e' t) as H';
      [| eapply eq_term_trans with (e12:=e');
         clear H']
  end.
  {
    try_break_elab_term.
    all:repeat (compute_eq_compilation;
                try term_refl; reduce).
  }
  2:{ by_reduction. }
  eapply eq_term_trans; cycle 1.
  {
    eredex_steps_with exists_block_lang "unpack-eta".
  }
  compute_eq_compilation.
  hide_implicits.
  reduce.
  term_refl.
  }
  Unshelve.
  all: repeat Matches.t'.
  lazymatch goal with
  | |- wf_term ?l ?c ?e ?t =>
        let c' := eval compute in (hide_ctx_implicits l c) in
        let t' := eval compute in (hide_sort_implicits l t) in
        let e' := eval compute in (hide_term_implicits l e) in
        change (wf_term l (lie_to_user (real:=c) (as_ctx c'))
                        (lie_to_user (real:=e) e')
                        (lie_to_user (real:=t) t'))
  end.
  
  eapply wf_term_by';[ solve_in |..].
  2:left;
  reflexivity.
  repeat eapply wf_args_cons; try eapply wf_args_nil.
  all:repeat Matches.t'.
  lazymatch goal with
  | |- wf_term ?l ?c ?e ?t =>
        let c' := eval compute in (hide_ctx_implicits l c) in
        let t' := eval compute in (hide_sort_implicits l t) in
        let e' := eval compute in (hide_term_implicits l e) in
        change (wf_term l (lie_to_user (real:=c) (as_ctx c'))
                        (lie_to_user (real:=e) e')
                        (lie_to_user (real:=t) t'))
  end.
  
  eapply wf_term_by';[ solve_in |..].
  2:{
    right.
    compute_eq_compilation.
    sort_cong; try term_refl.
    reduce.
    term_refl.
  }
  repeat eapply wf_args_cons; try eapply wf_args_nil.
  all:repeat Matches.t'.
  all:  match goal with
  | |- wf_term ?l ?c ?e ?t =>
        let c' := eval vm_compute in c in
        let e' := eval vm_compute in e in
        let t' := eval vm_compute in t in
        change_no_check (wf_term l c' e' t')
        end.
  {
    
    eapply wf_term_by';[ solve_in |..].
    2:left;reflexivity.
    repeat eapply wf_args_cons; try eapply wf_args_nil.
    all:repeat Matches.t'.
    
    eapply wf_term_by';[ solve_in |..].
  2:{
    right.
    compute_eq_compilation.
    sort_cong; try term_refl.
    reduce.
    term_refl.
  }
  repeat eapply wf_args_cons; try eapply wf_args_nil.
  all:repeat Matches.t'.
  }
  {
    eapply wf_term_by';[ solve_in |..].
    2:left;reflexivity.
    repeat eapply wf_args_cons; try eapply wf_args_nil.
    all:repeat Matches.t'.
    
    eapply wf_term_by';[ solve_in |..].
  2:{
    right.
    compute_eq_compilation.
    sort_cong; try term_refl.
    reduce.
    term_refl.
  }
  repeat eapply wf_args_cons; try eapply wf_args_nil.
  all:repeat Matches.t'.
  }
  Unshelve.
  all:repeat Matches.t'.
Qed.
#[export] Hint Resolve poly_cps_preserving : elab_pfs.

