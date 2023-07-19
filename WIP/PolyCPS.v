Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Theory.Renaming
  Tools.Matches Compilers.Parameterizer Compilers.Compilers Elab.Elab Elab.ElabCompilers.
From Pyrosome.Lang Require Import SimpleVCPS PolySubst PolyCompilers.
(*  SimpleVSubst SimpleVCPS SimpleEvalCtx
  SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC
  SimpleVCCHeap SimpleVFix.*)
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Definition val_poly_def : lang _ :=
  {[l
  [:| "D" : #"ty_env", "A" : #"ty" (#"ty_ext" "D")
      -----------------------------------------------
      #"All" "A" : #"ty" "D"
  ];
    [:| "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" (#"ty_ext" "D"),
       "v" : #"val" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") "A"
       -----------------------------------------------
       #"Lam" "v" : #"val" "D" "G" (#"All" "A")
  ];
  [:| "D" : #"ty_env",
      "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"All" "A"),
       "B" : #"ty" "D"
       -----------------------------------------------
       #"@" "v" "B"
       : #"val" "D" "G"
         (#"ty_subst" (#"ty_snoc" #"ty_id" "B") "A")
  ];
  [:=  "D" : #"ty_env",
      "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
       "v" : #"val" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") "A",
       "B" : #"ty" "D"
      ----------------------------------------------- ("Lam-beta")
      #"@" (#"Lam" "v") "B"
      = #"val_ty_subst" (#"ty_snoc" #"ty_id" "B") "v"
      : #"val" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "B") "A")
  ]
    (*
  [:= "D" : #"ty_env",
      "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"All" "A")
        ----------------------------------------------- ("Lam-eta")
      #"Lam" (#"@" (#"ret" "v") (#"ret" #"ty_hd"))
      = "v"
      : #"val" "D" "G" (#"All" "A")
  ] *)
  ]}.

Derive val_poly
  SuchThat (elab_lang_ext (block_and_val_param_substs
                             ++ block_ty_subst
                             ++env_ty_subst
                             ++block_and_val_parameterized
                             ++ty_subst_lang)
              val_poly_def val_poly)
       As val_poly_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve val_poly_wf : elab_pfs.

Definition exp_tysubst_ident_def : compiler _ :=
  match # from (exp_and_val_param_substs
                 ++ exp_ty_subst
                 ++env_ty_subst) with
  | {{e #"exp_ty_subst" "D" "D'" "g" "G" "A" "e" }} =>
    {{e #"blk_ty_subst" "g" "e" }}
  end.


Import GenericSubst (eqn_rules, type_subst_mode).
Definition ir_param_substs_def :=
  (skipn 6 (firstn 7
     (eqn_rules type_subst_mode (block_ty_subst++env_ty_subst++ir_parameterized++block_and_val_parameterized ++ty_subst_lang)
    ir_parameterized_def))).
             
Derive ir_param_substs
  SuchThat (elab_lang_ext (block_and_val_param_substs
                             ++ block_ty_subst
                             ++env_ty_subst
                             ++ ir_parameterized
                             ++block_and_val_parameterized
                             ++ty_subst_lang)
              ir_param_substs_def
              ir_param_substs)
  As ir_param_substs_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve ir_param_substs_wf : elab_pfs.


Derive exp_tysubst_ident
  SuchThat (elab_preserving_compiler (cps_parameterized++ty_subst_cmp)
              (ir_param_substs
                 ++ block_and_val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ir_parameterized
                 ++ block_and_val_parameterized
                 ++ty_subst_lang)
              exp_tysubst_ident_def
              exp_tysubst_ident
              (exp_and_val_param_substs
                 ++ exp_ty_subst
                 ++env_ty_subst))
       As  exp_tysubst_ident_preserving.
Proof.
  cleanup_elab_after setup_elab_compiler.
  all: try solve [unshelve (repeat Matches.t); repeat t'].
  1:shelve.
  1:cleanup_elab_after try (solve [ by_reduction ]).
  1:cleanup_elab_after try (solve [ by_reduction ]).
  {
    eapply elab_term_conv.
    {
      cleanup_elab_after (repeat Matches.t).
    }
    cleanup_elab_after (sort_cong; try term_refl).
    unfold Model.eq_term; cleanup_elab_after by_reduction.
  }
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  {
    compute in exp_tysubst_ident.
    (*TODO: Coq bug?*)
    compute_eq_compilation.
    compute_eq_compilation.
    cleanup_elab_after (solve [ by_reduction ]).
  }
  1:cleanup_elab_after (solve [ by_reduction ]).
  {
    (*TODO: Coq bug?*)
    compute_eq_compilation.
    compute_eq_compilation.
    (*TODO: why doesn't reduce work?
    reduce.*)
    cleanup_elab_after eredex_steps_with block_and_val_param_substs "sub_ty_subst forget".
  }
  1:cleanup_elab_after (solve [ by_reduction ]).
  {
    (*TODO: Coq bug?*)
    compute_eq_compilation.
    compute_eq_compilation.
    cleanup_elab_after eredex_steps_with block_and_val_param_substs "sub_ty_subst snoc".
  }
  {
    (*TODO: Coq bug?*)
    compute_eq_compilation.
    compute_eq_compilation.
    cleanup_elab_after eredex_steps_with block_and_val_param_substs "sub_ty_subst wkn".
  }
  {
    (*TODO: Coq bug?*)
    compute_eq_compilation.
    compute_eq_compilation.
    cleanup_elab_after eredex_steps_with block_and_val_param_substs "val_ty_subst hd".
  }
  (*TODO: Coq bug?*)
  all: repeat compute_eq_compilation.
  {
      eredex_steps_with block_and_val_param_substs "blk_ty_subst blk_subst".
  }
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).
  1:cleanup_elab_after (solve [ by_reduction ]).

  auto_elab_compiler.
       
       TODO: nonsyntactic eqn in type
1: cbv.       5: solve_in.
       1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
       1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                             | constructor ]].
       { cbv
           TODO: where is the ""?
         cbv.
       1: solve_in.
       all: try solve [unshelve (repeat Matches.t); repeat t'].
Qed.
#[export] Hint Resolve block_tysubst_ident_preserving : elab_pfs.

Definition poly_cps_def : compiler string:=
  match # from (poly) with
  | {{e #"All" "A"}} =>
    {{e #"All" (#"neg" (#"neg" "A")) }}
  | {{e #"Lam" "D" "G" "A" "e"}} =>
    {{e #"Lam" (#"cont" (#"neg" "A") "e") }}
  | {{e #"@" "D" "G" "A" "e" "B"}} =>
      bind_k 1 (var "e") {{e #"All" (#"neg" (#"neg" "A"))}}
        {{e #"jmp" (#"@" {ovar 0} "B") {ovar 1} }}
  end.

Derive poly_cps
  SuchThat (elab_preserving_compiler (cps_parameterized++ty_subst_cmp)
              (val_poly
                 ++ block_and_val_param_substs
                 ++ block_ty_subst
                 ++env_ty_subst
                 ++ir_parameterized
                 ++ block_and_val_parameterized
                 ++ty_subst_lang)
              poly_cps_def
              poly_cps
              poly)
       As poly_cps_preserving.
Proof.
  (*Temp workaround for vm_compute issue*)
  Ltac solve_in ::=
     apply named_list_lookup_err_in;
      reflexivity.
  setup_elab_compiler.
  1:solve [unshelve (repeat Matches.t); repeat t'].
  {
    TODO: compile_ctx the issue: no rule for env_ty_subst; need id compiler
    match goal with
    | |- elab_term ?l ?c ?e ?ee ?t =>
        let c' := eval vm_compute in c in
          let e' := eval vm_compute in e in
            let t' := eval vm_compute in t in
              change_no_check (elab_term l c' e' ee t')
    end.
    cbn.
    unshelve (repeat Matches.t); repeat t'.
    all: repeat t'.
    solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
  repeat Matches.t; cleanup_elab_after try (solve [ by_reduction ])

  auto_elab_compiler.
  
  1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
  1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                        | constructor ]].
  {
  TODO: lam case: "" as second arg to cont
    1:match goal with
    | |- wf_term ?l ?c ?e ?t =>
        let c' := eval vm_compute in c in
          let e' := eval vm_compute in e in
            let t' := eval vm_compute in t in
              change_no_check (wf_term l c' e' t')
    end. TODO: empty string means error; instead of G in DGAe blk
    1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
  1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
  1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
  1:solve [repeat first [ eapply wf_term_by'
                      | eapply wf_term_var
                      | solve_in
                      | reflexivity
                      | constructor ]].
    
    1:solve_in.
    2: reflexivity.
    constructor.
    {
      eapply wf_term_var.
      solve_in.
    }
    match goal with
    | |- wf_term ?l ?c ?e ?t =>
        let c' := eval vm_compute in c in
          let e' := eval vm_compute in e in
            let t' := eval vm_compute in t in
              change_no_check (wf_term l c' e' t')
    end.
    
    ea
         tryif (first [ has_evar c' | has_evar e' | has_evar t' ]) then
          assumption || eapply wf_term_var || eapply wf_term_by' else ComputeWf.compute_noconv_term_wf 
  | |- wf_args _ _ _ _ => simple apply wf_args_nil || simple eapply wf_args_cons2 || simple eapply wf_args_cons
  | |- wf_subst _ _ _ => constructor
  | |- wf_ctx ?c =>
        let c' := eval vm_compute in c in
        change_no_check (wf_ctx c'); tryif has_evar c' then assumption || constructor else ComputeWf.solve_wf_ctx 
  | |- wf_sort ?l ?c ?t =>
        let c' := eval vm_compute in c in
        let t' := eval vm_compute in t in
        change_no_check (wf_sort l c' t'); eapply wf_sort_by
  | |- wf_lang _ => solve [ prove_from_known_elabs ]
  | |- _ = _ => compute; reflexivity
  end
    repeat Matches.t'.
   match goal with
  | |- elab_preserving_compiler _ ?tgt ?cmp ?ecmp ?src =>
        rewrite (as_nth_tail cmp); rewrite (as_nth_tail ecmp); rewrite (as_nth_tail src);
         assert (wf_lang tgt) by prove_from_known_elabs
  end. break_preserving.
  cleanup_elab_after setup_elab_compiler.
  repeat Matches.t; cleanup_elab_after try (solve [ by_reduction ])

  auto_elab_compiler. Qed.
#[export] Hint Resolve cps_preserving : elab_pfs.




