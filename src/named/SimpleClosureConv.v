Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilersWithPrefix
     SimpleVSubst SimpleVSTLC SimpleProd Matches
 CatProd.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

(*TODO: construct the right hierarchy on top of cat;
  currently copy-pasted
*)
(*
Depends on: (rename _ cat), catprod
ob -> ty
arr -> val

expr extension
*)
Definition closure_lang :=
  [
  (*[:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"val" %"G" %"A_fvs"
      ----------------------------------------------- ("ret_closure")
      (#"closure" %"A" %"e" (#"ret" %"fvs"))
      = #"ret" (#"closure_val" %"A" %"e" %"fvs")
      : #"exp" %"G" (#"clo" %"A" %"B")
  ];*)
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"val" %"G" %"A_fvs",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("closure_subst")
      #"val_subst" %"g" (#"closure" %"A" %"e" %"fvs")
      = #"closure" %"A" %"e" (#"val_subst" %"g" %"fvs")
      : #"val" %"G'" (#"clo" %"A" %"B")
  ];
  (*
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"exp" %"G" %"A_fvs",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("closure_subst")
      #"el_subst" %"g" (#"closure_exp" %"A" %"e" %"fvs")
      = #"closure" %"A" %"e" (#"el_subst" %"g" %"fvs")
      : #"exp" %"G'" (#"clo" %"A" %"B")
  ];*)
  [:> "G" : #"ty", "A" : #"ty", "B" : #"ty",
      "e" : #"exp" %"G" (#"clo" %"A" %"B"),
      "e'" : #"exp" %"G" %"A",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("clo_app_subst")
      #"el_subst" %"g" (#"clo_app" %"e" %"e'")
      = #"clo_app" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"exp" %"G'" %"B"
  ];
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" %"G" (#"clo" %"A" %"B")
      ----------------------------------------------- ("clo_eta")
      (#"closure" %"A"
        (#"clo_app" (#"ret" (#"val_subst" #".1" %"v")) (#"ret" #".2"))
        #"id")
      = %"v"
      : #"val" %"G" (#"clo" %"A" %"B")
  ];
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"val" %"G" %"A_fvs",
      "v" : #"val" %"G" %"A"
      ----------------------------------------------- ("clo_beta")
      #"clo_app" (#"ret" (#"closure" %"A" %"e" %"fvs")) (#"ret" %"v")
      = #"el_subst" (#"pair" %"fvs" %"v") %"e"
      : #"exp" %"G" %"B"
  ];
  [:| "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" %"G" (#"clo" %"A" %"B"),
       "e'" : #"exp" %"G" %"A"
       -----------------------------------------------
       #"clo_app" "e" "e'" : #"exp" %"G" %"B"
  ];
  [:| "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "A_fvs" : #"ty",
       "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
       "fvs" : #"val" %"G" %"A_fvs"
       -----------------------------------------------
       #"closure" "A" "e" "fvs" : #"val" %"G" (#"clo" %"A" %"B")
  ];
    (* we could add an expression closure to evaluate fvs
  [:| "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "A_fvs" : #"ty",
       "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
       "fvs" : #"exp" %"G" %"A_fvs"
       -----------------------------------------------
       #"closure_exp" "A" "e" "fvs" : #"exp" %"G" (#"clo" %"A" %"B")
  ];*)
  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"clo" "A" "B" : #"ty"
  ]]%arule
    ++
    (*****************************
      TODO: move language below out into multiple 
      dependencies

     *********************************)
    [[:> "G" : #"ty", "A" : #"ty"
       ----------------------------------------------- ("pair_wkn_hd")
        #"pair" #".1" #".2" = #"id" : #"val" (#"prod" %"G" %"A") (#"prod" %"G" %"A")
   ];
   [:> "G1" : #"ty", "G2" : #"ty", "G3" : #"ty",
       "f" : #"val" %"G1" %"G2",
       "g" : #"val" %"G2" %"G3",
       "A" : #"ty",
       "v" : #"val" %"G2" %"A"
       ----------------------------------------------- ("val_subst_pair")
       #"val_subst" %"f" (#"pair" %"g" %"v")
       = #"pair" (#"val_subst" %"f" %"g") (#"val_subst" %"f" %"v")
       : #"val" %"G1" (#"prod" %"G3" %"A")
   ];
   [:> "G" : #"ty", "G'" : #"ty",
       "g" : #"val" %"G" %"G'",
       "A" : #"ty",
       "v" : #"val" %"G" %"A"
       ----------------------------------------------- ("pair_hd")
       #"val_subst" (#"pair" %"g" %"v") #".2" = %"v"
       : #"val" %"G" %"A"
  ];
  [:> "G" : #"ty", "G'" : #"ty",
      "g" : #"val" %"G" %"G'",
      "A" : #"ty",
      "v" : #"val" %"G" %"A"
      ----------------------------------------------- ("wkn_pair")
      #"val_subst" (#"pair" %"g" %"v") #".1" = %"g" : #"val" %"G" %"G'"
  ];
  [:| "G" : #"ty", "A" : #"ty"
       -----------------------------------------------
       #".2" : #"val" (#"prod" %"G" %"A") %"A"
  ];
  [:| "G" : #"ty", "A" : #"ty"
       -----------------------------------------------
       #".1" : #"val" (#"prod" %"G" %"A") %"G"
  ];
  [:| "G" : #"ty", "G'" : #"ty", "A" : #"ty",
      "g" : #"val" %"G" %"G'",
      "v" : #"val" %"G" %"A" (*we restrict substitutions to values *)
       -----------------------------------------------
       #"pair" "g" "v" : #"val" %"G" (#"prod" %"G'" %"A")
  ];
  [:| "G" : #"ty", "A": #"ty"
       -----------------------------------------------
       #"prod" "G" "A" : #"ty"
  ];
    (*TODO: generalize to all programs of type unit?*)
  [:> 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"val" #"unit" #"unit"
  ];
  [:> "G" : #"ty", "G'" : #"ty", "g" : #"val" %"G" %"G'"
       ----------------------------------------------- ("val_subst_forget")
       #"val_subst" %"g" #"forget" = #"forget" : #"val" %"G" #"unit"
  ];
  [:| "G" : #"ty" 
      -----------------------------------------------
      #"forget" : #"val" %"G" #"unit"
  ];
  [:| 
      -----------------------------------------------
      #"unit" : #"ty"
  ];
  [:> "G1" : #"ty", "G2" : #"ty",
       "g" : #"val" %"G1" %"G2",
       "A" : #"ty", "v" : #"val" %"G2" %"A"
       ----------------------------------------------- ("el_subst_ret")
       #"el_subst" %"g" (#"ret" %"v")
       = #"ret" (#"val_subst" %"g" %"v")
       : #"exp" %"G1" %"A"
  ];
  [:| "G" : #"ty", "A" : #"ty", "v" : #"val" %"G" %"A"
       -----------------------------------------------
       #"ret" "v" : #"exp" %"G" %"A"
  ];
  [:> "G1" : #"ty", "G2" : #"ty", "G3" : #"ty",
       "f" : #"val" %"G1" %"G2", "g" : #"val" %"G2" %"G3",
       "A" : #"ty", "e" : #"exp" %"G3" %"A"
       ----------------------------------------------- ("el_subst_val_subst")
       #"el_subst" %"f" (#"el_subst" %"g" %"e")
       = #"el_subst" (#"val_subst" %"f" %"g") %"e"
       : #"exp" %"G1" %"A"
  ]; 
  [:> "G" : #"ty", "A" : #"ty", "e" : #"exp" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"exp" %"G" %"A"
  ]; 
  [:| "G" : #"ty", "G'" : #"ty", "g" : #"val" %"G" %"G'",
       "A" : #"ty", "e" : #"exp" %"G'" %"A"
       -----------------------------------------------
       #"el_subst" "g" "e" : #"exp" %"G" %"A"
  ]; 
  [s| "G" : #"ty", "A" : #"ty"
      -----------------------------------------------
      #"exp" "G" "A" srt
  ];
   [:> "G1" : #"ty",
         "G2" : #"ty",
         "G3" : #"ty",
         "G4" : #"ty",
         "f" : #"val" %"G1" %"G2",
         "g" : #"val" %"G2" %"G3",
         "h" : #"val"%"G3" %"G4"
         ----------------------------------------------- ("val_subst_assoc")
         #"val_subst" %"f" (#"val_subst" %"g" %"h")
         = #"val_subst" (#"val_subst" %"f" %"g") %"h"
         : #"val" %"G1" %"G4"
  ];  
  [:> "G" : #"ty", "G'" : #"ty", "f" : #"val" %"G" %"G'"
       ----------------------------------------------- ("id_left")
       #"val_subst" #"id" %"f" = %"f" : #"val" %"G"%"G'"
  ];
  [:> "G" : #"ty", "G'" : #"ty", "f" : #"val" %"G" %"G'"
      ----------------------------------------------- ("id_right")
      #"val_subst" %"f" #"id" = %"f" : #"val" %"G" %"G'"
  ];
  [:| "G1" : #"ty", "G2" : #"ty", "G3" : #"ty",
       "f" : #"val" %"G1" %"G2",
       "g" : #"val" %"G2" %"G3"
       -----------------------------------------------
       #"val_subst" "f" "g" : #"val" %"G1" %"G3"
  ];
  [:| "G" : #"ty" 
       -----------------------------------------------
       #"id" : #"val" %"G" %"G"
  ];
  [s| "G" : #"ty", "G'" : #"ty" 
      -----------------------------------------------
      #"val" "G" "G'" srt                     
  ];
  [s|
      -----------------------------------------------
      #"ty" srt
   ]]%arule.


Derive closure_elab
       SuchThat (Pre.elab_lang [] closure_lang closure_elab)
       As closure_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve closure_wf : elab_pfs.

(*TODO: write with target having a single type as its context.
   - Change lang above to match
   - collapses the diff. between a subst and a term
  TODO: complex values make sub a value; desirable or no?
*)
Definition cc : compiler :=
  match # from (stlc_elab ++ subst_elab) with
  | {{s #"env" }} => {{s #"ty"}}
  | {{s #"sub" "G" "G'"}} => {{s #"val" %"G" %"G'"}}
  | {{e #"id" "G"}} => {{e #"id"}}
  | {{e #"cmp" "G1" "G2" "G3" "f" "g"}} => {{e #"val_subst" %"f" %"g"}}
  | {{s #"el" "G" "A"}} => {{s #"exp" %"G" %"A" }}
  (*TODO: rename target to exp_subst*)
  | {{e #"el_subst" "G1" "G2" "f" "A" "e"}} => {{e #"el_subst" %"f" %"e"}}
  | {{s #"val" "G" "A"}} => {{s #"val" %"G" %"A" }}
  | {{e #"val_subst" "G1" "G2" "f" "A" "v"}} => {{e #"val_subst" %"f" %"v"}}
  | {{e #"ret" "G" "A" "v" }} => {{e #"ret" %"v"}}
  | {{e #"ext" "G" "A"}} => {{e #"prod" %"G" %"A" }}
  | {{e #"emp" }} => {{e #"unit"}}
  | {{e #"snoc" "G" "G'" "A" "g" "v"}} => {{e #"pair" %"g" %"v"}}
  (*Note that we need complex values here to accommodate this projection *)
  | {{e #"wkn" "G" "A"}} => {{e #".1" }}
  | {{e #"hd" "G" "A"}} => {{e #".2" }}
  | {{e #"->" "A" "B"}} => {{e #"clo" %"A" %"B" }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"closure" %"A" %"e" #"id"}}
  | {{e #"app" "G" "A" "B" "e" "e'"}} =>
    {{e #"clo_app" %"e" %"e'"}}
  end.

(*TODO: move *)

Inductive names_match (A B : Type) : named_list A -> named_list B -> Type :=
    nm_nil : names_match [] []
  | nm_cons : forall (a : A) (a' : B) l l' n,
      names_match l l' -> names_match ((n,a) :: l) ((n,a') :: l').
#[export] Hint Constructors names_match : lang_core.

Lemma eq_term_by'_right name l c e1 e2 t c' e1' e2' t' s s'
  : wf_lang l ->
    In [:> ! c
           ----------------------------------------------- (name)
           {e1} = {e2} : {t}
       ]%arule l ->
    names_match c s ->
    matches_unordered e2' e2 = Some s' ->
    incl s' s ->
    e2' = e2[/s/] ->
    e1' = e1[/s/] ->
    t' = t[/s/] ->
    wf_subst l c' s c ->
    eq_term l c' t' e1' e2'.
Proof.
  intros; subst.
  eapply eq_term_subst; [| eapply eq_subst_refl; eassumption | ..].
  use_rule_in_wf; basic_core_crush.
  basic_core_crush.
Qed.

Arguments eq_term_by'_right _ : clear implicits.

Derive cc_elab
       SuchThat (elab_preserving_compiler [] closure_elab
                                          cc cc_elab (stlc_elab ++ subst_elab))
       As cc_elab_preserving.
Proof.
  
  (*TODO: replace the original with this*)
  Ltac term_cong ::=
  eapply term_con_congruence;
   [ solve_in
   | solve_len_eq
   | compute; reflexivity
   | eauto with elab_pfs auto_elab
   | repeat
      match goal with
      | |- eq_args _ _ _ _ _ =>
            simple apply eq_args_nil || simple eapply eq_args_cons2 || simple eapply eq_args_cons
      end ].

  setup_elab_compiler; repeat t.
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].

  
  compute_eq_compilation.
  eapply eq_term_trans.
  reduce.
  eapply eq_term_sym.
  eapply eq_term_trans.
  reduce.
  eapply eq_term_trans.
  2:{
    eapply (eq_term_by'_right "clo_eta").
    eauto with auto_elab elab_pfs.
    solve_in.
    eauto with lang_core.
    compute;reflexivity.
    {
      repeat (rewrite incl_cons).
      intuition.
    }
    compute; reflexivity.
    compute; reflexivity.
    compute; reflexivity.
    repeat apply wf_subst_cons.
    constructor.
    repeat t'.
    repeat t'.
    repeat t'.
    repeat t'.
  }
  term_cong.
  term_refl.
  term_refl.
  term_refl.
  term_refl.
  compute_eq_compilation.
  {
    eapply eq_term_sym.
    eapply eq_term_trans.
    reduce.
    term_refl.
  }
  term_refl.
   
  Unshelve.
  all: repeat t'; eauto
   with elab_pfs auto_elab.
Qed.
#[export] Hint Resolve cc_elab_preserving : elab_pfs.


(*TODO: move to right place*)
Lemma elab_preserving_embed tgt' tgt cmp cmp_elab src
  : incl tgt tgt' ->
    ElabCompilers.elab_preserving_compiler tgt cmp cmp_elab src ->
    ElabCompilers.elab_preserving_compiler tgt' cmp cmp_elab src.
Proof.
  induction 2; basic_goal_prep; constructor; basic_core_crush.
  eauto using eq_sort_lang_monotonicity.
  eauto using eq_term_lang_monotonicity.
Qed.

Require Import CompilerForExt SimpleEvalCtx.

Lemma cc_with_eval_ctx
  : (ElabCompilers.elab_preserving_compiler (compile_ext cc_elab eval_ctx_elab ++ closure_elab)
                                           (ext_id eval_ctx_elab ++ cc)
                                           (ext_id_elab eval_ctx_elab ++ cc_elab)
                                           (eval_ctx_elab ++ stlc_elab ++ subst_elab)).
Proof.
  apply elab_compiler_prefix_implies_elab.
  2: {
    apply extension_preservation.
    apply use_compute_lang_args_sublist.
    compute; reflexivity.
  }
  eapply elab_preserving_embed.
  2:{
    rewrite (app_nil_end cc).
    rewrite (app_nil_end cc_elab).
    rewrite (app_nil_end (stlc_elab ++ subst_elab)).
    apply elab_compiler_prefix_implies_elab.
    constructor.
    apply cc_elab_preserving.
  }
  apply incl_appr.
  basic_utils_crush.
Qed.

Eval compute in (compile_ext cc subst_eval_ctx).

Definition clo_ctx : lang :=
  [
  [:> "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" %"A",
       "v" : #"val" %"G" (#"clo" %"A" %"B"),
       "e" : #"exp" %"G" %"C"
       ----------------------------------------------- ("plug clo_app_r")
       #"plug" (#"Eclo_app_r" %"v" %"E") %"e"
       = #"clo_app" (#"ret" %"v") (#"plug" %"E" %"e")
      : #"exp" %"G" %"B"
  ];
     [:> "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" (#"clo" %"A" %"B"),
       "e'" : #"exp" %"G" %"A",
       "e" : #"exp" %"G" %"C"
       ----------------------------------------------- ("plug app_l")
       #"plug" (#"Eclo_app_l" %"E" %"e'") %"e"
       = #"clo_app" (#"plug" %"E" %"e") %"e'"
      : #"exp" %"G" %"B"
  ];
  [:| "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "v" : #"val" %"G" (#"clo" %"A" %"B"),
       "E" : #"Ectx" %"G" %"C" %"A"
       -----------------------------------------------
       #"Eclo_app_r" "v" "E" : #"Ectx" %"G" %"C" %"B"
  ];
  [:| "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" (#"clo" %"A" %"B"),
       "e'" : #"exp" %"G" %"A"
       -----------------------------------------------
       #"Eclo_app_l" "E" "e'" : #"Ectx" %"G" %"C" %"B"
  ];
  [:> "G" : #"ty", "A" : #"ty", "e" : #"exp" %"G" %"A"
     ----------------------------------------------- ("plug hole")
     #"plug" #"[ ]" %"e" = %"e" : #"exp" %"G" %"A"
 ];
[:| "G" : #"ty", "A" : #"ty", "B" : #"ty", "E" : #"Ectx" %"G" %"A" %"B", "e" : #"exp" %"G" %"A"
    -----------------------------------------------
    #"plug" "E" "e" : #"exp" %"G" %"B"
];
  [:| "G" : #"ty", "A" : #"ty"
             -----------------------------------------------
             #"[ ]" : #"Ectx" %"G" %"A" %"A"
         ];
  [s| "G" : #"ty", "A" : #"ty", "B" : #"ty"
                      -----------------------------------------------
                      #"Ectx" "G" "A" "B" srt
                  ]
  ]%arule.


(*TODO: to do this in a more principled way and use properties of compile_ext,
  need a lemma that compile_ext is wf 
 *)
Derive clo_ctx_elab
       SuchThat (Pre.elab_lang closure_elab
                               clo_ctx
                               clo_ctx_elab)
       As clo_ctx_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve clo_ctx_wf : elab_pfs.

Definition cc_ctx : compiler :=
  match # from (Estlc_elab ++ eval_ctx_elab) with
  | {{e #"Eapp_l" "G" "A" "B" "C" "E" "e'"}} =>
    {{e #"Eclo_app_l" %"E" %"e'"}}
  | {{e #"Eapp_r" "G" "A" "B" "C" "v" "E"}} =>
    {{e #"Eclo_app_r" %"v" %"E"}}
  end.

Eval compute in cc_ctx.

Derive cc_ctx_elab
       SuchThat (elab_preserving_compiler cc_elab
                                          (clo_ctx_elab ++ closure_elab)
                                          cc_ctx cc_ctx_elab (Estlc_elab ++ eval_ctx_elab))
       As cc_ctx_elab_preserving.
Proof.
  auto_elab_compiler.
Qed.
#[export] Hint Resolve cc_ctx_elab_preserving : elab_pfs.


(*
TODO: use compilerforext to pull this through
via theorems, not copying

 *)

Definition bool_lang_cc :=
  [
    (*TODO: add if; add subst rules*)
    [:| "G" : #"ty"
        -----------------------------------------------
        #"false" : #"val" %"G" #"bool"
     ];
    [:| "G" : #"ty"
        -----------------------------------------------
        #"true" : #"val" %"G" #"bool"
     ];
    [:| 
        -----------------------------------------------
        #"bool" : #"ty"
  ]]%arule.

Derive bool_elab_cc
       SuchThat (Pre.elab_lang closure_elab bool_lang_cc bool_elab_cc)
       As bool_lang_cc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve bool_lang_cc_wf : elab_pfs.


(*depends on bool, eval_ctx*)
Definition global_cell_cc :=
  [
  [:> "S" : #"val" #"unit" #"bool",
      "v" : #"val" #"unit" #"bool",
      "A" : #"ty",            
      "E" : #"Ectx" #"unit" #"bool" %"A"
      ----------------------------------------------- ("eval_swap")
      #"mk_config" %"S" (#"plug" %"E" (#"swap" %"v"))
      = #"mk_config" %"v" (#"plug" %"E" (#"ret" %"S"))
      : #"config" %"A"
  ];
  [:> "S" : #"val" #"unit" #"bool",
      "A" : #"ty",            
      "E" : #"Ectx" #"unit" #"bool" %"A"
      ----------------------------------------------- ("eval_get")
      #"mk_config" %"S" (#"plug" %"E" #"get")
      = #"mk_config" %"S" (#"plug" %"E" (#"ret" %"S"))
      : #"config" %"A"
  ];
    [:| "S" : #"val" #"unit" #"bool",
        "A" : #"ty", "e" : #"exp" #"unit" %"A"                    
       -----------------------------------------------
       #"mk_config" "S" "e" : #"config" %"A"
  ];
    [s| "A" : #"ty"                   
       -----------------------------------------------
       #"config" "A" srt
  ];
  [:> "G" : #"ty",
      "v" : #"val" %"G" #"bool",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("swap_subst")
      #"el_subst" %"g" (#"swap" %"v")
      = #"swap" (#"val_subst" %"g" %"v")
      : #"exp" %"G'" #"bool"
  ];
  [:> "G" : #"ty",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("get_subst")
      #"el_subst" %"g" (#"get") = #"get" : #"exp" %"G'" #"bool"
  ];
  [:| "G" : #"ty", "v" : #"val" %"G" #"bool"
       -----------------------------------------------
       #"swap" "v" : #"exp" %"G" #"bool"
  ];
     [:| "G" : #"ty"
       -----------------------------------------------
       #"get" : #"exp" %"G" #"bool"
  ]]%arule.

Derive global_cell_elab_cc
       SuchThat (Pre.elab_lang (bool_elab_cc ++ clo_ctx_elab ++ closure_elab)
                               global_cell_cc
                               global_cell_elab_cc)
       As global_cell_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve global_cell_wf : elab_pfs.


(*TODO: make an empty match work?*)
Definition cc_global_cell : compiler :=
  match # from (global_cell_elab_cc ++ bool_elab_cc) with
  | {{e #"bool"}} => {{e#"bool"}}
  end.

Eval compute in cc_global_cell.

Require Import GlobalCell.

Derive cc_global_cell_elab
       SuchThat (elab_preserving_compiler (cc_ctx_elab ++ cc_elab)
                                          (global_cell_elab_cc ++ bool_elab_cc ++ clo_ctx_elab ++ closure_elab)
                                          cc_global_cell cc_global_cell_elab (global_cell_elab ++ bool_elab))
       As cc_global_cell_elab_preserving.
Proof.  
  auto_elab_compiler.
  eauto 8 with elab_pfs auto_elab.
  eauto 8 with elab_pfs auto_elab.
  eauto 8 with elab_pfs auto_elab.
  eauto 8 with elab_pfs auto_elab.
Qed.
#[export] Hint Resolve cc_global_cell_elab_preserving : elab_pfs.

Eval compute in cc_global_cell_elab.

(*TODO: move*)
Lemma elab_prefix_implies_elab_compiler tgt cmp ecmp src cmp' ecmp' src'
  : ElabCompilers.elab_preserving_compiler tgt cmp ecmp src ->
    elab_preserving_compiler ecmp tgt cmp' ecmp' src' ->
    ElabCompilers.elab_preserving_compiler tgt (cmp'++cmp) (ecmp'++ecmp) (src'++src).
Proof.
  induction 2; basic_goal_prep; basic_core_crush.
  all: constructor; basic_core_crush.
Qed.

(*TODO: move somewhere*)
Lemma elab_prefix_implies_elab_compiler' tgt cmp ecmp src tgt' cmp' ecmp' src'
  : ElabCompilers.elab_preserving_compiler tgt cmp ecmp src ->
    elab_preserving_compiler ecmp tgt' cmp' ecmp' src' ->
    incl tgt tgt' ->
    ElabCompilers.elab_preserving_compiler tgt' (cmp'++cmp) (ecmp'++ecmp) (src'++src).
Proof.
  intros.
  pose proof (elab_preserving_embed H1 H).
  apply elab_prefix_implies_elab_compiler; assumption.
Qed.
Hint Resolve elab_prefix_implies_elab_compiler' : auto_elab.

(* TODO: move somewhere*)
Lemma elab_prefix_implies_elab_compiler_nil tgt cmp ecmp src
  : elab_preserving_compiler [] tgt cmp ecmp src ->
    ElabCompilers.elab_preserving_compiler tgt cmp ecmp src.
Proof.
  rewrite (app_nil_end cmp) at 2.
  rewrite (app_nil_end ecmp) at 2.
  rewrite (app_nil_end src) at 2.
  eapply elab_prefix_implies_elab_compiler.
  constructor.
Qed.
#[export] Hint Resolve elab_prefix_implies_elab_compiler_nil : auto_elab.
#[export] Hint Resolve elab_prefix_implies_elab_compiler' : auto_elab.
#[export] Hint Resolve ElabCompilers.elab_compiler_implies_preserving : auto_elab.

Lemma sum_compiler
  : preserving_compiler (global_cell_elab_cc ++ bool_elab_cc ++ clo_ctx_elab ++ closure_elab)
                        ((cc_global_cell_elab ++ cc_ctx_elab ++ cc_elab))
                        (((global_cell_elab ++ bool_elab)
                            ++ (Estlc_elab ++ eval_ctx_elab)
                            ++ (stlc_elab ++ subst_elab))).
Proof.
  eauto 10 with elab_pfs auto_elab utils.
Qed.

Eval compute in ((cc_global_cell_elab ++ cc_ctx_elab ++ cc_elab)).
