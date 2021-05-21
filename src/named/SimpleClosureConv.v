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
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"val" %"G" %"A_fvs"
      ----------------------------------------------- ("ret_closure")
      (#"closure" %"A" %"e" (#"ret" %"fvs"))
      = #"ret" (#"closure_val" %"A" %"e" %"fvs")
      : #"exp" %"G" (#"clo" %"A" %"B")
  ];
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"val" %"G" %"A_fvs",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("closure_val_subst")
      #"val_subst" %"g" (#"closure_val" %"A" %"e" %"fvs")
      = #"closure_val" %"A" %"e" (#"val_subst" %"g" %"fvs")
      : #"val" %"G'" (#"clo" %"A" %"B")
  ];
  [:> "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
      "fvs" : #"exp" %"G" %"A_fvs",
      "G'" : #"ty",
      "g" : #"val" %"G'" %"G"
      ----------------------------------------------- ("closure_subst")
      #"el_subst" %"g" (#"closure" %"A" %"e" %"fvs")
      = #"closure" %"A" %"e" (#"el_subst" %"g" %"fvs")
      : #"exp" %"G'" (#"clo" %"A" %"B")
  ];
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
      (#"closure_val" %"A"
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
      #"clo_app" (#"ret" (#"closure_val" %"A" %"e" %"fvs")) (#"ret" %"v")
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
       #"closure_val" "A" "e" "fvs" : #"val" %"G" (#"clo" %"A" %"B")
  ];
    (* have an expression closure to evaluate fvs*)
  [:| "G" : #"ty",
       "A" : #"ty",
       "B" : #"ty",
       "A_fvs" : #"ty",
       "e" : #"exp" (#"prod" %"A_fvs" %"A") %"B",
       "fvs" : #"exp" %"G" %"A_fvs"
       -----------------------------------------------
       #"closure" "A" "e" "fvs" : #"exp" %"G" (#"clo" %"A" %"B")
  ];
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
    {{e #"closure_val" %"A" %"e" #"id"}}
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
