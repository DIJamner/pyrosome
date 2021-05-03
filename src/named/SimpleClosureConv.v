Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers
     SimpleVSubst SimpleVSTLC SimpleProd Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Definition closure_lang :=
  [
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"el" (#"ext" #"emp" (#"prod" %"A_fvs" %"A")) %"B",
      "fvs" : #"val" %"G" %"A_fvs"
      ----------------------------------------------- ("ret_closure")
      (#"closure" %"A" %"e" (#"ret" %"fvs"))
      = #"ret" (#"closure_val" %"A" %"e" %"fvs")
      : #"el" %"G" (#"clo" %"A" %"B")
  ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"el" (#"ext" #"emp" (#"prod" %"A_fvs" %"A")) %"B",
      "fvs" : #"val" %"G" %"A_fvs",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("closure_val_subst")
      #"val_subst" %"g" (#"closure_val" %"A" %"e" %"fvs")
      = #"closure_val" %"A" %"e" (#"val_subst" %"g" %"fvs")
      : #"val" %"G'" (#"clo" %"A" %"B")
  ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"el" (#"ext" #"emp" (#"prod" %"A_fvs" %"A")) %"B",
      "fvs" : #"el" %"G" %"A_fvs",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("closure_subst")
      #"el_subst" %"g" (#"closure" %"A" %"e" %"fvs")
      = #"closure" %"A" %"e" (#"el_subst" %"g" %"fvs")
      : #"el" %"G'" (#"clo" %"A" %"B")
  ];
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el"%"G" (#"clo" %"A" %"B"),
      "e'" : #"el" %"G" %"A",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("clo_app_subst")
      #"el_subst" %"g" (#"clo_app" %"e" %"e'")
      = #"clo_app" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"el" %"G'" %"B"
  ];
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "A_fvs" : #"ty",
      "e" : #"el" (#"ext" #"emp" (#"prod" %"A_fvs" %"A")) %"B",
      "fvs" : #"val" %"G" %"A_fvs",
      "v" : #"val" %"G" %"A"
      ----------------------------------------------- ("clo_beta")
      #"clo_app" (#"ret" (#"closure_val" %"A" %"e" %"fvs")) (#"ret" %"v")
      = #"el_subst" (#"snoc" #"forget" (#"pair_val" %"fvs" %"v")) %"e"
      : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"el" %"G" (#"clo" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       #"clo_app" "e" "e'" : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "A_fvs" : #"ty",
       "e" : #"el" (#"ext" #"emp" (#"prod" %"A_fvs" %"A")) %"B",
       "fvs" : #"val" %"G" %"A_fvs"
       -----------------------------------------------
       #"closure_val" "A" "e" "fvs" : #"val" %"G" (#"clo" %"A" %"B")
  ];
    (* have an expression closure to evaluate fvs*)
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "A_fvs" : #"ty",
       "e" : #"el" (#"ext" #"emp" (#"prod" %"A_fvs" %"A")) %"B",
       "fvs" : #"el" %"G" %"A_fvs"
       -----------------------------------------------
       #"closure" "A" "e" "fvs" : #"el" %"G" (#"clo" %"A" %"B")
  ];
  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"clo" "A" "B" : #"ty"
    ]]%arule.

Derive closure_elab
       SuchThat (Pre.elab_lang (prod_elab ++ subst_elab) closure_lang closure_elab)
       As closure_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve closure_wf : elab_pfs.


Definition cc : compiler :=
  match # from (stlc_elab ++ subst_elab) with
  | {{s #"el" "G" "A"}} => {{s #"el" (#"ext" %"G" (#"->" %"A" #"bot")) #"bot" }}
  | {{e #"->" "A" "B"}} => {{e #"->" %"A" {double_neg (var "B")} }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"lambda" %"A" (#"ret" (#"lambda" (#"->" %"B" #"bot") %"e"))}}
  | {{e #"app" "G" "A" "B" "e" "e'"}} =>
    let k := {{e #"ret" {vwkn_n 2 {{e #"hd"}} } }} in
    let x1 := {{e #"ret" {vwkn_n 1 {{e #"hd"}} } }} in
    let x2 := {{e #"ret" #"hd"}} in
    bind_k 1 (var "e") {{e #"->" %"A" {double_neg (var "B")} }}
    (bind_k 2 (var "e'") (var "A")
    {{e #"app" (#"app" {x1} {x2}) {k} }})
  | {{e #"el_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    ret_val (var "v")
  end.


Derive cps_elab
       SuchThat (elab_preserving_compiler stlc_bot cps cps_elab (nth_tail 1 stlc_bot))
       As cps_elab_preserving.
Proof.
  pose proof stlc_bot_wf.
 match goal with
  | |- elab_preserving_compiler _ ?cmp ?ecmp ?src =>
        rewrite (as_nth_tail cmp); rewrite (as_nth_tail ecmp); rewrite (as_nth_tail src)
 end.


 break_preserving.

 all: try solve[ repeat t; repeat t'].
 all: try solve [is_term_rule].

 solve[ compute_eq_compilation;by_reduction].
 solve[ compute_eq_compilation;by_reduction].
 solve[ compute_eq_compilation;by_reduction].
 apply cps_subst_preserved.
 apply cps_beta_preserved.

 solve[ compute_eq_compilation;by_reduction].
 Unshelve.
 compute in cps_elab.
 all: repeat t'.
Qed.


Local Lemma stlc_wf' : wf_lang (nth_tail 1 stlc_bot).
Proof.
  change (nth_tail 1 stlc_bot) with (stlc_elab ++ subst_elab).
  eauto 7 with auto_elab elab_pfs.
Qed.

Goal semantics_preserving stlc_bot cps_elab (nth_tail 1 stlc_bot).
Proof.
  apply inductive_implies_semantic.
  - apply stlc_wf'.
  - apply stlc_bot_wf.
  - eauto using cps_elab_preserving with lang_core.
Qed.

(*
TODO: make proof generate fully evalled cps_elab to print w/ the notation
Eval compute in cps_elab.
*)
