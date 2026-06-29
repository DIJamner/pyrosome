Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from high_level_multilanguage with` *)
(* CompilerDefs, for preserving_compiler_ext, is already imported. Prolly through something else. *)

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

Require Coq.derive.Derive.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC. 
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import BoolType. 
From Pyrosome.Lang Require Import SimpleVProd.
From Pyrosome.Lang.Multilanguages Require Import SimpleBoundaries. 


(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.

Definition boundaries_parameterized := 
    let ps := (elab_param "D" (boundaries ++ stlc ++ typed_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps boundaries.
Local Definition evp'_boundaries : lang := 
    let ps := (elab_param "D" (boundaries ++ stlc ++ typed_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (stlc ++ typed_bool ++ untyped_bool ++ utlc ++ star_type ++ error_t ++ exp_ret ++ exp_subst_base ++ value_subst).
Lemma boundaries_parameterized_wf (* this is necessary *)
  : wf_lang_ext ((stlc_parameterized ++ typed_bool_parameterized ++ untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      boundaries_parameterized.
Proof. 
  replace (stlc_parameterized ++ typed_bool_parameterized ++ untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized ++ exp_parameterized ++ val_parameterized) with evp'_boundaries.
  - eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor
    | now prove_by_lang_db..
    | vm_compute; exact I].
  - cbv; reflexivity. 
Qed. 
#[local] Definition boundaries_parameterized_entry :=
  lang_entry boundaries_parameterized_wf.
#[export] Hint Resolve boundaries_parameterized_entry : wf_lang_db.

Lemma polymorphic_interoperating_langs_wf :
  wf_lang polymorphic_interoperating_langs.
Proof. prove_by_lang_db. Qed.
#[local] Definition polymorphic_interoperating_langs_entry :=
  lang_entry polymorphic_interoperating_langs_wf.
#[export] Hint Resolve polymorphic_interoperating_langs_entry : wf_lang_db.

(* Lemma boundaries_parameterized_wf_2 : *)
(*   wf_lang (boundaries_parameterized ++ polymorphic_interoperating_langs). *)
(* Proof. prove_by_lang_db. Qed.  *)

Definition boundaries_ty_subst_def := Eval vm_compute in ty_subst_def_maker boundaries_parameterized (stlc_parameterized ++ typed_bool_parameterized ++ untyped_bool_parameterized ++ utlc_parameterized ++ star_type_parameterized ++ error_t_parameterized).
Derive boundaries_ty_subst
  SuchThat (elab_lang_ext
              (boundaries_parameterized ++ polymorphic_interoperating_langs)
              boundaries_ty_subst_def
              boundaries_ty_subst)
  As boundaries_ty_subst_wf. 
Proof. auto_elab. Qed. 
#[local] Definition boundaries_ty_subst_entry :=
  lang_entry (elab_lang_implies_wf boundaries_ty_subst_wf).
#[export] Hint Resolve boundaries_ty_subst_entry : wf_lang_db.

Definition poly_boundaries_def : lang := (* Matthews and Findler figure 11, page 12:33 *)
  {[l/subst [exp_subst++value_subst] 
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"), (* tau in Matthews and Findler *)
        "e" : #"exp" "D" "G" #"*"
        ----------------------------------------------- ("dtt forall")
        #"dtt" (#"All" "A") "e" =
        #"ret" (#"Lam" (#"dtt" "A" (#"exp_ty_subst" #"ty_wkn" "e")))
        : #"exp" "D" "G" (#"All" "A")
    ]; 
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"), (* tau in Matthews and Findler *)
        "e" : #"exp" "D" "G" (#"All" "A")
        ----------------------------------------------- ("ttd forall")
        #"ttd" (#"All" "A") "e" =
        #"ttd" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A") (#"@" "e" #"*") : #"exp" "D" "G" #"*"
    ]     
  ]}.

Derive poly_boundaries
  SuchThat (elab_lang_ext (boundaries_ty_subst ++
                             boundaries_parameterized ++ polymorphic_interoperating_langs)
                poly_boundaries_def poly_boundaries)
        As poly_boundaries_wf.
Proof. auto_elab. Qed.
#[local] Definition poly_boundaries_entry :=
  lang_entry (elab_lang_implies_wf poly_boundaries_wf).
#[export] Hint Resolve poly_boundaries_entry : wf_lang_db.
(* Aight so the problem you were having had to do with names and prove_by_lang_db. I think the moral solution is to add ty_subst to all the wf proofs for ty_subst langs above. But whatever I did works enough it looks like. *)



(* Matthews and Findler have lump cancellation as a rule. But, we don't need that rule, (I think) because we've collapsed the Lump and TST types! *)
Definition lump_cancellation_term_unelab :=
  {{e #"ttd" #"*" (#"dtt" #"*" "e") }}. 
Derive lump_cancellation_term
  in ( elab_term
         (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
         [("e", {{s #"exp" "D" "G" (#"*" "D")}}); (* the order of these matters! *)
          ("G", {{s #"env" "D"}});
          ("D", {{s #"ty_env"}})]
         lump_cancellation_term_unelab
         lump_cancellation_term
         {{s #"exp" "D" "G" (#"*" "D") }}
     ) as lump_cancellation_term_wf. 
Proof.
  solve_elab_term_or_sort (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs).
Qed.

Lemma lump_cancellation_holds :
  eq_term
    (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
    [("e", {{s #"exp" "D" "G" (#"*" "D")}}); (* the order of these matters! *)
     ("G", {{s #"env" "D"}});
     ("D", {{s #"ty_env"}})]
    {{s #"exp" "D" "G" (#"*" "D") }}
    {{e "e" }}
    lump_cancellation_term.
Proof.
  assert (wf_lang (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)) by prove_by_lang_db; by_reduction.
Qed.



(* Now the compiler. Three parts: base identity compiler, then a first pass partial evaluation to get rid of #"All" in typerecs, and then a second pass to get rid of the boundaries *)
Local Notation compiler := (compiler string).

Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
  (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

Definition polymorphic_interoperating_langs_compiler :=
  id_compiler polymorphic_interoperating_langs.

Lemma polymorphic_interoperating_langs_compiler_preserving :
  preserving_compiler_ext
    polymorphic_interoperating_langs
    []
    polymorphic_interoperating_langs_compiler
    polymorphic_interoperating_langs.
Proof.
  apply id_compiler_preserving; [ typeclasses eauto | prove_by_lang_db ]. 
Qed.
#[local] Definition polymorphic_interoperating_langs_compiler_entry :=
  cmp_entry polymorphic_interoperating_langs_compiler_preserving.
#[export] Hint Resolve polymorphic_interoperating_langs_compiler_entry : preserving_db.

(* begin getting the partial evaluator *)
Definition dtt_forall_partial_eval_ctx :=
  Eval vm_compute in Rule.get_ctx (named_list_lookup default poly_boundaries "dtt forall").

Definition dtt_forall_partial_eval_term_def :=
  {{e #"ret" (#"Lam" (#"dtt" "A" (#"exp_ty_subst" #"ty_wkn" "e"))) }}. 

Derive dtt_forall_partial_eval_term
  in ( elab_term (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
         dtt_forall_partial_eval_ctx
         dtt_forall_partial_eval_term_def
         dtt_forall_partial_eval_term
         {{s #"exp" "D" "G" (#"All" "D" "A") }}
     ) as dtt_forall_partial_eval_term_wf. 
Proof.
  solve_elab_term_or_sort (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs).
Qed.

Definition ttd_forall_partial_eval_ctx :=
  Eval vm_compute in Rule.get_ctx (named_list_lookup default poly_boundaries "ttd forall").

Definition ttd_forall_partial_eval_term_def :=
  {{e #"ttd" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A") (#"@" "e" #"*") }}.

Derive ttd_forall_partial_eval_term
  in ( elab_term (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs)
         ttd_forall_partial_eval_ctx
         ttd_forall_partial_eval_term_def
         ttd_forall_partial_eval_term
         {{s #"exp" "D" "G" (#"*" "D") }}
     ) as ttd_forall_partial_eval_term_wf. 
Proof.
  solve_elab_term_or_sort (poly_boundaries ++ boundaries_ty_subst ++ boundaries_parameterized ++ polymorphic_interoperating_langs).
Qed.

Fixpoint forall_partial_eval (program : term) : term :=
  match program with
  | {{e #"dtt" {D} {G} (#"All" {_} {A}) {e} }} =>
      dtt_forall_partial_eval_term [/ [ ("e", e); ("A", A); ("G", G); ("D", D) ] /]
  | {{e #"ttd" {D} {G} (#"All" {_} {A}) {e} }} =>
      ttd_forall_partial_eval_term [/ [ ("e", e); ("A", A); ("G", G); ("D", D) ] /]
  | con n s => con n (map forall_partial_eval s)
  | var n => var n
  end.

(* poly to poly compiler *)
Definition poly_multilang_compiler_def : compiler :=
  match # from boundaries_parameterized with
  | {{e #"dtt" "D" "G" "A" "e"}} => {{e #"app" (#".2" {trec_boundaries_unelab}) "e" }}
  | {{e #"ttd" "D" "G" "A" "e"}} => {{e #"app" (#".1" {trec_boundaries_unelab}) "e" }}
    (* we don't need a type variable case, since it's the same as the old compiler! *)
  end.
(* Derive poly_multilang_compiler  *)
(*   SuchThat (elab_preserving_compiler  *)
(*               interoperating_langs_compiler *)
(*               target_multilanguage *)
(*               poly_multilang_compiler_def *)
(*               poly_multilang_compiler *)
(*               boundaries)  *)
(*   As poly_multilang_compiler_preserving.  *)
(* Proof. solve_multilang_compiler. Qed.  *)
