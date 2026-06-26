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

(* for induction on wfness of terms *)
From Pyrosome.Theory Require Import WfCutElim CutFreeInd.

(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilers. (* for parameterizing existing languages*)
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.

(* Now the compiler. Three parts: base identity compiler, then a first pass partial evaluation to get rid of #"All" in typerecs, and then a second pass to get rid of the boundaries *)
Local Notation compiler := (compiler string).

Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
  (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).


(* partial evaluator to get rid of type casing. *)
Definition func_partial_eval_ctx' :=
  Eval vm_compute in Rule.get_ctx (named_list_lookup default target_multilanguage "typerec func").

Definition comp_t1_type := {{s #"exp" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") "t1") "sigma") }}.

Definition comp_t2_type := {{s #"exp" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") "t2") "sigma") }}.

Definition func_partial_eval_ctx := Eval vm_compute in [("comp_t2", comp_t2_type); ("comp_t1", comp_t1_type); ("e3", named_list_lookup default func_partial_eval_ctx' "e3"); ("t2", named_list_lookup default func_partial_eval_ctx' "t2"); ("t1", named_list_lookup default func_partial_eval_ctx' "t1"); ("sigma", named_list_lookup default func_partial_eval_ctx' "sigma"); ("G", named_list_lookup default func_partial_eval_ctx' "G"); ("D", named_list_lookup default func_partial_eval_ctx' "D")]. 

Definition func_partial_eval_term_def := (* comp_t1 ie computation of type t1. cf substitution in meta_typerec *)
  {{e #"app" (#"@" (#"app" (#"@" "e3" "t1") "comp_t1") "t2") "comp_t2" }}.

Derive func_partial_eval_term
  in ( elab_term target_multilanguage
         func_partial_eval_ctx
         func_partial_eval_term_def
         func_partial_eval_term
         {{s #"exp" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") (#"->" "D" "t1" "t2")) "sigma") }}
     ) as func_partial_eval_term_wf. 
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

Fixpoint meta_typerec (D G mu sigma e1 e2 e3 : term) : term :=
  match mu with
  | {{e #"*" {_} }} => e1
  | {{e #"bool" {_} }} => e2
  | {{e #"->" {_} {t1} {t2} }} =>
      func_partial_eval_term [/ [ ("e3", e3);
                                  ("t1", t1);
                                  ("comp_t1", meta_typerec D G t1 sigma e1 e2 e3);
                                  ("t2", t2);
                                  ("comp_t2", meta_typerec D G t2 sigma e1 e2 e3);
                                  ("G", G);
                                  ("D", D) ] /]
  | _ => mu
  end.

Fixpoint elim_typerec (program : term) : term :=
  match program with
  | {{e #"typerec" {D} {G} {mu} {sigma} {e1} {e2} {e3} }} => meta_typerec D G mu sigma (elim_typerec e1) (elim_typerec e2) (elim_typerec e3)
  | con n s => con n (map elim_typerec s)
  | var n => var n
  end.

Fixpoint is_simple_type (mu : term) : Prop :=
  match mu with
  | {{e #"*" {_} }} => True
  | {{e #"bool" {_} }} => True
  | {{e #"->" {_} {t1} {t2} }} => is_simple_type t1 /\ is_simple_type t2
  | _ => False
  end.

Fixpoint all_typerecs_simple (program : term) : Prop :=
  match program with
  | {{e #"typerec" {D} {G} {mu} {sigma} {e1} {e2} {e3} }} =>
      is_simple_type mu /\
        all_typerecs_simple e1 /\ all_typerecs_simple e2 /\ all_typerecs_simple e3
  | con _ s => all all_typerecs_simple s
  | var _ => True
  end.

Ltac invert_wf_args :=
        match goal with
        | H : ComputeWf.wf_args _ _ _ _ |- _ => inversion H; clear H
        end.

Lemma no_sort_eqns_in_sml : Is_true (no_sort_eqns source_multilanguage).
Proof. apply I. Qed. 
Check sort_names_equal.

Lemma source_multilanguage_wf : wf_lang source_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition source_multilanguage_entry :=
  lang_entry source_multilanguage_wf.
#[export] Hint Resolve source_multilanguage_entry : wf_lang_db.

Lemma ty_eq_sort_lemma : forall (t : sort), Core.wf_sort source_multilanguage [] t -> eq_sort source_multilanguage [] t {{s #"ty"}} <-> t = {{s #"ty" }}.
Proof.
  intros; inversion H;
    repeat (simpl in H0; destruct H0;
            [> first [ solve [ injection H0; intros HF; inversion HF ]
                     | solve [ apply conj; inversion H0; intros;
                               [ subst; apply (sort_names_equal source_multilanguage_wf no_sort_eqns_in_sml wf_ctx_nil) in H4; inversion H4
                               | discriminate ] ]
                     | solve [ apply conj; intros; inversion H0; rewrite <- H7 in H1; inversion H1;
                               [ reflexivity
                               | pose proof source_multilanguage_wf; sort_cong ] ] ]
            | .. ]); 
    destruct H0.
Qed.

Lemma ty_inversion_lemma' : forall (t : sort) (e : term),
    Core.wf_sort source_multilanguage [] t -> Core.wf_term source_multilanguage [] e t -> t = {{s #"ty" }} -> e = {{e #"*" }}  \/ e = {{e #"bool" }} \/ (exists a b, Core.wf_term source_multilanguage [] a {{s #"ty" }} /\ Core.wf_term source_multilanguage [] b {{s #"ty" }} /\ e = {{e #"->" {a} {b} }} ).
Proof.
  induction 2 using wf_term_cut_ind.
  - unshelve (repeat (destruct H0;
                      [> first [ solve [ injection H0; intros HF; inversion HF ]
                               | solve [ inversion H0; intros Ht; inversion Ht ]
                               | shelve ] | .. ]); destruct H0).
    + inversion H0; intros Ht; rewrite <- H5 in H1; repeat invert_wf_args. eauto. 
    + inversion H0; intros Ht; rewrite <- H5 in H1; repeat invert_wf_args. eauto. 
    + inversion H0; intros Ht; rewrite <- H5 in H1; repeat invert_wf_args. 
      rewrite <- H5 in H2; subst; destruct H2; repeat destruct H1.
      right. right. eauto. 
  - inversion H0.
  - intros Ht; rewrite Ht in H1.
    apply IHwf_term. 
    + rewrite <- Ht in H1. apply eq_sort_sym in H1. apply ty_eq_sort_lemma in Ht;
        [ eapply (eq_sort_wf_r source_multilanguage_wf wf_ctx_nil); apply H1 | apply H ]. 
    + apply ty_eq_sort_lemma;
        [ eapply (eq_sort_wf_l source_multilanguage_wf wf_ctx_nil); apply H1 | apply H1 ]. 
Qed.

Lemma ty_inversion_lemma : forall (e : term),
    Core.wf_term source_multilanguage [] e {{s #"ty" }} -> e = {{e #"*" }}  \/ e = {{e #"bool" }} \/ (exists a b, Core.wf_term source_multilanguage [] a {{s #"ty" }} /\ Core.wf_term source_multilanguage [] b {{s #"ty" }} /\ e = {{e #"->" {a} {b} }} ).
Proof.
  intros. eapply ty_inversion_lemma'.
  - assert (Core.wf_sort source_multilanguage {{c }} {{s #"ty" }});
      [ pose proof source_multilanguage_wf; compute_sort_wf | apply H0 ]. 
  - apply H.
  - reflexivity.
Qed.

Lemma compiled_types_are_simple :
  forall (t : sort) (e : term),
    Core.wf_term source_multilanguage [] e t -> t = {{s #"ty" }} ->
    is_simple_type (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e).
Proof.
  induction 1 using wf_term_cut_ind.
  - unshelve (repeat (destruct H;
                      [> first [ solve [ injection H; intros HF; inversion HF ]
                               | solve [ inversion H; intros Ht; inversion Ht ]
                               | shelve ] | .. ]); destruct H).
    + inversion H; intros Ht; rewrite <- H4 in H0; repeat invert_wf_args; vm_compute; apply I. 
    + inversion H; intros Ht; rewrite <- H4 in H0; repeat invert_wf_args; vm_compute; apply I. 
    + inversion H. intros Ht. rewrite <- H4 in H0. repeat invert_wf_args. subst. destruct H1;  repeat destruct H0. simpl in Ht.
      cbv [apply_subst] in H2; simpl in H2; cbv [apply_subst] in H1; simpl in H1.
      apply H1 in Ht.
      assert (Ht2 : {{s #"ty"}} = {{s #"ty"}}) by reflexivity. 
      apply H2 in Ht2. 
      simpl. apply conj; assumption.
  - inversion H.
  - intros Ht; rewrite Ht in H0. apply ty_eq_sort_lemma in H0.
    + apply IHwf_term in H0. apply H0.
    + eapply (eq_sort_wf_l source_multilanguage_wf wf_ctx_nil). apply H0.
Qed.

Ltac compute_match t :=
  let v := eval vm_compute in t in
    replace t with v by (vm_compute; reflexivity).

Theorem can_eliminate_typerec :
  forall (t: sort) (e : term),
    Core.wf_term source_multilanguage [] e t ->
    all_typerecs_simple (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e). 
Proof.
  induction 1 using wf_term_cut_ind.
  - unshelve (repeat (destruct H;
                      [> first [ solve [ injection H; intros HF; inversion HF ]
                               | injection H; intros H6 H5 H4 H3; rewrite <- H4 in H1; rewrite <- H4 in H0; cbn [compile]; compute_match (named_list_lookup_err (simple_multilang_compiler ++ interoperating_langs_compiler) name); rewrite <- H3; repeat invert_wf_args; subst; destruct H1; repeat destruct H0; cbn [map combine_r_padded] ]
                      | .. ]); destruct H).
    1-2: simpl in H14; apply ty_inversion_lemma in H14; try reflexivity;
    destruct H14 as [ HStar | [ HBool | HArrow ]];
        [ rewrite HStar; replace (compile (simple_multilang_compiler ++ interoperating_langs_compiler) {{e #"*"}}) with {{e #"*" #"ty_emp" }} by (vm_compute; reflexivity); cbn -[compile simple_multilang_compiler interoperating_langs_compiler]; repeat apply conj; apply I || assumption
        | rewrite HBool; replace (compile (simple_multilang_compiler ++ interoperating_langs_compiler) {{e #"bool"}}) with {{e #"bool" #"ty_emp" }} by (vm_compute; reflexivity); cbn -[compile simple_multilang_compiler interoperating_langs_compiler]; repeat apply conj; apply I || assumption
        | destruct HArrow as [ A [ B [ WfA [ WfB EAB ]]]]; cbn -[compile simple_multilang_compiler interoperating_langs_compiler]; apply compiled_types_are_simple in WfA; try reflexivity; apply compiled_types_are_simple in WfB; try reflexivity; repeat apply conj; try (apply I || assumption || rewrite EAB; apply conj; assumption) ].
    all: repeat apply conj; try assumption; apply I. Unshelve.
  - inversion H.
  - apply IHwf_term.
Qed.

Lemma target_multilanguage_wf : wf_lang target_multilanguage.
Proof. prove_by_lang_db. Qed.

Lemma no_sort_eqns_in_tml : Is_true (no_sort_eqns target_multilanguage).
Proof. apply I. Qed. 
Check sort_names_equal.

Lemma ty_env_eq_sort_lemma_tml : forall (t : sort), Core.wf_sort target_multilanguage [] t -> eq_sort target_multilanguage [] t {{s #"ty_env"}} <-> t = {{s #"ty_env" }}.
Proof.
  intros t H. inversion H. vm_compute in H0. 
    repeat (simpl in H0; destruct H0;
            [> first [ solve [ injection H0; intros HF; inversion HF ]
                     | solve [ apply conj; inversion H0; intros;
                               [ subst; apply (sort_names_equal target_multilanguage_wf no_sort_eqns_in_tml wf_ctx_nil) in H4; inversion H4
                               | discriminate ] ]
                     | solve [ apply conj; intros; inversion H0; rewrite <- H7 in H1; inversion H1;
                               [ reflexivity
                               | pose proof target_multilanguage_wf; sort_cong ] ] ]
            | .. ]); 
      destruct H0.
Qed.

Lemma ty_inversion_lemma_tml : forall (e ty_env : term),    
    Core.wf_term target_multilanguage [] e {{s #"ty" {ty_env} }} -> e = {{e #"*" {ty_env} }}  \/ e = {{e #"bool" {ty_env} }} \/ (exists a b, Core.wf_term source_multilanguage [] a {{s #"ty" {ty_env} }} /\ Core.wf_term source_multilanguage [] b {{s #"ty" {ty_env} }} /\ e = {{e #"->" {ty_env} {a} {b} }} ).
Proof. Admitted. (* STATEMENT IS NOT RIGHT!! product types and All types *)

(* 
(* OLD. Doesn't work for typerec because we don't have the inversion lemma and we have stuck terms with typerec *)
Theorem partial_eval_preserves_equality :
  forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    (* would need to say there are _no_ typerecs at all. that's a bit strong for what I had in mind. *)
    Core.eq_term target_multilanguage [] t e (elim_typerec e).
Proof.
  induction 1 using wf_term_cut_ind.
  - vm_compute in H. pose proof target_multilanguage_wf as tml_wf. 
    unshelve (repeat (destruct H;
                      [> first [ solve [ injection H; intros HF; inversion HF ]
                               | inversion H; rewrite <- H4 in H0; repeat invert_wf_args;
                                        subst; destruct H1; repeat destruct H0;
                                        setup_eq_terms; repeat eq_term_and_sort_solver ]
                      | .. ]); destruct H).
    + (* we need a type inversion lemma! *) admit. 
  - inversion H.
  - eq_term_and_sort_solver. 
Admitted.
 *)

(* Ltac compile_on := Transparent compile; Transparent simple_multilang_compiler; Transparent interoperating_langs_compiler. *)

(* Ltac compile_off := Opaque compile; Opaque simple_multilang_compiler; Opaque interoperating_langs_compiler. *)


Ltac do_substitutions := simpl; cbv [term_subst_lookup named_list_lookup]; simpl.
Ltac setup_eq_terms :=
  cbn [elim_typerec map]; do_substitutions; simpl in *; cbv [term_subst_lookup named_list_lookup] in *; simpl in *.
Ltac crush_eqs := do_substitutions; eauto using eq_term_conv.
Ltac sv :=
  match goal with
  | |- eq_term _ _ _ (con "typerec" _) _ => shelve
  | |- eq_term _ _ _ (con ?s _) (con ?s _) => term_cong; crush_eqs
  | |- eq_sort _ _ (scon ?s _) (scon ?s _) => sort_cong; crush_eqs
  | |- _ \/ _ => left
  | |- _ => eapply eq_term_conv; crush_eqs
  end.

Ltac contains_var t :=
  first
    [ is_var t
    | lazymatch t with
      | con ?n ?s =>
          first [ contains_var n | contains_var s ]
      | scon ?n ?s =>
          first [ contains_var n | contains_var s ]
      | cons ?n ?s =>
          first [ contains_var n | contains_var s ]
      end
    ].

Ltac act_depending_on_var e :=
  tryif contains_var e then
    idtac
    (* let x := fresh "c" in set (x := compile (simple_multilang_compiler ++ interoperating_langs_compiler) e) in * *)
  else 
    vm_compute in e.

Ltac generalize_compiles :=
  repeat match goal with
    | H : context[compile (simple_multilang_compiler ++ interoperating_langs_compiler) ?e] |- _ => act_depending_on_var e
    end.

Ltac collapse_match :=
  match goal with
  | |- context[match ?t with _ => _ end] =>
      let t' := eval vm_compute in t in
      change t with t'; compute_match t'
  end.

Ltac collapse_match_in H :=
  cbv [compile_sort] in H;
  match type of H with
  | context[match ?t with _ => _ end] =>
      let t' := eval vm_compute in t in
        change t with t' in H
  end.

Ltac collapse_match_in_hyps :=
  repeat match goal with
    | H : eq_term _ _ _ _ _ |- _ =>
        progress (repeat collapse_match_in H; cbv iota in H; cbv [map combine_r_padded] in H)
  | _ => idtac
    end.

Ltac remove_compile_sorts :=
  cbv [compile_sort]; repeat collapse_match; collapse_match_in_hyps.

Ltac setup_eq_goal H H0 H1 name :=
  injection H; intros Hsort Hargs H4 Hname; rewrite <- H4 in H0; cbn [compile]; 
      compute_match (named_list_lookup_err (simple_multilang_compiler ++ interoperating_langs_compiler) name); rewrite <- Hname;
      repeat invert_wf_args; subst; destruct H1; repeat destruct H0;
  remove_compile_sorts; cbv [map combine_r_padded].

Ltac first_pass :=
  do_substitutions; simpl in *; cbv [term_subst_lookup named_list_lookup_err] in *; simpl in *; sv; sv; sv; sv.

Ltac solve_eq_goal :=
  with_strategy opaque [compile simple_multilang_compiler interoperating_langs_compiler] first_pass; with_strategy transparent [compile simple_multilang_compiler interoperating_langs_compiler] simpl; repeat sv.

Check (elab_compiler_implies_preserving simple_multilang_compiler_preserving).


Lemma eq_sort_sml_implies_eq_sort_tml :
  forall (t t' : sort),
    eq_sort source_multilanguage [] t t' ->
    eq_sort target_multilanguage []
      (compile_sort (simple_multilang_compiler ++ interoperating_langs_compiler) t)
      (compile_sort (simple_multilang_compiler ++ interoperating_langs_compiler) t').
Proof. Admitted. 
  

Theorem partial_eval_preserves_equality :
forall (t: sort) (e : term),
    Core.wf_term source_multilanguage [] e t ->
    Core.eq_term
      target_multilanguage []
      (compile_sort (simple_multilang_compiler ++ interoperating_langs_compiler) t)
      (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e)
      (elim_typerec (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e)).
Proof.
  induction 1 using wf_term_cut_ind.
  - vm_compute in H. pose proof target_multilanguage_wf as tml_wf. 
    unshelve (repeat (destruct H;
                      [> first [ solve [ injection H; intros HF; inversion HF ]
                               | shelve ]
                      | .. ]); destruct H).
    1-2: admit.
    all: setup_eq_goal H H0 H1 name; solve_eq_goal.
  - inversion H.
  - apply eq_sort_sml_implies_eq_sort_tml in H0. sv. 
Admitted.

Definition target_multilanguage_without_typerec :=
  prod_ty_subst ++ prod_parameterized ++ (* can we also get rid of these? idt we partially evaluate that away but I think we could *)
    polymorphic_interoperating_langs.

Lemma target_multilanguage_without_typerec_wf : wf_lang target_multilanguage_without_typerec.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_without_typerec_entry :=
  lang_entry target_multilanguage_without_typerec_wf.
#[export] Hint Resolve target_multilanguage_without_typerec_entry : wf_lang_db.

Theorem partial_eval_wf_in_no_typerec_lang : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    Core.wf_term
      target_multilanguage_without_typerec
      []
      (elim_typerec e)
      t.
Proof. Admitted.

