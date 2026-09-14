Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Compilers.SemanticsPreservingDef
  Compilers.CompilerFacts Elab.ElabCompilers.
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
From Pyrosome.Lang Require Import PolyCompilers PolyCompilerLangs PolyCompilersCPS. (* for parameterizing existing languages*)
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

(* NOTE (this session): restated so that the "typerec" case is selected by a
   *boolean* test on the head name rather than by a nested pattern match.  This
   makes [all_typerecs_simple (con n s)] reducible when [n] is a variable known
   to be different from "typerec", which is what the cheap (non-enumerating)
   inversion below needs.  The new definition is also slightly stronger than the
   old one: it recurses into *every* argument of a [#"typerec"] node, not just
   [e1], [e2], [e3]. *)
Definition typerec_mu_ok (n : string) (s : list term) : Prop :=
  if eqb n "typerec"
  then match s with
       | [_;_;_;_;mu;_;_] => is_simple_type mu
       | _ => True
       end
  else True.

Fixpoint all_typerecs_simple (program : term) : Prop :=
  match program with
  | var _ => True
  | con n s => typerec_mu_ok n s /\ all all_typerecs_simple s
  end.

Ltac invert_wf_args :=
        match goal with
        | H : ComputeWf.wf_args _ _ _ _ |- _ => inversion H; clear H
        end.

(* ------------------------------------------------------------------ *)
(* Cheap (reflective) language inversion.                              *)
(*                                                                     *)
(* The cut-free induction [wf_term_cut_ind] hands us a hypothesis      *)
(* [In (name, term_rule c' args t) l].  Destructing that membership    *)
(* enumerates the whole language (193s / 6.5GB for                     *)
(* [source_multilanguage], see STATUS.md).  Instead we (a) turn the    *)
(* membership into a *lookup* equation, which is cheap because the     *)
(* languages are [all_fresh], and (b) restrict [name] to a handful of  *)
(* candidates with a boolean [forallb] check over the language,        *)
(* discharged once and for all by [vm_compute].                        *)
(* ------------------------------------------------------------------ *)

Local Notation CMP := (simple_multilang_compiler ++ interoperating_langs_compiler).

Lemma in_lang_lookup (l : lang) n (r : rule)
  : all_fresh l -> In (n,r) l -> named_list_lookup_err l n = Some r.
Proof.
  intros Hf Hin. symmetry.
  apply all_fresh_named_list_lookup_err_in; [ typeclasses eauto | exact Hf | exact Hin ].
Qed.

Lemma subst_sort_name_nil (t : sort) n sub
  : t[/sub/] = scon n [] -> t = scon n [].
Proof.
  destruct t; cbn; intro H; injection H as ? ?; subst.
  destruct l; cbn in *; congruence.
Qed.

(* a strong induction principle for terms *)
Section TermIndAll.
  Context (P : term -> Prop)
    (Hv : forall n, P (var n))
    (Hc : forall n l, all P l -> P (con n l)).
  Fixpoint term_ind_all (e : term) : P e :=
    match e with
    | var n => Hv n
    | con n l =>
        Hc n l ((fix f (l : list term) : all P l :=
                   match l with
                   | [] => I
                   | x::l' => conj (term_ind_all x) (f l')
                   end) l)
    end.
End TermIndAll.

(* every #"typerec" node's type argument is a variable *)
Fixpoint typerecs_are_var (e : term) : bool :=
  match e with
  | var _ => true
  | con n s =>
      (if eqb n "typerec"
       then match s with
            | [_;_;_;_;var _;_;_] => true
            | _ => false
            end
       else true)
      && (fix f (l : list term) : bool :=
            match l with [] => true | x::l' => typerecs_are_var x && f l' end) s
  end.

(* the variables used as the type argument of some #"typerec" node *)
Fixpoint typerec_mu_vars (e : term) : list string :=
  match e with
  | var _ => []
  | con n s =>
      (if eqb n "typerec"
       then match s with
            | [_;_;_;_;var m;_;_] => [m]
            | _ => []
            end
       else [])
      ++ (fix f (l : list term) : list string :=
            match l with [] => [] | x::l' => typerec_mu_vars x ++ f l' end) s
  end.

Lemma all_app A (P : A -> Prop) l1 l2 : all P (l1 ++ l2) <-> all P l1 /\ all P l2.
Proof. induction l1; cbn; tauto. Qed.

Lemma ats_lookup s n
  : all (fun p => all_typerecs_simple (snd p)) s ->
    all_typerecs_simple (term_subst_lookup s n).
Proof.
  induction s as [| [m e] s IH]; cbn; [ intros _; exact I | ].
  intros [He Hs]. cbv [term_subst_lookup] in *; cbn.
  destruct (eqb n m); [ exact He | apply IH; exact Hs ].
Qed.

(* The key substitution lemma: if every [#"typerec"] node of [b] has a
   *variable* as its type argument, and every such variable is instantiated by
   a simple type, then the instance [b[/s/]] has only simple typerecs. *)
Lemma ats_subst (b : term) (s : subst)
  : Is_true (typerecs_are_var b) ->
    all (fun p => all_typerecs_simple (snd p)) s ->
    all (fun m => is_simple_type (term_subst_lookup s m)) (typerec_mu_vars b) ->
    all_typerecs_simple b[/s/].
Proof.
  revert s. induction b using term_ind_all; intros sub Hv Hs Hm.
  { cbn. apply ats_lookup; exact Hs. }
  { cbn [term_subst term_var_map] in *.
    cbn [typerecs_are_var typerec_mu_vars] in Hv, Hm.
    apply andb_prop_elim in Hv; destruct Hv as [Hv1 Hv2].
    apply all_app in Hm; destruct Hm as [Hm1 Hm2].
    split.
    { cbv [typerec_mu_ok] in *.
      destruct (eqb n "typerec"); [ | exact I ].
      repeat (destruct l as [| ? l]; [ exact I | ]).
      destruct l; [ | exact I ].
      cbn in Hv1, Hm1. destruct t3; [ | destruct Hv1 ].
      cbn. cbn in Hm1. destruct Hm1 as [Hm1 _]. exact Hm1. }
    { clear Hm1 Hv1.
      revert Hm2 Hv2. induction l as [|x l IH']; cbn; [ intros; exact I | ].
      intros Hm2 Hv2. apply andb_prop_elim in Hv2; destruct Hv2 as [Hx Hl].
      apply all_app in Hm2; destruct Hm2 as [Hmx Hml].
      destruct H as [Hpx Hpl].
      split; [ apply Hpx; assumption | apply IH'; assumption ]. } }
Qed.

Lemma ats_default : all_typerecs_simple (@default term _).
Proof. vm_compute. tauto. Qed.

Lemma ats_combine (args : list string) (l : list term)
  : all all_typerecs_simple l ->
    all (fun p => all_typerecs_simple (snd p)) (combine_r_padded args l).
Proof.
  revert l; induction args as [|a args IH]; intros [|x l]; cbn; try tauto.
  - intros _. split; [ apply ats_default | apply IH; exact I ].
  - intros [Hx Hl]. split; [ exact Hx | apply IH; exact Hl ].
Qed.

Lemma all_map A B (Q : B -> Prop) (f : A -> B) l
  : all (fun x => Q (f x)) l -> all Q (map f l).
Proof. induction l; cbn; tauto. Qed.

Lemma pargs_all (Q : term -> Prop) (c' : ctx) (s : list term)
  : WfCutElim.P_args string (fun e (_ : sort) => Q e) s c' -> all Q s.
Proof.
  revert s; induction c' as [| [n t] c' IH]; intros [|e s]; cbn; try tauto.
  intros [H1 H2]; split; [ exact H2 | apply IH; exact H1 ].
Qed.

(* The reflective statement about the compiler: outside the two boundary
   cases, no compiler case emits a [#"typerec"] at all. *)
Definition cmp_case_ok (p : string * @compiler_case string term sort) : bool :=
  match p with
  | (n, term_case _ b) =>
      typerecs_are_var b
      && (inb n ["dtt";"ttd"] || match typerec_mu_vars b with [] => true | _ => false end)
  | _ => true
  end.

Lemma cmp_cases_ok : forallb cmp_case_ok CMP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma compile_star : compile CMP (con "*" []) = {{e #"*" #"ty_emp" }}.
Proof. reflexivity. Qed.
Lemma compile_bool : compile CMP (con "bool" []) = {{e #"bool" #"ty_emp" }}.
Proof. reflexivity. Qed.
Lemma compile_arrow a b
  : compile CMP (con "->" [b;a]) = con "->" [compile CMP b; compile CMP a; con "ty_emp" []].
Proof. reflexivity. Qed.
Lemma compile_dtt s
  : compile CMP (con "dtt" s)
    = dtt_case_tgt[/combine_r_padded ["e";"A";"G"] (map (compile CMP) s)/].
Proof. reflexivity. Qed.
Lemma compile_ttd s
  : compile CMP (con "ttd" s)
    = ttd_case_tgt[/combine_r_padded ["e";"A";"G"] (map (compile CMP) s)/].
Proof. reflexivity. Qed.
Lemma lookup_A (a b c : term)
  : term_subst_lookup (combine_r_padded ["e";"A";"G"] [a;b;c]) "A" = b.
Proof. reflexivity. Qed.

Lemma sml_all_fresh : all_fresh source_multilanguage.
Proof. compute_all_fresh. Qed.

Lemma sml_lookup n (r:rule)
  : In (n,r) source_multilanguage -> named_list_lookup_err source_multilanguage n = Some r.
Proof. apply (in_lang_lookup source_multilanguage n r sml_all_fresh). Qed.

Definition rule_ty_name_ok (p : string * rule) : bool :=
  match p with
  | (n, term_rule _ _ (scon "ty" [])) => inb n ["*";"bool";"->"]
  | _ => true
  end.

Lemma sml_ty_names : forallb rule_ty_name_ok source_multilanguage = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sml_ty_rule_name : forall n c' args,
    In (n, term_rule c' args (scon "ty" [])) source_multilanguage ->
    n = "*" \/ n = "bool" \/ n = "->".
Proof.
  intros n c' args Hin.
  pose proof sml_ty_names as Hb.
  rewrite forallb_forall in Hb.
  specialize (Hb _ Hin).
  cbv beta iota delta [rule_ty_name_ok] in Hb.
  apply Is_true_eq_left in Hb.
  autorewrite with utils in Hb. cbn in Hb.
  intuition (subst; auto).
Qed.

Lemma no_sort_eqns_in_sml : Is_true (no_sort_eqns source_multilanguage).
Proof. apply I. Qed.

(* source_multilanguage_wf is now proved in TypeCasing.v (Stage D). *)

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
  - intro Ht. apply subst_sort_name_nil in Ht; subst t.
    destruct (sml_ty_rule_name H0) as [-> | [-> | ->]];
      apply sml_lookup in H0; vm_compute in H0;
      injection H0; intros; subst.
    all: repeat invert_wf_args; subst; eauto 10.
  - destruct H0.
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
  - intro Ht. apply subst_sort_name_nil in Ht; subst t.
    destruct (sml_ty_rule_name H) as [-> | [-> | ->]];
      apply sml_lookup in H; vm_compute in H;
      injection H; intros; subst; repeat invert_wf_args; subst.
    + rewrite compile_star; exact I.
    + rewrite compile_bool; exact I.
    + rewrite compile_arrow.
      cbn [is_simple_type]; cbn [WfCutElim.P_args] in H1; destruct H1 as [[_ Pe0] Pe];
        split; [ apply Pe0 | apply Pe ]; reflexivity.
  - destruct H.
  - intros Ht; rewrite Ht in H0. apply ty_eq_sort_lemma in H0.
    + apply IHwf_term in H0. apply H0.
    + eapply (eq_sort_wf_l source_multilanguage_wf wf_ctx_nil). apply H0.
Qed.

Ltac compute_match t :=
  let v := eval vm_compute in t in
    change_no_check t with v.

Theorem can_eliminate_typerec :
  forall (t: sort) (e : term),
    Core.wf_term source_multilanguage [] e t ->
    all_typerecs_simple (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e). 
Proof.
  induction 1 using wf_term_cut_ind.
  - destruct (inb name ["dtt";"ttd"]) eqn:Hd.
    2:{ (* generic case: the compiler image of this rule has no #"typerec" *)
      cbn [compile].
      destruct (named_list_lookup_err CMP name) as [[cargs b|cargs t0]|] eqn:Hl.
      2,3: apply ats_default.
      assert (Hin : In (name, term_case cargs b) CMP)
        by (apply named_list_lookup_err_in; symmetry; exact Hl).
      pose proof cmp_cases_ok as Hb; rewrite forallb_forall in Hb; specialize (Hb _ Hin).
      cbv [cmp_case_ok] in Hb.
      apply andb_prop in Hb; destruct Hb as [Hvar Hmu].
      apply ats_subst.
      + apply Is_true_eq_left; exact Hvar.
      + apply ats_combine, all_map. eapply pargs_all; exact H1.
      + rewrite Hd in Hmu; cbn in Hmu.
        destruct (typerec_mu_vars b); [ exact I | discriminate ]. }
    { (* the two boundary cases: the #"typerec" type argument is the
         compiled source type, which is simple by compiled_types_are_simple *)
      apply Is_true_eq_left in Hd; autorewrite with utils in Hd; cbn in Hd.
      destruct Hd as [ Hd | [Hd | []]]; subst name.
      all: apply sml_lookup in H; vm_compute in H; injection H; intros; subst.
      all: repeat invert_wf_args; subst.
      all: [> rewrite compile_dtt | rewrite compile_ttd ].
      all: apply ats_subst;
        [ vm_compute; exact I
        | apply ats_combine, all_map; eapply pargs_all; exact H1
        | ].
      all: cbn [map].
      all: match goal with |- all _ ?L => replace L with ["A"] by (vm_compute; reflexivity) end.
      all: cbn [all]; split; [ | exact I ].
      all: rewrite lookup_A.
      all: eapply compiled_types_are_simple; [ apply H10 | reflexivity ]. }
  - destruct H.
  - apply IHwf_term.
Qed.

(* target_multilanguage_wf is now proved in TypeCasing.v (Stage D). *)

Lemma no_sort_eqns_in_tml : Is_true (no_sort_eqns target_multilanguage).
Proof. apply I. Qed.

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

(* The seven term rules of [target_multilanguage] whose result sort is
   [#"ty" _] are, by computation (see STATUS.md, stage H):
     "prod", "*", "bool", "->", "All", "ty_hd", "ty_subst".
   Note that the type-environment argument of the head constructor need not be
   syntactically the [D] of the ascribed sort: [target_multilanguage] has no
   sort equations, so a conversion step only tells us the two sorts have the
   same *name*, not the same arguments.  Hence every type-environment argument
   is existentially quantified.  [#"ty_hd"] is listed even though it cannot
   occur at [D = #"ty_emp"]: at a general [D] it is a legitimate closed term of
   sort [#"ty" (#"ty_ext" D')]. *)
Lemma tml_all_fresh : all_fresh target_multilanguage.
Proof. compute_all_fresh. Qed.

Lemma tml_lookup n (r:rule)
  : In (n,r) target_multilanguage -> named_list_lookup_err target_multilanguage n = Some r.
Proof. apply (in_lang_lookup target_multilanguage n r tml_all_fresh). Qed.

Definition tml_rule_ty_name_ok (p : string * rule) : bool :=
  match p with
  | (n, term_rule _ _ (scon sn _)) =>
      if eqb sn "ty"
      then inb n ["prod";"*";"bool";"->";"All";"ty_hd";"ty_subst"]
      else true
  | _ => true
  end.

Lemma tml_ty_names : forallb tml_rule_ty_name_ok target_multilanguage = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tml_ty_rule_name : forall n c' args t,
    In (n, term_rule c' args t) target_multilanguage ->
    Parameterizer.sort_name t = "ty" ->
    In n ["prod";"*";"bool";"->";"All";"ty_hd";"ty_subst"].
Proof.
  intros n c' args [sn sargs] Hin Hsn; cbn in Hsn; subst sn.
  pose proof tml_ty_names as Hb.
  rewrite forallb_forall in Hb.
  specialize (Hb _ Hin).
  apply Is_true_eq_left in Hb.
  assert (Hb' : Is_true (inb n ["prod";"*";"bool";"->";"All";"ty_hd";"ty_subst"]))
    by exact Hb.
  autorewrite with utils in Hb'. exact Hb'.
Qed.

(* Generalized over the sort's arguments: [target_multilanguage] has no sort
   equations, so the conversion case of the cut-free induction only preserves
   the sort *name*. *)
Lemma ty_inversion_lemma_tml' : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    Parameterizer.sort_name t = "ty" ->
    (exists D, e = {{e #"*" {D} }})
    \/ (exists D, e = {{e #"bool" {D} }})
    \/ (exists D a b, e = {{e #"->" {D} {a} {b} }})
    \/ (exists D a b, e = {{e #"prod" {D} {a} {b} }})
    \/ (exists D a, e = {{e #"All" {D} {a} }})
    \/ (exists D, e = {{e #"ty_hd" {D} }})
    \/ (exists D D' g a, e = {{e #"ty_subst" {D} {D'} {g} {a} }}).
Proof.
  induction 1 using wf_term_cut_ind.
  - intro Hsn.
    assert (Hsn' : Parameterizer.sort_name t = "ty")
      by (destruct t; exact Hsn).
    pose proof (tml_ty_rule_name H Hsn') as Hn.
    cbn in Hn.
    repeat (destruct Hn as [Hn | Hn]; [ subst name | ]); [ | | | | | | | destruct Hn ].
    all: apply tml_lookup in H; vm_compute in H; injection H; intros; subst.
    all: repeat invert_wf_args; subst.
    all: eauto 12.
  - destruct H.
  - intro Hsn. apply IHwf_term.
    apply (sort_names_equal target_multilanguage_wf no_sort_eqns_in_tml wf_ctx_nil) in H0.
    rewrite H0; exact Hsn.
Qed.

Lemma ty_inversion_lemma_tml : forall (e ty_env : term),
    Core.wf_term target_multilanguage [] e {{s #"ty" {ty_env} }} ->
    (exists D, e = {{e #"*" {D} }})
    \/ (exists D, e = {{e #"bool" {D} }})
    \/ (exists D a b, e = {{e #"->" {D} {a} {b} }})
    \/ (exists D a b, e = {{e #"prod" {D} {a} {b} }})
    \/ (exists D a, e = {{e #"All" {D} {a} }})
    \/ (exists D, e = {{e #"ty_hd" {D} }})
    \/ (exists D D' g a, e = {{e #"ty_subst" {D} {D'} {g} {a} }}).
Proof.
  intros e ty_env H. eapply ty_inversion_lemma_tml'; [ exact H | reflexivity ].
Qed.

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

Local Notation semantics_preserving tgt cmp :=
  (semantics_preserving (tgt_Model := core_model tgt)
     (compile cmp)
     (compile_sort cmp)
     (compile_ctx cmp)
     (compile_args cmp)
     (compile_subst cmp)).

(* The whole simple-multilanguage compiler, as a compiler with an empty prefix.
   Modulo simple_multilang_compiler_preserving, which is Admitted upstream
   (see STATUS.md, stage F). *)
Lemma interop_preserving_tml
  : preserving_compiler_ext target_multilanguage []
      interoperating_langs_compiler simple_interoperating_langs.
Proof.
  eapply preserving_compiler_embed.
  1: apply (elab_compiler_implies_preserving interoperating_langs_compiler_preserving).
  compute_incl.
Qed.

(* The whole simple-multilanguage compiler, with an empty prefix.
   Modulo simple_multilang_compiler_preserving, which is Admitted upstream
   (see STATUS.md, stage F). *)
Lemma source_multilanguage_compiler_preserving
  : preserving_compiler_ext target_multilanguage []
      (simple_multilang_compiler ++ interoperating_langs_compiler)
      source_multilanguage.
Proof.
  unfold source_multilanguage.
  eapply compiler_append.
  all: first [ typeclasses eauto
             | apply simple_multilang_compiler_preserving
             | apply interop_preserving_tml
             | apply incl_refl
             | compute_all_fresh
             | apply source_multilanguage_wf ].
Qed.

Lemma sml_semantics_preserving
  : semantics_preserving target_multilanguage
      (simple_multilang_compiler ++ interoperating_langs_compiler)
      source_multilanguage.
Proof.
  apply inductive_implies_semantic; try typeclasses eauto;
    eauto using ModelImpls.core_model_ok; try reflexivity.
  1: apply ModelImpls.core_model_ok; try typeclasses eauto.
  1: solve [prove_by_lang_db].
  1: solve [prove_by_lang_db].
  apply source_multilanguage_compiler_preserving.
Qed.

Lemma eq_sort_sml_implies_eq_sort_tml :
  forall (t t' : sort),
    eq_sort source_multilanguage [] t t' ->
    eq_sort target_multilanguage []
      (compile_sort (simple_multilang_compiler ++ interoperating_langs_compiler) t)
      (compile_sort (simple_multilang_compiler ++ interoperating_langs_compiler) t').
Proof.
  intros t t' H.
  pose proof (proj1 sml_semantics_preserving) as Hs.
  unfold sort_eq_preserving_sem in Hs.
  cbv beta iota zeta delta [core_model] in Hs.
  apply (Hs []); eauto with lang_core utils.
Qed.

(* Restore the old behavior because the new one broke this proof*)
Ltac compute_match t ::=
   let v := eval vm_compute in t in
     replace t with v by (vm_compute; reflexivity).

Theorem partial_eval_preserves_equality :
forall (t: sort) (e : term),
    Core.wf_term source_multilanguage [] e t ->
    Core.eq_term
      target_multilanguage []
      (compile_sort (simple_multilang_compiler ++ interoperating_langs_compiler) t)
      (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e)
      (elim_typerec (compile (simple_multilang_compiler ++ interoperating_langs_compiler) e)).
Admitted. (* ISSUE: see STATUS.md *)
(* Partial proof (2 of 13 cases admitted; also not run because the enumeration
   over source_multilanguage exhausts the 7GB box, as for can_eliminate_typerec):
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

*)

Definition target_multilanguage_without_typerec :=
  let_eta_parameterized ++ let_ty_subst ++ let_parameterized ++
    prod_ty_subst ++ prod_parameterized ++ (* can we also get rid of these? idt we partially evaluate that away but I think we could *)
    polymorphic_interoperating_langs.

Lemma target_multilanguage_without_typerec_wf : wf_lang target_multilanguage_without_typerec.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_without_typerec_entry :=
  lang_entry target_multilanguage_without_typerec_wf.
#[export] Hint Resolve target_multilanguage_without_typerec_entry : wf_lang_db.

(* STATEMENT FIXED (this session).  The old statement -- without the
   [all_typerecs_simple] hypothesis -- is false: [elim_typerec] only removes a
   [#"typerec"] node whose type argument is a *simple* type ([meta_typerec]
   falls through to [| _ => mu] otherwise), so a term containing
   [#"typerec" D G "A" ...] at a type variable or an [#"All"] type is left
   unchanged and still mentions [#"typerec"], which is not a constructor of
   [target_multilanguage_without_typerec]. *)
Theorem partial_eval_wf_in_no_typerec_lang : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    all_typerecs_simple e ->
    Core.wf_term
      target_multilanguage_without_typerec
      []
      (elim_typerec e)
      t.
Admitted. (* ISSUE: see STATUS.md *)

(* The form in which the theorem above is meant to be used: for compiled
   source terms the [all_typerecs_simple] hypothesis is discharged by
   [can_eliminate_typerec], which is now Qed. *)
Corollary compiled_partial_eval_wf : forall (t t' : sort) (e : term),
    Core.wf_term source_multilanguage [] e t ->
    Core.wf_term target_multilanguage [] (compile CMP e) t' ->
    Core.wf_term target_multilanguage_without_typerec []
      (elim_typerec (compile CMP e)) t'.
Proof.
  intros t t' e Hsrc Htgt.
  apply partial_eval_wf_in_no_typerec_lang; [ exact Htgt | ].
  eapply can_eliminate_typerec; exact Hsrc.
Qed.

