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
From Pyrosome.Theory Require Conservativity.

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

Definition comp_t1_type := {{s #"val" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") "t1") "sigma") }}.

Definition comp_t2_type := {{s #"val" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") "t2") "sigma") }}.

Definition func_partial_eval_ctx := Eval vm_compute in [("comp_t2", comp_t2_type); ("comp_t1", comp_t1_type); ("v3", named_list_lookup default func_partial_eval_ctx' "v3"); ("t2", named_list_lookup default func_partial_eval_ctx' "t2"); ("t1", named_list_lookup default func_partial_eval_ctx' "t1"); ("sigma", named_list_lookup default func_partial_eval_ctx' "sigma"); ("G", named_list_lookup default func_partial_eval_ctx' "G"); ("D", named_list_lookup default func_partial_eval_ctx' "D")]. 

(* NOTE (value-level typerec): the arrow case of the partial evaluator is now
   the *value* produced by the new ["typerec func"] rule, i.e. the two
   recursive results substituted into the (type-instantiated) function case
   ["v3"], rather than two [#"@"]/[#"app"] applications. *)
Definition func_partial_eval_term_def :=
  {{e #"val_subst" (#"snoc" (#"snoc" #"id" "comp_t1") "comp_t2")
      (#"val_ty_subst" (#"ty_snoc" (#"ty_snoc" #"ty_id" "t1") "t2") "v3") }}.

Derive func_partial_eval_term
  in ( elab_term target_multilanguage
         func_partial_eval_ctx
         func_partial_eval_term_def
         func_partial_eval_term
         {{s #"val" "D" "G" (#"ty_subst" "D" (#"ty_ext" "D") (#"ty_snoc" "D" "D" (#"ty_id" "D") (#"->" "D" "t1" "t2")) "sigma") }}
     ) as func_partial_eval_term_wf. 
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

(* ------------------------------------------------------------------ *)
(* The arrow case of the partial evaluator (rewritten this session).     *)
(*                                                                       *)
(* It used to be built from [func_partial_eval_term], the separately      *)
(* elaborated copy of the right-hand side of ["typerec func"].  The two   *)
(* elaborations differ in the *implicit* environment/type arguments of    *)
(* the outermost [#"val_subst"] (elaborating the rule simplifies an       *)
(* [#"env_ty_subst"] away, elaborating the standalone term does not), so  *)
(* an instance of the rule's RHS was not syntactically an instance of     *)
(* [func_partial_eval_term], and the metatheory could not be closed.      *)
(* [fpe2] below is read off from the rule itself: it *is* the RHS of      *)
(* ["typerec func"] with the two recursive [#"typerec"] calls replaced by *)
(* the variables ["comp_t1"]/["comp_t2"].  The old substitution was also  *)
(* missing ["sigma"], which occurs free in the RHS, so [elim_typerec] of  *)
(* a closed term used to have a free variable in it.                      *)
Definition rule_parts (n : string) :=
  match named_list_lookup_err target_multilanguage n with
  | Some (term_eq_rule c e1 e2 t) => (c,e1,e2,t)
  | _ => ([],var "",var "",{{s #"X"}})
  end.
Definition R_star := Eval vm_compute in rule_parts "typerec star".
Definition R_bool := Eval vm_compute in rule_parts "typerec bool".
Definition R_func := Eval vm_compute in rule_parts "typerec func".
Definition R_star_c := Eval vm_compute in fst (fst (fst R_star)).
Definition R_bool_c := Eval vm_compute in fst (fst (fst R_bool)).
Definition R_func_c := Eval vm_compute in fst (fst (fst R_func)).
Definition R_func_r := Eval vm_compute in snd (fst R_func).
Definition R_func_t := Eval vm_compute in snd R_func.

(* [#"val" D G (sigma[X])], the sort of [#"typerec"] at type [X]. *)
Definition Sgt (D G sigma X : term) : sort :=
  {{s #"val" {D} {G} (#"ty_subst" {D} (#"ty_ext" {D}) (#"ty_snoc" {D} {D} (#"ty_id" {D}) {X}) {sigma}) }}.

Fixpoint abstract_typerec (e : term) : term :=
  match e with
  | con "typerec" [_;_;_;_;var "t1";_;_] => var "comp_t1"
  | con "typerec" [_;_;_;_;var "t2";_;_] => var "comp_t2"
  | con n l => con n (map abstract_typerec l)
  | var x => var x
  end.
Definition fpe2 := Eval vm_compute in abstract_typerec R_func_r.
Definition fpe2_ctx := Eval vm_compute in
  ("comp_t2", Sgt {{e "D"}} {{e "G"}} {{e "sigma"}} {{e "t2"}})
  :: ("comp_t1", Sgt {{e "D"}} {{e "G"}} {{e "sigma"}} {{e "t1"}})
  :: (filter (fun p => negb (orb (eqb (fst p) "v1") (eqb (fst p) "v2"))) R_func_c).

Lemma fpe2_ctx_wf : @Model.wf_ctx _ _ _ (core_model target_multilanguage) fpe2_ctx.
Proof. pose proof target_multilanguage_wf. solve_wf_ctx. Qed.

Lemma fpe2_wf : Core.wf_term target_multilanguage fpe2_ctx fpe2 R_func_t.
Proof. pose proof target_multilanguage_wf. compute_term_wf. Qed.

Definition MT_func (D G sigma t1 t2 r1 r2 v3 : term) : term :=
  fpe2[/[("comp_t2",r2);("comp_t1",r1);("v3",v3);("t2",t2);("t1",t1);
         ("sigma",sigma);("G",G);("D",D)]/].

Fixpoint meta_typerec (D G mu sigma e1 e2 e3 : term) {struct mu} : term :=
  match mu with
  | var _ => mu
  | con n l =>
      if eqb n "*" then e1
      else if eqb n "bool" then e2
      else if eqb n "->" then
             match l with
             | [t2;t1;_] =>
                 MT_func D G sigma t1 t2
                   (meta_typerec D G t1 sigma e1 e2 e3)
                   (meta_typerec D G t2 sigma e1 e2 e3) e3
             | _ => mu end
      else mu
  end.

Fixpoint elim_typerec (program : term) : term :=
  match program with
  | var n => var n
  | con n s =>
      if eqb n "typerec"
      then match s with
           | [e3;e2;e1;sigma;mu;G;D] =>
               meta_typerec D G mu sigma (elim_typerec e1) (elim_typerec e2) (elim_typerec e3)
           | _ => con n (map elim_typerec s)
           end
      else con n (map elim_typerec s)
  end.

(* NOTE (this session): [is_simple_type] is now indexed by the type
   environment: [simple_type_at D mu] says that [mu] is built from [#"*"],
   [#"bool"] and [#"->"] *at the type environment [D]*.  Without that index
   the arrow case of [typerec_elim_eq] is unprovable: the ["typerec func"]
   rule instance needs the [#"->"] node's type-environment argument to be the
   same term as the [#"typerec"] node's, and [target_multilanguage] has no
   sort-injectivity principle to recover it.  [is_simple_type] is the instance
   at the empty type environment, which is where every *compiled* source type
   lives ([compile_star] / [compile_bool] / [compile_arrow]). *)
Fixpoint simple_type_at (D mu : term) {struct mu} : Prop :=
  match mu with
  | var _ => False
  | con n l =>
      if eqb n "*" then match l with [D'] => D' = D | _ => False end
      else if eqb n "bool" then match l with [D'] => D' = D | _ => False end
      else if eqb n "->" then
             match l with
             | [t2;t1;D'] => D' = D /\ simple_type_at D t1 /\ simple_type_at D t2
             | _ => False end
      else False
  end.

Definition is_simple_type (mu : term) : Prop := simple_type_at {{e #"ty_emp"}} mu.

(* NOTE (previous session): stated so that the "typerec" case is selected by a
   *boolean* test on the head name rather than by a nested pattern match.  This
   makes [all_typerecs_simple (con n s)] reducible when [n] is a variable known
   to be different from "typerec", which is what the cheap (non-enumerating)
   inversion below needs.  It recurses into *every* argument of a [#"typerec"]
   node, not just [e1], [e2], [e3].  This session: the type argument is now
   required to be simple *at the node's own type environment*. *)
Definition typerec_mu_ok (n : string) (s : list term) : Prop :=
  if eqb n "typerec"
  then match s with
       | [_;_;_;_;mu;_;D] => simple_type_at D mu
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

(* every #"typerec" node's type argument is a variable, and its type
   environment is the empty one (so that a substitution instance is simple
   *at that node's own type environment*, which is what [typerec_mu_ok]
   now demands) *)
Definition typerec_head_ok (s : list term) : bool :=
  match s with
  | [_;_;_;_;mu;_;D] =>
      (match mu with var _ => true | _ => false end) && eqb D {{e #"ty_emp"}}
  | _ => false
  end.

Fixpoint typerecs_are_var (e : term) : bool :=
  match e with
  | var _ => true
  | con n s =>
      (if eqb n "typerec" then typerec_head_ok s else true)
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
      cbv [typerec_head_ok] in Hv1.
      destruct l as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|? ?]]]]]]]];
        try solve [ destruct Hv1 ].
      destruct a4 as [m|]; [ | destruct Hv1 ].
      cbn [andb] in Hv1. apply Is_true_eq_true in Hv1.
      pose proof (eqb_spec a6 {{e #"ty_emp"}}) as Hsp; rewrite Hv1 in Hsp; subst a6.
      cbn [map term_subst term_var_map].
      cbn in Hm1. destruct Hm1 as [Hm1 _]. exact Hm1. }
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
    + rewrite compile_star; exact eq_refl.
    + rewrite compile_bool; exact eq_refl.
    + rewrite compile_arrow.
      cbv [is_simple_type]; cbn [simple_type_at];
        cbn [WfCutElim.P_args] in H1; destruct H1 as [[_ Pe0] Pe];
        split; [ reflexivity | split; [ apply Pe0 | apply Pe ]; reflexivity ].
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

(* ------------------------------------------------------------------ *)
(* Metatheory of the partial evaluator (this session).                  *)
(*                                                                      *)
(* [Implicit Arguments] is off in this block: the lemmas below are       *)
(* applied with positional arguments.                                   *)
(* ------------------------------------------------------------------ *)
Unset Implicit Arguments.
Local Notation wf_ctx' c := (@Model.wf_ctx _ _ _ (core_model target_multilanguage) c).
Local Notation wf_subst' s c := (@Model.wf_subst _ _ _ (core_model target_multilanguage) [] s c).
Local Notation wf_args' s c := (@Model.wf_args _ _ _ (core_model target_multilanguage) [] s c).
Local Notation eq_subst' c s1 s2 := (@Model.eq_subst _ _ _ (core_model target_multilanguage) [] c s1 s2).
Local Notation eq_args' c s1 s2 := (@Model.eq_args _ _ _ (core_model target_multilanguage) [] c s1 s2).

Ltac to_core := cbv beta iota zeta delta [Model.wf_term Model.eq_term core_model] in *.
Ltac norm_sort_goal :=
  to_core;
  match goal with
  | |- Core.wf_term ?l ?c ?e ?T => let T' := eval vm_compute in T in change (Core.wf_term l c e T')
  | |- Core.eq_term ?l ?c ?T ?A ?B =>
      let T' := eval vm_compute in T in
      let A' := eval vm_compute in A in
      let B' := eval vm_compute in B in change (Core.eq_term l c T' A' B')
  end.
Ltac norm_sort_only :=
  to_core;
  match goal with
  | |- Core.wf_term ?l ?c ?e ?T => let T' := eval vm_compute in T in change (Core.wf_term l c e T')
  | |- Core.eq_term ?l ?c ?T ?A ?B => let T' := eval vm_compute in T in change (Core.eq_term l c T' A B)
  end.

Ltac norm_wf_hyp H :=
  to_core;
  match type of H with
  | Core.wf_term ?l ?c ?e ?T => let T' := eval vm_compute in T in change (Core.wf_term l c e T') in H
  end.

Ltac norm_eq_hyp H :=
  match type of H with
  | Core.eq_term ?l ?c ?T ?A ?B =>
      let T' := eval vm_compute in T in
      let A' := eval vm_compute in A in
      let B' := eval vm_compute in B in
      change (Core.eq_term l c T' A' B') in H
  end.



Lemma R_star_lookup : named_list_lookup_err target_multilanguage "typerec star"
  = Some (term_eq_rule R_star_c (snd (fst (fst R_star))) (snd (fst R_star)) (snd R_star)).
Proof. vm_compute. reflexivity. Qed.
Lemma R_bool_lookup : named_list_lookup_err target_multilanguage "typerec bool"
  = Some (term_eq_rule R_bool_c (snd (fst (fst R_bool))) (snd (fst R_bool)) (snd R_bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma R_func_lookup : named_list_lookup_err target_multilanguage "typerec func"
  = Some (term_eq_rule R_func_c (snd (fst (fst R_func))) R_func_r R_func_t).
Proof. vm_compute. reflexivity. Qed.

Lemma tml_eq_rule_ctx_wf name c' e1 e2 t :
  In (name, term_eq_rule c' e1 e2 t) target_multilanguage -> wf_ctx' c'.
Proof.
  intro Hin. pose proof (rule_in_wf _ _ target_multilanguage_wf Hin) as Hr.
  rewrite app_nil_r in Hr. inversion Hr; subst; assumption.
Qed.

Lemma eq_by_rule (name : string) (c' : ctx) (t:sort) e1 e2 (s : subst)
  : named_list_lookup_err target_multilanguage name = Some (term_eq_rule c' e1 e2 t) ->
    wf_subst' s c' ->
    Core.eq_term target_multilanguage [] t[/s/] e1[/s/] e2[/s/].
Proof.
  intros Hl Hs.
  assert (In (name, term_eq_rule c' e1 e2 t) target_multilanguage)
    by (apply named_list_lookup_err_in; symmetry; exact Hl).
  eapply eq_term_subst.
  - eapply eq_term_by; eauto.
  - apply eq_subst_refl; exact Hs.
  - eapply tml_eq_rule_ctx_wf; eauto.
Qed.

Lemma wf_by_rule (name : string) (c' : ctx) (t:sort) args (s : list term)
  : named_list_lookup_err target_multilanguage name = Some (term_rule c' args t) ->
    wf_args' s c' ->
    Core.wf_term target_multilanguage [] (con name s) t[/with_names_from c' s/].
Proof.
  intros Hl Hs. eapply wf_term_by; [ | exact Hs ].
  apply named_list_lookup_err_in; symmetry; exact Hl.
Qed.



Lemma simple_type_wf D (HD : Core.wf_term target_multilanguage [] D {{s #"ty_env"}})
  : forall mu, simple_type_at D mu -> Core.wf_term target_multilanguage [] mu {{s #"ty" {D} }}.
Proof.
  induction mu using term_ind_all; [ intros [] | ].
  cbn [simple_type_at]. intro Hs.
  pose proof (eqb_spec n "*") as Hn1; destruct (eqb n "*"); [ subst n | ].
  { destruct l as [|D' [|? ?]]; try contradiction. cbn in Hs. subst D'.
    pose proof (wf_by_rule "*" [("D", {{s #"ty_env"}})] {{s #"ty" "D"}} [] [D]
                  ltac:(vm_compute; reflexivity)) as Hb.
    norm_sort_goal. apply Hb. to_core.
    econstructor; [ norm_sort_goal; exact HD | econstructor ]. }
  pose proof (eqb_spec n "bool") as Hn2; destruct (eqb n "bool"); [ subst n | ].
  { destruct l as [|D' [|? ?]]; try contradiction. cbn in Hs. subst D'.
    pose proof (wf_by_rule "bool" [("D", {{s #"ty_env"}})] {{s #"ty" "D"}} [] [D]
                  ltac:(vm_compute; reflexivity)) as Hb.
    norm_sort_goal. apply Hb. to_core.
    econstructor; [ norm_sort_goal; exact HD | econstructor ]. }
  pose proof (eqb_spec n "->") as Hn3; destruct (eqb n "->"); [ subst n | contradiction ].
  destruct l as [|t2 [|t1 [|D' [|? ?]]]]; try contradiction.
  destruct Hs as [HD' [Hs1 Hs2]]. subst D'.
  cbn [all] in H. destruct H as [IH2 [IH1 _]].
  pose proof (wf_by_rule "->" [("t'", {{s #"ty" "D"}});("t", {{s #"ty" "D"}});("D", {{s #"ty_env"}})]
                {{s #"ty" "D"}} ["t'";"t"] [t2;t1;D]
                ltac:(vm_compute; reflexivity)) as Hb.
  norm_sort_goal. apply Hb. to_core.
  econstructor; [ norm_sort_goal; apply IH2; exact Hs2 | ].
  econstructor; [ norm_sort_goal; apply IH1; exact Hs1 | ].
  econstructor; [ norm_sort_goal; exact HD | econstructor ].
Qed.


Lemma meta_typerec_arrow D G sigma X t1 t2 e1 e2 e3
  : meta_typerec D G (con "->" [t2;t1;X]) sigma e1 e2 e3
    = MT_func D G sigma t1 t2 (meta_typerec D G t1 sigma e1 e2 e3)
        (meta_typerec D G t2 sigma e1 e2 e3) e3.
Proof. reflexivity. Qed.



Section TyperecElim.
  Context (D G sigma v1 v2 v3 : term)
    (HD : Core.wf_term target_multilanguage [] D {{s #"ty_env"}})
    (HG : Core.wf_term target_multilanguage [] G {{s #"env" {D} }})
    (Hsig : Core.wf_term target_multilanguage [] sigma {{s #"ty" (#"ty_ext" {D}) }})
    (Hv1 : Core.wf_term target_multilanguage [] v1 (Sgt D G sigma {{e #"*" {D} }}))
    (Hv2 : Core.wf_term target_multilanguage [] v2 (Sgt D G sigma {{e #"bool" {D} }}))
    (Hv3 : Core.wf_term target_multilanguage [] v3 ((named_list_lookup default R_func_c "v3")
                                     [/[("sigma",sigma);("G",G);("D",D)]/])).

  Ltac wf_solve := norm_sort_goal; cbv [Sgt] in *; assumption.

  Lemma base_subst_wf : wf_subst' [("v3",v3);("v2",v2);("v1",v1);("sigma",sigma);("G",G);("D",D)] R_star_c.
  Proof.
    cbv [R_star_c]. repeat apply Model.wf_subst_cons.
    all: try apply Model.wf_subst_nil.
    all: wf_solve.
  Qed.

  Lemma base_subst_wf_b : wf_subst' [("v3",v3);("v2",v2);("v1",v1);("sigma",sigma);("G",G);("D",D)] R_bool_c.
  Proof.
    cbv [R_bool_c]. repeat apply Model.wf_subst_cons.
    all: try apply Model.wf_subst_nil.
    all: wf_solve.
  Qed.

  Lemma func_subst_wf t1 t2
    (Ht1 : Core.wf_term target_multilanguage [] t1 {{s #"ty" {D} }})
    (Ht2 : Core.wf_term target_multilanguage [] t2 {{s #"ty" {D} }})
    : wf_subst' [("v3",v3);("v2",v2);("v1",v1);("t2",t2);("t1",t1);("sigma",sigma);("G",G);("D",D)] R_func_c.
  Proof.
    cbv [R_func_c]. repeat apply Model.wf_subst_cons.
    all: try apply Model.wf_subst_nil.
    all: wf_solve.
  Qed.

  Theorem typerec_elim_eq : forall mu, simple_type_at D mu ->
    Core.eq_term target_multilanguage [] (Sgt D G sigma mu)
      (con "typerec" [v3;v2;v1;sigma;mu;G;D])
      (meta_typerec D G mu sigma v1 v2 v3).
  Proof.
    induction mu using term_ind_all; [ intros [] | ].
    cbn [simple_type_at]. intro Hs.
    pose proof (eqb_spec n "*") as Hn1; destruct (eqb n "*"); [ subst n | ].
    { destruct l as [|D' [|? ?]]; try contradiction. cbn in Hs; subst D'.
      pose proof (eq_by_rule _ _ _ _ _ _ R_star_lookup base_subst_wf) as Hq.
      norm_eq_hyp Hq. cbv [Sgt meta_typerec]. exact Hq. }
    pose proof (eqb_spec n "bool") as Hn2; destruct (eqb n "bool"); [ subst n | ].
    { destruct l as [|D' [|? ?]]; try contradiction. cbn in Hs; subst D'.
      pose proof (eq_by_rule _ _ _ _ _ _ R_bool_lookup base_subst_wf_b) as Hq.
      norm_eq_hyp Hq. cbv [Sgt meta_typerec]. exact Hq. }
    pose proof (eqb_spec n "->") as Hn3; destruct (eqb n "->"); [ subst n | contradiction ].
    destruct l as [|t2 [|t1 [|D' [|? ?]]]]; try contradiction.
    destruct Hs as [HD' [Hs1 Hs2]]; subst D'.
    cbn [all] in H; destruct H as [IH2 [IH1 _]].
    assert (Ht1 : Core.wf_term target_multilanguage [] t1 {{s #"ty" {D} }})
      by (apply (simple_type_wf D HD); exact Hs1).
    assert (Ht2 : Core.wf_term target_multilanguage [] t2 {{s #"ty" {D} }})
      by (apply (simple_type_wf D HD); exact Hs2).
    pose proof (eq_by_rule _ _ _ _ _ _ R_func_lookup (func_subst_wf t1 t2 Ht1 Ht2)) as Hq.
    norm_eq_hyp Hq.
    rewrite meta_typerec_arrow.
    eapply eq_term_trans; [ | ].
    2:{ (* fpe2[/sa/] = fpe2[/sb/] *)
      pose proof (eq_term_subst (l:=target_multilanguage) (c:=[]) (c':=fpe2_ctx)
                    (s1:=[("comp_t2", con "typerec" [v3;v2;v1;sigma;t2;G;D]);
                          ("comp_t1", con "typerec" [v3;v2;v1;sigma;t1;G;D]);
                          ("v3",v3);("t2",t2);("t1",t1);("sigma",sigma);("G",G);("D",D)])
                    (s2:=[("comp_t2", meta_typerec D G t2 sigma v1 v2 v3);
                          ("comp_t1", meta_typerec D G t1 sigma v1 v2 v3);
                          ("v3",v3);("t2",t2);("t1",t1);("sigma",sigma);("G",G);("D",D)])
                    (t:=R_func_t) (e1:=fpe2) (e2:=fpe2)) as Hsub.
      cbv [MT_func].
      apply Hsub; [ apply eq_term_refl; apply fpe2_wf | | apply fpe2_ctx_wf ].
      cbv [fpe2_ctx]. repeat apply Model.eq_subst_cons.
      all: try apply Model.eq_subst_nil.
      all: to_core.
      all: try (norm_sort_only; solve [ apply eq_term_refl; cbv [Sgt] in *; assumption ]).
      all: norm_sort_only.
      - cbv [Sgt] in IH1. apply IH1; exact Hs1.
      - cbv [Sgt] in IH2. apply IH2; exact Hs2. }
    exact Hq.
  Qed.
End TyperecElim.

Lemma eq_args_elim : forall c' s,
    WfCutElim.P_args string
      (fun e t => all_typerecs_simple e -> Core.eq_term target_multilanguage [] t e (elim_typerec e)) s c' ->
    all all_typerecs_simple s ->
    eq_args' c' (map elim_typerec s) s.
Proof.
  induction c' as [|[n t] c' IH]; intros [|e s]; cbn [WfCutElim.P_args map all]; try tauto.
  - intros _ _. apply Model.eq_args_nil.
  - intros [Hp Hpe] [Ha Has]. apply Model.eq_args_cons.
    + apply IH; assumption.
    + apply eq_term_sym. apply Hpe. exact Ha.
Qed.

Lemma pargs_len : forall (P : term -> sort -> Prop) c' s,
    WfCutElim.P_args string P s c' -> length s = length c'.
Proof.
  induction c' as [|[n t] c' IH]; intros [|e s]; cbn [WfCutElim.P_args length]; try tauto.
  intros [Hp _]; f_equal; apply IH; exact Hp.
Qed.

Lemma elim_typerec_con7 (D G mu sigma e1 e2 e3 : term) :
  elim_typerec (con "typerec" [e3;e2;e1;sigma;mu;G;D])
  = meta_typerec D G mu sigma (elim_typerec e1) (elim_typerec e2) (elim_typerec e3).
Proof. reflexivity. Qed.



Theorem elim_typerec_eq : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    all_typerecs_simple e ->
    Core.eq_term target_multilanguage [] t e (elim_typerec e).
Proof.
  induction 1 using wf_term_cut_ind.
  - intro Hats.
    pose proof (eqb_spec name "typerec") as Hn; destruct (eqb name "typerec") eqn:Hnb.
    2:{
      assert (Helim : elim_typerec (con name s) = con name (map elim_typerec s))
        by (cbn [elim_typerec]; rewrite Hnb; reflexivity).
      rewrite Helim. apply eq_term_sym.
      eapply term_con_congruence;
        [ exact H | right; reflexivity | exact target_multilanguage_wf | ].
      apply eq_args_elim; [ exact H1 | ]. destruct Hats as [_ Hall]; exact Hall. }
    subst name. assert (Hin := H).
    apply tml_lookup in H. vm_compute in H. injection H as Hc' Hargs Ht. subst.
    assert (Hlen : length s = 7) by (rewrite (pargs_len _ _ _ H1); reflexivity).
    destruct s as [|e3 [|e2 [|e1 [|sg [|mu [|Gv [|Dv [|? ?]]]]]]]];
      cbn [length] in Hlen; try discriminate Hlen.
    (destruct H1 as [[[[[[[_ IHD] IHG] IHmu] IHsg] IH1] IH2] IH3]).
    (destruct Hats as [Hsimple [Ha3 [Ha2 [Ha1 [Hasg [Hamu [HaG [HaD _]]]]]]]]).
    inversion H0 as [|? ? ? ? ? W3 H0a]; subst; clear H0.
    inversion H0a as [|? ? ? ? ? W2 H0b]; subst; clear H0a.
    inversion H0b as [|? ? ? ? ? W1 H0c]; subst; clear H0b.
    inversion H0c as [|? ? ? ? ? Wsg H0d]; subst; clear H0c.
    inversion H0d as [|? ? ? ? ? Wmu H0e]; subst; clear H0d.
    inversion H0e as [|? ? ? ? ? WG H0f]; subst; clear H0e.
    inversion H0f as [|? ? ? ? ? WD H0g]; subst; clear H0f.
    norm_wf_hyp W3. norm_wf_hyp W2. norm_wf_hyp W1.
    norm_wf_hyp Wsg. norm_wf_hyp Wmu. norm_wf_hyp WG. norm_wf_hyp WD.
    assert (Hnil : wf_ctx' (@nil (string * sort))) by constructor.
    rewrite elim_typerec_con7.
    eapply eq_term_trans
      with (e12 := con "typerec" [elim_typerec e3; elim_typerec e2; elim_typerec e1; sg; mu; Gv; Dv]).
    { eapply term_con_congruence;
        [ exact Hin | right; vm_compute; reflexivity | exact target_multilanguage_wf | ].
      repeat apply Model.eq_args_cons.
      all: try apply Model.eq_args_nil.
      all: try (norm_sort_only; solve [ apply eq_term_refl; assumption ]).
      all: norm_sort_only.
      - apply IH1; exact Ha1.
      - apply IH2; exact Ha2.
      - apply IH3; exact Ha3. }
    assert (E1 : Core.wf_term target_multilanguage [] (elim_typerec e1)
                   (Sgt Dv Gv sg {{e #"*" {Dv} }}))
      by (cbv [Sgt]; eapply eq_term_wf_r;
          try typeclasses eauto; try exact target_multilanguage_wf; try exact Hnil;
          norm_sort_only; apply IH1; exact Ha1).
    assert (E2 : Core.wf_term target_multilanguage [] (elim_typerec e2)
                   (Sgt Dv Gv sg {{e #"bool" {Dv} }}))
      by (cbv [Sgt]; eapply eq_term_wf_r;
          try typeclasses eauto; try exact target_multilanguage_wf; try exact Hnil;
          norm_sort_only; apply IH2; exact Ha2).
    assert (E3 : Core.wf_term target_multilanguage [] (elim_typerec e3)
                   ((named_list_lookup default R_func_c "v3")
                      [/[("sigma",sg);("G",Gv);("D",Dv)]/]))
      by (norm_sort_only; eapply eq_term_wf_r;
          try typeclasses eauto; try exact target_multilanguage_wf; try exact Hnil;
          norm_sort_only; apply IH3; exact Ha3).
    norm_sort_only.
    pose proof (typerec_elim_eq Dv Gv sg _ _ _ WD WG Wsg E1 E2 E3 mu Hsimple) as Hfin.
    cbv [Sgt] in Hfin. exact Hfin.
  - destruct H.
  - intro Hats. eapply eq_term_conv; [ apply IHwf_term; exact Hats | exact H0 ].
Qed.
Set Implicit Arguments.



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
Proof.
  intros t e H.
  apply elim_typerec_eq.
  - (* the compiled term is well-typed in the target *)
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 sml_semantics_preserving))))) as Hw.
    unfold term_wf_preserving_sem in Hw.
    specialize (Hw [] e t H ltac:(constructor)).
    cbv beta iota zeta delta [core_model] in Hw.
    cbn [compile_ctx] in Hw. exact Hw.
  - (* every typerec it contains has a simple type argument *)
    eapply can_eliminate_typerec; exact H.
Qed.

(* Well-typedness of the partially evaluated term, in the *full* target.
   (The sublanguage version is below; see STATUS.md for why it does not
   follow from this one.) *)
Corollary partial_eval_wf_in_target : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    all_typerecs_simple e ->
    Core.wf_term target_multilanguage [] (elim_typerec e) t.
Proof.
  intros t e H Hats.
  eapply eq_term_wf_r;
    try typeclasses eauto;
    try exact target_multilanguage_wf;
    try (constructor; fail);
    apply elim_typerec_eq; assumption.
Qed.

Definition target_multilanguage_without_typerec :=
  boundary_cases ++
  let_eta_parameterized ++ let_ty_subst ++ let_parameterized ++
    prod_ty_subst ++ prod_parameterized ++ (* can we also get rid of these? idt we partially evaluate that away but I think we could *)
    polymorphic_interoperating_langs.

Lemma target_multilanguage_without_typerec_wf : wf_lang target_multilanguage_without_typerec.
Proof.
  unfold target_multilanguage_without_typerec.
  apply wf_lang_concat; [ prove_by_lang_db | ].
  (* [boundary_cases] does not mention [#"typerec"], so it is still an
     extension of the typerec-free target. *)
  Time compute_wf_lang.
Qed.
#[local] Definition target_multilanguage_without_typerec_entry :=
  lang_entry target_multilanguage_without_typerec_wf.
#[export] Hint Resolve target_multilanguage_without_typerec_entry : wf_lang_db.

(* STATEMENT FIXED (this session).  The old statement -- without the
   [all_typerecs_simple] hypothesis -- is false: [elim_typerec] only removes a
   [#"typerec"] node whose type argument is a *simple* type ([meta_typerec]
   falls through to [| _ => mu] otherwise), so a term containing
   [#"typerec" D G "A" ...] at a type variable or an [#"All"] type is left
   unchanged and still mentions [#"typerec"], which is not a constructor of
   [target_multilanguage_without_typerec].

   STILL ADMITTED (this session), for one localized reason: the *conversion*
   case of [wf_term_cut_ind].  Everything else is now in place:
   [partial_eval_wf_in_target] above gives well-typedness of [elim_typerec e]
   in the full [target_multilanguage], and by computation the only rules of
   [target_multilanguage] that are absent from
   [target_multilanguage_without_typerec] are the six typerec rules
   ["typerec"], ["typerec star"], ["typerec bool"], ["typerec func"],
   ["ty_subst typerec"], ["val_subst typerec"] -- of which exactly one,
   ["typerec"], is a *term* rule.  So the constructor case transfers by a
   [vm_compute]d membership check, and the [#"typerec"] case is discharged by
   [meta_typerec] (whose output mentions no typerec).  What does not transfer
   is the hypothesis [eq_sort target_multilanguage [] t t'] of the conversion
   case: to re-apply [wf_term_conv] in the sublanguage one needs
   [eq_sort target_multilanguage_without_typerec [] t t'], and
   [target_multilanguage] has no sort equations, so this [eq_sort] is built
   from sort-congruence over *term* equalities inside the sort arguments,
   which may legitimately use the five typerec equations.  Transferring it is
   a conservativity statement about the extension
   [target_multilanguage_without_typerec] |- [target_multilanguage], which
   Pyrosome does not currently provide.  The residual goal is exactly:

     forall t t', eq_sort target_multilanguage [] t t' ->
                  wf_sort target_multilanguage_without_typerec [] t ->
                  wf_sort target_multilanguage_without_typerec [] t' ->
                  eq_sort target_multilanguage_without_typerec [] t t'.
 *)
(* [partial_eval_wf_in_no_typerec_lang] and [compiled_partial_eval_wf] are
   stated and proved at the end of the file. *)



(* ================================================================== *)
(* Metatheory: the partially evaluated term lives in the typerec-free  *)
(* sublanguage (modulo conservativity of the sort equality).           *)
(* ================================================================== *)
(* ------------------------------------------------------------------ *)
(* [no_typerec]: a syntactic check that a term mentions no [#"typerec"] *)
(* ------------------------------------------------------------------ *)
Fixpoint no_typerec (e : term) : bool :=
  match e with
  | var _ => true
  | con n s =>
      negb (eqb n "typerec")
      && (fix f (l : list term) : bool :=
            match l with [] => true | x::l' => no_typerec x && f l' end) s
  end.

Lemma no_typerec_unfold n s
  : no_typerec (con n s) = negb (eqb n "typerec") && forallb no_typerec s.
Proof.
  cbn [no_typerec]. f_equal; induction s; cbn; congruence.
Qed.

Lemma forallb_of_all (f : term -> bool) l
  : all (fun x => f x = true) l -> forallb f l = true.
Proof. induction l; cbn; [ reflexivity | ]. intros [H1 H2]. rewrite H1; auto. Qed.

Lemma all_of_forallb (f : term -> bool) l
  : forallb f l = true -> all (fun x => f x = true) l.
Proof.
  induction l; cbn; [ tauto | ].
  intro H. apply andb_prop in H. destruct H. split; auto.
Qed.

Lemma no_typerec_lookup (s : subst) n
  : all (fun p => no_typerec (snd p) = true) s ->
    no_typerec (term_subst_lookup s n) = true.
Proof.
  induction s as [| [m e] s IH]; cbn; [ intros _; reflexivity | ].
  intros [He Hs]. cbv [term_subst_lookup] in *; cbn.
  destruct (eqb n m); [ exact He | apply IH; exact Hs ].
Qed.

Lemma no_typerec_subst (b : term) (s : subst)
  : no_typerec b = true ->
    all (fun p => no_typerec (snd p) = true) s ->
    no_typerec b[/s/] = true.
Proof.
  revert s; induction b using term_ind_all; intros sub Hb Hs.
  { cbn. apply no_typerec_lookup; exact Hs. }
  rewrite no_typerec_unfold in Hb. apply andb_prop in Hb. destruct Hb as [Hn Hl].
  change ((con n l)[/sub/]) with (con n (map (term_subst sub) l)).
  rewrite no_typerec_unfold, Hn; cbn [andb].
  apply forallb_of_all. apply all_map.
  apply all_of_forallb in Hl.
  clear Hn. revert Hl H. induction l as [|x l IHl]; cbn; [ tauto | ].
  intros [Hx Hl] [Hpx Hpl].
  split; [ apply Hpx; assumption | apply IHl; assumption ].
Qed.

(* ------------------------------------------------------------------ *)
(* Terms at "type-level" sorts contain no typerec                       *)
(* ------------------------------------------------------------------ *)
Definition strat_names : list string := ["ty_env";"env";"ty";"ty_sub"].

Definition strat_rule_ok (p : string * rule) : bool :=
  match snd p with
  | term_rule c' _ t =>
      if inb (Parameterizer.sort_name t) strat_names
      then negb (eqb (fst p) "typerec")
           && forallb (fun q => inb (Parameterizer.sort_name (snd q)) strat_names) c'
      else true
  | _ => true
  end.

Lemma inb_string_true_iff (n : string) (l : list string) : inb n l = true <-> In n l.
Proof.
  induction l as [|a l IH]; cbv [inb] in *; cbn [existsb In] in *.
  { split; [ discriminate | tauto ]. }
  pose proof (eqb_spec n a) as Hs; destruct (eqb n a).
  { cbn [orb]. split; [ intros _; left; symmetry; exact Hs | intros _; reflexivity ]. }
  cbn [orb]. rewrite IH. split; [ tauto | ].
  intros [He | He]; [ congruence | exact He ].
Qed.

Lemma strat_ok : forallb strat_rule_ok target_multilanguage = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sort_name_subst (t : sort) (s : subst)
  : Parameterizer.sort_name t[/s/] = Parameterizer.sort_name t.
Proof. destruct t; reflexivity. Qed.

Lemma pargs_all_named (Q : term -> Prop) (R : string -> Prop) (c' : ctx) (s : list term)
  : WfCutElim.P_args string (fun e t => R (Parameterizer.sort_name t) -> Q e) s c' ->
    all (fun p => R (Parameterizer.sort_name (snd p))) c' ->
    all Q s.
Proof.
  revert s; induction c' as [| [n t] c' IH]; intros [|e s]; cbn; try tauto.
  intros [H1 H2] [Hr Hrs]. split.
  - apply H2. rewrite sort_name_subst. exact Hr.
  - apply IH; assumption.
Qed.

Lemma stratum_no_typerec : forall (e : term) (t : sort),
    Core.wf_term target_multilanguage [] e t ->
    In (Parameterizer.sort_name t) strat_names ->
    no_typerec e = true.
Proof.
  induction 1 using wf_term_cut_ind.
  - rewrite sort_name_subst. intro Hn.
    pose proof strat_ok as Hb. rewrite forallb_forall in Hb.
    specialize (Hb _ H). cbn [strat_rule_ok fst snd] in Hb.
    assert (Hin : inb (Parameterizer.sort_name t) strat_names = true)
      by (apply inb_string_true_iff; exact Hn).
    rewrite Hin in Hb.
    apply andb_prop in Hb. destruct Hb as [Hnm Hc].
    rewrite no_typerec_unfold, Hnm. cbn [andb].
    apply forallb_of_all.
    eapply pargs_all_named with (R := fun m => In m strat_names); [ exact H1 | ].
    rewrite forallb_forall in Hc.
    clear - Hc. induction c' as [|p c' IH]; cbn [all]; [ exact I | ].
    split.
    + apply inb_string_true_iff. apply Hc. left; reflexivity.
    + apply IH. intros x Hx. apply Hc. right; exact Hx.
  - destruct H.
  - intro Hn. apply IHwf_term.
    apply (sort_names_equal target_multilanguage_wf no_sort_eqns_in_tml wf_ctx_nil) in H0.
    rewrite H0; exact Hn.
Qed.

Ltac in_strat := vm_compute; repeat first [ left; reflexivity | right ].

Lemma simple_type_no_typerec (D : term) (HD : no_typerec D = true)
  : forall mu, simple_type_at D mu -> no_typerec mu = true.
Proof.
  induction mu using term_ind_all; [ intros [] | ].
  cbn [simple_type_at]. intro Hs.
  rewrite no_typerec_unfold.
  pose proof (eqb_spec n "*") as Hn1; destruct (eqb n "*"); [ subst n | ].
  { destruct l as [|D' [|? ?]]; try contradiction. cbn in Hs. subst D'.
    cbn [forallb]. rewrite HD. reflexivity. }
  pose proof (eqb_spec n "bool") as Hn2; destruct (eqb n "bool"); [ subst n | ].
  { destruct l as [|D' [|? ?]]; try contradiction. cbn in Hs. subst D'.
    cbn [forallb]. rewrite HD. reflexivity. }
  pose proof (eqb_spec n "->") as Hn3; destruct (eqb n "->"); [ subst n | ].
  { destruct l as [|t2 [|t1 [|D' [|? ?]]]]; try contradiction.
    destruct Hs as [HD' [Hs1 Hs2]]. subst D'.
    cbn [all] in H. destruct H as [IH2 [IH1 _]].
    cbn [forallb]. rewrite HD, (IH1 Hs1), (IH2 Hs2). reflexivity. }
  destruct Hs.
Qed.

Lemma no_typerec_fpe2 : no_typerec fpe2 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma meta_typerec_no_typerec (D G sigma e1 e2 e3 : term)
  (HD : no_typerec D = true) (HG : no_typerec G = true)
  (Hsg : no_typerec sigma = true)
  (H1 : no_typerec e1 = true) (H2 : no_typerec e2 = true) (H3 : no_typerec e3 = true)
  : forall mu, simple_type_at D mu ->
               no_typerec (meta_typerec D G mu sigma e1 e2 e3) = true.
Proof.
  induction mu using term_ind_all; [ intros [] | ].
  cbn [simple_type_at meta_typerec]. intro Hs.
  pose proof (eqb_spec n "*") as Hn1; destruct (eqb n "*"); [ exact H1 | ].
  pose proof (eqb_spec n "bool") as Hn2; destruct (eqb n "bool"); [ exact H2 | ].
  pose proof (eqb_spec n "->") as Hn3; destruct (eqb n "->"); [ | destruct Hs ].
  destruct l as [|t2 [|t1 [|D' [|? ?]]]]; try contradiction.
  destruct Hs as [HD' [Hs1 Hs2]]. subst D'.
  cbn [all] in H. destruct H as [IH2 [IH1 _]].
  cbv [MT_func]. apply no_typerec_subst; [ exact no_typerec_fpe2 | ].
  cbn [all snd].
  repeat split.
  - apply IH2; exact Hs2.
  - apply IH1; exact Hs1.
  - exact H3.
  - eapply simple_type_no_typerec; [ exact HD | exact Hs2 ].
  - eapply simple_type_no_typerec; [ exact HD | exact Hs1 ].
  - exact Hsg.
  - exact HG.
  - exact HD.
Qed.

Lemma elim_typerec_no_typerec : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    all_typerecs_simple e ->
    no_typerec (elim_typerec e) = true.
Proof.
  induction 1 using wf_term_cut_ind.
  - intro Hats.
    pose proof (eqb_spec name "typerec") as Hn; destruct (eqb name "typerec") eqn:Hnb.
    2:{
      assert (Helim : elim_typerec (con name s) = con name (map elim_typerec s))
        by (cbn [elim_typerec]; rewrite Hnb; reflexivity).
      rewrite Helim, no_typerec_unfold, Hnb; cbn [negb andb].
      apply forallb_of_all, all_map.
      destruct Hats as [_ Hall].
      pose proof (pargs_all (fun e => all_typerecs_simple e -> no_typerec (elim_typerec e) = true)
                    c' s H1) as Hp.
      clear - Hall Hp. revert Hall Hp.
      induction s as [|x s IH]; cbn [all]; [ tauto | ].
      intros [Hx Hs] [Hpx Hps]; split; [ apply Hpx; exact Hx | apply IH; assumption ]. }
    subst name. assert (Hin := H).
    apply tml_lookup in H. vm_compute in H. injection H as Hc' Hargs Ht. subst.
    assert (Hlen : length s = 7) by (rewrite (pargs_len _ _ _ H1); reflexivity).
    destruct s as [|e3 [|e2 [|e1 [|sg [|mu [|Gv [|Dv [|? ?]]]]]]]];
      cbn [length] in Hlen; try discriminate Hlen.
    (destruct H1 as [[[[[[[_ IHD] IHG] IHmu] IHsg] IH1] IH2] IH3]).
    (destruct Hats as [Hsimple [Ha3 [Ha2 [Ha1 [Hasg [Hamu [HaG [HaD _]]]]]]]]).
    inversion H0 as [|? ? ? ? ? W3 H0a]; subst; clear H0.
    inversion H0a as [|? ? ? ? ? W2 H0b]; subst; clear H0a.
    inversion H0b as [|? ? ? ? ? W1 H0c]; subst; clear H0b.
    inversion H0c as [|? ? ? ? ? Wsg H0d]; subst; clear H0c.
    inversion H0d as [|? ? ? ? ? Wmu H0e]; subst; clear H0d.
    inversion H0e as [|? ? ? ? ? WG H0f]; subst; clear H0e.
    inversion H0f as [|? ? ? ? ? WD H0g]; subst; clear H0f.
    rewrite elim_typerec_con7.
    assert (HD : no_typerec Dv = true)
      by (eapply stratum_no_typerec; [ exact WD | in_strat ]).
    assert (HG : no_typerec Gv = true)
      by (eapply stratum_no_typerec; [ exact WG | in_strat ]).
    assert (HS : no_typerec sg = true)
      by (eapply stratum_no_typerec; [ exact Wsg | in_strat ]).
    apply meta_typerec_no_typerec; try assumption.
    + apply IH1; exact Ha1.
    + apply IH2; exact Ha2.
    + apply IH3; exact Ha3.
  - destruct H.
  - intro Hats. apply IHwf_term; exact Hats.
Qed.

(* ------------------------------------------------------------------ *)
(* Transfer of typerec-free terms into the sublanguage                  *)
(* ------------------------------------------------------------------ *)
Definition sub_rule_ok (p : string * rule) : bool :=
  match snd p with
  | term_rule _ _ _ =>
      eqb (fst p) "typerec"
      || (match named_list_lookup_err target_multilanguage_without_typerec (fst p) with
          | Some r => eqb r (snd p)
          | None => false
          end)
  | _ => true
  end.

Lemma sub_rules_ok : forallb sub_rule_ok target_multilanguage = true.
Proof. vm_compute. reflexivity. Qed.

Lemma term_rule_transfer name c' args t
  : In (name, term_rule c' args t) target_multilanguage ->
    name <> "typerec" ->
    In (name, term_rule c' args t) target_multilanguage_without_typerec.
Proof.
  intros Hin Hne.
  pose proof sub_rules_ok as Hb. rewrite forallb_forall in Hb.
  specialize (Hb _ Hin). cbv [sub_rule_ok fst snd] in Hb.
  pose proof (eqb_spec name "typerec") as Hsp.
  destruct (eqb name "typerec"); [ contradiction | ].
  cbn [orb] in Hb.
  destruct (named_list_lookup_err target_multilanguage_without_typerec name) as [r|] eqn:Hl;
    [ | discriminate ].
  pose proof (eqb_spec r (term_rule c' args t)) as Hr.
  destruct (eqb r (term_rule c' args t)); [ subst r | discriminate ].
  apply named_list_lookup_err_in. symmetry. exact Hl.
Qed.

Section Conservativity.
  Context (Hconserv : forall t t' : sort,
              Core.eq_sort target_multilanguage [] t t' ->
              Core.eq_sort target_multilanguage_without_typerec [] t t').

  Lemma pargs_wf_args (c' : ctx) (s : list term)
    : WfCutElim.P_args string
        (fun e t => no_typerec e = true ->
                    Core.wf_term target_multilanguage_without_typerec [] e t) s c' ->
      forallb no_typerec s = true ->
      @Model.wf_args _ _ _ (core_model target_multilanguage_without_typerec) [] s c'.
  Proof.
    revert s; induction c' as [| [n t] c' IH]; intros [|e s]; cbn [WfCutElim.P_args];
      try tauto.
    { intros _ _. constructor. }
    intros [HP HPe] Hf. cbn [forallb] in Hf. apply andb_prop in Hf. destruct Hf as [He Hs].
    constructor.
    - apply HPe; exact He.
    - apply IH; assumption.
  Qed.

  Lemma no_typerec_transfer : forall (t : sort) (e : term),
      Core.wf_term target_multilanguage [] e t ->
      no_typerec e = true ->
      Core.wf_term target_multilanguage_without_typerec [] e t.
  Proof.
    induction 1 using wf_term_cut_ind.
    - rewrite no_typerec_unfold. intro Hnt.
      apply andb_prop in Hnt. destruct Hnt as [Hname Hargs].
      pose proof (eqb_spec name "typerec") as Hsp.
      destruct (eqb name "typerec"); [ discriminate Hname | ].
      eapply Core.wf_term_by.
      + apply term_rule_transfer; [ exact H | exact Hsp ].
      + apply pargs_wf_args; assumption.
    - destruct H.
    - intro Hnt. eapply Core.wf_term_conv; [ apply IHwf_term; exact Hnt | ].
      apply Hconserv; exact H0.
  Qed.

  Theorem partial_eval_wf_in_no_typerec_lang_modulo : forall (t : sort) (e : term),
      Core.wf_term target_multilanguage [] e t ->
      all_typerecs_simple e ->
      Core.wf_term target_multilanguage_without_typerec [] (elim_typerec e) t.
  Proof.
    intros t e H Hats.
    apply no_typerec_transfer with (t := t).
    - apply partial_eval_wf_in_target; assumption.
    - eapply elim_typerec_no_typerec; eassumption.
  Qed.
End Conservativity.

(* ------------------------------------------------------------------ *)
(* Conservativity of the typerec extension for sort equality.           *)
(* [target_multilanguage_without_typerec] contains every rule of         *)
(* [target_multilanguage] whose sort is type-level ([ty_env], [env],     *)
(* [ty], [ty_sub]); sorts only mention type-level terms, so a sort       *)
(* equality in the full target is derivable in the sublanguage           *)
(* (Theory/Conservativity.v, via the cut-free induction principle).      *)

Definition tml_stratum (n : string) : bool := inb n strat_names.

Lemma tml_conservative_check :
  @Conservativity.lang_conservative string _ tml_stratum target_multilanguage
    target_multilanguage_without_typerec = true.
Proof. vm_compute. reflexivity. Qed.

Lemma eq_sort_conservative_tml : forall t t',
    eq_sort target_multilanguage [] t t' ->
    eq_sort target_multilanguage_without_typerec [] t t'.
Proof.
  apply (proj1 (@Conservativity.eq_conservative_check string _ _ _ _ _
                  target_multilanguage_wf target_multilanguage_without_typerec_wf
                  tml_stratum tml_conservative_check []
                  ltac:(constructor) ltac:(constructor))).
Qed.

Theorem partial_eval_wf_in_no_typerec_lang : forall (t : sort) (e : term),
    Core.wf_term target_multilanguage [] e t ->
    all_typerecs_simple e ->
    Core.wf_term
      target_multilanguage_without_typerec
      []
      (elim_typerec e)
      t.
Proof.
  apply partial_eval_wf_in_no_typerec_lang_modulo.
  exact eq_sort_conservative_tml.
Qed.

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
