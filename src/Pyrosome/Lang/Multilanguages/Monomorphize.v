(* Monomorphization of the polymorphic multilanguage target.

   [mono] is RigidRewrite.v's generic rewriting engine instantiated on
   [poly_target_multilanguage] with [mono_rule_names] (PolyTrecTerms.v): the
   ["Lam-beta"] redex plus every rule that pushes a type substitution through
   a constructor and the type-substitution category laws.  Soundness and
   well-formedness come for free from the engine ([mono_sound], [mono_wf]).

   Monomorphization is not complete (System F is not monomorphizable), so
   the pipeline's completeness is a *decidable side condition*:
   [all_typerecs_simple_b] (a boolean refinement of TyperecPartialEval.v's
   [all_typerecs_simple]) together with
   [WfTransfer.avoids ["btrec"; "bAll"]].  When
   both hold, the term transfers down to [target_multilanguage] and
   TyperecPartialEval.v's partial evaluator [elim_typerec] finishes the job:
   [mono_elim_eq] / [mono_elim_wf].

   The file ends with worked examples, checked by [vm_compute].
   See PLAN-poly.md decisions 8, 9 and 10.                                  *)

Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches Compilers.Compilers Elab.ElabCompilers.
Import Core.Notations.
From Stdlib Require derive.Derive.

From Pyrosome.Theory Require Import WfTransfer PatternRigidity RigidRewrite.
From Pyrosome.Theory Require Conservativity.

From Pyrosome.Lang.Multilanguages Require Import PolyTrecTerms TyperecPartialEval PolySource.

Local Notation term := (@Term.term string).
Local Notation sort := (@Term.sort string).
Local Notation lang := (@Rule.lang string).
(* ---------------- 1. the monomorphizer ---------------- *)

Definition mono_fuel := 1000.

(* [mono] is two passes of the engine: monomorphize (["Lam-beta"], the
   type-substitution pushes and laws, and ["typerec to btrec"]), then
   de-sugar the [#"btrec"]s back into [#"typerec"]s with ["btrec def"] so
   that TyperecPartialEval.v's [elim_typerec] applies.  The de-sugaring pass
   has to be separate: ["btrec def"] is the converse of ["typerec to btrec"],
   so running them together would loop. *)
Definition monomorphize (e : term) : term :=
  RigidRewrite.rewrite_n (V:=string) poly_target_multilanguage mono_rule_names mono_fuel e.

Definition desugar (e : term) : term :=
  RigidRewrite.rewrite_n (V:=string) poly_target_multilanguage desugar_rule_names mono_fuel e.

Definition mono (e : term) : term := desugar (monomorphize e).

Theorem monomorphize_sound : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    eq_term poly_target_multilanguage [] t e (monomorphize e).
Proof.
  intros e t Hwf. unfold monomorphize.
  apply (RigidRewrite.rewrite_n_sound (V:=string) poly_target_multilanguage_wf
           mono_rule_names mono_rules_rigid ltac:(constructor) mono_fuel).
  exact Hwf.
Qed.

Theorem monomorphize_wf : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    wf_term poly_target_multilanguage [] (monomorphize e) t.
Proof.
  intros e t Hwf. unfold monomorphize.
  apply (RigidRewrite.rewrite_n_wf (V:=string) poly_target_multilanguage_wf
           mono_rule_names mono_rules_rigid ltac:(constructor) mono_fuel).
  exact Hwf.
Qed.

Theorem desugar_sound : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    eq_term poly_target_multilanguage [] t e (desugar e).
Proof.
  intros e t Hwf. unfold desugar.
  apply (RigidRewrite.rewrite_n_sound (V:=string) poly_target_multilanguage_wf
           desugar_rule_names desugar_rules_rigid ltac:(constructor) mono_fuel).
  exact Hwf.
Qed.

Theorem desugar_wf : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    wf_term poly_target_multilanguage [] (desugar e) t.
Proof.
  intros e t Hwf. unfold desugar.
  apply (RigidRewrite.rewrite_n_wf (V:=string) poly_target_multilanguage_wf
           desugar_rule_names desugar_rules_rigid ltac:(constructor) mono_fuel).
  exact Hwf.
Qed.

Theorem mono_sound : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    eq_term poly_target_multilanguage [] t e (mono e).
Proof.
  intros e t Hwf. unfold mono.
  eapply eq_term_trans;
    [ apply monomorphize_sound; exact Hwf
    | apply desugar_sound; apply monomorphize_wf; exact Hwf ].
Qed.

Theorem mono_wf : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    wf_term poly_target_multilanguage [] (mono e) t.
Proof.
  intros e t Hwf. unfold mono.
  apply desugar_wf; apply monomorphize_wf; exact Hwf.
Qed.

(* ---------------- 2. the decidable simplicity check ---------------- *)

Lemma term_eqb_true (x y : term) : eqb x y = true -> x = y.
Proof.
  intro H.
  pose proof (@eqb_spec (Term.term string) _ (@term_eqb_ok string _ _) x y) as Hs.
  rewrite H in Hs. exact Hs.
Qed.

Fixpoint simple_type_at_b (D mu : term) {struct mu} : bool :=
  match mu with
  | var _ => false
  | con n l =>
      if eqb n "*" then match l with [D'] => eqb D' D | _ => false end
      else if eqb n "bool" then match l with [D'] => eqb D' D | _ => false end
      else if eqb n "->" then
             match l with
             | [t2;t1;D'] =>
                 (eqb D' D && simple_type_at_b D t1 && simple_type_at_b D t2)%bool
             | _ => false end
      else false
  end.

Lemma simple_type_at_b_spec
  : forall mu D, simple_type_at_b D mu = true -> simple_type_at D mu.
Proof.
  induction mu using term_ind; intros D Hb; [ discriminate |].
  rename H into IHl; rename Hb into H.
  cbn [simple_type_at_b simple_type_at] in *.
  destruct (eqb n "*").
  { destruct l as [|D' [|? ?]]; try discriminate.
    apply term_eqb_true in H; exact H. }
  destruct (eqb n "bool").
  { destruct l as [|D' [|? ?]]; try discriminate.
    apply term_eqb_true in H; exact H. }
  destruct (eqb n "->"); [| discriminate].
  destruct l as [|t2 [|t1 [|D' [|? ?]]]]; try discriminate.
  cbn [all] in IHl. destruct IHl as [H2 [H1 [_ _]]].
  apply andb_prop in H; destruct H as [H Ht2].
  apply andb_prop in H; destruct H as [HD Ht1].
  repeat split.
  - apply term_eqb_true in HD; exact HD.
  - apply H1; exact Ht1.
  - apply H2; exact Ht2.
Qed.

Definition typerec_mu_ok_b (n : string) (s : list term) : bool :=
  if eqb n "typerec"
  then match s with
       | [_;_;_;_;mu;_;D] => simple_type_at_b D mu
       | _ => true
       end
  else true.

Lemma typerec_mu_ok_b_spec n s
  : typerec_mu_ok_b n s = true -> typerec_mu_ok n s.
Proof.
  cbv [typerec_mu_ok_b typerec_mu_ok].
  destruct (eqb n "typerec"); [| trivial].
  destruct s as [|?[|?[|?[|?[|mu[|?[|D [|? ?]]]]]]]]; try trivial.
  apply simple_type_at_b_spec.
Qed.

Fixpoint all_typerecs_simple_b (program : term) : bool :=
  match program with
  | var _ => true
  | con n s =>
      (typerec_mu_ok_b n s
       && (fix f (l : list term) : bool :=
             match l with
             | [] => true
             | x::l' => (all_typerecs_simple_b x && f l')%bool
             end) s)%bool
  end.

Lemma all_typerecs_simple_b_unfold n s
  : all_typerecs_simple_b (con n s)
    = (typerec_mu_ok_b n s && forallb all_typerecs_simple_b s)%bool.
Proof.
  cbn [all_typerecs_simple_b]. f_equal; induction s; cbn; congruence.
Qed.

Lemma all_typerecs_simple_b_spec
  : forall e, all_typerecs_simple_b e = true -> all_typerecs_simple e.
Proof.
  induction e using term_ind; intro He; [ exact I |].
  rewrite all_typerecs_simple_b_unfold in He.
  apply andb_prop in He; destruct He as [Hm Hs].
  split; [ apply typerec_mu_ok_b_spec; exact Hm |].
  revert H Hs; clear; induction l as [|e l IH]; cbn [all forallb]; [ tauto |].
  intros [He Hl] Hf. apply andb_prop in Hf; destruct Hf as [H1 H2].
  split; [ apply He; exact H1 | apply IH; assumption ].
Qed.

(* ---------------- 3. transfer down to [target_multilanguage] ---------------- *)

(* The two constructors of the polymorphic extension that
   [target_multilanguage] does not have, and that therefore have to be gone
   before the term can be handed to TyperecPartialEval.v.

   Neither is guaranteed to disappear, which is why this is a per-term
   decidable side condition rather than a theorem:
     - [#"btrec"] is introduced by ["typerec to btrec"] during
       monomorphization and removed again by the de-sugaring pass, but only
       at nodes where ["btrec def"] matches;
     - [#"bAll"] is introduced by ["typerec All"], i.e. by a boundary at a
       polymorphic type; nothing removes it, so a program whose boundaries
       survive monomorphization at an [#"All"] type fails this check (as it
       must -- it also fails [all_typerecs_simple_b]).
   In particular [mono] never introduces either constructor at a node where
   the input had none: the only rules that produce one are ["typerec to
   btrec"] (from a [#"typerec"]) and, outside [mono_rule_names] entirely,
   ["typerec All"].                                                        *)
Definition mono_excluded_cons : list string := ["btrec"; "bAll"].

Lemma poly_to_tml_cov
  : WfTransfer.term_rules_covered string mono_excluded_cons
      target_multilanguage poly_target_multilanguage = true.
Proof. vm_compute. reflexivity. Qed.

Lemma poly_to_tml_conservative
  : @Conservativity.lang_conservative string _ tml_stratum
      poly_target_multilanguage target_multilanguage = true.
Proof. vm_compute. reflexivity. Qed.

Theorem wf_poly_to_tml : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    WfTransfer.avoids string mono_excluded_cons e = true ->
    wf_term target_multilanguage [] e t.
Proof.
  apply (@WfTransfer.wf_term_transfer_check string _ _ _ _ _
           target_multilanguage_wf poly_target_multilanguage_wf
           tml_stratum poly_to_tml_conservative mono_excluded_cons poly_to_tml_cov).
Qed.

(* ---------------- 4. the pipeline ---------------- *)

Lemma tml_incl_poly : incl target_multilanguage poly_target_multilanguage.
Proof.
  unfold poly_target_multilanguage.
  do 5 apply incl_appr. apply incl_refl.
Qed.

Theorem mono_elim_eq : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    all_typerecs_simple_b (mono e) = true ->
    WfTransfer.avoids string mono_excluded_cons (mono e) = true ->
    eq_term poly_target_multilanguage [] t e (elim_typerec (mono e)).
Proof.
  intros e t Hwf Hsimple Havoid.
  assert (Hmt : wf_term target_multilanguage [] (mono e) t)
    by (apply wf_poly_to_tml; [ apply mono_wf; exact Hwf | exact Havoid ]).
  eapply eq_term_trans; [ apply mono_sound; exact Hwf |].
  eapply eq_term_lang_monotonicity; [ exact tml_incl_poly |].
  apply elim_typerec_eq; [ exact Hmt | apply all_typerecs_simple_b_spec; exact Hsimple ].
Qed.

Theorem mono_elim_wf : forall e t,
    wf_term poly_target_multilanguage [] e t ->
    all_typerecs_simple_b (mono e) = true ->
    WfTransfer.avoids string mono_excluded_cons (mono e) = true ->
    wf_term target_multilanguage_without_typerec [] (elim_typerec (mono e)) t.
Proof.
  intros e t Hwf Hsimple Havoid.
  apply partial_eval_wf_in_no_typerec_lang.
  - apply wf_poly_to_tml; [ apply mono_wf; exact Hwf | exact Havoid ].
  - apply all_typerecs_simple_b_spec; exact Hsimple.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Worked examples.                                                  *)
(*                                                                      *)
(* All three are closed poly-source programs, elaborated in             *)
(* [poly_source_multilanguage] and compiled with                        *)
(* [PCMP = poly_multilang_compiler ++ polymorphic_interoperating_langs_compiler]. *)
(* ------------------------------------------------------------------ *)

Definition ex_star_sort_unelab : sort := {{s #"exp" #"ty_emp" #"emp" #"*" }}.

Derive ex_star_sort
  in (elab_sort poly_source_multilanguage [] ex_star_sort_unelab ex_star_sort)
  as ex_star_sort_wf.
Proof. solve_elab_term_or_sort poly_source_multilanguage. Qed.

(* --- Positive example.

   [ttd_bool ((Lam. lambda x:ty_hd. x) @ bool) T]:
   the polymorphic identity, instantiated at [#"bool"], applied to [#"T"],
   and then sent to the dynamic side by a [#"ttd"] boundary.  Monomorphizing
   contracts the ["Lam-beta"] redex and pushes the resulting type
   substitution through the body, leaving a [#"typerec"] at the *concrete*
   type [#"bool"], which [elim_typerec] then removes.                      *)
Definition ex1_unelab : term :=
  {{e #"ttd" #"bool"
       (#"app" (#"@" (#"ret" (#"Lam" (#"ret" (#"lambda" #"ty_hd" (#"ret" #"hd"))))) #"bool")
               (#"ret" #"T")) }}.

Derive ex1
  in (elab_term poly_source_multilanguage [] ex1_unelab ex1 ex_star_sort)
  as ex1_wf.
Proof. solve_elab_term_or_sort poly_source_multilanguage. Qed.

Definition ex1_compiled := Eval vm_compute in compile PCMP ex1.
Definition ex1_mono := Eval vm_compute in mono ex1_compiled.

Lemma ex1_compiled_eq : compile PCMP ex1 = ex1_compiled.
Proof. vm_cast_no_check (@eq_refl term ex1_compiled). Qed.

Lemma ex1_mono_eq : mono (compile PCMP ex1) = ex1_mono.
Proof. rewrite ex1_compiled_eq. vm_cast_no_check (@eq_refl term ex1_mono). Qed.

Lemma ex1_simple : all_typerecs_simple_b (mono (compile PCMP ex1)) = true.
Proof. rewrite ex1_mono_eq. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ex1_avoids
  : WfTransfer.avoids string mono_excluded_cons (mono (compile PCMP ex1)) = true.
Proof. rewrite ex1_mono_eq. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ex1_no_typerec
  : no_typerec (elim_typerec (mono (compile PCMP ex1))) = true.
Proof. rewrite ex1_mono_eq. vm_cast_no_check (@eq_refl bool true). Qed.

(* The result of the whole pipeline, for any [t] at which the compiled
   program is well formed (the compiler-preservation half of the pipeline
   lives in PolyMultilangCompiler.v). *)
Corollary ex1_pipeline : forall t,
    wf_term poly_target_multilanguage [] (compile PCMP ex1) t ->
    eq_term poly_target_multilanguage [] t (compile PCMP ex1)
      (elim_typerec (mono (compile PCMP ex1)))
    /\ wf_term target_multilanguage_without_typerec []
         (elim_typerec (mono (compile PCMP ex1))) t.
Proof.
  intros t Hwf.
  exact (conj (mono_elim_eq Hwf ex1_simple ex1_avoids)
              (mono_elim_wf Hwf ex1_simple ex1_avoids)).
Qed.

(* [Eval vm_compute in (elim_typerec (mono (compile PCMP ex1)))] is

   #"let" (#"app" (#"ret" (#"lambda" #"bool" (#"ret" #"hd"))) (#"ret" #"T"))
     (#"app" (#".1" (#"ret" (#"val_subst" #"wkn" #"bbool"))) (#"ret" #"hd"))

   (implicit arguments elided): the polymorphism is gone, the [#"typerec"]
   has been replaced by the [#"bbool"] boundary case, and the whole term is
   well formed in [target_multilanguage_without_typerec].                  *)

(* --- Negative example.

   A program that *exports* a polymorphic function cannot be monomorphized:
   the [#"ttd"] boundary sits under a [#"Lam"], at the bound type variable
   [#"ty_hd"], and no instantiation ever reaches it.                        *)
Definition ex2_sort_unelab : sort :=
  {{s #"exp" #"ty_emp" #"emp" (#"All" (#"->" #"ty_hd" #"*")) }}.

Derive ex2_sort
  in (elab_sort poly_source_multilanguage [] ex2_sort_unelab ex2_sort)
  as ex2_sort_wf.
Proof. solve_elab_term_or_sort poly_source_multilanguage. Qed.

Definition ex2_unelab : term :=
  {{e #"ret" (#"Lam" (#"ret" (#"lambda" #"ty_hd" (#"ttd" #"ty_hd" (#"ret" #"hd"))))) }}.

Derive ex2
  in (elab_term poly_source_multilanguage [] ex2_unelab ex2 ex2_sort)
  as ex2_wf.
Proof. solve_elab_term_or_sort poly_source_multilanguage. Qed.

Definition ex2_compiled := Eval vm_compute in compile PCMP ex2.
Definition ex2_mono := Eval vm_compute in mono ex2_compiled.

Lemma ex2_compiled_eq : compile PCMP ex2 = ex2_compiled.
Proof. vm_cast_no_check (@eq_refl term ex2_compiled). Qed.

Lemma ex2_mono_eq : mono (compile PCMP ex2) = ex2_mono.
Proof. rewrite ex2_compiled_eq. vm_cast_no_check (@eq_refl term ex2_mono). Qed.

Lemma ex2_not_simple : all_typerecs_simple_b (mono (compile PCMP ex2)) = false.
Proof. rewrite ex2_mono_eq. vm_cast_no_check (@eq_refl bool false). Qed.

(* --- Second positive example: a *polymorphic* to-dynamic function,
   instantiated.

   [((Lam. lambda x:ty_hd. ttd_ty_hd x) @ bool) T] sends its argument to the
   dynamic side at the *bound type variable* [#"ty_hd"], so the boundary only
   becomes concrete after monomorphization.  This is the example that
   motivated [#"btrec"] (PolyTrecTerms.v Stage 5): with ["ty_subst typerec'"]
   alone the type substitution could never be pushed into the [#"typerec"]
   node, and the check below was [false].                                   *)
Definition ex3_unelab : term :=
  {{e #"app" (#"@" (#"ret" (#"Lam" (#"ret" (#"lambda" #"ty_hd"
                              (#"ttd" #"ty_hd" (#"ret" #"hd")))))) #"bool")
       (#"ret" #"T") }}.

Derive ex3
  in (elab_term poly_source_multilanguage [] ex3_unelab ex3 ex_star_sort)
  as ex3_wf.
Proof. solve_elab_term_or_sort poly_source_multilanguage. Qed.

Definition ex3_compiled := Eval vm_compute in compile PCMP ex3.
Definition ex3_mono := Eval vm_compute in mono ex3_compiled.

Lemma ex3_compiled_eq : compile PCMP ex3 = ex3_compiled.
Proof. vm_cast_no_check (@eq_refl term ex3_compiled). Qed.

Lemma ex3_mono_eq : mono (compile PCMP ex3) = ex3_mono.
Proof. rewrite ex3_compiled_eq. vm_cast_no_check (@eq_refl term ex3_mono). Qed.

Lemma ex3_simple : all_typerecs_simple_b (mono (compile PCMP ex3)) = true.
Proof. rewrite ex3_mono_eq. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ex3_avoids
  : WfTransfer.avoids string mono_excluded_cons (mono (compile PCMP ex3)) = true.
Proof. rewrite ex3_mono_eq. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ex3_no_typerec
  : no_typerec (elim_typerec (mono (compile PCMP ex3))) = true.
Proof. rewrite ex3_mono_eq. vm_cast_no_check (@eq_refl bool true). Qed.

Corollary ex3_pipeline : forall t,
    wf_term poly_target_multilanguage [] (compile PCMP ex3) t ->
    eq_term poly_target_multilanguage [] t (compile PCMP ex3)
      (elim_typerec (mono (compile PCMP ex3)))
    /\ wf_term target_multilanguage_without_typerec []
         (elim_typerec (mono (compile PCMP ex3))) t.
Proof.
  intros t Hwf.
  exact (conj (mono_elim_eq Hwf ex3_simple ex3_avoids)
              (mono_elim_wf Hwf ex3_simple ex3_avoids)).
Qed.

(* [Eval vm_compute in (elim_typerec (mono (compile PCMP ex3)))] is

   #"app" (#"ret" (#"lambda" #"bool"
             (#"let" (#"ret" #"hd")
                (#"app" (#".1" (#"ret" (#"val_subst" #"wkn" #"bbool")))
                        (#"ret" #"hd")))))
          (#"ret" #"T")

   (implicit arguments elided): the polymorphic to-dynamic function has been
   specialized to [#"bool"] and its boundary has become the [#"bbool"] case.
   No [#"btrec"], no [#"bAll"], no [#"typerec"] remain.                     *)
