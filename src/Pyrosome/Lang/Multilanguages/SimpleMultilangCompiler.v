Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* imports for compilers *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations.

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.

(* import the relevant language fragments *)
From Pyrosome.Lang Require Import SimpleVSTLC.
From Pyrosome.Lang Require Import UTLC.
From Pyrosome.Lang Require Import BoolType.
From Pyrosome.Lang Require Import SimpleVProd.

(* imports for polymorphism *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers.
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Export TrecTerms.

Local Notation compiler :=
  (@CompilerDefs.compiler string (Term.term string) (Term.sort string)).

(* ------------------------------------------------------------------ *)
(* The compiler, as originally written (unelaborated).  Kept for
   documentation: the two target terms below are its elaboration.      *)
Definition simple_multilang_compiler_def : compiler :=
    match # from boundaries with
    | {{e #"dtt" "G" "A" "e"}} =>
        {{e #"let" "e" (#"app" (#".2" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                               (#"ret" #"hd")) }}
    | {{e #"ttd" "G" "A" "e"}} =>
        {{e #"let" "e" (#"app" (#".1" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                               (#"ret" #"hd")) }}
    end.

(* ------------------------------------------------------------------ *)
(* The elaborated compiler.

   The two cases are elaborated individually, on top of [trec_boundaries],
   the already-elaborated typerec term from TrecTerms.v; the computational
   route [infer_compiler_simple_autoinj 4 target_multilanguage ...] does not
   apply to this compiler.

   The compiled body binds the source argument ["e"] with [#"let"] and
   applies the boundary function to [#"ret" #"hd"].  A variable is a value,
   so [STLC-beta] fires, which is what makes the ["dtt star"]/["ttd star"]
   equations provable (via the ["let eta"] rule).  *)

Definition dtt_case_unelab :=
  {{e #"let" "e" (#"app" (#".2" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                         (#"ret" #"hd")) }}.

Derive dtt_case_tgt
  in ( elab_term target_multilanguage
         [("e", {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}});
          ("A", {{s #"ty" #"ty_emp"}});
          ("G", {{s #"env" #"ty_emp"}})]
         dtt_case_unelab
         dtt_case_tgt
         {{s #"exp" #"ty_emp" "G" "A"}}
     ) as dtt_case_tgt_wf.
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

Definition ttd_case_unelab :=
  {{e #"let" "e" (#"app" (#".1" (#"ret" (#"val_subst" #"wkn" {trec_boundaries_unelab})))
                         (#"ret" #"hd")) }}.

Derive ttd_case_tgt
  in ( elab_term target_multilanguage
         [("e", {{s #"exp" #"ty_emp" "G" "A"}});
          ("A", {{s #"ty" #"ty_emp"}});
          ("G", {{s #"env" #"ty_emp"}})]
         ttd_case_unelab
         ttd_case_tgt
         {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}}
     ) as ttd_case_tgt_wf.
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

(* The entries must be in the SAME ORDER as the term rules of [boundaries],
   whose name list is [... ; "dtt"; "exp_subst ttd"; "ttd"], i.e. ["dtt"]
   comes first.  With the opposite order [preserving_compiler_ext] cannot be
   assembled at all (the [term] constructor tries to unify ["dtt"] with
   ["ttd"]).  Compilation itself is by name lookup, so the order does not
   change any compiled term. *)
Definition simple_multilang_compiler : compiler :=
  [("dtt", term_case ["e"; "A"; "G"] dtt_case_tgt);
   ("ttd", term_case ["e"; "A"; "G"] ttd_case_tgt)].

(* ------------------------------------------------------------------ *)
(* The two term-constructor obligations of [preserving_compiler_ext].   *)

Lemma dtt_case_wf
  : wf_term target_multilanguage
      [("e", {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}});
       ("A", {{s #"ty" #"ty_emp"}});
       ("G", {{s #"env" #"ty_emp"}})]
      dtt_case_tgt {{s #"exp" #"ty_emp" "G" "A"}}.
Proof. pose proof target_multilanguage_wf. compute_term_wf. Qed.

Lemma ttd_case_wf
  : wf_term target_multilanguage
      [("e", {{s #"exp" #"ty_emp" "G" "A"}});
       ("A", {{s #"ty" #"ty_emp"}});
       ("G", {{s #"env" #"ty_emp"}})]
      ttd_case_tgt {{s #"exp" #"ty_emp" "G" (#"*" #"ty_emp")}}.
Proof. pose proof target_multilanguage_wf. compute_term_wf. Qed.

(* ------------------------------------------------------------------ *)
(* One [eq_term] lemma per boundary equation, each discharged by the e-graph
   reducer.

   [norev] makes every rule of the target language usable LEFT-TO-RIGHT only.
   Forward-only saturation is essential here: with rules also applied
   backwards the search is dominated by backward rewrites, and the
   ["exp_subst"] and ["typerec func"] equations do not converge within any
   practical budget.  It is also what closes the two mismatch equations at
   [#"->"], where the eager [#"bool?"] check must reduce to [#"Error"].

   [by_reduction_fwd] is [Automation.by_reduction'] under that filter, with
   the well-formedness side conditions discharged: the context by
   [solve_wf_ctx] and the two [wf_term] goals by [compute_term_wf], whose
   first goal is [assumption] on [wf_lang target_multilanguage] -- hence the
   [pose proof].  It is exported for reuse by PolyBoundaries.v.             *)

Definition norev : string * Rule.rule string -> bool := fun _ => false.

Ltac by_reduction_fwd :=
  pose proof target_multilanguage_wf;
  Automation.by_reduction' norev Automation.empty_inj_rules;
  [ solve_wf_ctx | compute_term_wf | compute_term_wf ].

(* ------------------------------------------------------------------ *)
(* The three [#"typerec"] cases are the value constants [#"bstar"] /
   [#"bbool"] / [#"bfunc"] of [boundary_cases], whose substitution rules are
   one-step rewrites; that is what lets the two ["exp_subst"] equations go
   through without per-case helper lemmas.                                 *)

Definition CMP := simple_multilang_compiler ++ interoperating_langs_compiler.

Definition brule (n:string) := named_list_lookup (Rule.sort_rule [] []) boundaries n.
Definition gctx n := match brule n with Rule.term_eq_rule c _ _ _ => compile_ctx CMP c | _ => [] end.
Definition gsrt n := match brule n with Rule.term_eq_rule _ _ _ t => compile_sort CMP t | _ => default end.
Definition glhs n := match brule n with Rule.term_eq_rule _ e _ _ => compile CMP e | _ => default end.
Definition grhs n := match brule n with Rule.term_eq_rule _ _ e _ => compile CMP e | _ => default end.

Definition c_dtt_star := Eval vm_compute in gctx "dtt star".
Definition s_dtt_star := Eval vm_compute in gsrt "dtt star".
Definition l_dtt_star := Eval vm_compute in glhs "dtt star".
Definition r_dtt_star := Eval vm_compute in grhs "dtt star".
(* Provable because the compiler let-binds "e": the beta-redex has a value
   (the variable [#"hd"]) as its argument, and ["let eta"] collapses the
   residual [#"let" "e" (#"ret" #"hd")] back to ["e"]. *)
Lemma eq_dtt_star : eq_term target_multilanguage c_dtt_star s_dtt_star l_dtt_star r_dtt_star.
Proof. unfold c_dtt_star, s_dtt_star, l_dtt_star, r_dtt_star. by_reduction_fwd. Qed.

Definition c_ttd_star := Eval vm_compute in gctx "ttd star".
Definition s_ttd_star := Eval vm_compute in gsrt "ttd star".
Definition l_ttd_star := Eval vm_compute in glhs "ttd star".
Definition r_ttd_star := Eval vm_compute in grhs "ttd star".
(* As "dtt star", via the other projection. *)
Lemma eq_ttd_star : eq_term target_multilanguage c_ttd_star s_ttd_star l_ttd_star r_ttd_star.
Proof. unfold c_ttd_star, s_ttd_star, l_ttd_star, r_ttd_star. by_reduction_fwd. Qed.

Definition c_dtt_True := Eval vm_compute in gctx "dtt True".
Definition s_dtt_True := Eval vm_compute in gsrt "dtt True".
Definition l_dtt_True := Eval vm_compute in glhs "dtt True".
Definition r_dtt_True := Eval vm_compute in grhs "dtt True".
Lemma eq_dtt_True : eq_term target_multilanguage c_dtt_True s_dtt_True l_dtt_True r_dtt_True.
Proof. unfold c_dtt_True, s_dtt_True, l_dtt_True, r_dtt_True. by_reduction_fwd. Qed.

Definition c_dtt_False := Eval vm_compute in gctx "dtt False".
Definition s_dtt_False := Eval vm_compute in gsrt "dtt False".
Definition l_dtt_False := Eval vm_compute in glhs "dtt False".
Definition r_dtt_False := Eval vm_compute in grhs "dtt False".
Lemma eq_dtt_False : eq_term target_multilanguage c_dtt_False s_dtt_False l_dtt_False r_dtt_False.
Proof. unfold c_dtt_False, s_dtt_False, l_dtt_False, r_dtt_False. by_reduction_fwd. Qed.

Definition c_ttd_True := Eval vm_compute in gctx "ttd True".
Definition s_ttd_True := Eval vm_compute in gsrt "ttd True".
Definition l_ttd_True := Eval vm_compute in glhs "ttd True".
Definition r_ttd_True := Eval vm_compute in grhs "ttd True".
Lemma eq_ttd_True : eq_term target_multilanguage c_ttd_True s_ttd_True l_ttd_True r_ttd_True.
Proof. unfold c_ttd_True, s_ttd_True, l_ttd_True, r_ttd_True. by_reduction_fwd. Qed.

Definition c_ttd_False := Eval vm_compute in gctx "ttd False".
Definition s_ttd_False := Eval vm_compute in gsrt "ttd False".
Definition l_ttd_False := Eval vm_compute in glhs "ttd False".
Definition r_ttd_False := Eval vm_compute in grhs "ttd False".
Lemma eq_ttd_False : eq_term target_multilanguage c_ttd_False s_ttd_False l_ttd_False r_ttd_False.
Proof. unfold c_ttd_False, s_ttd_False, l_ttd_False, r_ttd_False. by_reduction_fwd. Qed.

Definition c_dtt_func := Eval vm_compute in gctx "dtt func".
Definition s_dtt_func := Eval vm_compute in gsrt "dtt func".
Definition l_dtt_func := Eval vm_compute in glhs "dtt func".
Definition r_dtt_func := Eval vm_compute in grhs "dtt func".
(* Proved below, after the hop lemmas. *)

Definition c_ttd_func := Eval vm_compute in gctx "ttd func".
Definition s_ttd_func := Eval vm_compute in gsrt "ttd func".
Definition l_ttd_func := Eval vm_compute in glhs "ttd func".
Definition r_ttd_func := Eval vm_compute in grhs "ttd func".
(* Proved below, after the hop lemmas. *)

(* ------------------------------------------------------------------ *)
(* The two ["func"] equations, each proved in TWO HOPS through an explicit
   intermediate term.

   The two compiled sides are not mismatched; what the e-graph cannot do in
   one go is the ["typerec func"] rewrite, which strictly GROWS the term.
   [egraph_reducing_equal] restarts saturation from the extracted (smallest)
   representative as soon as a weight decrease is observed, so a
   term-growing first step is discarded: the [#"typerec"] node is re-created
   un-unfolded at every restart and the remaining work (["bfunc def"],
   STLC-beta, ["bool?-func"], ["mif false"], the substitution laws) never
   runs in the same round.  Supplying the once-unfolded term as an explicit
   intermediate splits the equation into two hops that each converge.

   [I1] / [J1] are the compiled left-hand sides with
   [#"typerec" (#"->" "A" "B") ...] replaced by its ["typerec func"] reduct
   [#"bfunc" "A" "B" TREC["A"] TREC["B"]].                                  *)

Definition TRECv X := {{e #"typerec" {X} {boundary_sigma} #"bstar" #"bbool"
                          (#"bfunc" {tva} {tvb} {ovar 1} {ovar 0}) }}.

Definition I1_unelab :=
  {{e #"let" (#"ret" (#"ulambda" "e"))
       (#"app" (#".2" (#"ret" (#"val_subst" #"wkn"
          (#"bfunc" "A" "B" {TRECv {{e "A"}} } {TRECv {{e "B"}} }))))
          (#"ret" #"hd")) }}.

Derive I1 in (elab_term target_multilanguage c_dtt_func I1_unelab I1 s_dtt_func)
  as I1_wf.
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

Definition J1_unelab :=
  {{e #"let" (#"ret" "v")
       (#"app" (#".1" (#"ret" (#"val_subst" #"wkn"
          (#"bfunc" "A" "B" {TRECv {{e "A"}} } {TRECv {{e "B"}} }))))
          (#"ret" #"hd")) }}.

Derive J1 in (elab_term target_multilanguage c_ttd_func J1_unelab J1 s_ttd_func)
  as J1_wf.
Proof. solve_elab_term_or_sort target_multilanguage. Qed.

(* hop 1: ["typerec func"] only. *)
Lemma eq_dtt_func_hop1
  : eq_term target_multilanguage c_dtt_func s_dtt_func l_dtt_func I1.
Proof. unfold l_dtt_func, c_dtt_func, s_dtt_func. by_reduction_fwd. Qed.

(* hop 2: ["bfunc def"], STLC-beta, ["bool?-func"], ["mif false"], substitution. *)
Lemma eq_dtt_func_hop2
  : eq_term target_multilanguage c_dtt_func s_dtt_func I1 r_dtt_func.
Proof. unfold r_dtt_func, c_dtt_func, s_dtt_func. by_reduction_fwd. Qed.

Lemma eq_ttd_func_hop1
  : eq_term target_multilanguage c_ttd_func s_ttd_func l_ttd_func J1.
Proof. unfold l_ttd_func, c_ttd_func, s_ttd_func. by_reduction_fwd. Qed.

Lemma eq_ttd_func_hop2
  : eq_term target_multilanguage c_ttd_func s_ttd_func J1 r_ttd_func.
Proof. unfold r_ttd_func, c_ttd_func, s_ttd_func. by_reduction_fwd. Qed.

Lemma eq_dtt_func : eq_term target_multilanguage c_dtt_func s_dtt_func l_dtt_func r_dtt_func.
Proof. eapply eq_term_trans; [apply eq_dtt_func_hop1 | apply eq_dtt_func_hop2]. Qed.

Lemma eq_ttd_func : eq_term target_multilanguage c_ttd_func s_ttd_func l_ttd_func r_ttd_func.
Proof. eapply eq_term_trans; [apply eq_ttd_func_hop1 | apply eq_ttd_func_hop2]. Qed.

Definition c_dtt_ulambda_mismatch := Eval vm_compute in gctx "dtt ulambda mismatch".
Definition s_dtt_ulambda_mismatch := Eval vm_compute in gsrt "dtt ulambda mismatch".
Definition l_dtt_ulambda_mismatch := Eval vm_compute in glhs "dtt ulambda mismatch".
Definition r_dtt_ulambda_mismatch := Eval vm_compute in grhs "dtt ulambda mismatch".
Lemma eq_dtt_ulambda_mismatch : eq_term target_multilanguage c_dtt_ulambda_mismatch s_dtt_ulambda_mismatch l_dtt_ulambda_mismatch r_dtt_ulambda_mismatch.
Proof. unfold c_dtt_ulambda_mismatch, s_dtt_ulambda_mismatch, l_dtt_ulambda_mismatch, r_dtt_ulambda_mismatch. by_reduction_fwd. Qed.

Definition c_dtt_uT_mismatch := Eval vm_compute in gctx "dtt uT mismatch".
Definition s_dtt_uT_mismatch := Eval vm_compute in gsrt "dtt uT mismatch".
Definition l_dtt_uT_mismatch := Eval vm_compute in glhs "dtt uT mismatch".
Definition r_dtt_uT_mismatch := Eval vm_compute in grhs "dtt uT mismatch".
(* Closed by the explicit-argument [#"bfunc"] plus the forward-only filter:
   ["typerec func"] instantiates [#"bfunc"] in one rewrite
   (["ty_subst bfunc"] + ["val_subst bfunc"]), so ["bfunc def"] unfolds an
   already-instantiated body and the eager [#"mif"] / [#"bool?"] check
   reduces to [#"Error"]. *)
Lemma eq_dtt_uT_mismatch : eq_term target_multilanguage c_dtt_uT_mismatch s_dtt_uT_mismatch l_dtt_uT_mismatch r_dtt_uT_mismatch.
Proof. unfold c_dtt_uT_mismatch, s_dtt_uT_mismatch, l_dtt_uT_mismatch, r_dtt_uT_mismatch. by_reduction_fwd. Qed.

Definition c_dtt_uF_mismatch := Eval vm_compute in gctx "dtt uF mismatch".
Definition s_dtt_uF_mismatch := Eval vm_compute in gsrt "dtt uF mismatch".
Definition l_dtt_uF_mismatch := Eval vm_compute in glhs "dtt uF mismatch".
Definition r_dtt_uF_mismatch := Eval vm_compute in grhs "dtt uF mismatch".
(* As "dtt uT mismatch". *)
Lemma eq_dtt_uF_mismatch : eq_term target_multilanguage c_dtt_uF_mismatch s_dtt_uF_mismatch l_dtt_uF_mismatch r_dtt_uF_mismatch.
Proof. unfold c_dtt_uF_mismatch, s_dtt_uF_mismatch, l_dtt_uF_mismatch, r_dtt_uF_mismatch. by_reduction_fwd. Qed.

Definition c_exp_subst_dtt := Eval vm_compute in gctx "exp_subst dtt".
Definition s_exp_subst_dtt := Eval vm_compute in gsrt "exp_subst dtt".
Definition l_exp_subst_dtt := Eval vm_compute in glhs "exp_subst dtt".
Definition r_exp_subst_dtt := Eval vm_compute in grhs "exp_subst dtt".
(* The three typerec cases are constants with one-step substitution rules
   ("val_subst bstar"/"bbool"/"bfunc"), so this reduces directly. *)
Lemma eq_exp_subst_dtt : eq_term target_multilanguage c_exp_subst_dtt s_exp_subst_dtt l_exp_subst_dtt r_exp_subst_dtt.
Proof. unfold c_exp_subst_dtt, s_exp_subst_dtt, l_exp_subst_dtt, r_exp_subst_dtt. by_reduction_fwd. Qed.

Definition c_exp_subst_ttd := Eval vm_compute in gctx "exp_subst ttd".
Definition s_exp_subst_ttd := Eval vm_compute in gsrt "exp_subst ttd".
Definition l_exp_subst_ttd := Eval vm_compute in glhs "exp_subst ttd".
Definition r_exp_subst_ttd := Eval vm_compute in grhs "exp_subst ttd".
(* As "exp_subst dtt". *)
Lemma eq_exp_subst_ttd : eq_term target_multilanguage c_exp_subst_ttd s_exp_subst_ttd l_exp_subst_ttd r_exp_subst_ttd.
Proof. unfold c_exp_subst_ttd, s_exp_subst_ttd, l_exp_subst_ttd, r_exp_subst_ttd. by_reduction_fwd. Qed.

(* ------------------------------------------------------------------ *)
(* All 13 boundary equations are discharged above, so the whole-compiler
   theorem is assembled from them by hand.  [compute_preserving_compiler]
   is NOT usable: its [eq_term_oracle] would re-run the e-graph on every
   equation, including the two ["func"] ones that only converge when split
   into the two hops above.

   [pct] is [CompilerDefs.preserving_compiler_term] restated with the
   [map fst c = cargs] side condition as an explicit (computational)
   premise: the constructor as stated cannot be applied, since unifying
   [map fst ?c] with the literal argument list of a [term_case] is not a
   unification problem Coq can solve. *)
Lemma pct
  : forall cmp l n c args e t cargs,
    preserving_compiler_ext (tgt_Model := core_model target_multilanguage)
      interoperating_langs_compiler cmp l ->
    map fst c = cargs ->
    Model.wf_term (Model := core_model target_multilanguage)
      (compile_ctx (cmp ++ interoperating_langs_compiler) c) e
      (compile_sort (cmp ++ interoperating_langs_compiler) t) ->
    preserving_compiler_ext (tgt_Model := core_model target_multilanguage)
      interoperating_langs_compiler ((n, term_case cargs e)::cmp)
      ((n, term_rule c args t) :: l).
Proof. intros; subst; constructor; auto. Qed.

Ltac solve_boundary_case :=
  solve [ exact dtt_case_wf | exact ttd_case_wf
        | exact eq_dtt_star | exact eq_ttd_star
        | exact eq_dtt_True | exact eq_dtt_False
        | exact eq_ttd_True | exact eq_ttd_False
        | exact eq_dtt_func | exact eq_ttd_func
        | exact eq_dtt_ulambda_mismatch
        | exact eq_dtt_uT_mismatch | exact eq_dtt_uF_mismatch
        | exact eq_exp_subst_dtt | exact eq_exp_subst_ttd ].

Lemma simple_multilang_compiler_preserving
  : preserving_compiler_ext (tgt_Model := core_model target_multilanguage)
      interoperating_langs_compiler simple_multilang_compiler boundaries.
Proof.
  unfold boundaries, simple_multilang_compiler.
  repeat lazymatch goal with
    | |- preserving_compiler_ext _ _ _ =>
        first [ eapply pct; [ | vm_compute; reflexivity | ]
              | constructor ]
    end.
  all: solve_boundary_case.
Qed.

#[local] Definition simple_multilang_compiler_entry :=
  cmp_entry simple_multilang_compiler_preserving.
#[export] Hint Resolve simple_multilang_compiler_entry : preserving_db.
