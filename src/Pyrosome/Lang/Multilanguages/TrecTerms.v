(* The boundary case constants [#"bstar"], [#"bbool"] and [#"bfunc"] that
   [#"typerec"] recurses with, the full [target_multilanguage] they complete,
   and [trec_boundaries], the derived coercion pair at an arbitrary type. *)

Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* Compiler infrastructure. *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from <lang> with` compiler syntax *)

From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference Tools.Resolution Tools.EGraph.ComputeWf.
Import Core.Notations.

From Stdlib Require derive.Derive.
From Pyrosome Require Import Tools.EGraph.InjRuleGen.

(* The language fragments that make up the two interoperating languages. *)
From Pyrosome.Lang Require Import SimpleVSTLC.
From Pyrosome.Lang Require Import UTLC.
From Pyrosome.Lang Require Import BoolType.
From Pyrosome.Lang Require Import SimpleVProd.


(* Machinery for building the polymorphic (parameterized) versions of those fragments. *)
From Pyrosome.Lang Require Import PolySubst SimpleVSubst.
From Pyrosome.Lang Require Import PolyCompilerLangs PolyCompilersCPS PolyCompilers.
From Pyrosome.Compilers Require Import Parameterizer.
Import Pyrosome.Tools.UnElab.
From Pyrosome.Lang.Multilanguages Require Export TypeCasing.


(* Helpers for de Bruijn-style value variables in the derived terms. *)
Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | 1 => {{e #"wkn"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Definition ovar n := {{e #"val_subst" {wkn_n n} #"hd" }}.

Ltac solve_eq_sort_disj :=
  right; compute_eq_compilation; sort_cong; repeat by_reduction.

(* Discharges an [elab_term] (or the sort side condition of one) in
   [language].  The trailing [by_reduction] after the [repeat by_reduction]
   is load-bearing: the leaves left over from the repeat are order-sensitive,
   and one further round closes them. *)
Ltac solve_elab_term_or_sort language :=
  assert (wf_lang language) by prove_by_lang_db;
  unshelve (repeat t; decompose_sort_eq; repeat by_reduction; by_reduction); compute_term_wf.

(* Diagnostic: reports whether an [elab_term] goal can be decomposed
   further.  Unused, but kept as an example of the Pyrosome workflow. *)
Ltac quick_goal_match :=
  lazymatch goal with
  | |- elab_term _ _ (con ?s _) (con ?s _) _ =>
      idtac "can go further"
  | |- elab_term _ _ (con ?s _) (con ?s' _) _ =>
      fail "cannot go further"
  | |- _  => idtac "neither case"
  end.


(* ------------------------------------------------------------------ *)
(* The three boundary cases, as value constants.

   Each case is a constant with a defining equation rather than a derived
   term plugged directly into [#"typerec"].  This matters for substitution:
   pushing a substitution -- a term substitution, for the
   ["exp_subst dtt"] / ["exp_subst ttd"] equations, or the type substitution
   produced by ["typerec func"] -- through a derived term means traversing
   its whole body, which is far beyond what the e-graph can do, whereas a
   constant absorbs it in a single rewrite from its ["val_subst"] /
   ["ty_subst"] equation.                                                 *)

(* [P X] is [sigma[X]] for the concrete [sigma] used by the boundaries,
   [sigma] being [prod (arrow ty_hd star) (arrow star ty_hd)]. *)
Definition P X := {{e #"prod" (#"->" {X} #"*") (#"->" #"*" {X}) }}.
Definition boundary_sigma := Eval compute in P {{e #"ty_hd"}}.

Definition Pa := Eval compute in P tva.
Definition Pb := Eval compute in P tvb.
Definition Pab := Eval compute in P {{e #"->" {tva} {tvb} }}.

(* [#"bfunc"] takes its instantiation as explicit arguments: the two types
   and the two recursive results.  This is what makes ["typerec func"] cheap:
   the instantiating type substitution it produces is absorbed by
   ["ty_subst bfunc"] in one rewrite instead of being pushed through the
   whole wrapper body. *)
Definition bfunc_ty := Eval compute in P {{e #"->" "t1" "t2"}}.
Definition bfunc_sort :=
  {{s #"val" "D" "G" {bfunc_ty} }}.

Definition bstar_body :=
  {{e #"pair_val" (#"lambda" #"*" (#"ret" #"hd")) (#"lambda" #"*" (#"ret" #"hd")) }}.

Definition bbool_body :=
  {{e #"pair_val"
      (#"lambda" #"bool" (#"if" (#"ret" #"hd") (#"ret" #"uT") (#"ret" #"uF")))
      (#"lambda" #"*" (#"mif" (#"ret" #"hd") (#"ret" #"T") (#"ret" #"F"))) }}.

(* The two wrappers.  The recursive results are the explicit arguments
   ["c1"] / ["c2"], weakened under the three binders that separate them from
   the environment [G], and the two types are the arguments ["t1"] / ["t2"]
   rather than bound type variables. *)
Definition c1w := {{e #"val_subst" {wkn_n 3} "c1" }}.
Definition c2w := {{e #"val_subst" {wkn_n 3} "c2" }}.

Definition bfunc_body :=
  {{e #"pair_val"
      (#"lambda" (#"->" "t1" "t2")
         (#"ret" (#"ulambda"
            (#"let" (#"app" (#"ret" {ovar 1})
                            (#"let" (#"ret" {ovar 0})
                                    (#"app" (#".2" (#"ret" {c1w})) (#"ret" {ovar 0}))))
                    (#"app" (#".1" (#"ret" {c2w})) (#"ret" {ovar 0}))))))
      (#"lambda" #"*"
         (#"mif" (#"bool?" (#"ret" {ovar 0}))
            (#"Error" (#"->" "t1" "t2"))
            (#"ret" (#"lambda" "t1"
               (#"let" (#"uapp" (#"ret" {ovar 1})
                                (#"let" (#"ret" {ovar 0})
                                        (#"app" (#".1" (#"ret" {c1w})) (#"ret" {ovar 0}))))
                       (#"app" (#".2" (#"ret" {c2w})) (#"ret" {ovar 0}))))))) }}.

Definition boundary_cases_def : lang :=
  {[l
    [:| "D" : #"ty_env", "G" : #"env" "D"
        -----------------------------------------------
        #"bstar" : #"val" "D" "G" {P {{e #"*"}} }
    ];
    [:| "D" : #"ty_env", "G" : #"env" "D"
        -----------------------------------------------
        #"bbool" : #"val" "D" "G" {P {{e #"bool"}} }
    ];
    [:| "D" : #"ty_env", "G" : #"env" "D",
        "t1" : #"ty" "D", "t2" : #"ty" "D",
        "c1" : #"val" "D" "G" {P {{e "t1"}} },
        "c2" : #"val" "D" "G" {P {{e "t2"}} }
        -----------------------------------------------
        #"bfunc" "t1" "t2" "c1" "c2" : {bfunc_sort}
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G"
        ----------------------------------------------- ("val_subst bstar")
        #"val_subst" "g" #"bstar" = #"bstar" : #"val" "D" "G'" {P {{e #"*"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G"
        ----------------------------------------------- ("val_subst bbool")
        #"val_subst" "g" #"bbool" = #"bbool" : #"val" "D" "G'" {P {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D", "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G",
        "t1" : #"ty" "D", "t2" : #"ty" "D",
        "c1" : #"val" "D" "G" {P {{e "t1"}} },
        "c2" : #"val" "D" "G" {P {{e "t2"}} }
        ----------------------------------------------- ("val_subst bfunc")
        #"val_subst" "g" (#"bfunc" "t1" "t2" "c1" "c2")
        = #"bfunc" "t1" "t2" (#"val_subst" "g" "c1") (#"val_subst" "g" "c2")
        : #"val" "D" "G'" {bfunc_ty}
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D"
        ----------------------------------------------- ("ty_subst bstar")
        #"val_ty_subst" "g" #"bstar" = #"bstar"
        : #"val" "D'" (#"env_ty_subst" "g" "G") {P {{e #"*"}} }
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D"
        ----------------------------------------------- ("ty_subst bbool")
        #"val_ty_subst" "g" #"bbool" = #"bbool"
        : #"val" "D'" (#"env_ty_subst" "g" "G") {P {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D"
        ----------------------------------------------- ("bstar def")
        #"bstar" = {bstar_body} : #"val" "D" "G" {P {{e #"*"}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D"
        ----------------------------------------------- ("bbool def")
        #"bbool" = {bbool_body} : #"val" "D" "G" {P {{e #"bool"}} }
    ];
    [:= "D" : #"ty_env", "D'" : #"ty_env", "G" : #"env" "D",
        "g" : #"ty_sub" "D'" "D",
        "t1" : #"ty" "D", "t2" : #"ty" "D",
        "c1" : #"val" "D" "G" {P {{e "t1"}} },
        "c2" : #"val" "D" "G" {P {{e "t2"}} }
        ----------------------------------------------- ("ty_subst bfunc")
        #"val_ty_subst" "g" (#"bfunc" "t1" "t2" "c1" "c2")
        = #"bfunc" (#"ty_subst" "g" "t1") (#"ty_subst" "g" "t2")
            (#"val_ty_subst" "g" "c1") (#"val_ty_subst" "g" "c2")
        : #"val" "D'" (#"env_ty_subst" "g" "G")
            {P {{e #"->" (#"ty_subst" "g" "t1") (#"ty_subst" "g" "t2")}} }
    ];
    [:= "D" : #"ty_env", "G" : #"env" "D",
        "t1" : #"ty" "D", "t2" : #"ty" "D",
        "c1" : #"val" "D" "G" {P {{e "t1"}} },
        "c2" : #"val" "D" "G" {P {{e "t2"}} }
        ----------------------------------------------- ("bfunc def")
        #"bfunc" "t1" "t2" "c1" "c2" = {bfunc_body} : {bfunc_sort}
    ]
  ]}.

Definition boundary_cases :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 target_multilanguage_pre boundary_cases_def.

Lemma boundary_cases_wf : wf_lang_ext target_multilanguage_pre boundary_cases.
Proof. compute_wf_lang. Qed.
#[local] Definition boundary_cases_entry := lang_entry boundary_cases_wf.
#[export] Hint Resolve boundary_cases_entry : wf_lang_db.

Definition target_multilanguage := boundary_cases ++ target_multilanguage_pre.
Hint Unfold target_multilanguage : auto_elab.

Lemma target_multilanguage_wf : wf_lang target_multilanguage.
Proof. prove_by_lang_db. Qed.
#[local] Definition target_multilanguage_entry :=
  lang_entry target_multilanguage_wf.
#[export] Hint Resolve target_multilanguage_entry : wf_lang_db.

(* ------------------------------------------------------------------ *)
(* [trec_boundaries] is the [#"typerec"] value applied to the three boundary
   case constants: the pair of coercions between a type [A] and the dynamic
   type, built by recursion on [A].                                        *)
Definition trec_boundaries_unelab :=
  {{e #"typerec" "A" {boundary_sigma} #"bstar" #"bbool"
       (#"bfunc" {tva} {tvb} {ovar 1} {ovar 0}) }}.

Definition trec_boundaries_sort :=
  {{s #"val" #"ty_emp" "G"
      (#"prod" #"ty_emp"
         (#"->" #"ty_emp" "A" (#"*" #"ty_emp"))
         (#"->" #"ty_emp" (#"*" #"ty_emp") "A")) }}.

Derive trec_boundaries
  in ( elab_term target_multilanguage
         [("A", {{s #"ty" #"ty_emp"}}); ("G", {{s #"env" #"ty_emp"}})]
         trec_boundaries_unelab
         trec_boundaries
         trec_boundaries_sort
     ) as trec_boundaries_wf.
Proof. solve_elab_term_or_sort target_multilanguage. Qed.
