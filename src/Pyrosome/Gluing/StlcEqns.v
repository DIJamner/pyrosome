Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Tools.Matches.
From Pyrosome.Gluing Require Import StlcModel StlcNormalization.
Import Core.Notations.

(* The equational toolkit for [stlc_unit].

   Each of the language's 18 equations is repackaged here as a directly usable
   lemma: the equation instance is stated with explicit term arguments in the
   abbreviation vocabulary of Gluing/StlcModel.v ([Cmp], [Snoc], [ValSubst],
   ...), and carries exactly the well-formedness hypotheses the instantiation
   needs -- one [wf_term] per variable of the rule's context, at that variable's
   sort, already instantiated by the preceding arguments.  The congruence rules
   for the seven constructors the later layers use get the same treatment.

   [Tools.Matches.eredex_steps_with] does the actual instantiation: given a
   rule name, it looks the rule up in [stlc_unit] and infers, by unification
   against the goal, the substitution that turns the rule's LHS/RHS into the
   goal's; all that is left is to discharge the resulting well-formedness
   side conditions. *)

(* A rule's context is well formed, since the language is.  [eredex_steps_with]
   leaves exactly this goal (headed by the rule's own, unsubstituted context)
   whenever the built substitution doesn't already settle it via
   [cleanup_auto_elab]. *)
Lemma stlc_unit_rule_ctx_wf n r
  : named_list_lookup_err stlc_unit n = Some r ->
    wf_ctx (Model := core_model stlc_unit) (Rule.get_ctx r).
Proof.
  intro Hlook.
  pose proof (rule_in_wf (l_pre := []) _ _ stlc_unit_wf
                (named_list_lookup_err_in _ _ (eq_sym Hlook))) as Hr.
  rewrite app_nil_r in Hr.
  destruct r; cbn in *; inversion Hr; subst; assumption.
Qed.

Ltac wf_subst_solve :=
  repeat first [ simple apply wf_subst_nil
               | simple eapply wf_subst_cons
               | progress cbn [combine map fst]
               | progress cbn [Model.wf_term core_model]
               | eassumption ].

(* [eredex_steps_with] leaves either one goal ([wf_ctx], when the built
   substitution is itself trivial) or two ([wf_subst] then [wf_ctx]); the
   plain semicolon below runs the combined solver on every goal it leaves,
   whichever shape that turns out to be. *)
Ltac estep nm :=
  eredex_steps_with stlc_unit nm;
  first [ solve [ wf_subst_solve ]
        | exact (stlc_unit_rule_ctx_wf nm eq_refl) ].

(* Instantiating a term rule's congruence. *)
Lemma stlc_unit_cong_inst (name : string) c' args t' (s1 s2 : list (term string))
  : In (name, term_rule c' args t') stlc_unit ->
    eq_args (Model := core_model stlc_unit) [] c' s1 s2 ->
    eq_term stlc_unit [] t'[/with_names_from c' s2/]
      (con name s1) (con name s2).
Proof.
  intros Hin Hargs.
  eapply term_con_congruence.
  - exact Hin.
  - right; reflexivity.
  - apply stlc_unit_wf.
  - exact Hargs.
Qed.

Ltac eq_args_solve :=
  repeat apply eq_args_cons;
  first [ apply eq_args_nil | eassumption ].

(* [name_list_lookup_err_in ... eq_refl] pins the rule's [term_rule] shape to
   the concrete value [named_list_lookup_err stlc_unit nm] reduces to; [refine]
   (unlike [apply]) propagates that expected-type information down into the
   hole, so the reduction actually fires instead of getting stuck on an
   uninstantiated evar. *)
Ltac cong_step nm s1 s2 :=
  refine (stlc_unit_cong_inst (named_list_lookup_err_in stlc_unit nm eq_refl)
            (s1 := s1) (s2 := s2) _);
  eq_args_solve.

(* ---------------------------------------------------------------- *)
(* value_subst: the substitution calculus                             *)
(* ---------------------------------------------------------------- *)

Lemma eq_id_right G G' f
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] f (Ssub G G') ->
    eq_term stlc_unit [] (Ssub G G') (Cmp G G' G' f (Id G')) f.
Proof. intros; estep "id_right". Qed.

Lemma eq_id_left G G' f
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] f (Ssub G G') ->
    eq_term stlc_unit [] (Ssub G G') (Cmp G G G' (Id G) f) f.
Proof. intros; estep "id_left". Qed.

Lemma eq_cmp_assoc G1 G2 G3 G4 f g h
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] G4 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] h (Ssub G3 G4) ->
    eq_term stlc_unit [] (Ssub G1 G4)
      (Cmp G1 G2 G4 f (Cmp G2 G3 G4 g h))
      (Cmp G1 G3 G4 (Cmp G1 G2 G3 f g) h).
Proof. intros; estep "cmp_assoc". Qed.

Lemma eq_val_subst_id G A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Sval G A) (ValSubst G G (Id G) A v) v.
Proof. intros; estep "val_subst_id". Qed.

Lemma eq_val_subst_cmp G1 G2 G3 f g A v
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G3 A) ->
    eq_term stlc_unit [] (Sval G1 A)
      (ValSubst G1 G2 f A (ValSubst G2 G3 g A v))
      (ValSubst G1 G3 (Cmp G1 G2 G3 f g) A v).
Proof. intros; estep "val_subst_cmp". Qed.

Lemma eq_cmp_forget G G' g
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    eq_term stlc_unit [] (Ssub G Emp)
      (Cmp G G' Emp g (Forget G')) (Forget G).
Proof. intros; estep "cmp_forget". Qed.

Lemma eq_id_emp_forget
  : eq_term stlc_unit [] (Ssub Emp Emp) (Id Emp) (Forget Emp).
Proof. estep "id_emp_forget". Qed.

Lemma eq_wkn_snoc G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Ssub G G')
      (Cmp G (Ext G' A) G' (Snoc G G' g A v) (Wkn G' A)) g.
Proof. intros; estep "wkn_snoc". Qed.

Lemma eq_snoc_hd G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Sval G A)
      (ValSubst G (Ext G' A) (Snoc G G' g A v) A (Hd G' A)) v.
Proof. intros; estep "snoc_hd". Qed.

Lemma eq_cmp_snoc G1 G2 G3 f g A v
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G2 A) ->
    eq_term stlc_unit [] (Ssub G1 (Ext G3 A))
      (Cmp G1 G2 (Ext G3 A) f (Snoc G2 G3 g A v))
      (Snoc G1 G3 (Cmp G1 G2 G3 f g) A (ValSubst G1 G2 f A v)).
Proof. intros; estep "cmp_snoc". Qed.

Lemma eq_snoc_wkn_hd G A
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    eq_term stlc_unit [] (Ssub (Ext G A) (Ext G A))
      (Snoc (Ext G A) G (Wkn G A) A (Hd G A)) (Id (Ext G A)).
Proof. intros; estep "snoc_wkn_hd". Qed.

(* ---------------------------------------------------------------- *)
(* exp_subst                                                          *)
(* ---------------------------------------------------------------- *)

Lemma eq_exp_subst_id G A e
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] e (Sexp G A) ->
    eq_term stlc_unit [] (Sexp G A) (ExpSubst G G (Id G) A e) e.
Proof. intros; estep "exp_subst_id". Qed.

Lemma eq_exp_subst_cmp G1 G2 G3 f g A e
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] e (Sexp G3 A) ->
    eq_term stlc_unit [] (Sexp G1 A)
      (ExpSubst G1 G2 f A (ExpSubst G2 G3 g A e))
      (ExpSubst G1 G3 (Cmp G1 G2 G3 f g) A e).
Proof. intros; estep "exp_subst_cmp". Qed.

(* [exp_subst ret]: substitution commutes with the value/expression coercion.
   The rule's context interleaves the two environments, but [estep] infers the
   substitution by unification, so the argument order here doesn't matter. *)
Lemma eq_exp_subst_ret G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sexp G' A)
      (ExpSubst G' G g A (Ret G A v))
      (Ret G' A (ValSubst G' G g A v)).
Proof. intros; estep "exp_subst ret". Qed.

(* ---------------------------------------------------------------- *)
(* stlc                                                               *)
(* ---------------------------------------------------------------- *)

Lemma eq_exp_subst_app G G' g A B e e'
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp G (Arr A B)) ->
    wf_term stlc_unit [] e' (Sexp G A) ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sexp G' B)
      (ExpSubst G' G g B (App G A B e e'))
      (App G' A B (ExpSubst G' G g (Arr A B) e) (ExpSubst G' G g A e')).
Proof. intros; estep "exp_subst app". Qed.

Lemma eq_val_subst_lambda G G' g A B e
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp (Ext G A) B) ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sval G' (Arr A B))
      (ValSubst G' G g (Arr A B) (Lam G A B e))
      (Lam G' A B
         (ExpSubst (Ext G' A) (Ext G A)
            (Snoc (Ext G' A) G (Cmp (Ext G' A) G' G (Wkn G' A) g) A (Hd G' A))
            B e)).
Proof. intros; estep "val_subst lambda". Qed.

Lemma eq_stlc_beta G A B e v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp (Ext G A) B) ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Sexp G B)
      (App G A B (Ret G (Arr A B) (Lam G A B e)) (Ret G A v))
      (ExpSubst G (Ext G A) (Snoc G G (Id G) A v) B e).
Proof. intros; estep "STLC-beta". Qed.

(* ---------------------------------------------------------------- *)
(* unit                                                               *)
(* ---------------------------------------------------------------- *)

Lemma eq_val_subst_tt G G' g
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sval G' Unit)
      (ValSubst G' G g Unit (Tt G)) (Tt G').
Proof. intros; estep "val_subst tt". Qed.

(* ---------------------------------------------------------------- *)
(* Congruences                                                        *)
(* ---------------------------------------------------------------- *)

(* Note the asymmetry: the sorts of the later hypotheses, and of the conclusion,
   are instantiated at the RIGHT-hand arguments.  That is what [eq_args]
   provides and what [term_con_congruence] concludes. *)

Lemma Ret_cong G1 G2 A1 A2 v1 v2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sval G2 A2) v1 v2 ->
    eq_term stlc_unit [] (Sexp G2 A2) (Ret G1 A1 v1) (Ret G2 A2 v2).
Proof. intros; cong_step "ret" [v1; A1; G1] [v2; A2; G2]. Qed.

Lemma App_cong G1 G2 A1 A2 B1 B2 e1 e2 e1' e2'
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] Sty B1 B2 ->
    eq_term stlc_unit [] (Sexp G2 (Arr A2 B2)) e1 e2 ->
    eq_term stlc_unit [] (Sexp G2 A2) e1' e2' ->
    eq_term stlc_unit [] (Sexp G2 B2)
      (App G1 A1 B1 e1 e1') (App G2 A2 B2 e2 e2').
Proof. intros; cong_step "app" [e1'; e1; B1; A1; G1] [e2'; e2; B2; A2; G2]. Qed.

Lemma Lam_cong G1 G2 A1 A2 B1 B2 e1 e2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] Sty B1 B2 ->
    eq_term stlc_unit [] (Sexp (Ext G2 A2) B2) e1 e2 ->
    eq_term stlc_unit [] (Sval G2 (Arr A2 B2))
      (Lam G1 A1 B1 e1) (Lam G2 A2 B2 e2).
Proof. intros; cong_step "lambda" [e1; B1; A1; G1] [e2; B2; A2; G2]. Qed.

Lemma ValSubst_cong G1 G2 G1' G2' g1 g2 A1 A2 v1 v2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Senv G1' G2' ->
    eq_term stlc_unit [] (Ssub G2 G2') g1 g2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sval G2' A2) v1 v2 ->
    eq_term stlc_unit [] (Sval G2 A2)
      (ValSubst G1 G1' g1 A1 v1) (ValSubst G2 G2' g2 A2 v2).
Proof.
  intros; cong_step "val_subst" [v1; A1; g1; G1'; G1] [v2; A2; g2; G2'; G2].
Qed.

Lemma ExpSubst_cong G1 G2 G1' G2' g1 g2 A1 A2 e1 e2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Senv G1' G2' ->
    eq_term stlc_unit [] (Ssub G2 G2') g1 g2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sexp G2' A2) e1 e2 ->
    eq_term stlc_unit [] (Sexp G2 A2)
      (ExpSubst G1 G1' g1 A1 e1) (ExpSubst G2 G2' g2 A2 e2).
Proof.
  intros; cong_step "exp_subst" [e1; A1; g1; G1'; G1] [e2; A2; g2; G2'; G2].
Qed.

Lemma Snoc_cong G1 G2 G1' G2' g1 g2 A1 A2 v1 v2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Senv G1' G2' ->
    eq_term stlc_unit [] (Ssub G2 G2') g1 g2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sval G2 A2) v1 v2 ->
    eq_term stlc_unit [] (Ssub G2 (Ext G2' A2))
      (Snoc G1 G1' g1 A1 v1) (Snoc G2 G2' g2 A2 v2).
Proof.
  intros; cong_step "snoc" [v1; A1; g1; G1'; G1] [v2; A2; g2; G2'; G2].
Qed.

Lemma Cmp_cong X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2
  : eq_term stlc_unit [] Senv X1 Y1 ->
    eq_term stlc_unit [] Senv X2 Y2 ->
    eq_term stlc_unit [] Senv X3 Y3 ->
    eq_term stlc_unit [] (Ssub Y1 Y2) f1 f2 ->
    eq_term stlc_unit [] (Ssub Y2 Y3) g1 g2 ->
    eq_term stlc_unit [] (Ssub Y1 Y3)
      (Cmp X1 X2 X3 f1 g1) (Cmp Y1 Y2 Y3 f2 g2).
Proof. intros; cong_step "cmp" [g1; f1; X3; X2; X1] [g2; f2; Y3; Y2; Y1]. Qed.
