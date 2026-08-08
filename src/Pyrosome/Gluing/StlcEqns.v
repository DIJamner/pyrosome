Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac.
From Pyrosome Require Import Theory.Core Tools.Matches.
From Pyrosome.Tools.EGraph Require Import Automation ComputeWf.
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

(* ---------------------------------------------------------------- *)
(* Derived rules                                                     *)
(* ---------------------------------------------------------------- *)

(* Every lemma above repackages a rule the LANGUAGE actually has.  A DERIVED
   rule is the next thing up: an [eq_term] fact the language does NOT state as
   a rule, but the theory proves -- typically a short chain of the equations
   above, glued by [eq_term_trans] and congruence.  Proving such a chain by
   hand, every time the goal happens to match it, costs a multi-step
   [eapply eq_term_trans; [ apply eq_X; ... | apply eq_Y; ... ]] proof term.
   Proving it ONCE instead, stated over OBJECT-LEVEL variables ([var "D"], ...)
   in a concrete context, and discharging the whole chain in a single call to
   the e-graph, turns it into something that can be INSTANTIATED at
   meta-level terms exactly like a primitive rule: [dstep] does for a derived
   rule what [estep] (via [eredex_steps_with]) does for a rule of the
   language -- infer the substitution from the goal by unification, leaving
   only the well-formedness side conditions to discharge. *)

(* [egraph_eq]: discharge an [eq_term stlc_unit c e1 e2] goal, where [c], [e1],
   [e2] are all CONCRETE (built from [var "D"]-style object variables), by
   running the e-graph.  [solve_wf_ctx] and [compute_term_wf] both open with
   [assumption] against a [wf_lang stlc_unit] fact, hence the leading
   [pose proof].  As with [flagged_exact] elsewhere in this development, the
   check itself is deferred to [Qed] (it is implemented with
   [vm_cast_no_check]): a BROKEN derived rule looks like it went through until
   [Qed] actually runs. *)
Ltac egraph_eq :=
  pose proof stlc_unit_wf;
  apply (egraph_sound 100 100 100 100 filter_rules
           (fun _ : string * Rule.rule string => true) empty_inj_rules);
  [ exact stlc_unit_wf | solve_wf_ctx | compute_term_wf | compute_term_wf
  | flagged_exact I ].

(* [dstep lem]: instantiate a derived rule [lem : eq_term stlc_unit cr tp
   e1p e2p] at the current goal, inferring the substitution [s : cr -> c']
   from the goal's own subject terms by unification (the same unification
   [eredex_steps_with] performs for a rule of the language), then discharging
   [wf_subst cr s s] with [wf_subst_solve] and leaving exactly [wf_ctx cr] as
   the one remaining obligation -- symmetrically to how [estep] leaves
   [stlc_unit_rule_ctx_wf nm eq_refl] for a primitive rule. *)
Ltac dstep lem :=
  let ty := type of lem in
  lazymatch ty with
  | @eq_term ?V _ ?l ?cr ?tp ?e1p ?e2p =>
      lazymatch goal with
      | [|- @eq_term ?V' _ ?l' ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_ : @NamedList.named_list V (Term.term V)) in
          first [ unify_var_names V s cr | fail 2 "could not unify var names" ];
          first [ replace (@eq_term V' _ l' c' t e1 e2)
                    with (@eq_term V _ l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [ | f_equal; vm_compute; reflexivity ]
                | fail 2 "could not replace with subst" ];
          eapply (@eq_term_subst V _ l c' s s cr);
          [ exact lem
          | apply eq_subst_refl; try unfold cr; wf_subst_solve
          | ]
      end
  end.

(* Object-level variable vocabulary for the derived rules below.  The same
   string can appear in more than one rule's context without collision: each
   context is its own self-contained [ctx], so reusing e.g. [var "A"] as the
   domain type of one rule and the operand type of another means nothing more
   than picking the same pretty-printed name twice. *)
Definition Dv := var "D".
Definition Gv := var "G".
Definition Av := var "A".
Definition Bv := var "B".
Definition gv := var "g".
Definition uv := var "u".
Definition ev := var "e".
Definition D0v := var "D0".
Definition G0v := var "G0".
Definition Xv := var "X".
Definition w0v := var "w0".

(* ---- a lifted weakening composed with a drop peels the lift ---- *)

(* The workhorse of [Wk_cmp]'s lift branch (Gluing/StlcNormalForms.v):
   post-composing a lifted weakening with a [wkn] drop collapses to a [wkn]
   in front of the composite of the two smaller weakenings. *)
Definition c_lift_cmp_wkn : ctx string :=
  [("u", Ssub G0v Xv); ("w0", Ssub D0v G0v); ("A", Sty);
   ("X", Senv); ("G0", Senv); ("D0", Senv)].

Lemma d_lift_cmp_wkn
  : eq_term stlc_unit c_lift_cmp_wkn (Ssub (Ext D0v Av) Xv)
      (Cmp (Ext D0v Av) (Ext G0v Av) Xv
         (Snoc (Ext D0v Av) G0v (Cmp (Ext D0v Av) D0v G0v (Wkn D0v Av) w0v)
            Av (Hd D0v Av))
         (Cmp (Ext G0v Av) G0v Xv (Wkn G0v Av) uv))
      (Cmp (Ext D0v Av) D0v Xv (Wkn D0v Av) (Cmp D0v G0v Xv w0v uv)).
Proof.
  unfold c_lift_cmp_wkn, D0v, G0v, Xv, Av, w0v, uv,
    Ssub, Senv, Sty, Ext, Cmp, Snoc, Wkn, Hd.
  egraph_eq.
Qed.

Lemma wf_ctx_c_lift_cmp_wkn
  : wf_ctx (Model := core_model stlc_unit) c_lift_cmp_wkn.
Proof.
  pose proof stlc_unit_wf.
  unfold c_lift_cmp_wkn, D0v, G0v, Xv, Av, w0v, uv, Ssub, Senv, Sty, Ext.
  solve_wf_ctx.
Qed.

Lemma lift_cmp_wkn D0 G0 X A w0 u
  : wf_term stlc_unit [] D0 Senv -> wf_term stlc_unit [] G0 Senv ->
    wf_term stlc_unit [] X Senv -> wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] w0 (Ssub D0 G0) -> wf_term stlc_unit [] u (Ssub G0 X) ->
    eq_term stlc_unit [] (Ssub (Ext D0 A) X)
      (Cmp (Ext D0 A) (Ext G0 A) X
         (Snoc (Ext D0 A) G0 (Cmp (Ext D0 A) D0 G0 (Wkn D0 A) w0) A (Hd D0 A))
         (Cmp (Ext G0 A) G0 X (Wkn G0 A) u))
      (Cmp (Ext D0 A) D0 X (Wkn D0 A) (Cmp D0 G0 X w0 u)).
Proof.
  intros.
  dstep d_lift_cmp_wkn.
  exact wf_ctx_c_lift_cmp_wkn.
Qed.

(* ---- instantiating a lifted substitution ---- *)

(* [<id, u> o <wkn o g, hd> = <g, u>].  This is the equational heart of both
   lambda cases in Gluing/StlcSemCore.v: it is what turns "substitute under
   the binder, then beta" into "extend the substitution by the argument". *)
Definition c_lift_inst : ctx string :=
  [("u", Sval Dv Av); ("g", Ssub Dv Gv); ("A", Sty); ("G", Senv); ("D", Senv)].

Lemma d_lift_inst
  : eq_term stlc_unit c_lift_inst (Ssub Dv (Ext Gv Av))
      (Cmp Dv (Ext Dv Av) (Ext Gv Av)
         (Snoc Dv Dv (Id Dv) Av uv)
         (Snoc (Ext Dv Av) Gv (Cmp (Ext Dv Av) Dv Gv (Wkn Dv Av) gv) Av (Hd Dv Av)))
      (Snoc Dv Gv gv Av uv).
Proof.
  unfold c_lift_inst, Dv, Gv, Av, gv, uv,
    Ssub, Sval, Senv, Sty, Ext, Cmp, Snoc, Wkn, Hd, Id.
  egraph_eq.
Qed.

Lemma wf_ctx_c_lift_inst : wf_ctx (Model := core_model stlc_unit) c_lift_inst.
Proof.
  pose proof stlc_unit_wf.
  unfold c_lift_inst, Dv, Gv, Av, gv, uv, Ssub, Sval, Senv, Sty, Ext.
  solve_wf_ctx.
Qed.

Lemma eq_lift_inst D G g A u
  : wf_term stlc_unit [] D Senv -> wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty -> wf_term stlc_unit [] g (Ssub D G) ->
    wf_term stlc_unit [] u (Sval D A) ->
    eq_term stlc_unit [] (Ssub D (Ext G A))
      (Cmp D (Ext D A) (Ext G A)
         (Snoc D D (Id D) A u)
         (Snoc (Ext D A) G (Cmp (Ext D A) D G (Wkn D A) g) A (Hd D A)))
      (Snoc D G g A u).
Proof.
  intros.
  dstep d_lift_inst.
  exact wf_ctx_c_lift_inst.
Qed.

(* ---- beta at a substituted lambda ---- *)

(* [(g[lambda A e]) u = e[<g,u>]]: push the substitution under the binder
   ([val_subst lambda]), fire [STLC-beta], then reassociate via
   [eq_lift_inst] above.  This is the equational content behind both the
   [lambda] congruence and the [STLC-beta] equation case of
   Gluing/StlcSemCore.v -- what used to be a four-step hand-written chain is
   now one e-graph call. *)
Definition c_beta_lift : ctx string :=
  [("e", Sexp (Ext Gv Av) Bv); ("u", Sval Dv Av); ("g", Ssub Dv Gv);
   ("B", Sty); ("A", Sty); ("G", Senv); ("D", Senv)].

Lemma d_beta_lift
  : eq_term stlc_unit c_beta_lift (Sexp Dv Bv)
      (App Dv Av Bv
         (Ret Dv (Arr Av Bv) (ValSubst Dv Gv gv (Arr Av Bv) (Lam Gv Av Bv ev)))
         (Ret Dv Av uv))
      (ExpSubst Dv (Ext Gv Av) (Snoc Dv Gv gv Av uv) Bv ev).
Proof.
  unfold c_beta_lift, Dv, Gv, Av, Bv, gv, uv, ev,
    Ssub, Sval, Sexp, Senv, Sty, Cmp, Snoc, Wkn, Ext, Hd, Id,
    App, Ret, ValSubst, ExpSubst, Lam, Arr.
  egraph_eq.
Qed.

Lemma wf_ctx_c_beta_lift : wf_ctx (Model := core_model stlc_unit) c_beta_lift.
Proof.
  pose proof stlc_unit_wf.
  unfold c_beta_lift, Dv, Gv, Av, Bv, gv, uv, ev,
    Ssub, Sval, Sexp, Senv, Sty, Ext, Arr.
  solve_wf_ctx.
Qed.

Lemma eq_beta_lift D G g A B u e
  : wf_term stlc_unit [] D Senv -> wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty -> wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] g (Ssub D G) -> wf_term stlc_unit [] u (Sval D A) ->
    wf_term stlc_unit [] e (Sexp (Ext G A) B) ->
    eq_term stlc_unit [] (Sexp D B)
      (App D A B (Ret D (Arr A B) (ValSubst D G g (Arr A B) (Lam G A B e)))
         (Ret D A u))
      (ExpSubst D (Ext G A) (Snoc D G g A u) B e).
Proof.
  intros.
  dstep d_beta_lift.
  exact wf_ctx_c_beta_lift.
Qed.
