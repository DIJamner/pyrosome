Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core CutFreeInd.
From Pyrosome.Proof Require Import TreeProofs.
From Pyrosome.Gluing Require Import CutTModel Eval.
Import Core.Notations.

(* The checker guards its results with [eqb] tests.  [cbn] would happily unfold
   [eqb] into the underlying decision fixpoint, which destroys the [eqb x x]
   pattern that [eqb_refl] needs; keeping it folded lets the reductions below
   expose exactly those tests and no more. *)
Local Arguments eqb : simpl never.

(* COMPLETENESS of the tree-proof representation, and the resulting bridge into
   an arbitrary [CutTModel].

   [Eval.v] evaluates a proof tree into a [CutTModel]: given [p] with
   [check_proof l c p = Some (e1,e2,t)] it produces [ceq_term t e1 e2].  What was
   missing is the converse -- that a judgemental [eq_term] derivation HAS such a
   tree.  That is [tree_complete] below, proved by the cut-free induction
   principle of Theory/CutFreeInd.v (whose motives are exactly the shape of the
   [pf] constructors, since both mirror the cut-free system).

   The two compose to [cut_model_inhabited]: [eq_term l c t e1 e2] implies
   [inhabited (ceq_term t e1 e2)].  The [inhabited] is essential and not a
   weakness: [ceq_term] is Type-valued while [eq_term] is a Prop, so no
   *designated* member can be extracted -- but [inhabited _ : Prop], so the
   existential witness produced by [tree_complete] may legitimately be
   eliminated into it.  For a normalization model, whose conclusions ("this term
   has a normal form") are themselves Props, this is precisely the usable form. *)

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation lang := (@lang V).
  Notation pf := (@pf V).

  (* [with_names_from] re-attaches a context's names to a list of values, so
     stripping and re-attaching a substitution that already carries exactly those
     names is the identity.  (The [utils] database advertises a lemma of this
     shape, but PosListMap.v leaves it [Admitted], so we prove what we need.) *)
  Lemma with_names_from_map_snd_eq {A B} (c' : @NamedList.named_list V A)
    (s : @NamedList.named_list V B)
    : map fst s = map fst c' -> with_names_from c' (map snd s) = s.
  Proof.
    revert s; induction c'; destruct s;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Section WithLangAndCtx.
    Context (l : lang)
      (wfl : wf_lang l)
      (c : ctx)
      (wfc : wf_ctx (Model := core_model l) c).

    Local Notation eq_subst := (eq_subst (Model := core_model l) c).
    Local Notation eq_args := (eq_args (Model := core_model l) c).

    (* ---------------------------------------------------------------- *)
    (* Unfolding equations for the checker.                              *)
    (*                                                                   *)
    (* [check_proof]/[check_sort_proof] are a mutual [Fixpoint], and [cbn]
       unfolds them into a raw [fix ... for check_proof] that it never refolds
       back to [check_proof l c].  That makes hypotheses about [check_proof l c]
       fail to match syntactically.  Stating the per-constructor equations and
       proving them by [reflexivity] (which uses full conversion) sidesteps the
       problem entirely. *)
    (* ---------------------------------------------------------------- *)

    Lemma check_proof_pvar n
      : check_proof l c (pvar n)
        = @! let t <- named_list_lookup_err c n in ret (var n, var n, t).
    Proof. reflexivity. Qed.

    Lemma check_proof_pcon n s
      : check_proof l c (pcon n s)
        = @! let r <- named_list_lookup_err l n in
             match r with
             | term_rule c' _ t =>
                 @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
                    ret (con n lhs, con n rhs, t[/with_names_from c' rhs/])
             | term_eq_rule c' e1 e2 t =>
                 @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (e1[/lsub/], e2[/rsub/], t[/rsub/])
             | _ => None
             end.
    Proof. reflexivity. Qed.

    Lemma check_proof_ptrans p0 p1
      : check_proof l c (ptrans p0 p1)
        = @! let (e1, e2, t) <- check_proof l c p0 in
             let (e1', e2', t') <- check_proof l c p1 in
             let ! eqb t t' in
             let ! eqb e2 e1' in
             ret (e1, e2', t).
    Proof. reflexivity. Qed.

    Lemma check_proof_psym p
      : check_proof l c (psym p)
        = @! let (e1, e2, t) <- check_proof l c p in ret (e2, e1, t).
    Proof. reflexivity. Qed.

    Lemma check_proof_pconv p0 p1
      : check_proof l c (pconv p0 p1)
        = @! let (t1, t2) <- check_sort_proof l c p0 in
             let (e1, e2, t) <- check_proof l c p1 in
             let ! eqb t t1 in
             ret (e1, e2, t2).
    Proof. reflexivity. Qed.

    Lemma check_sort_proof_pcon n s
      : check_sort_proof l c (pcon n s)
        = @! let r <- named_list_lookup_err l n in
             match r with
             | sort_rule c' _ =>
                 @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
                    ret (scon n lhs, scon n rhs)
             | sort_eq_rule c' t1 t2 =>
                 @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (t1[/lsub/], t2[/rsub/])
             | _ => None
             end.
    Proof. reflexivity. Qed.

    Lemma check_sort_proof_ptrans p0 p1
      : check_sort_proof l c (ptrans p0 p1)
        = @! let (t1, t2) <- check_sort_proof l c p0 in
             let (t1', t2') <- check_sort_proof l c p1 in
             let ! eqb t2 t1' in
             ret (t1, t2').
    Proof. reflexivity. Qed.

    Lemma check_sort_proof_psym p
      : check_sort_proof l c (psym p)
        = @! let (t1, t2) <- check_sort_proof l c p in ret (t2, t1).
    Proof. reflexivity. Qed.

    Lemma check_args_proof_nil
      : check_args_proof (check_proof l c) [] [] = Some ([], []).
    Proof. reflexivity. Qed.

    Lemma check_args_proof_cons p ps name t c'
      : check_args_proof (check_proof l c) (p :: ps) ((name, t) :: c')
        = @! let (lhs, rhs) <- check_args_proof (check_proof l c) ps c' in
             let (e1, e2, t') <- check_proof l c p in
             let ! eqb t[/with_names_from c' rhs/] t' in
             ret (e1 :: lhs, e2 :: rhs).
    Proof. reflexivity. Qed.

    (* Rule/variable lookup: the checker looks things up by name, so each [In]
       premise coming out of [cut_ind] must become a successful lookup.  This is
       where well-formedness (freshness of names) is used. *)
    Lemma lookup_of_in n r
      : In (n, r) l -> named_list_lookup_err l n = Some r.
    Proof.
      intros; symmetry.
      apply all_fresh_named_list_lookup_err_in; eauto.
      basic_core_crush.
    Qed.

    Lemma lookup_of_in_ctx n t
      : In (n, t) c -> named_list_lookup_err c n = Some t.
    Proof.
      intros; symmetry.
      apply all_fresh_named_list_lookup_err_in; eauto.
      basic_core_crush.
    Qed.

    (* The checker guards each composite step with [eqb] tests that are
       reflexivity instances by construction (transitivity matches a shared
       middle term, conversion a shared sort, and so on).  Guards nest, so we
       alternate discharging the outermost with reducing to expose the next.
       The tests live at both [sort] and [term], hence the instance search. *)
    Local Ltac close_guards :=
      repeat (rewrite eqb_refl_true by typeclasses eauto; try cbn); reflexivity.

    (* Specializing each [pcon] equation to a *successful* lookup lets
       [reflexivity] absorb the monadic bind, so the remaining goal mentions the
       rule's own context (not a match-bound copy of it) and the argument-list
       hypothesis applies directly. *)
    Lemma check_sort_proof_sort_eq_rule n s c' t1 t2
      : In (n, sort_eq_rule c' t1 t2) l ->
        check_sort_proof l c (pcon n s)
        = @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
             ret (t1[/with_names_from c' lhs/], t2[/with_names_from c' rhs/]).
    Proof.
      intro H; rewrite check_sort_proof_pcon, (lookup_of_in _ _ H); reflexivity.
    Qed.

    Lemma check_sort_proof_sort_rule n s c' args
      : In (n, sort_rule c' args) l ->
        check_sort_proof l c (pcon n s)
        = @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
             ret (scon n lhs, scon n rhs).
    Proof.
      intro H; rewrite check_sort_proof_pcon, (lookup_of_in _ _ H); reflexivity.
    Qed.

    Lemma check_proof_term_eq_rule n s c' e1 e2 t
      : In (n, term_eq_rule c' e1 e2 t) l ->
        check_proof l c (pcon n s)
        = @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
             ret (e1[/with_names_from c' lhs/],
                  e2[/with_names_from c' rhs/],
                  t[/with_names_from c' rhs/]).
    Proof.
      intro H; rewrite check_proof_pcon, (lookup_of_in _ _ H); reflexivity.
    Qed.

    Lemma check_proof_term_rule n s c' args t
      : In (n, term_rule c' args t) l ->
        check_proof l c (pcon n s)
        = @! let (lhs, rhs) <- check_args_proof (check_proof l c) s c' in
             ret (con n lhs, con n rhs, t[/with_names_from c' rhs/]).
    Proof.
      intro H; rewrite check_proof_pcon, (lookup_of_in _ _ H); reflexivity.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* Completeness.                                                     *)
    (* ---------------------------------------------------------------- *)

    (* [has_pf_subst] carries the name equations alongside the tree: the checker
       works on positional argument lists while [eq_subst] works on named ones,
       and threading [map fst] through the induction is what reconciles the two
       at the axiom-instance cases, where a rule's context is instantiated by a
       substitution. *)
    Definition has_pf_sort t1 t2 : Prop :=
      exists p, check_sort_proof l c p = Some (t1, t2).
    Definition has_pf_term t e1 e2 : Prop :=
      exists p, check_proof l c p = Some (e1, e2, t).
    Definition has_pf_args (c' : ctx) (s1 s2 : list term) : Prop :=
      exists ps, check_args_proof (check_proof l c) ps c' = Some (s1, s2).
    Definition has_pf_subst (c' : ctx) (s1 s2 : subst) : Prop :=
      map fst s1 = map fst c'
      /\ map fst s2 = map fst c'
      /\ exists ps,
          check_args_proof (check_proof l c) ps c' = Some (map snd s1, map snd s2).

    Theorem tree_complete
      : (forall t1 t2, eq_sort l c t1 t2 -> has_pf_sort t1 t2)
        /\ (forall t e1 e2, eq_term l c t e1 e2 -> has_pf_term t e1 e2)
        /\ (forall c' s1 s2, eq_subst c' s1 s2 -> has_pf_subst c' s1 s2)
        /\ (forall c' s1 s2, eq_args c' s1 s2 -> has_pf_args c' s1 s2).
    Proof.
      (* [cut_ind] generalizes over the instance arguments and the
         well-formedness side conditions; all of them are in scope here. *)
      apply cut_ind; try assumption.
      (* Hsort0 : sort_eq_rule instance *)
      - intros c' name t1 t2 s1 s2 Hin Hsub [Hfst1 [Hfst2 [ps Hps]]].
        exists (pcon name ps).
        rewrite (check_sort_proof_sort_eq_rule _ _ _ _ _ Hin), Hps; cbn.
        rewrite !with_names_from_map_snd_eq by assumption.
        reflexivity.
      (* Hsort1 : sort_rule congruence *)
      - intros c' name args s1 s2 Hin Hargs [ps Hps].
        exists (pcon name ps).
        rewrite (check_sort_proof_sort_rule _ _ _ _ Hin), Hps; cbn.
        reflexivity.
      (* Hsort2 : transitivity *)
      - intros t1 t12 t2 _ [p1 Hp1] _ [p2 Hp2].
        exists (ptrans p1 p2).
        rewrite check_sort_proof_ptrans, Hp1, Hp2; cbn.
        close_guards.
      (* Hsort3 : symmetry *)
      - intros t1 t2 _ [p Hp].
        exists (psym p).
        rewrite check_sort_proof_psym, Hp; cbn; reflexivity.
      (* f : term_eq_rule instance *)
      - intros c' name t e1 e2 s1 s2 Hin Hsub [Hfst1 [Hfst2 [ps Hps]]].
        exists (pcon name ps).
        rewrite (check_proof_term_eq_rule _ _ _ _ _ _ Hin), Hps; cbn.
        rewrite !with_names_from_map_snd_eq by assumption.
        reflexivity.
      (* f0 : term_rule congruence *)
      - intros c' name t args s1 s2 Hin Hargs [ps Hps].
        exists (pcon name ps).
        rewrite (check_proof_term_rule _ _ _ _ _ Hin), Hps; cbn.
        reflexivity.
      (* f01 : variable *)
      - intros n t Hin.
        exists (pvar n).
        rewrite check_proof_pvar, (lookup_of_in_ctx _ _ Hin); cbn; reflexivity.
      (* f1 : transitivity *)
      - intros t e1 e12 e2 _ [p1 Hp1] _ [p2 Hp2].
        exists (ptrans p1 p2).
        rewrite check_proof_ptrans, Hp1, Hp2; cbn.
        close_guards.
      (* f2 : symmetry *)
      - intros t e1 e2 _ [p Hp].
        exists (psym p).
        rewrite check_proof_psym, Hp; cbn; reflexivity.
      (* f3 : conversion *)
      - intros t t' _ [pt Hpt] e1 e2 _ [p Hp].
        exists (pconv pt p).
        rewrite check_proof_pconv, Hpt, Hp; cbn.
        close_guards.
      (* f4 : empty substitution *)
      - repeat split; exists []; apply check_args_proof_nil.
      (* f5 : substitution extension *)
      - intros c' s1 s2 Hsub [Hfst1 [Hfst2 [ps Hps]]] name t e1 e2 _ [p Hp].
        repeat split; cbn; try (f_equal; assumption).
        exists (p :: ps).
        rewrite check_args_proof_cons, Hps; cbn.
        rewrite with_names_from_map_snd_eq by assumption.
        rewrite Hp; cbn.
        close_guards.
      (* f6 : empty argument list *)
      - exists []; apply check_args_proof_nil.
      (* f7 : argument-list extension *)
      - intros c' s1 s2 Hargs [ps Hps] name t e1 e2 _ [p Hp].
        exists (p :: ps).
        rewrite check_args_proof_cons, Hps; cbn.
        rewrite Hp; cbn.
        close_guards.
    Qed.

    Definition tree_complete_term := proj1 (proj2 tree_complete).

    (* ---------------------------------------------------------------- *)
    (* The bridge into an arbitrary cut-free model.                      *)
    (* ---------------------------------------------------------------- *)
    Section WithModel.
      Context {CM : CutTModel}
        {CMok : CutTModel_ok l c}.

      Theorem cut_model_inhabited t e1 e2
        : eq_term l c t e1 e2 ->
          inhabited (ceq_term (CutTModel := CM) t e1 e2).
      Proof.
        intro Heq.
        destruct (tree_complete_term Heq) as [p Hp].
        constructor.
        eapply eval_term; eassumption.
      Qed.

      (* The normalization driver.  Instantiating at [e1 = e2 = e] via
         reflexivity turns well-typedness alone into the model's content at [e].
         For a model whose [ceq_term t e e] says "e has a normal form of type t",
         this IS the normalization statement -- so building such a model is all
         that a normalization proof for [l] requires. *)
      Corollary cut_model_normalization t e
        : wf_term l c e t -> inhabited (ceq_term (CutTModel := CM) t e e).
      Proof.
        intro Hwf.
        apply cut_model_inhabited.
        apply eq_term_refl; assumption.
      Qed.

    End WithModel.

  End WithLangAndCtx.

End WithVar.
