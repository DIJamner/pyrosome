Set Implicit Arguments.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils SymmetricInduction.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(* Substitution-typing reflection under syntactic sort equality.

   [syntactic_sort_eq l] is the semantic property certified by
   [SyntacticSorts.syntactic_sort_eq_langb].  Under it, the
   "use-sort = declared-sort" equation a covering would need collapses to
   propositional equality, so the per-variable declared-sort wf of a covered
   term can be read off its image WITHOUT constructing a full [wf_subst]
   ([covering_var_leaf_syn]).  These are the Core-level lemmas behind the
   minimized e-graph rule queries (the [no_sort]/skip-sorts feature); they
   were factored out of Core.v, whose foundations they do not belong in. *)

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
    {|
      premodel := @syntax_model V V_Eqb;
      Model.eq_sort := eq_sort;
      Model.eq_term := eq_term;
      Model.wf_sort := wf_sort;
      Model.wf_term := wf_term;
    |}.

  Notation eq_subst l :=
    (eq_subst (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation eq_args l :=
    (eq_args (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation wf_subst l :=
    (wf_subst (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation wf_args l :=
    (wf_args (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation wf_ctx l :=
    (wf_ctx (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).

(* Inversion of a [con]'s well-formedness down to its argument list.  Unlike a
   direct [inversion], this peels any trailing conversions. *)
Lemma wf_term_con_args (l : lang) c n s t
  : wf_term l c (con n s) t ->
    exists c', wf_args l c s c'
            /\ (exists args tret, In (n, term_rule c' args tret) l).
Proof.
  intro H.
  remember (con n s) as e eqn:Heqe.
  revert Heqe.
  induction H; intro Heqe; try (exfalso; discriminate Heqe).
  - (* wf_term_by *)
    safe_invert Heqe.
    match goal with
    | Hwa : wf_args _ _ _ ?cc |- _ =>
        exists cc; split; [exact Hwa | repeat eexists; eassumption]
    end.
  - (* wf_term_conv *)
    match goal with
    | IH : _ = con _ _ -> _ |- _ => apply IH; exact Heqe
    end.
Qed.

(* Syntactic sort equality: a language where all [eq_sort] proofs reduce to
   propositional equality.  Used as a Prop hypothesis in Core so that
   SyntacticSorts.v (which imports Core) need not be imported here. *)
Definition syntactic_sort_eq (l : lang) : Prop :=
  forall c t1 t2, eq_sort l c t1 t2 -> t1 = t2.

(* ===================================================================== *)
(* COVERING WITHOUT SELF-REFERENCE (args helper).                         *)
(*                                                                        *)
(* Under [syntactic_sort_eq], the use=declared equation [eq_sort l c' t1 t'] *)
(* for a var in [fv e0] collapses to [t1 = t'] by [Hsyn], so [t1[/s/] =  *)
(* t'[/s/]] by [f_equal] and the image wf already lands at [t'[/s/]].    *)
(* No [wf_subst l c s c'] self-reference is needed.  The sort-alignment   *)
(* step ([Himgsort]) is the standard telescope [subst_assoc] computation, *)
(* wired into an args walk that takes an external term-level IH so the     *)
(* mutual recursion closes. *)
Lemma covering_var_leaf_syn_args_aux (l : lang) (wfl : wf_lang l)
      (c c' : ctx) (s : subst)
      (Hsyn : syntactic_sort_eq l)
      (Hwfc' : wf_ctx l c') (Hmap : map fst s = map fst c')
      (* [args] is a top-level parameter so [IHterm] can refer to it. *)
      (args : list term)
      (* term-level IH passed in: restricted to elements of [args] so callers
         can supply [all P args] (from [term_ind]) directly. *)
      (IHterm : forall e, In e args ->
                  forall t, wf_term l c' e t -> wf_term l c (e[/s/]) (t[/s/]) ->
                  forall x t', In x (fv e) -> In (x,t') c' ->
                    wf_term l c (subst_lookup s x) (t'[/s/]))
    : forall cA,
        wf_ctx l cA ->
        wf_args l c' args cA -> wf_args l c (args[/s/]) cA ->
        forall x t', In x (fv_args args) -> In (x,t') c' ->
          wf_term l c (subst_lookup s x) (t'[/s/]).
Proof.
  intros cA HwfcA Hsrc.
  revert HwfcA.
  induction Hsrc as [| rest_args cA'' nm e0 tnm He0 Hrest IHrest].
  - (* nil case: fv_args [] = [], contradiction *)
    intros _ Himg x t' Hfv _.
    cbn [fv_args flat_map] in Hfv. exact (False_ind _ Hfv).
  - (* cons case: args = e0::rest_args, cA = (nm,tnm)::cA'' *)
    intros HwfcA Himg x t' Hfv Hin.
    apply invert_wf_ctx_cons in HwfcA.
    destruct HwfcA as [HfrcA [HwfcA'' HwftnmA]].
    cbn [apply_subst substable_args args_subst apply_subst0 substable_term map] in Himg.
    safe_invert Himg.
    unfold fv_args in Hfv; cbn [flat_map] in Hfv; rewrite in_app_iff in Hfv.
    destruct Hfv as [Hfv_e0 | Hfv_rest].
    + (* x in fv e0: apply the term IH *)
      assert (Hlen : length cA'' = length rest_args)
        by (eapply wf_args_length_eq; eassumption).
      assert (Hwst_tnm : ws_sort (map fst cA'') tnm)
        by exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) HwftnmA).
      (* Sort alignment: tnm[/wnf cA'' rest_args/][/s/] = tnm[/wnf cA'' (rest_args[/s/])/] *)
      assert (Himgsort : tnm [/ with_names_from cA'' rest_args /] [/ s /] =
                         tnm [/ with_names_from cA'' (rest_args [/ s /]) /]).
      { rewrite with_names_from_args_subst.
        erewrite subst_assoc; [ reflexivity | typeclasses eauto | ].
        rewrite map_fst_with_names_from by exact Hlen.
        exact Hwst_tnm. }
      assert (H_img_e0 : wf_term l c (e0[/s/]) (tnm [/ with_names_from cA'' rest_args /] [/ s /])).
      { rewrite Himgsort.
        cbn [apply_subst substable_args args_subst apply_subst0 substable_term map].
        assumption. }
      exact (IHterm e0 (in_eq e0 rest_args) (tnm[/with_names_from cA'' rest_args/])
               He0 H_img_e0 x t' Hfv_e0 Hin).
    + (* x in fv_args rest_args: recurse on the tail via IHrest *)
      eapply IHrest.
      * (* IHterm restricted to rest_args *)
        intros e He_in. exact (IHterm e (in_cons e0 e rest_args He_in)).
      * eauto.
      * eauto.
      * exact Hfv_rest.
      * exact Hin.
Qed.

(* ===================================================================== *)
(* COVERING WITHOUT SELF-REFERENCE (term version).                        *)
(*                                                                        *)
(* Under [syntactic_sort_eq], for any e well-typed in c' whose image      *)
(* under s is well-typed in c, every occurrence of x in [fv e] has its   *)
(* image [s x] well-typed at the DECLARED sort [t'[/s/]].  Proved by     *)
(* structural induction on the term [e] via [term_ind], with the args     *)
(* walk handled by [covering_var_leaf_syn_args_aux]. *)
Lemma covering_var_leaf_syn (l : lang) (wfl : wf_lang l)
      (c c' : ctx) (s : subst)
      (Hsyn : syntactic_sort_eq l)
      (Hwfc' : wf_ctx l c') (Hmap : map fst s = map fst c') :
    forall e t, wf_term l c' e t -> wf_term l c (e[/s/]) (t[/s/]) ->
      forall x t', In x (fv e) -> In (x,t') c' ->
        wf_term l c (subst_lookup s x) (t'[/s/]).
Proof.
  induction e as [n | n se0 IHse0] using term_ind;
    intros t Hsrc Himg x t' Hfv Hin.
  - (* e = var n *)
    cbn [fv] in Hfv. destruct Hfv as [Hxn | []]. subst n.
    assert (Hvar : wf_term l c' (var x) t') by (apply wf_term_var; exact Hin).
    assert (Heqsrc : eq_sort l c' t t')
      by (exact (term_sorts_eq wfl Hwfc' Hsrc Hvar)).
    apply Hsyn in Heqsrc. subst t.
    exact Himg.
  - (* e = con n se0 *)
    cbn [fv] in Hfv.
    (* Invert source wf_term to get wf_args *)
    apply wf_term_con_args in Hsrc.
    destruct Hsrc as (cA_src & HwfA_src & argsA & tretA & HruleA_src).
    (* Invert image wf_term *)
    change ((con n se0)[/s/]) with (con n (se0[/s/])) in Himg.
    apply wf_term_con_args in Himg.
    destruct Himg as (cA_img & HwfA_img & argsI & tretI & HruleA_img).
    (* Pin the rule ctx to be the same *)
    pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) HruleA_src HruleA_img)
      as Heqr.
    safe_invert Heqr.
    (* wf_ctx l cA_img from the rule (cA_src = cA_img after safe_invert Heqr) *)
    assert (HwfcA : wf_ctx l cA_img)
      by (eapply rule_in_ctx_wf; [exact wfl | exact HruleA_img | reflexivity]).
    (* Build IHterm from IHse0 for the args walk.
       [IHse0 : all P se0] = [forall e, In e se0 -> P e] where
       P e = [forall t, wf_term l c' e t -> wf_term l c (e[/s/]) (t[/s/]) -> ...].
       The [covering_var_leaf_syn_args_aux] IHterm parameter now takes exactly this
       membership-restricted form, so we use [in_all IHse0] as the witness. *)
    assert (IHterm_aux : forall e, In e se0 ->
                forall t, wf_term l c' e t -> wf_term l c (e[/s/]) (t[/s/]) ->
                forall x t', In x (fv e) -> In (x,t') c' ->
                  wf_term l c (subst_lookup s x) (t'[/s/])).
    { intros e_arg He_in.
      (* IHse0 : all P se0 = forall e, In e se0 -> P e (via in_all).
         P e = the outer induction predicate, which is exactly the covering lemma
         for e.  So [in_all se0 e_arg IHse0 He_in : P e_arg] gives us the full IH. *)
      exact (@in_all _ _ se0 e_arg IHse0 He_in). }
    exact (covering_var_leaf_syn_args_aux wfl s Hsyn Hwfc' Hmap IHterm_aux
             HwfcA HwfA_src HwfA_img x t' Hfv Hin).
Qed.

End WithVar.
