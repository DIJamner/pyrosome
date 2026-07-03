(*
  Syntactic sort equality: a decision procedure that certifies, for a
  language [l], that judgmental sort equality coincides with structural
  equality (eq_sort l c t1 t2 -> t1 = t2).

  Motivation.  Pyrosome's e-graph query compiler skips the sort-of atom
  for context variables ("context matching that skips sorts of variables
  that appear in the pattern").  The SubstWfCounterexample series showed
  this can mis-type a variable when the language has SORT equations
  (A0 == A1 conversions).  Two refinements pin the real condition:

    (1) No sort_eq_rule.  This is the only axiom source for non-reflexive
        sort equality (eq_sort_by), so without it sort HEADS are stable
        under eq_sort.

    (2) (Necessary refinement.)  This alone is NOT sufficient for full
        syntactic equality.  eq_sort_subst carries an eq_subst whose two
        substitutions differ pointwise by eq_term, so a TERM equation
        a1 == a2 yields  scon n [a1] == scon n [a2]  -- same head, term-
        equal indices.  Genuine syntactic sort equality additionally
        requires that no term equation can fire at any sort used as an
        INDEX (an argument position of a sort constructor), transitively.

  In the simply-typed Pyrosome stack the index sorts are exactly
  {env, ty}, and all term equations conclude at sub/val/exp/blk -- never
  at an index sort -- so those languages satisfy the procedure.  (The
  polymorphic languages have ty_subst equations at ty and are correctly
  rejected.)

  This file is purely at the Theory layer; it does not touch the e-graph
  query code.  The certificate is the formal statement that, for an
  accepting language, a context variable's sort is structurally
  determined -- the property the counterexample series showed fails when
  sort/index equations are present.
*)

Set Implicit Arguments.

From Stdlib Require Import Lists.List.
Import ListNotations.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation eq_sort l := (eq_sort (V:=V) l).
  Notation eq_term l := (eq_term (V:=V) l).
  Notation eq_subst l := (eq_subst (Model:= core_model l)).
  Notation wf_sort l := (wf_sort (V:=V) l).
  Notation wf_term l := (wf_term (V:=V) l).
  Notation wf_args l := (wf_args (Model:= core_model l)).
  Notation wf_ctx l := (wf_ctx (Model:= core_model l)).

  (* ---------------------------------------------------------------- *)
  (* Basic projections                                                 *)
  (* ---------------------------------------------------------------- *)

  Definition sort_head (t : sort) : V := let (n,_) := t in n.

  Lemma sort_head_subst (s : subst) t : sort_head t[/s/] = sort_head t.
  Proof. destruct t; reflexivity. Qed.

  Definition ctx_sort_heads (c : ctx) : list V :=
    map (fun p => sort_head (snd p)) c.

  Definition is_sort_eq_ruleb (r : rule) : bool :=
    match r with sort_eq_rule _ _ _ => true | _ => false end.

  (* ---------------------------------------------------------------- *)
  (* Index heads: the sorts that occur (transitively) as indices.      *)
  (*                                                                    *)
  (* Inductive form (for proofs):                                       *)
  (*  - idx_seed: every head appearing in some sort_rule's context;     *)
  (*  - idx_term: if h is an index head and a term constructor concludes *)
  (*    at a sort with head h, then that constructor's context heads are *)
  (*    index heads (its arguments can be nested inside an index term).  *)
  (* ---------------------------------------------------------------- *)

  Inductive index_head (l : lang) : V -> Prop :=
  | idx_seed : forall n c args h,
      In (n, sort_rule c args) l ->
      In h (ctx_sort_heads c) ->
      index_head l h
  | idx_term : forall h n c args t h',
      index_head l h ->
      In (n, term_rule c args t) l ->
      sort_head t = h ->
      In h' (ctx_sort_heads c) ->
      index_head l h'.

  (* The directly-occurring index heads: every head appearing in a
     sort_rule context.  This already over-approximates [index_head]
     PROVIDED it is closed under one idx_term pass, which the decision
     procedure checks (see below) -- so no saturation/fixpoint iteration
     is needed. *)
  Definition seed_index_heads (l : lang) : list V :=
    flat_map (fun p => match snd p with
                       | sort_rule c _ => ctx_sort_heads c
                       | _ => [] end) l.

  (* One idx_term closure pass: for every term constructor whose
     conclusion head is already in [R], throw in its context heads. *)
  Definition close_index_step (l : lang) (R : list V) : list V :=
    R ++ flat_map (fun p => match snd p with
                            | term_rule c _ t =>
                                if inb (sort_head t) R then ctx_sort_heads c else []
                            | _ => [] end) l.

  Definition index_heads_b (l : lang) : list V := seed_index_heads l.

  (* [seed_index_heads] is only a sound over-approximation of [index_head]
     when it is already closed under one [close_index_step] pass.  The
     polymorphic languages break that: e.g. [ty_subst g A : ty] carries a
     [g : ty_sub] argument and concludes at the index head [ty], so [ty_sub]
     belongs in the cone -- yet nothing is *indexed by* a [ty_sub], so it is
     not in the seed.  [index_heads_sat] iterates the closure to a fixpoint
     (bounded by [length l], since each non-fixpoint step adds a head and
     heads are drawn from the finitely-many rule heads). *)
  Fixpoint saturate_heads (fuel : nat) (l : lang) (R : list V) : list V :=
    match fuel with
    | 0 => R
    | S fuel' =>
        let R' := close_index_step l R in
        if inclb R' R then R else saturate_heads fuel' l R'
    end.

  Definition index_heads_sat (l : lang) : list V :=
    saturate_heads (List.length l) l (seed_index_heads l).

  (* ---------------------------------------------------------------- *)
  (* The decision procedure                                            *)
  (* ---------------------------------------------------------------- *)

  Definition syntactic_sort_eq_langb (l : lang) : bool :=
    let R := index_heads_b l in
    forallb (fun p => negb (is_sort_eq_ruleb (snd p))) l
    && inclb (close_index_step l R) R
    && forallb (fun p => match snd p with
                         | term_eq_rule _ _ _ t => negb (inb (sort_head t) R)
                         | _ => true end) l.

  (* The WEAKENED procedure (candidate min-sorts gate for the polymorphic /
     existential languages).  Two relaxations vs. [syntactic_sort_eq_langb]:
     (a) index heads are computed by full saturation [index_heads_sat]
         (needed even for the simply-typed check's shape once [ty_subst]-style
         constructors are present);
     (b) a [term_eq_rule] concluding at an index head is permitted when it is
         UNGATED -- every context variable occurs in the equated terms
         (unlike the SubstWfCounterexample gates, whose witness variable
         occurs in neither side).

     CAUTION: this boolean ALONE does not certify the sort-transport property
     the skip soundness needs.  A trans-chain can route through a middle whose
     variables are pinned by only ONE side of an ungated equation, and if such
     a variable's sort has no closed inhabitant the chain does not replay in
     the empty context -- machine-checked counterexample in
     WIP/TransportCounterexample.v.  The intended soundness statement pairs
     this boolean with a per-language closed-inhabitation side condition for
     the index fragment (Prop-level; see WIP/SortTransport.v), whose
     sufficiency is itself still an open conjecture.  The e-graph gate
     remains [syntactic_sort_eq_langb] until that is settled. *)
  Definition ungated_index_term_eqb (R : list V) (r : rule) : bool :=
    match r with
    | term_eq_rule c e1 e2 t =>
        negb (inb (sort_head t) R) || inclb (map fst c) (fv e1 ++ fv e2)
    | _ => true
    end.

  Definition syntactic_sort_eq_langb' (l : lang) : bool :=
    let R := index_heads_sat l in
    forallb (fun p => negb (is_sort_eq_ruleb (snd p))) l
    && inclb (close_index_step l R) R
    && forallb (fun p => ungated_index_term_eqb R (snd p)) l.

  (* ---------------------------------------------------------------- *)
  (* Helper soundness lemmas about the decision procedure              *)
  (* ---------------------------------------------------------------- *)

  Section WithLang.
    Context (l : lang).

    (* (a) no sort equations. *)
    Lemma no_sort_eq :
      syntactic_sort_eq_langb l = true ->
      forall n c t1 t2, ~ In (n, sort_eq_rule c t1 t2) l.
    Proof.
      unfold syntactic_sort_eq_langb.
      rewrite !Bool.andb_true_iff.
      intros [[Hsort _] _] n c t1 t2 Hin.
      rewrite forallb_forall in Hsort.
      specialize (Hsort _ Hin).
      cbn in Hsort.
      discriminate.
    Qed.

    (* The seed over-approximates the inductive cone PROVIDED it is closed
       under one idx_term pass -- exactly what the decision procedure's
       [inclb] conjunct checks.  No saturation/fixpoint iteration needed. *)
    Lemma index_head_in_seed :
      inclb (close_index_step l (seed_index_heads l)) (seed_index_heads l) = true ->
      forall h, index_head l h -> In h (seed_index_heads l).
    Proof.
      intro Hcl.
      apply Is_true_eq_left in Hcl.
      apply use_inclb in Hcl.
      induction 1.
      - (* idx_seed *)
        apply in_flat_map.
        exists (n, sort_rule c args).
        split; [assumption | cbn; assumption].
      - (* idx_term *)
        apply Hcl.
        unfold close_index_step.
        apply in_or_app; right.
        apply in_flat_map.
        exists (n, term_rule c args t).
        split; [assumption | cbn].
        assert (inb (sort_head t) (seed_index_heads l) = true) as ->.
        { apply Is_true_eq_true.
          autorewrite with utils.
          rewrite H1; assumption. }
        assumption.
    Qed.

    (* Generalization of [index_head_in_seed] to any set [R] that contains the
       seed and is closed under one [close_index_step] pass.  This is what lets
       the saturated cone [index_heads_sat] soundly over-approximate. *)
    Lemma index_head_in_closed (R : list V) :
      incl (seed_index_heads l) R ->
      incl (close_index_step l R) R ->
      forall h, index_head l h -> In h R.
    Proof.
      intros Hseed Hcl.
      induction 1.
      - (* idx_seed *)
        apply Hseed. apply in_flat_map.
        exists (n, sort_rule c args). split; [assumption | cbn; assumption].
      - (* idx_term *)
        apply Hcl.
        unfold close_index_step.
        apply in_or_app; right.
        apply in_flat_map.
        exists (n, term_rule c args t).
        split; [assumption | cbn].
        assert (inb (sort_head t) R = true) as ->.
        { apply Is_true_eq_true. autorewrite with utils. rewrite H1; assumption. }
        assumption.
    Qed.

    (* [saturate_heads] only grows its input, so the seed sits inside the
       saturated cone. *)
    Lemma saturate_grows : forall fuel R, incl R (saturate_heads fuel l R).
    Proof.
      induction fuel; intro R; cbn [saturate_heads].
      - apply incl_refl.
      - destruct (inclb (close_index_step l R) R).
        + apply incl_refl.
        + eapply incl_tran; [ | apply IHfuel ].
          unfold close_index_step. apply incl_appl. apply incl_refl.
    Qed.

    Lemma seed_incl_sat : incl (seed_index_heads l) (index_heads_sat l).
    Proof. apply saturate_grows. Qed.

    (* The saturated cone soundly over-approximates [index_head], provided the
       decision procedure's closure conjunct holds for it. *)
    Lemma index_head_in_sat :
      inclb (close_index_step l (index_heads_sat l)) (index_heads_sat l) = true ->
      forall h, index_head l h -> In h (index_heads_sat l).
    Proof.
      intro Hcl.
      apply index_head_in_closed.
      - apply seed_incl_sat.
      - apply use_inclb. apply Is_true_eq_left. exact Hcl.
    Qed.

    (* (b) no term equation concludes at an index head. *)
    Lemma no_term_eq_at_index :
      syntactic_sort_eq_langb l = true ->
      forall n c e1 e2 t,
        In (n, term_eq_rule c e1 e2 t) l ->
        ~ index_head l (sort_head t).
    Proof.
      unfold syntactic_sort_eq_langb.
      rewrite !Bool.andb_true_iff.
      intros [[_ Hcl] Hterm] n c e1 e2 t Hin Hidx.
      rewrite forallb_forall in Hterm.
      specialize (Hterm _ Hin).
      cbn in Hterm.
      apply (index_head_in_seed Hcl) in Hidx.
      assert (Hb : inb (sort_head t) (index_heads_b l) = true).
      { apply Is_true_eq_true. autorewrite with utils. exact Hidx. }
      rewrite Hb in Hterm.
      cbn in Hterm.
      discriminate.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* Head determinacy (weaker; holds under (a) alone).                 *)
    (* ---------------------------------------------------------------- *)

    Lemma eq_sort_head_det :
      syntactic_sort_eq_langb l = true ->
      forall c t1 t2, eq_sort l c t1 t2 -> sort_head t1 = sort_head t2.
    Proof.
      intro Hdec.
      induction 1.
      - (* eq_sort_by: no sort equations *)
        exfalso; eapply no_sort_eq; eauto.
      - (* eq_sort_subst *)
        rewrite !sort_head_subst; assumption.
      - (* eq_sort_refl *) reflexivity.
      - (* eq_sort_trans *) etransitivity; eassumption.
      - (* eq_sort_sym *) symmetry; assumption.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* Structural lemma: every free variable of a wf sort/term has an    *)
    (* index-head sort in the context.  (The SORT case is unconditional: *)
    (* a sort's arguments always sit at index sorts, via idx_seed.  The  *)
    (* TERM case needs the subject sort to be an index head, and the     *)
    (* wf_term_conv case uses eq_sort_head_det to transport that.)        *)
    (* ---------------------------------------------------------------- *)

    Lemma fv_index :
      syntactic_sort_eq_langb l = true ->
      wf_lang l ->
      (forall c t, wf_sort l c t ->
         forall x, In x (fv_sort t) ->
           exists tx, In (x, tx) c /\ index_head l (sort_head tx))
      /\ (forall c e t, wf_term l c e t ->
         index_head l (sort_head t) ->
         forall x, In x (fv e) ->
           exists tx, In (x, tx) c /\ index_head l (sort_head tx))
      /\ (forall c s c', wf_args l c s c' ->
         (forall n t, In (n, t) c' -> index_head l (sort_head t)) ->
         forall x, In x (fv_args s) ->
           exists tx, In (x, tx) c /\ index_head l (sort_head tx)).
    Proof.
      intros Hdec wfl.
      apply wf_judge_ind.
      - (* wf_sort_by *)
        intros c n s args c' Hln Hwfargs IHargs x Hx.
        simpl in Hx.
        apply IHargs; [| exact Hx].
        intros n0 t0 Hin0.
        eapply idx_seed.
        + exact Hln.
        + unfold ctx_sort_heads.
          apply in_map_iff.
          exists (n0, t0). split; [reflexivity | exact Hin0].
      - (* wf_term_by *)
        intros c n s args c' t Hln Hwfargs IHargs Hidx x Hx.
        simpl in Hx.
        rewrite sort_head_subst in Hidx.
        apply IHargs; [| exact Hx].
        intros n0 t0 Hin0.
        eapply idx_term.
        + exact Hidx.
        + exact Hln.
        + reflexivity.
        + unfold ctx_sort_heads.
          apply in_map_iff.
          exists (n0, t0). split; [reflexivity | exact Hin0].
      - (* wf_term_conv *)
        intros c e t t' Hwf IHwf Heq Hidx' x Hx.
        apply IHwf; [| exact Hx].
        eapply eq_sort_head_det in Heq; [| exact Hdec].
        rewrite Heq.
        exact Hidx'.
      - (* wf_term_var *)
        intros c n t Hin Hidx x Hx.
        simpl in Hx. destruct Hx as [<- | []].
        exists t. split; [exact Hin | exact Hidx].
      - (* wf_args_nil *)
        intros c Hc x Hx.
        simpl in Hx. exact (False_ind _ Hx).
      - (* wf_args_cons *)
        intros c s c' name e t Hwfe IHwfe Hwfs IHwfs Hc x Hx.
        unfold fv_args in Hx.
        simpl in Hx.
        apply in_app_or in Hx.
        destruct Hx as [Hxe | Hxs].
        + apply IHwfe; [| exact Hxe].
          rewrite sort_head_subst.
          apply (Hc name t).
          left. reflexivity.
        + apply IHwfs; [| exact Hxs].
          intros n0 t0 Hin0.
          apply (Hc n0 t0).
          right. exact Hin0.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* Helper: substitutions that agree on free variables agree on       *)
    (* term/sort substitution.                                           *)
    (* ---------------------------------------------------------------- *)

    Local Lemma term_subst_fv_eq (s1 s2 : subst) (e : term) :
      (forall x, In x (fv e) -> subst_lookup s1 x = subst_lookup s2 x) ->
      e[/s1/] = e[/s2/].
    Proof.
      induction e using term_ind; simpl; intro Heq.
      - (* var n *)
        apply Heq. left. reflexivity.
      - (* con n l0 *)
        f_equal.
        induction l0 as [|a0 l0' IHl0].
        + reflexivity.
        + destruct H as [IHa IHl].
          simpl. f_equal.
          * apply IHa. intros x Hx. apply Heq.
            apply in_flat_map. exists a0. split; [left; reflexivity | exact Hx].
          * apply IHl0; [exact IHl |]. intros x Hx. apply Heq.
            apply in_flat_map in Hx. destruct Hx as [e' [He' Hx']].
            apply in_flat_map. exists e'. split; [right; exact He' | exact Hx'].
    Qed.

    Local Lemma sort_subst_fv_eq (s1 s2 : subst) (t : sort) :
      (forall x, In x (fv_sort t) -> subst_lookup s1 x = subst_lookup s2 x) ->
      t[/s1/] = t[/s2/].
    Proof.
      destruct t as [n args].
      simpl. unfold fv_sort. simpl.
      intro H.
      f_equal.
      induction args as [|a args' IHargs].
      - reflexivity.
      - simpl. f_equal.
        + apply term_subst_fv_eq. intros x Hx. apply H.
          apply in_flat_map. exists a. split; [left; reflexivity | exact Hx].
        + apply IHargs. intros x Hx. apply H.
          apply in_flat_map in Hx. destruct Hx as [e' [He' Hx']].
          apply in_flat_map. exists e'. split; [right; exact He' | exact Hx'].
    Qed.

    (* ---------------------------------------------------------------- *)
    (* The certificate: full syntactic sort equality.                    *)
    (* ---------------------------------------------------------------- *)

    (* Substitutions related by eq_subst agree (by lookup) on index-headed
       entries of a fresh context, once the term-equality-at-index motive
       is known.  This collapses the asymmetric s1/s2 in eq_sort_subst /
       eq_term_subst.  See P1 in the judge_ind proof below. *)

    Lemma syntactic_sort_eq_sound :
      syntactic_sort_eq_langb l = true ->
      wf_lang l ->
      forall c t1 t2, eq_sort l c t1 t2 -> t1 = t2.
    Proof.
      intros Hdec wfl.
      pose proof (@judge_ind V V_Eqb l
        (fun c t1 t2 => t1 = t2)
        (fun c t e1 e2 => index_head l (sort_head t) -> e1 = e2)
        (fun c c' s1 s2 =>
           all_fresh c' ->
           forall x tx, In (x,tx) c' -> index_head l (sort_head tx) ->
             subst_lookup s1 x = subst_lookup s2 x)
        (fun _ _ => True)
        (fun _ _ _ => True)
        (fun _ _ _ => True)
        (fun _ => True)) as Hind.
      (* f: eq_sort_by -- impossible *)
      lapply Hind; [clear Hind; intro Hind |
        intros c name t1 t2 Hin; exfalso; eapply no_sort_eq; eauto].
      (* f0: eq_sort_subst *)
      lapply Hind; [clear Hind; intro Hind |].
      2: {
        intros c s1 s2 c' t1' t2' Hwfc' _ Heqs Hs Heqsort Ht1t2.
        subst.
        apply sort_subst_fv_eq.
        intros x Hx.
        assert (Hwfs : wf_sort l c' t2').
        { eapply eq_sort_wf_l; eauto. }
        destruct (proj1 (fv_index Hdec wfl) _ _ Hwfs x Hx) as [tx [Hintx Hidx]].
        eapply Hs; eauto. eapply wf_ctx_all_fresh; eauto.
      }
      (* f1: eq_sort_refl *)
      lapply Hind; [clear Hind; intro Hind |]. 2: { intros; reflexivity. }
      (* f2: eq_sort_trans *)
      lapply Hind; [clear Hind; intro Hind |]. 2: { intros; congruence. }
      (* f3: eq_sort_sym *)
      lapply Hind; [clear Hind; intro Hind |]. 2: { intros; symmetry; assumption. }
      (* f4: eq_term_subst *)
      lapply Hind; [clear Hind; intro Hind |].
      2: {
        intros c s1 s2 c' t e1 e2 Hwfc' _ Heqs Hs Heqterm He1e2.
        intro Hidx.
        rewrite sort_head_subst in Hidx.
        specialize (He1e2 Hidx). subst.
        apply term_subst_fv_eq.
        intros x Hx.
        assert (Hwft : wf_term l c' e2 t).
        { eapply eq_term_wf_l; eauto. }
        destruct (proj1 (proj2 (fv_index Hdec wfl)) _ _ _ Hwft Hidx x Hx)
          as [tx [Hintx Hidxtx]].
        eapply Hs; eauto. eapply wf_ctx_all_fresh; eauto.
      }
      (* f5: eq_term_by -- impossible *)
      lapply Hind; [clear Hind; intro Hind |
        intros c name t e1 e2 Hin Hidx; exfalso; eapply no_term_eq_at_index; eauto].
      (* f6: eq_term_refl *)
      lapply Hind; [clear Hind; intro Hind |]. 2: { intros; reflexivity. }
      (* f7: eq_term_trans *)
      lapply Hind; [clear Hind; intro Hind |].
      2: { intros c t e1 e12 e2 _ IH1 _ IH2 Hidx.
           etransitivity; [apply IH1 | apply IH2]; exact Hidx. }
      (* f8: eq_term_sym *)
      lapply Hind; [clear Hind; intro Hind |].
      2: { intros c t e1 e2 _ IH Hidx. symmetry; apply IH; exact Hidx. }
      (* f9: eq_term_conv *)
      lapply Hind; [clear Hind; intro Hind |].
      2: {
        intros c t t' Heqsort Ht e1 e2 Heqterm IHe Hidx'.
        apply IHe. rewrite Ht. exact Hidx'.
      }
      (* f10: eq_subst_nil *)
      lapply Hind; [clear Hind; intro Hind |
        intros c Haf x tx Hin; simpl in Hin; exact (False_ind _ Hin)].
      (* f11: eq_subst_cons -- rewrite !subst_lookup_hd generates Eqb_ok side goals *)
      lapply Hind; [clear Hind; intro Hind |].
      2: intros c c' s1 s2 Heqs Hs name t e1 e2 Heqterm IHe Haf x tx Hinxt Hidx.
      2: destruct Haf as [Hfresh Haf'].
      2: destruct Hinxt as [[= <- <-] | Hinxt'].
      (* x = name, tx = t: rewrite both lookups to e1/e2 *)
      2: rewrite !subst_lookup_hd.
      2: apply IHe; rewrite sort_head_subst; exact Hidx.
      (* Eqb_ok side goals from rewrite !subst_lookup_hd (one per rewrite) *)
      3: exact V_Eqb_ok.
      2: exact V_Eqb_ok.
      (* x ≠ name: simplify lookup on both sides and use IH *)
      2: (assert (Hne : x <> name) by
           (intro Hxn; subst x; eapply fresh_notin; [exact Hfresh | exact Hinxt']);
         unfold subst_lookup; simpl;
         destruct (eqb x name) eqn:Hxn;
         [pose proof (@eqb_spec V V_Eqb V_Eqb_ok x name) as Hspec;
          rewrite Hxn in Hspec; exact (False_ind _ (Hne Hspec)) |
          exact (Hs Haf' x tx Hinxt' Hidx)]).
      (* wf cases f12..f19: all True *)
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      lapply Hind; [clear Hind; intro Hind | exact I].
      lapply Hind; [clear Hind; intro Hind | intros; exact I].
      (* Extract the eq_sort component *)
      exact (proj1 Hind).
    Qed.

    (* A context variable's sort is structurally determined: the property
       the cex series showed FAILS when sort/index equations are present. *)
    Theorem syntactic_sort_eq_var_det :
      syntactic_sort_eq_langb l = true ->
      wf_lang l ->
      forall c, wf_ctx l c ->
      forall n t t',
        In (n, t) c ->
        wf_term l c (var n) t' ->
        t = t'.
    Proof.
      intros Hdec wfl c Hwfc n t t' Hint Hwft.
      (* Invert wf_term (var n) t' to get t0 with In(n,t0)c and (t0=t' or eq_sort c t0 t') *)
      remember (var n) as e eqn:He.
      revert He.
      induction Hwft; intro He; try discriminate.
      - (* wf_term_conv: wf_term c e t0, eq_sort c t0 t' *)
        subst.
        specialize (IHHwft Hwfc Hint eq_refl).
        subst.
        (* now t0 = t, eq_sort c t t' *)
        apply syntactic_sort_eq_sound with (c := c); assumption.
      - (* wf_term_var: In (n, t') c *)
        injection He as <-.
        eapply in_all_fresh_same; eauto.
        eapply wf_ctx_all_fresh; eauto.
    Qed.

  End WithLang.

End WithVar.
