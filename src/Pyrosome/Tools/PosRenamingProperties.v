(* Bijection theorems for the operations in PosRenaming.v.

   Each renaming operation produces a state [r'] for which the
   corresponding [unrename_*] function is a left inverse, and every
   positive in its output is bound in [r']. *)

Set Implicit Arguments.

From Stdlib Require Import Lists.List NArith.
Import ListNotations.
Open Scope list.
Open Scope positive.

From coqutil Require Import Map.Interface.
From Tries Require Import Canonical.

From Utils Require Import Utils Monad TrieMap.
Import StateMonad.

From Pyrosome Require Import Theory.Core Tools.PosRenaming.
From Pyrosome Require Theory.Renaming.

(* [of_p], [next_id], [empty_rename], [alloc] are defined in
   PosRenaming.v inside sections that make [V] explicit.  Restate
   [Arguments] so calls look natural in this file. *)
Arguments of_p {V}%_type_scope {V_default} r p.
Arguments next_id {V}%_type_scope r.
Arguments empty_rename {V}%_type_scope.
Arguments alloc {V}%_type_scope n _.
Arguments rename_ctx {V}%_type_scope {V_Eqb} c _.
Arguments rename_rule {V}%_type_scope {V_Eqb} r _.

#[local] Instance positive_Eqb : Eqb positive := Pos.eqb.

#[local] Instance positive_Eqb_ok : Eqb_ok positive_Eqb.
Proof.
  intros a b.
  unfold eqb, positive_Eqb.
  destruct (Pos.eqb_spec a b); auto.
Qed.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation pterm := (Term.term positive).
  Notation psort := (Term.sort positive).
  Notation pctx := (Term.ctx positive).
  Notation prule := (Rule.rule positive).
  Notation plang := (Rule.lang positive).

  Notation renaming := (PosRenaming.renaming V).

  (* Local notations for the lang-parameterized core-model judgments,
     mirroring the ones in Theory/Renaming.v.  [eq_sort]/[eq_term]/
     [wf_sort]/[wf_term] are already parameterized by [lang] in
     [Theory/Core.v]; only the [Model]-based ones need re-instantiation. *)
  #[local] Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  #[local] Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  #[local] Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  #[local] Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  (** ** Inverse operations on sorts/contexts/rules/languages.
      [unrename_term] is already defined in PosRenaming.v. *)

  Definition unrename_sort (r : renaming) (ts : psort) : sort :=
    let (n, s) := ts in
    scon (of_p r n) (map (unrename_term r) s).

  Definition unrename_ctx (r : renaming) (c : pctx) : ctx :=
    map (fun p => (of_p r (fst p), unrename_sort r (snd p))) c.

  Definition unrename_rule (r : renaming) (rr : prule) : rule :=
    match rr with
    | sort_rule c args =>
        sort_rule (unrename_ctx r c) (map (of_p r) args)
    | term_rule c args ts =>
        term_rule (unrename_ctx r c) (map (of_p r) args) (unrename_sort r ts)
    | sort_eq_rule c ts1 ts2 =>
        sort_eq_rule (unrename_ctx r c)
          (unrename_sort r ts1) (unrename_sort r ts2)
    | term_eq_rule c e1 e2 ts =>
        term_eq_rule (unrename_ctx r c)
          (unrename_term r e1) (unrename_term r e2) (unrename_sort r ts)
    end.

  Definition unrename_lang (r : renaming) (l : plang) : lang :=
    map (fun p => (of_p r (fst p), unrename_rule r (snd p))) l.

  (** ** State well-formedness invariant *)

  Record renaming_ok (r : renaming) : Prop :=
    {
      ren_all_fresh : all_fresh r.(v_to_p);
      ren_v_to_p_in_p_to_v :
        forall v p, In (v, p) r.(v_to_p) -> map.get r.(p_to_v) p = Some v;
      ren_p_to_v_in_v_to_p :
        forall v p, map.get r.(p_to_v) p = Some v -> In (v, p) r.(v_to_p);
      ren_bound :
        forall v p, In (v, p) r.(v_to_p) -> Pos.lt p r.(next_id)
    }.

  Lemma empty_renaming_ok : renaming_ok empty_rename.
  Proof.
    constructor; cbn.
    - exact I.
    - intros ? ? [].
    - intros v p Hget; cbn in Hget; congruence.
    - intros ? ? [].
  Qed.

  Lemma renaming_ok_next_id r :
    renaming_ok r -> map.get r.(p_to_v) r.(next_id) = None.
  Proof.
    intros [_ _ Hpv Hbnd].
    destruct (map.get r.(p_to_v) r.(next_id)) eqn:Heq; auto.
    apply Hpv in Heq; apply Hbnd in Heq.
    apply Pos.lt_irrefl in Heq; contradiction.
  Qed.

  (** ** Growth (extension) relation between states *)

  Definition rename_grows (r r' : renaming) : Prop :=
    forall p v, map.get r.(p_to_v) p = Some v ->
                map.get r'.(p_to_v) p = Some v.

  Lemma rename_grows_refl r : rename_grows r r.
  Proof. intros ? ? ?; assumption. Qed.

  Lemma rename_grows_trans r1 r2 r3 :
    rename_grows r1 r2 -> rename_grows r2 r3 -> rename_grows r1 r3.
  Proof. intros H1 H2 p v Hp. apply H2, H1; assumption. Qed.

  Lemma of_p_lookup {r p v} :
    map.get r.(p_to_v) p = Some v -> of_p r p = v.
  Proof. intros H; unfold of_p; rewrite H; reflexivity. Qed.

  Lemma of_p_grows {r r' p v} :
    rename_grows r r' ->
    map.get r.(p_to_v) p = Some v -> of_p r' p = v.
  Proof. intros Hg Hr; apply of_p_lookup, Hg, Hr. Qed.

  (** ** Domain predicates: every positive head in a value is bound. *)

  Definition pbound (r : renaming) (p : positive) : Prop :=
    exists v, map.get r.(p_to_v) p = Some v.

  Lemma pbound_grows {r r' p} :
    rename_grows r r' -> pbound r p -> pbound r' p.
  Proof. intros Hg [v Hv]; exists v; eapply Hg; eauto. Qed.

  Lemma of_p_eq {r r' p} :
    rename_grows r r' -> pbound r p -> of_p r' p = of_p r p.
  Proof.
    intros Hg [v Hv].
    rewrite (of_p_lookup Hv), (of_p_grows Hg Hv); reflexivity.
  Qed.

  (** A concrete [V -> positive] function read off the renaming.  On
      V's bound in [r] it returns the corresponding positive; otherwise
      it returns [xH] (the [positive_default]).  This is the canonical
      function the final preservation theorems use. *)

  #[local] Instance positive_default : WithDefault positive := xH.

  Definition pos_of_v (r : renaming) (v : V) : positive :=
    unwrap_with_default (named_list_lookup_err r.(v_to_p) v).

  Fixpoint term_bound (r : renaming) (e : pterm) : Prop :=
    match e with
    | var p => pbound r p
    | con n s => pbound r n /\ all (term_bound r) s
    end.

  Definition sort_bound (r : renaming) (ts : psort) : Prop :=
    let (n, s) := ts in pbound r n /\ all (term_bound r) s.

  Definition ctx_bound (r : renaming) (c : pctx) : Prop :=
    all (fun p => pbound r (fst p) /\ sort_bound r (snd p)) c.

  Definition rule_bound (r : renaming) (rr : prule) : Prop :=
    match rr with
    | sort_rule c args => ctx_bound r c /\ all (pbound r) args
    | term_rule c args ts =>
        ctx_bound r c /\ all (pbound r) args /\ sort_bound r ts
    | sort_eq_rule c ts1 ts2 =>
        ctx_bound r c /\ sort_bound r ts1 /\ sort_bound r ts2
    | term_eq_rule c e1 e2 ts =>
        ctx_bound r c
        /\ term_bound r e1 /\ term_bound r e2 /\ sort_bound r ts
    end.

  Definition lang_bound (r : renaming) (l : plang) : Prop :=
    all (fun p => pbound r (fst p) /\ rule_bound r (snd p)) l.

  (** ** Growth lemmas for bound predicates and inverse functions. *)

  Lemma all_grows {A} (P P' : A -> Prop) (l : list A) :
    (forall x, P x -> P' x) -> all P l -> all P' l.
  Proof.
    intros HPP'.
    induction l; cbn; auto.
    intros [Ha Hl]; split; auto.
  Qed.

  Lemma term_bound_grows {r r' e} :
    rename_grows r r' -> term_bound r e -> term_bound r' e.
  Proof.
    intros Hg.
    induction e using term_ind; cbn.
    - apply (pbound_grows Hg).
    - intros [Hn Hs]; split; [apply (pbound_grows Hg); assumption|].
      induction l; cbn in *; auto.
      destruct H as [Ha Hrest]; destruct Hs as [Hsa Hsr]; split; auto.
  Qed.

  Lemma unrename_term_grows {r r' e} :
    rename_grows r r' -> term_bound r e ->
    unrename_term r' e = unrename_term r e.
  Proof.
    intros Hg.
    induction e using term_ind; cbn.
    - intros Hb; f_equal; apply (of_p_eq Hg Hb).
    - intros [Hn Hs].
      f_equal.
      + apply (of_p_eq Hg Hn).
      + induction l; cbn in *; auto.
        destruct H as [Ha Hrest]; destruct Hs as [Hsa Hsr].
        f_equal; auto.
  Qed.

  Lemma sort_bound_grows {r r' ts} :
    rename_grows r r' -> sort_bound r ts -> sort_bound r' ts.
  Proof.
    destruct ts as [n s]; cbn.
    intros Hg [Hn Hs].
    split; [apply (pbound_grows Hg Hn)|].
    eapply all_grows; [|exact Hs].
    intros x; apply (term_bound_grows Hg).
  Qed.

  Lemma unrename_sort_grows {r r' ts} :
    rename_grows r r' -> sort_bound r ts ->
    unrename_sort r' ts = unrename_sort r ts.
  Proof.
    destruct ts as [n s]; cbn.
    intros Hg [Hn Hs].
    f_equal.
    - apply (of_p_eq Hg Hn).
    - induction s; cbn in *; auto.
      destruct Hs as [Ha Hs'].
      f_equal; auto.
      apply unrename_term_grows; auto.
  Qed.

  Lemma ctx_bound_grows {r r' c} :
    rename_grows r r' -> ctx_bound r c -> ctx_bound r' c.
  Proof.
    intros Hg.
    induction c as [|p c IH]; cbn; auto.
    intros Hpc.
    destruct Hpc as [Hhead Hc].
    destruct Hhead as [Hh Hsh].
    split; [split|].
    - apply (pbound_grows Hg Hh).
    - apply (sort_bound_grows Hg Hsh).
    - apply IH; auto.
  Qed.

  Lemma unrename_ctx_grows {r r' c} :
    rename_grows r r' -> ctx_bound r c ->
    unrename_ctx r' c = unrename_ctx r c.
  Proof.
    intros Hg.
    induction c as [|p c IH]; cbn; auto.
    intros Hpc.
    destruct Hpc as [Hhead Hc].
    destruct Hhead as [Hh Hsh].
    f_equal.
    - f_equal; [apply (of_p_eq Hg Hh) | apply (unrename_sort_grows Hg Hsh)].
    - apply IH; auto.
  Qed.

  Lemma all_pbound_grows {r r' xs} :
    rename_grows r r' -> all (pbound r) xs -> all (pbound r') xs.
  Proof.
    intros Hg.
    induction xs; cbn; auto.
    intros [Ha Hs]; split; auto.
    apply (pbound_grows Hg Ha).
  Qed.

  Lemma map_of_p_eq {r r' xs} :
    rename_grows r r' -> all (pbound r) xs ->
    map (of_p r') xs = map (of_p r) xs.
  Proof.
    intros Hg.
    induction xs; cbn; auto.
    intros [Ha Hs].
    f_equal; auto.
    apply (of_p_eq Hg Ha).
  Qed.

  Lemma rule_bound_grows {r r' rr} :
    rename_grows r r' -> rule_bound r rr -> rule_bound r' rr.
  Proof.
    intros Hg Hrr.
    destruct rr as [c args | c args ts | c ts1 ts2 | c e1 e2 ts]; cbn in *.
    - destruct Hrr as [Hc Hargs].
      split; [apply (ctx_bound_grows Hg Hc)
             | apply (all_pbound_grows Hg Hargs)].
    - destruct Hrr as [Hc Hrest].
      destruct Hrest as [Hargs Hts].
      split; [apply (ctx_bound_grows Hg Hc)|].
      split; [apply (all_pbound_grows Hg Hargs)
             | apply (sort_bound_grows Hg Hts)].
    - destruct Hrr as [Hc Hrest].
      destruct Hrest as [Hts1 Hts2].
      split; [apply (ctx_bound_grows Hg Hc)|].
      split; [apply (sort_bound_grows Hg Hts1)
             | apply (sort_bound_grows Hg Hts2)].
    - destruct Hrr as [Hc Hrest].
      destruct Hrest as [He1 Hrest2].
      destruct Hrest2 as [He2 Hts].
      split; [apply (ctx_bound_grows Hg Hc)|].
      split; [apply (term_bound_grows Hg He1)|].
      split; [apply (term_bound_grows Hg He2)
             | apply (sort_bound_grows Hg Hts)].
  Qed.

  Lemma unrename_rule_grows {r r' rr} :
    rename_grows r r' -> rule_bound r rr ->
    unrename_rule r' rr = unrename_rule r rr.
  Proof.
    intros Hg.
    destruct rr as [c args | c args ts | c ts1 ts2 | c e1 e2 ts]; cbn.
    - intros [Hc Hargs].
      f_equal.
      + apply (unrename_ctx_grows Hg Hc).
      + apply (map_of_p_eq Hg Hargs).
    - intros (Hc & Hargs & Hts).
      f_equal.
      + apply (unrename_ctx_grows Hg Hc).
      + apply (map_of_p_eq Hg Hargs).
      + apply (unrename_sort_grows Hg Hts).
    - intros (Hc & Hts1 & Hts2).
      f_equal.
      + apply (unrename_ctx_grows Hg Hc).
      + apply (unrename_sort_grows Hg Hts1).
      + apply (unrename_sort_grows Hg Hts2).
    - intros (Hc & He1 & He2 & Hts).
      f_equal.
      + apply (unrename_ctx_grows Hg Hc).
      + apply (unrename_term_grows Hg He1).
      + apply (unrename_term_grows Hg He2).
      + apply (unrename_sort_grows Hg Hts).
  Qed.

  Lemma lang_bound_grows {r r' l} :
    rename_grows r r' -> lang_bound r l -> lang_bound r' l.
  Proof.
    intros Hg.
    induction l as [|p l IH]; cbn; auto.
    intros Hpl.
    destruct Hpl as [Hhead Hl].
    destruct Hhead as [Hh Hrh].
    split; [split|].
    - apply (pbound_grows Hg Hh).
    - apply (rule_bound_grows Hg Hrh).
    - apply IH; auto.
  Qed.

  Lemma unrename_lang_grows {r r' l} :
    rename_grows r r' -> lang_bound r l ->
    unrename_lang r' l = unrename_lang r l.
  Proof.
    intros Hg.
    induction l as [|p l IH]; cbn; auto.
    intros Hpl.
    destruct Hpl as [Hhead Hl].
    destruct Hhead as [Hh Hrh].
    f_equal.
    - f_equal; [apply (of_p_eq Hg Hh) | apply (unrename_rule_grows Hg Hrh)].
    - apply IH; auto.
  Qed.

  (** ** Correctness of [to_p]. *)

  Lemma to_p_correct {r v p r'} :
    renaming_ok r ->
    to_p v r = (p, r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ map.get r'.(p_to_v) p = Some v.
  Proof.
    intros Hr.
    unfold to_p.
    destruct (named_list_lookup_err r.(v_to_p) v) eqn:Hlook.
    - intros Heq; inversion Heq; subst.
      split; [exact Hr|]. split; [apply rename_grows_refl|].
      apply (ren_v_to_p_in_p_to_v Hr).
      eapply named_list_lookup_err_in.
      symmetry; exact Hlook.
    - unfold alloc.
      intros Heq; inversion Heq; subst.
      symmetry in Hlook.
      apply named_list_lookup_none_iff in Hlook.
      destruct Hr as [Hfresh Hvp Hpv Hbnd].
      assert (Hnf : map.get r.(p_to_v) r.(next_id) = None).
      { destruct (map.get r.(p_to_v) r.(next_id)) eqn:Heq2; auto.
        apply Hpv in Heq2; apply Hbnd in Heq2.
        apply Pos.lt_irrefl in Heq2; contradiction. }
      split; [|split].
      + (* renaming_ok of the new state *)
        constructor; cbn.
        * split; auto.
        * intros v0 p0 Hor.
          destruct Hor as [Heq2 | Hin].
          { inversion Heq2; subst.
            unfold map.get, map.put; cbn.
            apply PTree.gss. }
          { specialize (Hvp _ _ Hin).
            assert (p0 <> r.(next_id)) as Hne.
            { intro; subst.
              apply Hbnd in Hin.
              apply Pos.lt_irrefl in Hin; contradiction. }
            unfold map.get, map.put in *; cbn in *.
            rewrite PTree.gso by auto; assumption. }
        * intros v0 p0 Hget.
          unfold map.get, map.put in Hget; cbn in Hget.
          destruct (Pos.eq_dec p0 r.(next_id)) as [Heq2 | Hne].
          { subst.
            rewrite PTree.gss in Hget.
            inversion Hget; subst; left; reflexivity. }
          { rewrite PTree.gso in Hget by auto.
            right; apply Hpv; auto. }
        * intros v0 p0 [Heq2 | Hin].
          { inversion Heq2; subst.
            rewrite Pos.add_1_r.
            apply Pos.lt_succ_diag_r. }
          { apply Hbnd in Hin.
            rewrite Pos.add_1_r.
            apply Pos.lt_trans with r.(next_id); auto.
            apply Pos.lt_succ_diag_r. }
      + (* rename_grows *)
        intros p0 v0 Hget.
        assert (p0 <> r.(next_id)) as Hne.
        { intro; subst.
          rewrite Hnf in Hget; congruence. }
        unfold map.get, map.put in *; cbn in *.
        rewrite PTree.gso by auto; assumption.
      + (* output get gives back v *)
        unfold map.get, map.put; cbn.
        apply PTree.gss.
  Qed.

  Corollary to_p_of_p {r v p r'} :
    renaming_ok r ->
    to_p v r = (p, r') -> of_p r' p = v.
  Proof.
    intros Hr Hto.
    apply (to_p_correct Hr) in Hto.
    destruct Hto as (_ & _ & Hget).
    apply (of_p_lookup Hget).
  Qed.

  Corollary to_p_pbound {r v p r'} :
    renaming_ok r ->
    to_p v r = (p, r') -> pbound r' p.
  Proof.
    intros Hr Hto.
    apply (to_p_correct Hr) in Hto.
    destruct Hto as (_ & _ & Hget).
    exists v; assumption.
  Qed.

  (** ** Correctness of [list_Mmap to_p]. *)

  Lemma list_Mmap_to_p_correct {args r ps r'} :
    renaming_ok r ->
    list_Mmap to_p args r = (ps, r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ all (pbound r') ps
    /\ map (of_p r') ps = args.
  Proof.
    revert r ps r'.
    induction args as [|a args IH]; intros r ps r' Hr; cbn.
    - intros Heq; inversion Heq; subst.
      split; [exact Hr|]. split; [apply rename_grows_refl|].
      split; [exact I | reflexivity].
    - destruct (to_p a r) as [p1 r1] eqn:Hr1.
      destruct (list_Mmap to_p args r1) as [ps1 r2] eqn:Hr2.
      intros Heq; inversion Heq; clear Heq; subst ps r'.
      pose proof (to_p_correct Hr Hr1) as (Hr1ok & Hg1 & Hget).
      specialize (IH r1 ps1 r2 Hr1ok Hr2) as (Hr2ok & Hg2 & Hbnd & Hmap).
      split; [exact Hr2ok|].
      split; [apply (rename_grows_trans Hg1 Hg2)|].
      split.
      + cbn; split; auto.
        exists a; apply Hg2; assumption.
      + cbn; f_equal; auto.
        apply (of_p_grows Hg2 Hget).
  Qed.

  (** ** Correctness of [rename_term]. *)

  Lemma rename_term_correct (e : term)
    {r : renaming} {e' : pterm} {r' : renaming} :
    renaming_ok r ->
    rename_term e r = (e', r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ term_bound r' e'
    /\ unrename_term r' e' = e.
  Proof.
    revert r e' r'.
    induction e using term_ind; intros r e' r' Hr; cbn.
    - (* var n *)
      destruct (to_p n r) as [p r1] eqn:Hto.
      intros Heq; inversion Heq; subst.
      pose proof (to_p_correct Hr Hto) as (Hr1ok & Hg & Hget).
      split; [exact Hr1ok|]. split; [exact Hg|].
      split.
      + cbn; exists n; assumption.
      + cbn; f_equal; apply (of_p_lookup Hget).
    - (* con n l *)
      (* Inner list lemma proved by induction on l using H. *)
      assert (Hlist : forall r0 s r0',
                 renaming_ok r0 ->
                 list_Mmap rename_term l r0 = (s, r0') ->
                 renaming_ok r0'
                 /\ rename_grows r0 r0'
                 /\ all (term_bound r0') s
                 /\ map (unrename_term r0') s = l).
      { clear r e' r' Hr.
        induction l as [|a l IHl]; intros r0 s r0' Hr0; cbn.
        - intros Heq; inversion Heq; subst.
          split; [exact Hr0|]. split; [apply rename_grows_refl|].
          split; [exact I | reflexivity].
        - destruct H as [Ha Hrest].
          destruct (rename_term a r0) as [b r1] eqn:Hr1.
          destruct (list_Mmap rename_term l r1) as [bs r2] eqn:Hr2.
          intros Heq; inversion Heq; clear Heq; subst s r0'.
          specialize (Ha r0 b r1 Hr0 Hr1) as (Hr1ok & Hg1 & Hb1 & Hu1).
          specialize (IHl Hrest r1 bs r2 Hr1ok Hr2) as
              (Hr2ok & Hg2 & Hb2 & Hmap).
          split; [exact Hr2ok|].
          split; [apply (rename_grows_trans Hg1 Hg2)|].
          split.
          + cbn; split; auto.
            apply (term_bound_grows Hg2 Hb1).
          + cbn; f_equal; auto.
            rewrite (unrename_term_grows Hg2 Hb1); exact Hu1. }
      destruct (list_Mmap rename_term l r) as [sp r1] eqn:Hr1.
      destruct (to_p n r1) as [p r2] eqn:Hto.
      intros Heq; inversion Heq; clear Heq; subst e' r'.
      specialize (Hlist r sp r1 Hr Hr1) as (Hr1ok & Hg1 & Hbs & Hmap).
      pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg2 & Hget).
      split; [exact Hr2ok|].
      split; [apply (rename_grows_trans Hg1 Hg2)|].
      split.
      + cbn; split.
        * exists n; exact Hget.
        * eapply all_grows;
            [intros x; apply (term_bound_grows Hg2)| exact Hbs].
      + cbn; f_equal.
        * apply (of_p_lookup Hget).
        * rewrite <- Hmap.
          clear -Hbs Hg2.
          induction sp as [|b bs IH']; cbn; auto.
          destruct Hbs as [Hb Hbs].
          f_equal; auto.
          apply (unrename_term_grows Hg2 Hb).
  Qed.

  (** ** Correctness of [list_Mmap rename_term]. *)

  Lemma list_Mmap_rename_term_correct l :
    forall r s r',
      renaming_ok r ->
      list_Mmap rename_term l r = (s, r') ->
      renaming_ok r'
      /\ rename_grows r r'
      /\ all (term_bound r') s
      /\ map (unrename_term r') s = l.
  Proof.
    induction l as [|a l IH]; intros r s r' Hr; cbn.
    - intros Heq; inversion Heq; subst.
      split; [exact Hr|]. split; [apply rename_grows_refl|].
      split; [exact I | reflexivity].
    - destruct (rename_term a r) as [b r1] eqn:Hr1.
      destruct (list_Mmap rename_term l r1) as [bs r2] eqn:Hr2.
      intros Heq; inversion Heq; clear Heq; subst s r'.
      pose proof (rename_term_correct a Hr Hr1) as (Hr1ok & Hg1 & Hb1 & Hu1).
      specialize (IH r1 bs r2 Hr1ok Hr2) as (Hr2ok & Hg2 & Hbs & Hmap).
      split; [exact Hr2ok|].
      split; [apply (rename_grows_trans Hg1 Hg2)|].
      split.
      + cbn; split; auto.
        apply (term_bound_grows Hg2 Hb1).
      + cbn; f_equal; auto.
        rewrite (unrename_term_grows Hg2 Hb1); exact Hu1.
  Qed.

  (** ** Correctness of [rename_sort]. *)

  Lemma rename_sort_correct (ts : sort)
    {r : renaming} {ts' : psort} {r' : renaming} :
    renaming_ok r ->
    rename_sort ts r = (ts', r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ sort_bound r' ts'
    /\ unrename_sort r' ts' = ts.
  Proof.
    destruct ts as [n s]; cbn.
    intros Hr.
    destruct (list_Mmap rename_term s r) as [s1 r1] eqn:Hr1.
    destruct (to_p n r1) as [p r2] eqn:Hto.
    intros Heq; inversion Heq; clear Heq; subst ts' r'.
    pose proof (list_Mmap_rename_term_correct s Hr Hr1)
      as (Hr1ok & Hg1 & Hbs & Hmap).
    pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg2 & Hget).
    split; [exact Hr2ok|].
    split; [apply (rename_grows_trans Hg1 Hg2)|].
    split.
    - cbn; split.
      + exists n; exact Hget.
      + eapply all_grows;
          [intros x; apply (term_bound_grows Hg2)| exact Hbs].
    - cbn; f_equal.
      + apply (of_p_lookup Hget).
      + rewrite <- Hmap.
        clear -Hbs Hg2.
        induction s1 as [|b bs IH]; cbn; auto.
        destruct Hbs as [Hb Hbs].
        f_equal; auto.
        apply (unrename_term_grows Hg2 Hb).
  Qed.

  (** ** Correctness of [rename_ctx]. *)

  Lemma rename_ctx_correct (c : ctx)
    {r : renaming} {c' : pctx} {r' : renaming} :
    renaming_ok r ->
    rename_ctx c r = (c', r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ ctx_bound r' c'
    /\ unrename_ctx r' c' = c.
  Proof.
    revert r c' r'.
    induction c as [|p c IH]; intros r c' r' Hr; unfold rename_ctx; cbn.
    - intros Heq; inversion Heq; clear Heq; subst c' r'.
      split; [exact Hr|]. split; [apply rename_grows_refl|].
      split; [exact I | reflexivity].
    - destruct p as [x ts].
      destruct (rename_sort ts r) as [ts1 r1] eqn:Hr1.
      destruct (to_p x r1) as [x1 r2] eqn:Hto.
      destruct (rename_ctx c r2) as [c1 r3] eqn:Hr3.
      pose proof Hr3 as Hr3'.
      unfold rename_ctx in Hr3'; cbn in Hr3'.
      intros Heq.
      rewrite Hr3' in Heq.
      inversion Heq; clear Heq; subst c' r'.
      pose proof (rename_sort_correct ts Hr Hr1)
        as (Hr1ok & Hg1 & Hbts & Huts).
      pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg2 & Hget).
      specialize (IH r2 c1 r3 Hr2ok Hr3) as (Hr3ok & Hg3 & Hbc & Huc).
      split; [exact Hr3ok|].
      split; [apply (rename_grows_trans Hg1
                       (rename_grows_trans Hg2 Hg3))|].
      split.
      + cbn; split; [split|].
        * exists x; apply Hg3; assumption.
        * apply (sort_bound_grows
                   (rename_grows_trans Hg2 Hg3) Hbts).
        * exact Hbc.
      + cbn; f_equal.
        * f_equal.
          { rewrite (of_p_grows Hg3 Hget); reflexivity. }
          { rewrite (unrename_sort_grows
                       (rename_grows_trans Hg2 Hg3) Hbts).
            exact Huts. }
        * exact Huc.
  Qed.

  (** ** Correctness of [rename_rule]. *)

  Lemma rename_rule_correct (rr : rule)
    {r : renaming} {rr' : prule} {r' : renaming} :
    renaming_ok r ->
    rename_rule rr r = (rr', r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ rule_bound r' rr'
    /\ unrename_rule r' rr' = rr.
  Proof.
    intros Hr.
    destruct rr as [c args | c args ts | c ts1 ts2 | c e1 e2 ts]; cbn.
    - (* sort_rule *)
      destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
      destruct (list_Mmap to_p args r1) as [args1 r2] eqn:Hra.
      intros Heq; inversion Heq; clear Heq; subst rr' r'.
      pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & Hg1 & Hbc & Huc).
      pose proof (list_Mmap_to_p_correct Hr1ok Hra)
        as (Hr2ok & Hg2 & Hba & Hua).
      split; [exact Hr2ok|].
      split; [apply (rename_grows_trans Hg1 Hg2)|].
      split.
      + cbn; split.
        * apply (ctx_bound_grows Hg2 Hbc).
        * exact Hba.
      + cbn; f_equal.
        * rewrite (unrename_ctx_grows Hg2 Hbc); exact Huc.
        * exact Hua.
    - (* term_rule *)
      destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
      destruct (list_Mmap to_p args r1) as [args1 r2] eqn:Hra.
      destruct (rename_sort ts r2) as [ts1' r3] eqn:Hrt.
      intros Heq; inversion Heq; clear Heq; subst rr' r'.
      pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & Hg1 & Hbc & Huc).
      pose proof (list_Mmap_to_p_correct Hr1ok Hra)
        as (Hr2ok & Hg2 & Hba & Hua).
      pose proof (rename_sort_correct ts Hr2ok Hrt)
        as (Hr3ok & Hg3 & Hbt & Hut).
      split; [exact Hr3ok|].
      split; [apply (rename_grows_trans Hg1
                       (rename_grows_trans Hg2 Hg3))|].
      split.
      + cbn; split; [|split].
        * apply (ctx_bound_grows
                   (rename_grows_trans Hg2 Hg3) Hbc).
        * apply (all_pbound_grows Hg3 Hba).
        * exact Hbt.
      + cbn; f_equal.
        * rewrite (unrename_ctx_grows
                     (rename_grows_trans Hg2 Hg3) Hbc); exact Huc.
        * rewrite (map_of_p_eq Hg3 Hba); exact Hua.
        * exact Hut.
    - (* sort_eq_rule *)
      destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
      destruct (rename_sort ts1 r1) as [ts1' r2] eqn:Hr2.
      destruct (rename_sort ts2 r2) as [ts2' r3] eqn:Hr3.
      intros Heq; inversion Heq; clear Heq; subst rr' r'.
      pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & Hg1 & Hbc & Huc).
      pose proof (rename_sort_correct ts1 Hr1ok Hr2)
        as (Hr2ok & Hg2 & Hbt1 & Hut1).
      pose proof (rename_sort_correct ts2 Hr2ok Hr3)
        as (Hr3ok & Hg3 & Hbt2 & Hut2).
      split; [exact Hr3ok|].
      split; [apply (rename_grows_trans Hg1
                       (rename_grows_trans Hg2 Hg3))|].
      split.
      + cbn; split; [|split].
        * apply (ctx_bound_grows
                   (rename_grows_trans Hg2 Hg3) Hbc).
        * apply (sort_bound_grows Hg3 Hbt1).
        * exact Hbt2.
      + cbn; f_equal.
        * rewrite (unrename_ctx_grows
                     (rename_grows_trans Hg2 Hg3) Hbc); exact Huc.
        * rewrite (unrename_sort_grows Hg3 Hbt1); exact Hut1.
        * exact Hut2.
    - (* term_eq_rule *)
      destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
      destruct (rename_term e1 r1) as [e1' r2] eqn:Hre1.
      destruct (rename_term e2 r2) as [e2' r3] eqn:Hre2.
      destruct (rename_sort ts r3) as [ts'' r4] eqn:Hrt.
      intros Heq; inversion Heq; clear Heq; subst rr' r'.
      pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & Hg1 & Hbc & Huc).
      pose proof (rename_term_correct e1 Hr1ok Hre1)
        as (Hr2ok & Hg2 & Hbe1 & Hue1).
      pose proof (rename_term_correct e2 Hr2ok Hre2)
        as (Hr3ok & Hg3 & Hbe2 & Hue2).
      pose proof (rename_sort_correct ts Hr3ok Hrt)
        as (Hr4ok & Hg4 & Hbt & Hut).
      pose (Hg12 := rename_grows_trans Hg1 Hg2).
      pose (Hg23 := rename_grows_trans Hg2 Hg3).
      pose (Hg34 := rename_grows_trans Hg3 Hg4).
      pose (Hg13 := rename_grows_trans Hg12 Hg3).
      pose (Hg14 := rename_grows_trans Hg13 Hg4).
      pose (Hg24 := rename_grows_trans Hg23 Hg4).
      split; [exact Hr4ok|].
      split; [exact Hg14|].
      split.
      + cbn.
        split.
        { apply (ctx_bound_grows
                   (rename_grows_trans Hg23 Hg4) Hbc). }
        split.
        { apply (term_bound_grows
                   (rename_grows_trans Hg3 Hg4) Hbe1). }
        split.
        { apply (term_bound_grows Hg4 Hbe2). }
        exact Hbt.
      + cbn; f_equal.
        * rewrite (unrename_ctx_grows
                     (rename_grows_trans Hg23 Hg4) Hbc); exact Huc.
        * rewrite (unrename_term_grows
                     (rename_grows_trans Hg3 Hg4) Hbe1); exact Hue1.
        * rewrite (unrename_term_grows Hg4 Hbe2); exact Hue2.
        * exact Hut.
  Qed.

  (** ** Correctness of [rename_lang]. *)

  Lemma rename_lang_correct (l : lang)
    {r : renaming} {l' : plang} {r' : renaming} :
    renaming_ok r ->
    rename_lang l r = (l', r') ->
    renaming_ok r'
    /\ rename_grows r r'
    /\ lang_bound r' l'
    /\ unrename_lang r' l' = l.
  Proof.
    revert r l' r'.
    induction l as [|p l IH]; intros r l' r' Hr; unfold rename_lang; cbn.
    - intros Heq; inversion Heq; clear Heq; subst l' r'.
      split; [exact Hr|]. split; [apply rename_grows_refl|].
      split; [exact I | reflexivity].
    - destruct p as [x rr].
      destruct (rename_rule rr r) as [rr1 r1] eqn:Hrr.
      destruct (to_p x r1) as [x1 r2] eqn:Hto.
      destruct (rename_lang l r2) as [l1 r3] eqn:Hrl.
      pose proof Hrl as Hrl'.
      unfold rename_lang in Hrl'; cbn in Hrl'.
      intros Heq; rewrite Hrl' in Heq.
      inversion Heq; clear Heq; subst l' r'.
      pose proof (rename_rule_correct rr Hr Hrr)
        as (Hr1ok & Hg1 & Hbrr & Hurr).
      pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg2 & Hget).
      specialize (IH r2 l1 r3 Hr2ok Hrl) as (Hr3ok & Hg3 & Hbl & Hul).
      pose (Hg12 := rename_grows_trans Hg1 Hg2).
      pose (Hg23 := rename_grows_trans Hg2 Hg3).
      pose (Hg13 := rename_grows_trans Hg12 Hg3).
      split; [exact Hr3ok|].
      split; [exact Hg13|].
      split.
      + cbn; split; [split|].
        * exists x; apply Hg3; assumption.
        * apply (rule_bound_grows Hg23 Hbrr).
        * exact Hbl.
      + cbn; f_equal.
        * f_equal.
          { apply (of_p_grows Hg3 Hget). }
          { rewrite (unrename_rule_grows Hg23 Hbrr); exact Hurr. }
        * exact Hul.
  Qed.

  (** ** Top-level bijection corollaries.

      For each [rename_X X r = (X', r')], [unrename_X r' X' = X]. *)

  Corollary rename_term_bijection e r e' r' :
    renaming_ok r ->
    rename_term e r = (e', r') ->
    unrename_term r' e' = e.
  Proof.
    intros Hr Heq.
    apply (rename_term_correct e Hr) in Heq.
    destruct Heq as (_ & _ & _ & ?); assumption.
  Qed.

  Corollary rename_sort_bijection ts r ts' r' :
    renaming_ok r ->
    rename_sort ts r = (ts', r') ->
    unrename_sort r' ts' = ts.
  Proof.
    intros Hr Heq.
    apply (rename_sort_correct ts Hr) in Heq.
    destruct Heq as (_ & _ & _ & ?); assumption.
  Qed.

  Corollary rename_ctx_bijection c r c' r' :
    renaming_ok r ->
    rename_ctx c r = (c', r') ->
    unrename_ctx r' c' = c.
  Proof.
    intros Hr Heq.
    apply (rename_ctx_correct c Hr) in Heq.
    destruct Heq as (_ & _ & _ & ?); assumption.
  Qed.

  Corollary rename_rule_bijection rr r rr' r' :
    renaming_ok r ->
    rename_rule rr r = (rr', r') ->
    unrename_rule r' rr' = rr.
  Proof.
    intros Hr Heq.
    apply (rename_rule_correct rr Hr) in Heq.
    destruct Heq as (_ & _ & _ & ?); assumption.
  Qed.

  Corollary rename_lang_bijection l r l' r' :
    renaming_ok r ->
    rename_lang l r = (l', r') ->
    unrename_lang r' l' = l.
  Proof.
    intros Hr Heq.
    apply (rename_lang_correct l Hr) in Heq.
    destruct Heq as (_ & _ & _ & ?); assumption.
  Qed.

  (** ** Inverse direction: [rename] applied to an already-unrenamed
         value is the identity on the state. *)

  Lemma to_p_of_p_inverse {r : renaming} {p : positive} :
    renaming_ok r ->
    pbound r p ->
    to_p (of_p r p) r = (p, r).
  Proof.
    intros Hr [v Hget].
    rewrite (of_p_lookup Hget).
    unfold to_p.
    assert (Some p = named_list_lookup_err r.(v_to_p) v) as Hlook.
    { destruct Hr as [Hfresh _ Hpv _].
      apply Hpv in Hget.
      apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ Hfresh)).
      exact Hget. }
    rewrite <- Hlook; reflexivity.
  Qed.

  Lemma rename_term_inverse (e : pterm) {r : renaming} :
    renaming_ok r ->
    term_bound r e ->
    rename_term (unrename_term r e) r = (e, r).
  Proof.
    revert r.
    induction e using term_ind; intros r Hr; cbn.
    - intros Hb.
      rewrite (to_p_of_p_inverse Hr Hb); reflexivity.
    - intros HconBound.
      destruct HconBound as [Hn Hl].
      assert (Hlist : list_Mmap rename_term (map (unrename_term r) l) r
                      = (l, r)).
      { clear Hn. induction l as [|a l IHl]; cbn; auto.
        destruct H as [Ha Hrest]; destruct Hl as [Hb Hbl].
        rewrite (Ha r Hr Hb).
        rewrite (IHl Hrest Hbl); reflexivity. }
      rewrite Hlist.
      rewrite (to_p_of_p_inverse Hr Hn); reflexivity.
  Qed.

  Lemma rename_sort_inverse (ts : psort) {r : renaming} :
    renaming_ok r ->
    sort_bound r ts ->
    rename_sort (unrename_sort r ts) r = (ts, r).
  Proof.
    intros Hr.
    destruct ts as [n s]; cbn.
    intros HsortBound.
    destruct HsortBound as [Hn Hs].
    assert (Hlist : list_Mmap rename_term (map (unrename_term r) s) r
                    = (s, r)).
    { induction s as [|a s IH]; cbn; auto.
      destruct Hs as [Hb Hbs].
      rewrite (rename_term_inverse a Hr Hb).
      rewrite (IH Hbs); reflexivity. }
    rewrite Hlist.
    rewrite (to_p_of_p_inverse Hr Hn); reflexivity.
  Qed.

  (** ** Bridge to [Theory.Renaming]

     The stateful rename operations agree with the function-based
     [Theory.Renaming.rename_*] for any function [f : V -> positive]
     that matches the final state's [v_to_p] mapping.  Combined with
     [Theory.Renaming.rename_mono] / [rename_lang_mono], this yields
     preservation of all the core judgments. *)

  Section Bridge.

    Context (f : V -> positive).

    (* [f] agrees with the renaming on every entry of [r.(v_to_p)]. *)
    Definition f_matches (r : renaming) : Prop :=
      forall v p, In (v, p) r.(v_to_p) -> f v = p.

    Lemma f_matches_grows r r' :
      renaming_ok r ->
      renaming_ok r' ->
      rename_grows r r' ->
      f_matches r' ->
      f_matches r.
    Proof.
      intros Hr Hr' Hg Hfm v p Hin.
      apply Hfm.
      apply (ren_p_to_v_in_v_to_p Hr').
      apply Hg.
      apply (ren_v_to_p_in_p_to_v Hr).
      assumption.
    Qed.

    Lemma to_p_via_f {r v p r'} :
      renaming_ok r ->
      to_p v r = (p, r') ->
      f_matches r' ->
      f v = p.
    Proof.
      intros Hr Hto Hfm.
      pose proof (to_p_correct Hr Hto) as (Hr' & _ & Hget).
      apply Hfm.
      apply (ren_p_to_v_in_v_to_p Hr'); exact Hget.
    Qed.

    Lemma rename_term_via_f (e : term) :
      forall r ep r',
        renaming_ok r ->
        rename_term e r = (ep, r') ->
        f_matches r' ->
        ep = Renaming.rename f e.
    Proof.
      induction e using term_ind; intros r ep r' Hr Hre Hfm; cbn in *.
      - destruct (to_p n r) as [p1 r1] eqn:Hto.
        inversion Hre; clear Hre; subst.
        f_equal; symmetry; eapply to_p_via_f; eauto.
      - destruct (list_Mmap rename_term l r) as [sp r1] eqn:Hr1.
        destruct (to_p n r1) as [p1 r2] eqn:Hto.
        inversion Hre; clear Hre; subst ep r'.
        (* From the inner list_Mmap + to_p, derive grow facts. *)
        assert (Hlist :
                  forall r0 sp0 r0',
                    renaming_ok r0 ->
                    list_Mmap rename_term l r0 = (sp0, r0') ->
                    f_matches r0' ->
                    sp0 = map (Renaming.rename f) l).
        { clear r Hr Hr1 Hto Hfm sp r1 p1 r2 n.
          induction l as [|a l' IHl']; intros r0 sp0 r0' Hr0 Hl Hfm0;
            cbn in *.
          - inversion Hl; reflexivity.
          - destruct H as [Ha Hrest].
            destruct (rename_term a r0) as [b r0''] eqn:Hra.
            destruct (list_Mmap rename_term l' r0'') as [bs r0'''] eqn:Hrl.
            inversion Hl; clear Hl; subst sp0 r0'.
            pose proof (rename_term_correct a Hr0 Hra) as
              (Hr0''ok & Hg0 & _ & _).
            pose proof (list_Mmap_rename_term_correct l' Hr0''ok Hrl) as
              (Hr0'''ok & Hg0' & _ & _).
            assert (Hfm0'' : f_matches r0'').
            { eapply (f_matches_grows Hr0''ok Hr0'''ok Hg0' Hfm0). }
            f_equal.
            + eapply (Ha r0 b r0'' Hr0 Hra Hfm0'').
            + eapply (IHl' Hrest r0''); eauto. }
        pose proof (list_Mmap_rename_term_correct l Hr Hr1) as
          (Hr1ok & _ & _ & _).
        pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg & _).
        assert (Hfm1 : f_matches r1).
        { eapply (f_matches_grows Hr1ok Hr2ok Hg Hfm). }
        f_equal.
        + symmetry; eapply (to_p_via_f Hr1ok Hto Hfm).
        + eapply (Hlist r sp r1 Hr Hr1 Hfm1).
    Qed.

    Lemma list_Mmap_rename_term_via_f l :
      forall r sp r',
        renaming_ok r ->
        list_Mmap rename_term l r = (sp, r') ->
        f_matches r' ->
        sp = map (Renaming.rename f) l.
    Proof.
      induction l as [|a l IH]; intros r sp r' Hr Hl Hfm; cbn in *.
      - inversion Hl; reflexivity.
      - destruct (rename_term a r) as [b r1] eqn:Hra.
        destruct (list_Mmap rename_term l r1) as [bs r2] eqn:Hrl.
        inversion Hl; clear Hl; subst sp r'.
        pose proof (rename_term_correct a Hr Hra) as (Hr1ok & _ & _ & _).
        pose proof (list_Mmap_rename_term_correct l Hr1ok Hrl) as
          (Hr2ok & Hg & _ & _).
        assert (Hfm1 : f_matches r1).
        { eapply (f_matches_grows Hr1ok Hr2ok Hg Hfm). }
        f_equal.
        + eapply (rename_term_via_f a Hr Hra Hfm1).
        + eapply (IH r1 bs r2 Hr1ok Hrl Hfm).
    Qed.

    Lemma list_Mmap_to_p_via_f args :
      forall r ps r',
        renaming_ok r ->
        list_Mmap to_p args r = (ps, r') ->
        f_matches r' ->
        ps = map f args.
    Proof.
      induction args as [|a args IH]; intros r ps r' Hr Hl Hfm; cbn in *.
      - inversion Hl; reflexivity.
      - destruct (to_p a r) as [p1 r1] eqn:Hto.
        destruct (list_Mmap to_p args r1) as [ps1 r2] eqn:Hrl.
        inversion Hl; clear Hl; subst ps r'.
        pose proof (to_p_correct Hr Hto) as (Hr1ok & _ & _).
        pose proof (list_Mmap_to_p_correct Hr1ok Hrl) as
          (Hr2ok & Hg & _ & _).
        assert (Hfm1 : f_matches r1).
        { eapply (f_matches_grows Hr1ok Hr2ok Hg Hfm). }
        f_equal.
        + symmetry; eapply (to_p_via_f Hr Hto Hfm1).
        + eapply (IH r1 ps1 r2 Hr1ok Hrl Hfm).
    Qed.

    Lemma rename_sort_via_f (ts : sort) r tsp r' :
      renaming_ok r ->
      rename_sort ts r = (tsp, r') ->
      f_matches r' ->
      tsp = Renaming.rename_sort f ts.
    Proof.
      destruct ts as [n s]; cbn.
      intros Hr.
      destruct (list_Mmap rename_term s r) as [sp r1] eqn:Hr1.
      destruct (to_p n r1) as [p1 r2] eqn:Hto.
      intros Hre Hfm.
      inversion Hre; clear Hre; subst tsp r'.
      pose proof (list_Mmap_rename_term_correct s Hr Hr1) as
        (Hr1ok & _ & _ & _).
      pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg & _).
      assert (Hfm1 : f_matches r1).
      { eapply (f_matches_grows Hr1ok Hr2ok Hg Hfm). }
      f_equal.
      - symmetry; eapply (to_p_via_f Hr1ok Hto Hfm).
      - eapply (list_Mmap_rename_term_via_f s Hr Hr1 Hfm1).
    Qed.

    Lemma rename_ctx_via_f (c : ctx) :
      forall r cp r',
        renaming_ok r ->
        rename_ctx c r = (cp, r') ->
        f_matches r' ->
        cp = Renaming.rename_ctx f c.
    Proof.
      induction c as [|[x ts] c IH]; intros r cp r' Hr Hrc Hfm;
        unfold rename_ctx in Hrc; cbn in *.
      - inversion Hrc; reflexivity.
      - destruct (rename_sort ts r) as [ts1 r1] eqn:Hr1.
        destruct (to_p x r1) as [x1 r2] eqn:Hto.
        destruct (rename_ctx c r2) as [c1 r3] eqn:Hrc'.
        pose proof Hrc' as Hrc''.
        unfold rename_ctx in Hrc''; cbn in Hrc''.
        rewrite Hrc'' in Hrc.
        inversion Hrc; clear Hrc; subst cp r'.
        pose proof (rename_sort_correct ts Hr Hr1) as
          (Hr1ok & Hg01 & _ & _).
        pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg12 & _).
        pose proof (rename_ctx_correct c Hr2ok Hrc') as
          (Hr3ok & Hg23 & _ & _).
        assert (Hfm2 : f_matches r2).
        { eapply (f_matches_grows Hr2ok Hr3ok Hg23 Hfm). }
        assert (Hfm1 : f_matches r1).
        { eapply (f_matches_grows Hr1ok Hr2ok Hg12 Hfm2). }
        f_equal.
        + f_equal.
          * symmetry; eapply (to_p_via_f Hr1ok Hto Hfm2).
          * eapply (rename_sort_via_f ts Hr Hr1 Hfm1).
        + eapply (IH r2 c1 r3 Hr2ok Hrc' Hfm).
    Qed.

    Lemma rename_rule_via_f (rr : rule) r rrp r' :
      renaming_ok r ->
      rename_rule rr r = (rrp, r') ->
      f_matches r' ->
      rrp = Renaming.rename_rule f rr.
    Proof.
      intros Hr.
      destruct rr as [c args | c args ts | c ts1 ts2 | c e1 e2 ts]; cbn.
      - destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
        destruct (list_Mmap to_p args r1) as [args1 r2] eqn:Hra.
        intros Hre Hfm; inversion Hre; clear Hre; subst rrp r'.
        pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & _ & _ & _).
        pose proof (list_Mmap_to_p_correct Hr1ok Hra) as
          (Hr2ok & Hg12 & _ & _).
        assert (Hfm1 : f_matches r1) by
          (eapply (f_matches_grows Hr1ok Hr2ok Hg12 Hfm)).
        f_equal.
        + eapply (rename_ctx_via_f c Hr Hrc Hfm1).
        + eapply (list_Mmap_to_p_via_f args Hr1ok Hra Hfm).
      - destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
        destruct (list_Mmap to_p args r1) as [args1 r2] eqn:Hra.
        destruct (rename_sort ts r2) as [ts1 r3] eqn:Hrt.
        intros Hre Hfm; inversion Hre; clear Hre; subst rrp r'.
        pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & _ & _ & _).
        pose proof (list_Mmap_to_p_correct Hr1ok Hra) as
          (Hr2ok & Hg12 & _ & _).
        pose proof (rename_sort_correct ts Hr2ok Hrt) as
          (Hr3ok & Hg23 & _ & _).
        assert (Hfm2 : f_matches r2) by
          (eapply (f_matches_grows Hr2ok Hr3ok Hg23 Hfm)).
        assert (Hfm1 : f_matches r1) by
          (eapply (f_matches_grows Hr1ok Hr2ok Hg12 Hfm2)).
        f_equal.
        + eapply (rename_ctx_via_f c Hr Hrc Hfm1).
        + eapply (list_Mmap_to_p_via_f args Hr1ok Hra Hfm2).
        + eapply (rename_sort_via_f ts Hr2ok Hrt Hfm).
      - destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
        destruct (rename_sort ts1 r1) as [tp1 r2] eqn:Hr2.
        destruct (rename_sort ts2 r2) as [tp2 r3] eqn:Hr3.
        intros Hre Hfm; inversion Hre; clear Hre; subst rrp r'.
        pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & _ & _ & _).
        pose proof (rename_sort_correct ts1 Hr1ok Hr2) as
          (Hr2ok & Hg12 & _ & _).
        pose proof (rename_sort_correct ts2 Hr2ok Hr3) as
          (Hr3ok & Hg23 & _ & _).
        assert (Hfm2 : f_matches r2) by
          (eapply (f_matches_grows Hr2ok Hr3ok Hg23 Hfm)).
        assert (Hfm1 : f_matches r1) by
          (eapply (f_matches_grows Hr1ok Hr2ok Hg12 Hfm2)).
        f_equal.
        + eapply (rename_ctx_via_f c Hr Hrc Hfm1).
        + eapply (rename_sort_via_f ts1 Hr1ok Hr2 Hfm2).
        + eapply (rename_sort_via_f ts2 Hr2ok Hr3 Hfm).
      - destruct (rename_ctx c r) as [c1 r1] eqn:Hrc.
        destruct (rename_term e1 r1) as [e1p r2] eqn:Hre1.
        destruct (rename_term e2 r2) as [e2p r3] eqn:Hre2.
        destruct (rename_sort ts r3) as [tsp r4] eqn:Hrt.
        intros Hre Hfm; inversion Hre; clear Hre; subst rrp r'.
        pose proof (rename_ctx_correct c Hr Hrc) as (Hr1ok & _ & _ & _).
        pose proof (rename_term_correct e1 Hr1ok Hre1) as
          (Hr2ok & Hg12 & _ & _).
        pose proof (rename_term_correct e2 Hr2ok Hre2) as
          (Hr3ok & Hg23 & _ & _).
        pose proof (rename_sort_correct ts Hr3ok Hrt) as
          (Hr4ok & Hg34 & _ & _).
        assert (Hfm3 : f_matches r3) by
          (eapply (f_matches_grows Hr3ok Hr4ok Hg34 Hfm)).
        assert (Hfm2 : f_matches r2) by
          (eapply (f_matches_grows Hr2ok Hr3ok Hg23 Hfm3)).
        assert (Hfm1 : f_matches r1) by
          (eapply (f_matches_grows Hr1ok Hr2ok Hg12 Hfm2)).
        f_equal.
        + eapply (rename_ctx_via_f c Hr Hrc Hfm1).
        + eapply (rename_term_via_f e1 Hr1ok Hre1 Hfm2).
        + eapply (rename_term_via_f e2 Hr2ok Hre2 Hfm3).
        + eapply (rename_sort_via_f ts Hr3ok Hrt Hfm).
    Qed.

    Lemma rename_lang_via_f (l : lang) :
      forall r lp r',
        renaming_ok r ->
        rename_lang l r = (lp, r') ->
        f_matches r' ->
        lp = Renaming.rename_lang f l.
    Proof.
      induction l as [|[x rr] l IH]; intros r lp r' Hr Hrl Hfm;
        unfold rename_lang in Hrl; cbn in *.
      - inversion Hrl; reflexivity.
      - destruct (rename_rule rr r) as [rr1 r1] eqn:Hrr.
        destruct (to_p x r1) as [x1 r2] eqn:Hto.
        destruct (rename_lang l r2) as [l1 r3] eqn:Hrl'.
        pose proof Hrl' as Hrl''.
        unfold rename_lang in Hrl''; cbn in Hrl''.
        rewrite Hrl'' in Hrl.
        inversion Hrl; clear Hrl; subst lp r'.
        pose proof (rename_rule_correct rr Hr Hrr) as
          (Hr1ok & Hg01 & _ & _).
        pose proof (to_p_correct Hr1ok Hto) as (Hr2ok & Hg12 & _).
        pose proof (rename_lang_correct l Hr2ok Hrl') as
          (Hr3ok & Hg23 & _ & _).
        assert (Hfm2 : f_matches r2) by
          (eapply (f_matches_grows Hr2ok Hr3ok Hg23 Hfm)).
        assert (Hfm1 : f_matches r1) by
          (eapply (f_matches_grows Hr1ok Hr2ok Hg12 Hfm2)).
        f_equal.
        + f_equal.
          * symmetry; eapply (to_p_via_f Hr1ok Hto Hfm2).
          * eapply (rename_rule_via_f rr Hr Hrr Hfm1).
        + eapply (IH r2 l1 r3 Hr2ok Hrl' Hfm).
    Qed.

  End Bridge.

  (* [pos_of_v r] always satisfies [f_matches] on a well-formed [r];
     this is what eliminates the [f_matches] hypothesis from the
     preservation theorems below. *)
  Lemma pos_of_v_matches r :
    renaming_ok r -> f_matches (pos_of_v r) r.
  Proof.
    intros Hr v p Hin.
    unfold pos_of_v.
    destruct Hr as [Hfresh _ _ _].
    erewrite <- (all_fresh_named_list_lookup_err_in _ _ _ Hfresh) in Hin.
    rewrite <- Hin; reflexivity.
  Qed.

  (** ** Preservation of [Theory.Core] judgments

     [pos_of_v r'] is the canonical [V -> positive] function read off
     the final renaming state; it agrees with [r'.(v_to_p)] on bound
     V's by [pos_of_v_matches].  Each preservation theorem only needs
     [Renaming.Injective (pos_of_v r')] (where [r'] is the final state
     of the renaming pipeline) as an additional hypothesis. *)

  Theorem rename_lang_preserves_wf_lang l r lp r' :
    wf_lang l ->
    renaming_ok r ->
    rename_lang l r = (lp, r') ->
    Renaming.Injective (pos_of_v r') ->
    wf_lang lp.
  Proof.
    intros Hwf Hr Hrl Hinj.
    pose proof (rename_lang_correct l Hr Hrl) as (Hr'ok & _ & _ & _).
    erewrite (rename_lang_via_f (f := pos_of_v r') l Hr Hrl
                (pos_of_v_matches Hr'ok)).
    apply Renaming.rename_lang_mono; auto.
  Qed.

  Theorem rename_preserves_eq_sort l c ts1 ts2 r r1 r2 r3 r4
    lp cp tsp1 tsp2 :
    eq_sort l c ts1 ts2 ->
    renaming_ok r ->
    rename_lang l r = (lp, r1) ->
    rename_ctx c r1 = (cp, r2) ->
    rename_sort ts1 r2 = (tsp1, r3) ->
    rename_sort ts2 r3 = (tsp2, r4) ->
    Renaming.Injective (pos_of_v r4) ->
    eq_sort lp cp tsp1 tsp2.
  Proof.
    intros Heq Hr Hrl Hrc Hr1 Hr2 Hinj.
    pose proof (rename_lang_correct l Hr Hrl) as
      (Hr1ok & Hg01 & _ & _).
    pose proof (rename_ctx_correct c Hr1ok Hrc) as
      (Hr2ok & Hg12 & _ & _).
    pose proof (rename_sort_correct ts1 Hr2ok Hr1) as
      (Hr3ok & Hg23 & _ & _).
    pose proof (rename_sort_correct ts2 Hr3ok Hr2) as
      (Hr4ok & Hg34 & _ & _).
    set (f := pos_of_v r4).
    assert (Hfm4 : f_matches f r4) by exact (pos_of_v_matches Hr4ok).
    assert (Hfm3 : f_matches f r3) by
      (eapply (f_matches_grows (f := f) Hr3ok Hr4ok Hg34 Hfm4)).
    assert (Hfm2 : f_matches f r2) by
      (eapply (f_matches_grows (f := f) Hr2ok Hr3ok Hg23 Hfm3)).
    assert (Hfm1 : f_matches f r1) by
      (eapply (f_matches_grows (f := f) Hr1ok Hr2ok Hg12 Hfm2)).
    erewrite (rename_lang_via_f (f := f) l Hr Hrl Hfm1).
    erewrite (rename_ctx_via_f (f := f) c Hr1ok Hrc Hfm2).
    erewrite (rename_sort_via_f (f := f) ts1 Hr2ok Hr1 Hfm3).
    erewrite (rename_sort_via_f (f := f) ts2 Hr3ok Hr2 Hfm4).
    eapply (proj1 (Renaming.rename_mono Hinj l) c ts1 ts2 Heq).
  Qed.

  Theorem rename_preserves_eq_term l c ts e1 e2 r r1 r2 r3 r4 r5
    lp cp tsp e1p e2p :
    eq_term l c ts e1 e2 ->
    renaming_ok r ->
    rename_lang l r = (lp, r1) ->
    rename_ctx c r1 = (cp, r2) ->
    rename_sort ts r2 = (tsp, r3) ->
    rename_term e1 r3 = (e1p, r4) ->
    rename_term e2 r4 = (e2p, r5) ->
    Renaming.Injective (pos_of_v r5) ->
    eq_term lp cp tsp e1p e2p.
  Proof.
    intros Heq Hr Hrl Hrc Hrt He1 He2 Hinj.
    pose proof (rename_lang_correct l Hr Hrl) as
      (Hr1ok & Hg01 & _ & _).
    pose proof (rename_ctx_correct c Hr1ok Hrc) as
      (Hr2ok & Hg12 & _ & _).
    pose proof (rename_sort_correct ts Hr2ok Hrt) as
      (Hr3ok & Hg23 & _ & _).
    pose proof (rename_term_correct e1 Hr3ok He1) as
      (Hr4ok & Hg34 & _ & _).
    pose proof (rename_term_correct e2 Hr4ok He2) as
      (Hr5ok & Hg45 & _ & _).
    set (f := pos_of_v r5).
    assert (Hfm5 : f_matches f r5) by exact (pos_of_v_matches Hr5ok).
    assert (Hfm4 : f_matches f r4) by
      (eapply (f_matches_grows (f := f) Hr4ok Hr5ok Hg45 Hfm5)).
    assert (Hfm3 : f_matches f r3) by
      (eapply (f_matches_grows (f := f) Hr3ok Hr4ok Hg34 Hfm4)).
    assert (Hfm2 : f_matches f r2) by
      (eapply (f_matches_grows (f := f) Hr2ok Hr3ok Hg23 Hfm3)).
    assert (Hfm1 : f_matches f r1) by
      (eapply (f_matches_grows (f := f) Hr1ok Hr2ok Hg12 Hfm2)).
    erewrite (rename_lang_via_f (f := f) l Hr Hrl Hfm1).
    erewrite (rename_ctx_via_f (f := f) c Hr1ok Hrc Hfm2).
    erewrite (rename_sort_via_f (f := f) ts Hr2ok Hrt Hfm3).
    erewrite (rename_term_via_f (f := f) e1 Hr3ok He1 Hfm4).
    erewrite (rename_term_via_f (f := f) e2 Hr4ok He2 Hfm5).
    eapply (proj1 (proj2 (Renaming.rename_mono Hinj l)) c ts e1 e2 Heq).
  Qed.

  Theorem rename_preserves_wf_ctx l c r r1 r2 lp cp :
    wf_ctx l c ->
    renaming_ok r ->
    rename_lang l r = (lp, r1) ->
    rename_ctx c r1 = (cp, r2) ->
    Renaming.Injective (pos_of_v r2) ->
    wf_ctx lp cp.
  Proof.
    intros Hwf Hr Hrl Hrc Hinj.
    pose proof (rename_lang_correct l Hr Hrl) as
      (Hr1ok & Hg01 & _ & _).
    pose proof (rename_ctx_correct c Hr1ok Hrc) as
      (Hr2ok & Hg12 & _ & _).
    set (f := pos_of_v r2).
    assert (Hfm2 : f_matches f r2) by exact (pos_of_v_matches Hr2ok).
    assert (Hfm1 : f_matches f r1) by
      (eapply (f_matches_grows (f := f) Hr1ok Hr2ok Hg12 Hfm2)).
    erewrite (rename_lang_via_f (f := f) l Hr Hrl Hfm1).
    erewrite (rename_ctx_via_f (f := f) c Hr1ok Hrc Hfm2).
    pose proof (Renaming.rename_mono Hinj l) as Hmono.
    do 6 (apply proj2 in Hmono).
    eapply Hmono; exact Hwf.
  Qed.

  (** [eq_args] is not part of [Theory.Renaming.rename_mono], so we
      prove it by direct induction. *)

  Lemma eq_args_preserve_via (f : V -> positive) (f_inj : Renaming.Injective f) :
    forall (l : lang) c c' es1 es2,
      eq_args l c c' es1 es2 ->
      let lp := Renaming.rename_lang f l in
      let cp := Renaming.rename_ctx f c in
      let cp' := Renaming.rename_ctx f c' in
      let es1p := map (Renaming.rename f) es1 in
      let es2p := map (Renaming.rename f) es2 in
      eq_args lp cp cp' es1p es2p.
  Proof.
    intros l c c' es1 es2 H.
    induction H; cbn; eauto with lang_core.
    eapply eq_args_cons; auto.
    pose proof (proj1 (proj2 (Renaming.rename_mono f_inj l))) as Hterm.
    specialize (Hterm c (t[/with_names_from c' es2/]) e1 e2 H0).
    cbn in Hterm.
    pose proof (Renaming.rename_sort_distr_subst
                  (f := f) f_inj t (with_names_from c' es2))
      as Heq1.
    cbn in Heq1.
    pose proof (Renaming.rename_subst_distr_with_names_from
                  f c' es2) as Heq2.
    rewrite Heq2 in Heq1.
    rewrite Heq1 in Hterm.
    exact Hterm.
  Qed.

  Theorem rename_preserves_eq_args l c c' es1 es2 r r1 r2 r3 r4 r5
    lp cp cp' es1p es2p :
    eq_args l c c' es1 es2 ->
    renaming_ok r ->
    rename_lang l r = (lp, r1) ->
    rename_ctx c r1 = (cp, r2) ->
    rename_ctx c' r2 = (cp', r3) ->
    list_Mmap rename_term es1 r3 = (es1p, r4) ->
    list_Mmap rename_term es2 r4 = (es2p, r5) ->
    Renaming.Injective (pos_of_v r5) ->
    eq_args lp cp cp' es1p es2p.
  Proof.
    intros Heq Hr Hrl Hrc Hrc' He1 He2 Hinj.
    pose proof (rename_lang_correct l Hr Hrl) as
      (Hr1ok & Hg01 & _ & _).
    pose proof (rename_ctx_correct c Hr1ok Hrc) as
      (Hr2ok & Hg12 & _ & _).
    pose proof (rename_ctx_correct c' Hr2ok Hrc') as
      (Hr3ok & Hg23 & _ & _).
    pose proof (list_Mmap_rename_term_correct es1 Hr3ok He1) as
      (Hr4ok & Hg34 & _ & _).
    pose proof (list_Mmap_rename_term_correct es2 Hr4ok He2) as
      (Hr5ok & Hg45 & _ & _).
    set (f := pos_of_v r5).
    assert (Hfm5 : f_matches f r5) by exact (pos_of_v_matches Hr5ok).
    assert (Hfm4 : f_matches f r4) by
      (eapply (f_matches_grows (f := f) Hr4ok Hr5ok Hg45 Hfm5)).
    assert (Hfm3 : f_matches f r3) by
      (eapply (f_matches_grows (f := f) Hr3ok Hr4ok Hg34 Hfm4)).
    assert (Hfm2 : f_matches f r2) by
      (eapply (f_matches_grows (f := f) Hr2ok Hr3ok Hg23 Hfm3)).
    assert (Hfm1 : f_matches f r1) by
      (eapply (f_matches_grows (f := f) Hr1ok Hr2ok Hg12 Hfm2)).
    erewrite (rename_lang_via_f (f := f) l Hr Hrl Hfm1).
    erewrite (rename_ctx_via_f (f := f) c Hr1ok Hrc Hfm2).
    erewrite (rename_ctx_via_f (f := f) c' Hr2ok Hrc' Hfm3).
    erewrite (list_Mmap_rename_term_via_f (f := f) es1 Hr3ok He1 Hfm4).
    erewrite (list_Mmap_rename_term_via_f (f := f) es2 Hr4ok He2 Hfm5).
    apply (eq_args_preserve_via Hinj); auto.
  Qed.

End WithVar.

Arguments unrename_sort {V}%_type_scope {V_default} r ts.
Arguments unrename_ctx {V}%_type_scope {V_default} r c.
Arguments unrename_rule {V}%_type_scope {V_default} r rr.
Arguments unrename_lang {V}%_type_scope {V_default} r l.
