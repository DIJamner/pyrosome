Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Determinism ApplyLemmas SortInj.
Import Core.Notations.

(* Semantic typing of the NbE value domain (Domain.v).

   Values are ENVIRONMENT-FREE / absolute: a value over a context [G] has its free
   neutral de Bruijn indices in [0, ctx_len G).  A semantic environment [senv =
   list svalty] records the TYPES of those variables (index 0 = innermost).  The
   shifts that [eval_env]'s [ev_env_ext] bakes into the list mean a neutral [nVar k]
   over [Ge] is typed DIRECTLY by [nth_error Ge k]. *)

(* ===== Scopedness: every neutral index is below [m] ===== *)
Fixpoint ne_below_ty (m : nat) (T : svalty) : Prop :=
  match T with
  | dU _ _ => True
  | dEl e => ne_below_val m e
  end
with ne_below_val (m : nat) (v : sval) : Prop :=
  match v with
  | vNe n => ne_below_ne m n
  | vZero => True
  | vSuc v' => ne_below_val m v'
  | vNat => True
  | vEmpty => True
  end
with ne_below_ne (m : nat) (n : neutral) : Prop :=
  match n with
  | nVar k => k < m
  | nEmptyrec _ _ A scrut => ne_below_val m A /\ ne_below_ne m scrut
  end.

(* ===== Typing judgments ===== *)
Section Typing.
  Notation term := (@term string).

  Unset Elimination Schemes.
  Inductive wf_svalty : senv -> svalty -> Prop :=
  | wf_dU  : forall Ge r l, wf_svalty Ge (dU r l)
  | wf_dEl : forall Ge e r l, has_svalty Ge e (dU r l) -> wf_svalty Ge (dEl e)
  with has_svalty : senv -> sval -> svalty -> Prop :=
  | t_ne    : forall Ge n T, wf_neutral Ge n T -> has_svalty Ge (vNe n) T
  | t_zero  : forall Ge, has_svalty Ge vZero (dEl vNat)
  | t_suc   : forall Ge v, has_svalty Ge v (dEl vNat) -> has_svalty Ge (vSuc v) (dEl vNat)
  | t_Nat   : forall Ge r l, has_svalty Ge vNat   (dU r l)     (* Nat is a CODE in U *)
  | t_Empty : forall Ge r l, has_svalty Ge vEmpty (dU r l)     (* Empty is a CODE in U *)
  with wf_neutral : senv -> neutral -> svalty -> Prop :=
  | n_var   : forall Ge k T, nth_error Ge k = Some T -> wf_neutral Ge (nVar k) T
  | n_emptyrec : forall Ge rA lA A scrut r l,
        has_svalty Ge A (dU r l) ->
        wf_neutral Ge scrut (dEl vEmpty) ->
        wf_neutral Ge (nEmptyrec rA lA A scrut) (dEl A).
  Set Elimination Schemes.

End Typing.

(* sigma : Delta -> Gamma  is well typed when it has one value per Gamma-variable,
   each of the Gamma-type with the WHOLE substitution applied.  POINTWISE / absolute-
   index (the senv stores types with shifts baked in, so [Gamma[k]] references absolute
   indices < length Gamma and [apply_ty sigma] substitutes them uniformly).  Matches
   [eval_sub]: [id_list] via [apply_id_ty], [wkn_list] via the shift, [snoc]/[cmp]
   pointwise. *)
Definition wf_ssub (Delta : senv) (sigma : ssub) (Gamma : senv) : Type :=
  ((length sigma = length Gamma) *
   (forall k T, nth_error Gamma k = Some T ->
       has_svalty Delta (nth_default (vNe (nVar 0)) sigma k) (apply_ty sigma T)))%type.

(* The value-typing mutual pair (neither references [wf_svalty], which only sits on top). *)
Scheme has_svalty_rect := Induction for has_svalty Sort Prop
  with wf_neutral_rect := Induction for wf_neutral Sort Prop.

(* Combined Scheme chokes on these indexed inductives; pair the two mutual [_rect]
   by hand (they share the [P0]/[P1] motive + minor-premise telescope). *)
Definition has_neutral_mutind
  (P0 : forall Ge v T, has_svalty Ge v T -> Prop)
  (P1 : forall Ge n T, wf_neutral Ge n T -> Prop) := fun
  fne fzero fsuc fNat fEmpty fvar femptyrec =>
  ( @has_svalty_rect P0 P1 fne fzero fsuc fNat fEmpty fvar femptyrec
  , @wf_neutral_rect P0 P1 fne fzero fsuc fNat fEmpty fvar femptyrec ).

(* Canonical forms at El Empty: only a neutral inhabits it. *)
Lemma canonical_empty : forall Ge v, has_svalty Ge v (dEl vEmpty) -> exists n, v = vNe n.
Proof.
  intros Ge v H.
  inversion H; subst; try (eexists; reflexivity); try discriminate; try congruence.
Qed.

(* ===== Substitution lemma: typing is closed under well-typed substitution ===== *)
Lemma subst_has_svalty :
  (forall Ge v T, has_svalty Ge v T ->
     forall Delta sigma, wf_ssub Delta sigma Ge ->
       has_svalty Delta (apply_val sigma v) (apply_ty sigma T))
  * (forall Ge n T, wf_neutral Ge n T ->
     forall Delta sigma, wf_ssub Delta sigma Ge ->
       has_svalty Delta (apply_ne sigma n) (apply_ty sigma T)).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => forall Delta sigma, wf_ssub Delta sigma Ge ->
       has_svalty Delta (apply_val sigma v) (apply_ty sigma T))
    (fun Ge n T _ => forall Delta sigma, wf_ssub Delta sigma Ge ->
       has_svalty Delta (apply_ne sigma n) (apply_ty sigma T))
    _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn Delta sigma Hsub. cbn. apply IHn; exact Hsub.
  - (* t_zero *) intros Ge Delta sigma Hsub. cbn. apply t_zero.
  - (* t_suc *) intros Ge v hv IHv Delta sigma Hsub. cbn. apply t_suc. apply IHv; exact Hsub.
  - (* t_Nat *) intros Ge r l Delta sigma Hsub. cbn. apply t_Nat.
  - (* t_Empty *) intros Ge r l Delta sigma Hsub. cbn. apply t_Empty.
  - (* n_var *) intros Ge k T He Delta sigma [Hlen Hpt]. cbn.
    erewrite nth_default_irrel_sval; [ apply Hpt; exact He | ].
    rewrite Hlen. apply (proj1 (nth_error_Some Ge k)). rewrite He. discriminate.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr Delta sigma Hsub. cbn.
    pose proof (IHscr Delta sigma Hsub) as Hscrut. cbn in Hscrut.
    destruct (canonical_empty Hscrut) as [scrut' Hsc].
    rewrite Hsc. cbn.
    apply t_ne. econstructor.
    + (* motive code typed *) apply IHA; exact Hsub.
    + (* scrutinee neutral at dEl vEmpty *)
      rewrite Hsc in Hscrut. inversion Hscrut; subst. eassumption.
Qed.

(* ===== Apply-composition, conditioned on TYPING =====

   The scopedness-only version is FALSE for [nEmptyrec] (apply_ne's else-branch keeps the
   ORIGINAL scrutinee).  Under typing it holds: an [El Empty] scrutinee maps to a NEUTRAL
   under any well-typed substitution (canonical forms), so the else-branch never fires. *)
Lemma apply_compose_typed :
  (forall Ge v T, has_svalty Ge v T ->
     forall D1 D2 sf sg, wf_ssub D1 sf D2 -> wf_ssub D2 sg Ge ->
       apply_val (map (apply_val sf) sg) v = apply_val sf (apply_val sg v))
  * (forall Ge n T, wf_neutral Ge n T ->
     forall D1 D2 sf sg, wf_ssub D1 sf D2 -> wf_ssub D2 sg Ge ->
       apply_ne (map (apply_val sf) sg) n = apply_val sf (apply_ne sg n)).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => forall D1 D2 sf sg, wf_ssub D1 sf D2 -> wf_ssub D2 sg Ge ->
       apply_val (map (apply_val sf) sg) v = apply_val sf (apply_val sg v))
    (fun Ge n T _ => forall D1 D2 sf sg, wf_ssub D1 sf D2 -> wf_ssub D2 sg Ge ->
       apply_ne (map (apply_val sf) sg) n = apply_val sf (apply_ne sg n))
    _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn D1 D2 sf sg Hsf Hsg. cbn.
    exact (IHn D1 D2 sf sg Hsf Hsg).
  - (* t_zero *) intros; reflexivity.
  - (* t_suc *) intros Ge v hv IHv D1 D2 sf sg Hsf Hsg. cbn. f_equal.
    exact (IHv D1 D2 sf sg Hsf Hsg).
  - (* t_Nat *) intros; reflexivity.
  - (* t_Empty *) intros; reflexivity.
  - (* n_var *) intros Ge k T He D1 D2 sf sg Hsf Hsg. cbn.
    destruct Hsg as [Hglen Hgpt].
    assert (Hk : k < length sg)
      by (rewrite Hglen; apply (proj1 (nth_error_Some Ge k)); rewrite He; discriminate).
    unfold nth_default. rewrite nth_error_map.
    destruct (nth_error sg k) eqn:E.
    + cbn. reflexivity.
    + apply nth_error_None in E. exfalso. Lia.lia.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr D1 D2 sf sg Hsf Hsg.
    (* scrut substituted by sg stays neutral (s''), then by sf stays neutral (s3) *)
    pose proof (snd subst_has_svalty Ge scrut (dEl vEmpty) hscr D2 sg Hsg) as Hs2. cbn in Hs2.
    destruct (canonical_empty Hs2) as [s'' Hs''].
    assert (Hwf'' : wf_neutral D2 s'' (dEl vEmpty))
      by (rewrite Hs'' in Hs2; inversion Hs2; subst; assumption).
    pose proof (snd subst_has_svalty D2 s'' (dEl vEmpty) Hwf'' D1 sf Hsf) as Hs3. cbn in Hs3.
    destruct (canonical_empty Hs3) as [s3 Hs3eq].
    pose proof (IHscr D1 D2 sf sg Hsf Hsg) as IHsc.
    rewrite Hs'' in IHsc. cbn in IHsc. rewrite Hs3eq in IHsc.
    cbn. rewrite IHsc, Hs''. cbn. rewrite Hs3eq. cbn.
    rewrite (IHA D1 D2 sf sg Hsf Hsg). reflexivity.
Qed.

(* apply-composition on a WELL-FORMED type: dU is fixed; dEl pushes into its code, which
   is typed (the [wf_dEl] premise), so [apply_compose_typed] on the code applies. *)
Lemma apply_compose_ty_typed : forall Ge T, wf_svalty Ge T ->
  forall D1 D2 sf sg, wf_ssub D1 sf D2 -> wf_ssub D2 sg Ge ->
    apply_ty (map (apply_val sf) sg) T = apply_ty sf (apply_ty sg T).
Proof.
  intros Ge T HT D1 D2 sf sg Hsf Hsg. destruct T as [r l | e].
  - reflexivity.
  - cbn. f_equal. inversion HT; subst.
    match goal with H : has_svalty _ e _ |- _ =>
      exact (fst apply_compose_typed _ _ _ H _ _ sf sg Hsf Hsg) end.
Qed.

(* nth_default through a [map (apply_val sf)] (when the index is in range). *)
Lemma nth_default_map_apply : forall (sf sg : ssub) d1 d2 k,
    k < length sg -> nth_default d1 (map (apply_val sf) sg) k = apply_val sf (nth_default d2 sg k).
Proof.
  intros sf sg d1 d2 k Hk. unfold nth_default. rewrite nth_error_map.
  destruct (nth_error sg k) eqn:E.
  - reflexivity.
  - apply nth_error_None in E. exfalso. Lia.lia.
Qed.

(* A well-formed semantic environment: each variable's type is well-formed. *)
Definition wf_senv (Gamma : senv) : Type :=
  forall k T, nth_error Gamma k = Some T -> wf_svalty Gamma T.

(* The identity substitution is well typed. *)
Lemma wf_ssub_id : forall Gamma, wf_ssub Gamma (id_list (length Gamma)) Gamma.
Proof.
  intro Gamma. split.
  - unfold id_list. rewrite length_map, length_seq. reflexivity.
  - intros k T He.
    assert (Hk : k < length Gamma)
      by (apply (proj1 (nth_error_Some Gamma k)); rewrite He; discriminate).
    rewrite apply_id_ty.
    erewrite nth_default_irrel_sval;
      [ rewrite id_list_nth; apply t_ne, n_var; exact He
      | unfold id_list; rewrite length_map, length_seq; exact Hk ].
Qed.

(* Composition of well-typed substitutions (the [ev_cmp] case). *)
Lemma wf_ssub_comp : forall Gamma, wf_senv Gamma ->
  forall D1 D2 sf sg, wf_ssub D1 sf D2 -> wf_ssub D2 sg Gamma ->
    wf_ssub D1 (map (apply_val sf) sg) Gamma.
Proof.
  intros Gamma Hwf D1 D2 sf sg Hsf Hsg. split.
  - rewrite length_map. exact (fst Hsg).
  - intros k T He.
    assert (Hk : k < length sg)
      by (rewrite (fst Hsg); apply (proj1 (nth_error_Some Gamma k)); rewrite He; discriminate).
    rewrite (@nth_default_map_apply sf sg (vNe (nVar 0)) (vNe (nVar 0)) k Hk).
    rewrite (@apply_compose_ty_typed Gamma T (Hwf k T He) D1 D2 sf sg Hsf Hsg).
    exact (fst subst_has_svalty D2 (nth_default (vNe (nVar 0)) sg k) (apply_ty sg T)
             (snd Hsg k T He) D1 sf Hsf).
Qed.

(* ===== Non-vacuity ===== *)
Example ex_zero : has_svalty [] vZero (dEl vNat).
Proof. constructor. Qed.

Example ex_two : has_svalty [] (vSuc vZero) (dEl vNat).
Proof. repeat constructor. Qed.

Example ex_var0 : has_svalty [dEl vNat] (vNe (nVar 0)) (dEl vNat).
Proof. apply t_ne, n_var. reflexivity. Qed.

Example ex_canon : exists n, vNe (nVar 0) = vNe n.
Proof.
  apply canonical_empty with (Ge := [dEl vEmpty]).
  apply t_ne, n_var. reflexivity.
Qed.
