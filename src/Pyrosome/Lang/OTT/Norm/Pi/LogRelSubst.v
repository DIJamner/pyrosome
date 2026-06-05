Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply ApplyLemmas Reflect Typing Preservation ApplySubst
  LogRel LogRelInd LogRelLemmas LogRelRed LogRelRen.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Reducible substitution algebra (Layer A) and substitution-closure of    *)
(* reducibility (Layer B) for the semantic-domain logical relation.        *)
(*                                                                         *)
(* Layer A mirrors the [wf_ssub_*] algebra of [Preservation.v]/            *)
(* [ApplySubst.v] one level up, at [RedSub]/[RedTy]/[RedTm] instead of      *)
(* [wf_ssub]/[wf_svalty]/[has_svalty].  These are ordinary structural       *)
(* facts (no [LR]-recursion) EXCEPT the weakening lemmas [RedTy_shift]/     *)
(* [RedTm_shift], which recurse on the [LR2] derivation via [LR_mut].       *)
(* ===================================================================== *)

(* The reducible analogue of [wf_senv] ([Preservation.v]): every context
   entry is a reducible type. *)
Definition RedEnv (Ge : senv) : Type :=
  forall k T, nth_error Ge k = Some T -> RedTy Ge T.

Lemma RedEnv_nil : RedEnv [].
Proof. intros k T H. destruct k; cbn in H; discriminate. Qed.

(* ===================================================================== *)
(* Apply reverse-cancel (un-shift inversion): the converse of              *)
(* [ApplySubst.Apply_cancel].  Applying [s2] (which inserts a hole at        *)
(* cutoff [c] into [s], i.e. [InsAt c n0 s s2]) to a [c]-shifted scoped      *)
(* value is the same as applying [s] to the un-shifted value.  Where        *)
(* [Apply_cancel] runs the equation forward (build the shifted apply from    *)
(* the un-shifted one), [Apply_uncancel] runs it backward (recover the       *)
(* un-shifted apply from the shifted one) -- needed to RE-INDEX an arbitrary *)
(* substitution over an extended context back down to the original context   *)
(* when reusing a [PolyRedPack] under weakening (the [LRpi] case of          *)
(* [RedTy_shift]).  Same structure as [Apply_cancel]: induction on the value *)
(* with inversion of the [Apply] derivation on the shifted input. *)
Lemma Apply_uncancel :
  (forall T n0 m c s s2 T', ne_below_ty n0 T -> InsAt c n0 s s2 ->
     Apply_ty m s2 (shift_ty c 1 T) T' -> Apply_ty m s T T')
  * ((forall v n0 m c s s2 v', ne_below_val n0 v -> InsAt c n0 s s2 ->
       Apply_val m s2 (shift_val c 1 v) v' -> Apply_val m s v v')
  *  (forall nn n0 m c s s2 w, ne_below_ne n0 nn -> InsAt c n0 s s2 ->
       Apply_ne m s2 (shift_ne c 1 nn) w -> Apply_ne m s nn w)).
Proof.
  apply (sval_mutind
    (fun T => forall n0 m c s s2 T', ne_below_ty n0 T -> InsAt c n0 s s2 ->
       Apply_ty m s2 (shift_ty c 1 T) T' -> Apply_ty m s T T')
    (fun v => forall n0 m c s s2 v', ne_below_val n0 v -> InsAt c n0 s s2 ->
       Apply_val m s2 (shift_val c 1 v) v' -> Apply_val m s v v')
    (fun nn => forall n0 m c s s2 w, ne_below_ne n0 nn -> InsAt c n0 s s2 ->
       Apply_ne m s2 (shift_ne c 1 nn) w -> Apply_ne m s nn w)).
  - (* dU *) intros r l n0 m c s s2 T' _ Hins Hap. cbn in Hap. inversion Hap; subst. apply ap_dU.
  - (* dEl *) intros e IHe n0 m c s s2 T' Hne Hins Hap. cbn in Hap. inversion Hap; subst.
    apply ap_dEl. eapply IHe; [ exact Hne | exact Hins | eassumption ].
  - (* vNe *) intros nn IHnn n0 m c s s2 v' Hne Hins Hap. cbn in Hap. inversion Hap; subst.
    apply ap_ne. eapply IHnn; [ exact Hne | exact Hins | eassumption ].
  - (* vZero *) intros n0 m c s s2 v' _ Hins Hap. cbn in Hap. inversion Hap; subst. apply ap_zero.
  - (* vSuc *) intros v IHv n0 m c s s2 v' Hne Hins Hap. cbn in Hap. inversion Hap; subst.
    apply ap_suc. eapply IHv; [ exact Hne | exact Hins | eassumption ].
  - (* vNat *) intros n0 m c s s2 v' _ Hins Hap. cbn in Hap. inversion Hap; subst. apply ap_nat.
  - (* vEmpty *) intros n0 m c s s2 v' _ Hins Hap. cbn in Hap. inversion Hap; subst. apply ap_empty.
  - (* vPi *) intros F IHF B IHB n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB].
    cbn in Hap. inversion Hap; subst. apply ap_pi.
    + eapply IHF; [ exact HneF | exact Hins | eassumption ].
    + eapply IHB; [ exact HneB | apply InsAt_up; exact Hins | eassumption ].
  - (* vPiI *) intros F IHF B IHB n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB].
    cbn in Hap. inversion Hap; subst. apply ap_piI.
    + eapply IHF; [ exact HneF | exact Hins | eassumption ].
    + eapply IHB; [ exact HneB | apply InsAt_up; exact Hins | eassumption ].
  - (* vLam *) intros b IHb n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. cbn in Hap. inversion Hap; subst. apply ap_lam.
    eapply IHb; [ exact Hne | apply InsAt_up; exact Hins | eassumption ].
  - (* vLamI *) intros b IHb n0 m c s s2 v' Hne Hins Hap.
    cbn [ne_below_val] in Hne. cbn in Hap. inversion Hap; subst. apply ap_lamI.
    eapply IHb; [ exact Hne | apply InsAt_up; exact Hins | eassumption ].
  - (* nVar *) intros k n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. cbn [shift_ne] in Hap.
    replace (if Nat.ltb k c then k else k + 1) with (sh c k) in Hap
      by (unfold sh; destruct (Nat.ltb k c); [ reflexivity | f_equal; Lia.lia ]).
    inversion Hap; subst. rewrite (Hins k Hne). apply ap_var.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. destruct Hne as [HneA Hnescr].
    cbn [shift_ne] in Hap. inversion Hap; subst. eapply ap_emptyrec.
    + eapply IHA; [ exact HneA | exact Hins | eassumption ].
    + eapply IHscr; [ exact Hnescr | exact Hins | eassumption ].
  - (* nApp *) intros f IHf a IHa n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. destruct Hne as [Hnef Hnea].
    cbn [shift_ne] in Hap. inversion Hap; subst. eapply ap_app.
    + eapply IHf; [ exact Hnef | exact Hins | eassumption ].
    + eapply IHa; [ exact Hnea | exact Hins | eassumption ].
    + eassumption.
  - (* nAppI *) intros f IHf a IHa n0 m c s s2 w Hne Hins Hap.
    cbn [ne_below_ne] in Hne. destruct Hne as [Hnef Hnea].
    cbn [shift_ne] in Hap. inversion Hap; subst. eapply ap_appI.
    + eapply IHf; [ exact Hnef | exact Hins | eassumption ].
    + eapply IHa; [ exact Hnea | exact Hins | eassumption ].
    + eassumption.
Qed.

Definition Apply_ty_uncancel  := fst Apply_uncancel.
Definition Apply_val_uncancel := fst (snd Apply_uncancel).
Definition Apply_ne_uncancel  := snd (snd Apply_uncancel).

(* [InsAt] for inserting a hole at cutoff 1 (under one binder), keeping the
   head [a] fixed.  Used for the codomain ([shift_val 1 1 B]) reindexing in
   the [LRpi] case of [RedTy_shift]. *)
Lemma InsAt_1_cons : forall a h t, InsAt 1 (S (length t)) (a :: t) (a :: h :: t).
Proof.
  intros a h t k Hk.
  destruct k as [|k'].
  - reflexivity.
  - replace (sh 1 (S k')) with (S (S k'))
      by (unfold sh; cbn; reflexivity).
    rewrite !nth_default_cons_S.
    apply nth_default_irrel. cbn [length] in Hk. Lia.lia.
Qed.

(* Dropping the head of a well-typed substitution over a front-extended
   context: [sg = h :: t : Delta <- (T0 :: shift Ge)] restricts to
   [t : Delta <- Ge].  Each [Ge]-entry's [Apply_ty] image is recovered by
   the reverse-cancel [Apply_ty_uncancel] (the head [h] is never reached
   because [shift_ty 0 1] skips index 0); the per-entry scoping needed by
   the cancel comes from [wf_senv Ge].  Dual to [Preservation.wf_ssub_up]. *)
Lemma wf_ssub_tail : forall Delta h t T0 Ge,
  wf_senv Ge ->
  wf_ssub Delta (h :: t) (T0 :: map (shift_ty 0 1) Ge) ->
  wf_ssub Delta t Ge.
Proof.
  intros Delta h t T0 Ge Hwf [Hlen Hpt].
  assert (Hlent : length t = length Ge).
  { cbn [length] in Hlen. rewrite length_map in Hlen. Lia.lia. }
  split; [ exact Hlent | ].
  intros k T He.
  assert (He' : nth_error (T0 :: map (shift_ty 0 1) Ge) (S k) = Some (shift_ty 0 1 T)).
  { cbn [nth_error]. rewrite nth_error_map, He. reflexivity. }
  destruct (Hpt (S k) (shift_ty 0 1 T) He') as [T' [Hap Hty]].
  exists T'. split.
  - eapply Apply_ty_uncancel.
    2:{ apply InsAt_base. }
    { rewrite Hlent. exact (wf_svalty_scoped (Hwf k T He)). }
    exact Hap.
  - rewrite nth_default_cons_S in Hty. exact Hty.
Qed.

(* ===================================================================== *)
(* [RedTy_shift] : front-insertion weakening of reducibility -- the         *)
(* keystone of Layer A, independent of [reflect_red].                       *)
(*                                                                         *)
(* The [LRpi] case rebuilds a [PolyRedPack] over [(shift 0 1 F, shift 1 1   *)
(* B)] by REINDEXING an arbitrary substitution [sg : Delta <- (T0::shift    *)
(* Ge)] over the extended context back to one over [Ge]:                    *)
(*   - drop the head: [sg = h :: t], [wf_ssub_tail] gives [t : Delta<-Ge];  *)
(*   - domain: [Apply_val_uncancel] turns the caller's apply on             *)
(*     [shift 0 1 F] into one on [F] (cutoff 0, [InsAt_base]);              *)
(*   - codomain: [Apply_val_cancel] turns the reused pack's apply on [B]    *)
(*     into one on [shift 1 1 B] (cutoff 1, [InsAt_1_cons]);                *)
(*   then [shpRed]/[posRed]/[shpAd]/[posAd] all REUSE the original          *)
(*   [PA]/[ad] at the reindexed substitution.                              *)
(*                                                                         *)
(* RESOLVED (no irrelevance principle, no [LR_mut]).  A prior note feared a *)
(* coherence obstacle: [shpRed]/[posRed] are proof-RELEVANT in their        *)
(* [wf_ssub]/[Apply_val] arguments ([Type], not [Prop]), so reusing [PA]    *)
(* seemed to demand an IRRELEVANCE lemma to retype [ra].  It does not.  The *)
(* delegation is made DEFINITIONAL: [shpRed'] is *defined* to return        *)
(* [shpRed PA (wf_ssub_tail ..) (Apply_val_uncancel ..)], so after the      *)
(* [sg = h :: t] split the argument [ra : redTm (shpRed' ws af) a] reduces  *)
(* (iota) to exactly [redTm (shpRed PA wt af') a] and feeds straight into   *)
(* [posRed PA wt af' ra] with the indices recovered by UNIFICATION from     *)
(* [ra] (no transport).  [posRed'] uses [projT1]/[projT2] projections (not  *)
(* a [match]) so [posTy PA' ra]/[posPack PA' ra] reduce to [posTy PA ra]/   *)
(* [posPack PA ra], and [shpAd']/[posAd'] then discharge by [apply (shpAd   *)
(* p)] / [apply (posAd p)].  Because the case only REUSES [PA]/[ad] (never  *)
(* rebuilds shifted predicates), it needs no induction hypotheses, so a     *)
(* plain [destruct] on the [LR2] derivation suffices -- [LR_mut] is not     *)
(* used here.  [Apply_uncancel]/[InsAt_1_cons]/[wf_ssub_tail] are the       *)
(* reindexing inputs.                                                       *)
(* ===================================================================== *)

(* The construction above is LEVEL-GENERIC: nothing in the [LRpi] case uses
   [lvl = tl2], it only reuses [PA]/[ad] (which live at the ambient [lvl/rec]).
   So we prove front-insertion weakening for the RAW graph [LR lvl rec] at an
   arbitrary level, by [LR_mut].  This single lemma both subsumes the old
   tl2-specific [RedTy_shift] (now a one-line corollary) AND, instantiated at
   the lower tower levels [rec2 (lvl_of l) h] = [LR0]/[LR1], supplies the
   El-reducibility shift needed by the universe ([LRU]) case of [RedTm_shift].
   The [LRU] case here is trivial: [shift_ty 0 1 (dU r l) = dU r l], so the
   universe stays reducible at the SAME level with the SAME [h] (no recursion
   into the codes' El, which is a term-level, not type-level, concern). *)
Lemma LR_shift : forall lvl rec Ge T P, @LR lvl rec Ge T P ->
  wf_senv Ge -> forall T0,
    { P' & @LR lvl rec (T0 :: map (shift_ty 0 1) Ge) (shift_ty 0 1 T) P' }.
Proof.
  intros lvl rec.
  refine (@LR_mut lvl rec
    (fun Ge T P (_ : @LR lvl rec Ge T P) =>
       wf_senv Ge -> forall T0,
         { P' & @LR lvl rec (T0 :: map (shift_ty 0 1) Ge) (shift_ty 0 1 T) P' })
    _ _ _ _ _ _).
  - (* mnat *) intros Ge Hwf T0; cbn [shift_ty shift_val].
    eexists; apply LRnat.
  - (* mempty *) intros Ge Hwf T0; cbn [shift_ty shift_val].
    eexists; apply LRempty.
  - (* mne *) intros Ge n r l w Hwf T0; cbn [shift_ty shift_val].
    eexists; eapply LRne; exact (snd shift_typing _ _ _ w T0).
  - (* mpiI *) intros Ge F B w Hwf T0; cbn [shift_ty shift_val].
    eexists; apply LRpiI; exact (shift_wf_svalty w T0).
  - (* mpi : reuse [PA]/[ad] at the reindexed substitution (IHs unused). *)
    intros Ge F B PA wpi ad _IHs _IHp Hwf T0; cbn [shift_ty shift_val].
    pose proof (wf_svalty_scoped wpi) as Hsc. cbn [ne_below_ty ne_below_val] in Hsc.
    assert (HscF := proj1 Hsc). assert (HscB := proj2 Hsc). clear Hsc.
    unshelve eapply (existT _ _ (@LRpi lvl rec (T0 :: map (shift_ty 0 1) Ge)
                       (shift_val 0 1 F) (shift_val 1 1 B) _ (shift_wf_svalty wpi T0) _)).
    + (* PA' *) unshelve econstructor.
      * (* shpRed' *) intros Delta sg F'' ws af.
        destruct sg as [|h t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- assert (Hlent : length t = length Ge) by
             (pose proof (fst ws) as Hl; cbn [length] in Hl;
              rewrite length_map in Hl; exact (eq_add_S _ _ Hl)).
           refine (shpRed PA (wf_ssub_tail Hwf ws)
                     (@Apply_val_uncancel F (length t) (length Delta) 0 t (h::t) F''
                        _ (InsAt_base t h) af)).
           rewrite Hlent. exact HscF.
      * (* posRed' *) intros Delta sg a F'' ws af ra.
        destruct sg as [|h t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- assert (Hlent : length t = length Ge) by
             (pose proof (fst ws) as Hl; cbn [length] in Hl;
              rewrite length_map in Hl; exact (eq_add_S _ _ Hl)).
           refine (existT _ (projT1 (posRed PA a _ _ ra))
                     (_ , snd (projT2 (posRed PA a _ _ ra)))).
           refine (@Apply_val_cancel B (S (length t)) (length Delta) 1 (a::t) (a::h::t)
                     (projT1 (posRed PA a _ _ ra)) _ (InsAt_1_cons a h t)
                     (fst (projT2 (posRed PA a _ _ ra)))).
           rewrite Hlent. exact HscB.
    + (* ad' *) unshelve econstructor.
      * (* shpAd' *) intros Delta sg F'' ws af.
        destruct sg as [|h t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- apply (shpAd ad).
      * (* posAd' *) intros Delta sg a F'' ws af ra.
        destruct sg as [|h t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- apply (posAd ad).
  - (* mU : universe stays reducible at the same level, same [h]. *)
    intros Ge r l h Hwf T0; cbn [shift_ty shift_val].
    eexists; exact (@LRU lvl rec (T0 :: map (shift_ty 0 1) Ge) r l h).
Qed.

(* tl2 corollary: front-insertion weakening of type-reducibility. *)
Lemma RedTy_shift : forall Ge T, wf_senv Ge -> RedTy Ge T ->
  forall T0, RedTy (T0 :: map (shift_ty 0 1) Ge) (shift_ty 0 1 T).
Proof.
  intros Ge T Hwf [P HLR] T0. exact (LR_shift HLR Hwf T0).
Qed.

(* Structural shift of natural-number reducibility (no [LR]-recursion). *)
Lemma RedNat_shift : forall Ge v, RedNat Ge v ->
  forall T0, RedNat (T0 :: map (shift_ty 0 1) Ge) (shift_val 0 1 v).
Proof.
  intros Ge v H T0. induction H; cbn [shift_val].
  - apply rn_zero.
  - apply rn_suc; assumption.
  - apply rn_ne. exact (snd shift_typing _ _ _ w T0).
Qed.

(* ===================================================================== *)
(* [RedTm_shift] : front-insertion weakening of term-reducibility at an      *)
(* El-type [dEl t] -- the case the Pi-fragment Fundamental Lemma and the     *)
(* codomain-substitution lemma [subst_has_svalty] need (a function value's   *)
(* reducibility weakened under a fresh binder).                              *)
(*                                                                         *)
(* Mirrors [LR_shift]/[RedTy_shift]: case on the [LR2] derivation at [dEl t] *)
(* (the [LRU] universe former cannot occur -- [dU] /= [dEl]), and in each    *)
(* El-former rebuild the SHIFTED predicate and show the shifted value        *)
(* inhabits it.  Base/Pi/neutral formers use the structural shift lemmas.    *)
(* (The universe-typed analogue -- reducibility of a CODE at [dU r l] -- is  *)
(* blocked by a genuine universe stratification: a code's [El]-predicate     *)
(* lives at [RedRel]'s predicate universe, strictly above the slot [LR_shift]*)
(* targets, so it would need a universe-polymorphic [LR]/[LR_mut].  Not      *)
(* needed for the Pi normalization milestone.)                              *)
(*                                                                         *)
(* The [LRpi] case is pure DELEGATION, not the [Vapp]-commutation work a    *)
(* prior note feared: rebuild [PA']/[ad'] exactly as in [LR_shift], then    *)
(* for the application clause un-shift the caller's argument-apply with     *)
(* [Apply_val_uncancel] (cutoff 0) and feed the ORIGINAL clause [snd Pv] at *)
(* the reindexed tail substitution -- letting unification recover the [af]  *)
(* index from [ra] (whose type reduces through [PA']'s definitional         *)
(* [shpRed']).  The returned [Vapp] is already at the shifted [Delta], and  *)
(* [posPack PA'] reduces to [posPack PA], so the codomain membership        *)
(* transfers with no transport and no commutation lemma.                    *)
(* ===================================================================== *)
Lemma RedTm_shift : forall Ge ty v, wf_senv Ge -> RedTm Ge (dEl ty) v ->
  forall T0, RedTm (T0 :: map (shift_ty 0 1) Ge) (shift_ty 0 1 (dEl ty))
                   (shift_val 0 1 v).
Proof.
  intros Ge ty v Hwf RT T0. destruct RT as [P [HLR Pv]]. unfold LR2 in HLR.
  (* [remember] the El-index as a variable so [destruct] eliminates cleanly;
     the [LRU] case is then refuted by [discriminate] on [ET : dU r l = dEl ty]. *)
  remember (dEl ty) as Tt eqn:ET. revert Pv. revert ET.
  destruct HLR as [ Ge0 | Ge0 | Ge0 n r l w | Ge0 F B wpi
                  | Ge0 F B PA wpi p | Ge0 r l h ]; intros ET Pv.
  - (* LRnat *) cbn [shift_ty shift_val].
    exact (redTm_nat (RedNat_shift Pv T0)).
  - (* LRempty *) inversion Pv as [n0 w0 Heqn]; subst; cbn [shift_ty shift_val].
    exact (redTm_empty (snd shift_typing _ _ _ w0 T0)).
  - (* LRne *) inversion Pv as [m0 wm Heqm]; subst; cbn [shift_ty shift_val].
    exact (redTm_neEl (snd shift_typing _ _ _ w T0)
                      (snd shift_typing _ _ _ wm T0)).
  - (* LRpiI *) cbn [shift_ty shift_val].
    exact (redTm_piI (shift_wf_svalty wpi T0) (fst shift_typing _ _ _ Pv T0)).
  - (* LRpi : delegation (PA'/ad' as in [LR_shift]; membership by reuse). *)
    cbn [shift_ty shift_val].
    pose proof (wf_svalty_scoped wpi) as Hsc. cbn [ne_below_ty ne_below_val] in Hsc.
    assert (HscF := proj1 Hsc). assert (HscB := proj2 Hsc). clear Hsc.
    unshelve eapply (RedTmOf_RedTm (redTy_pi (shift_wf_svalty wpi T0) _) _).
    + (* PA' *) unshelve econstructor.
      * (* shpRed' *) intros Delta sg F'' ws af.
        destruct sg as [|hh t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- assert (Hlent : length t = length Ge0) by
             (pose proof (fst ws) as Hl; cbn [length] in Hl;
              rewrite length_map in Hl; exact (eq_add_S _ _ Hl)).
           refine (shpRed PA (wf_ssub_tail Hwf ws)
                     (@Apply_val_uncancel F (length t) (length Delta) 0 t (hh::t) F''
                        _ (InsAt_base t hh) af)).
           rewrite Hlent. exact HscF.
      * (* posRed' *) intros Delta sg a F'' ws af ra.
        destruct sg as [|hh t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- assert (Hlent : length t = length Ge0) by
             (pose proof (fst ws) as Hl; cbn [length] in Hl;
              rewrite length_map in Hl; exact (eq_add_S _ _ Hl)).
           refine (existT _ (projT1 (posRed PA a _ _ ra))
                     (_ , snd (projT2 (posRed PA a _ _ ra)))).
           refine (@Apply_val_cancel B (S (length t)) (length Delta) 1 (a::t) (a::hh::t)
                     (projT1 (posRed PA a _ _ ra)) _ (InsAt_1_cons a hh t)
                     (fst (projT2 (posRed PA a _ _ ra)))).
           rewrite Hlent. exact HscB.
    + (* ad' *) unshelve econstructor.
      * (* shpAd' *) intros Delta sg F'' ws af.
        destruct sg as [|hh t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- apply (shpAd p).
      * (* posAd' *) intros Delta sg a F'' ws af ra.
        destruct sg as [|hh t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- apply (posAd p).
    + (* membership : PiRedTmPred PA' (shift_val 0 1 v) *)
      cbn [RedTmOf redTy_pi projT1 PiRedTmPred]. split.
      * (* well-typedness *) exact (fst shift_typing _ _ _ (fst Pv) T0).
      * (* application clause *)
        intros Delta sg a F' fsg ws rn af afs ra.
        destruct sg as [|hh t].
        -- exfalso. pose proof (fst ws) as Hl. cbn [length] in Hl.
           rewrite length_map in Hl. discriminate.
        -- assert (Hlent : length t = length Ge0) by
             (pose proof (fst ws) as Hl; cbn [length] in Hl;
              rewrite length_map in Hl; exact (eq_add_S _ _ Hl)).
           assert (Hscv : ne_below_val (length t) v) by
             (rewrite Hlent; exact (has_svalty_scoped (fst Pv))).
           pose (afsV := @Apply_val_uncancel v (length t) (length Delta) 0 t (hh::t)
                           fsg Hscv (InsAt_base t hh) afs).
           destruct (snd Pv Delta t a F' fsg (wf_ssub_tail Hwf ws) (is_ren_tl rn) _ afsV ra)
             as [v' [Hvapp Hrtm]].
           exists v'. split; [ exact Hvapp | exact Hrtm ].
  - (* LRU : impossible -- the type is an El-type [dEl t], not a universe. *)
    discriminate ET.
Qed.

(* ===================================================================== *)
(* NEXT (Layer A/B).  With [RedTy_shift]/[RedTm_shift] (front-insertion       *)
(* weakening) and the [LR_shift] engine done, the remaining Layer-A/B work    *)
(* is full substitution-closure [RedTy_subst]/[RedSub_*] and the entangled    *)
(* Fundamental-Lemma core ([reflect_red] + [Apply_total_red]).               *)
(* ===================================================================== *)
