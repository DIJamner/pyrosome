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
  LogRel LogRelInd LogRelRed LogRelLemmas.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* The entangled Fundamental-Lemma core (Layer C).                         *)
(*                                                                         *)
(* [reflect_red] : every neutral typed at a reducible type reflects to a    *)
(* REDUCIBLE value.  Proved by [LR_mut] on the [LR2] derivation.            *)
(*                                                                         *)
(* Per the simplification review (2026-06-04), [Apply_total_red] is NOT a    *)
(* separate mutual companion: on reducible inputs, application totality is   *)
(* the second projection of [PiRedTmPred] membership (LogRel.v:138-144), so  *)
(* the Pi case builds that clause inline using the [posAd] codomain IH.      *)
(*                                                                         *)
(* This file establishes the FULL [LR_mut] induction modulo the relevant-Pi  *)
(* case, which is abstracted as the premise [reflect_pi_step].  All the      *)
(* base/universe cases and the induction wiring are discharged here          *)
(* (axiom-free); [reflect_pi_step] isolates exactly the entangled            *)
(* eta-expansion + beta/application content that is the remaining            *)
(* normalization core (see the ROADMAP block at the end of the file for the  *)
(* fully-worked proof recipe and the precise outstanding obligation).        *)
(* ===================================================================== *)

(* The induction motive: at a well-formed context, a neutral typed at [T]
   reflects to a value satisfying the candidate predicate [P]. *)
Definition reflect_motive (Ge : senv) (T : svalty) (P : sval -> Type)
  (_ : @LR tl2 rec2 Ge T P) : Type :=
  wf_senv Ge -> forall n, wf_neutral Ge n T ->
  { v & (Reflect (length Ge) T n v * P v)%type }.

(* The relevant-Pi case of the reflection induction, abstracted as a premise.
   It receives the two codomain/domain induction hypotheses ([shpAd]/[posAd]
   reflections supplied by [LR_mut]) and must produce the eta-expanded
   reflection together with its [PiRedTmPred] membership (typing + the
   beta/application clause).  This is the sole obligation separating the
   present development from the full Fundamental Lemma. *)
Definition reflect_pi_step : Type :=
  forall Ge F B (PA : PolyRedPack Ge F B)
    (wpi : wf_svalty Ge (dEl (vPi F B)))
    (ad : PolyRedPackAdequate (@LR tl2 rec2) PA),
    (forall Delta sg F' (ws : wf_ssub Delta sg Ge)
        (af : Apply_val (length Delta) sg F F'),
        reflect_motive (shpAd ad ws af)) ->
    (forall Delta sg a F' (ws : wf_ssub Delta sg Ge)
        (af : Apply_val (length Delta) sg F F')
        (ra : redTm (shpRed PA ws af) a),
        reflect_motive (posAd ad ws af ra)) ->
    reflect_motive (LRpi wpi ad).

(* The reflection induction, modulo the relevant-Pi case. *)
Lemma reflect_red_mut (Hpi : reflect_pi_step) :
  forall Ge T P (H : @LR tl2 rec2 Ge T P), reflect_motive H.
Proof.
  intros Ge T P H. revert Ge T P H.
  refine (LR_mut tl2 rec2 reflect_motive _ _ _ _ _ _).
  - (* mnat *) intros Ge Hwf n wn. exists (vNe n); split.
    + apply refl_Nat.
    + apply rn_ne; exact wn.
  - (* mempty *) intros Ge Hwf n wn. exists (vNe n); split.
    + apply refl_Empty.
    + apply rne; exact wn.
  - (* mne *) intros Ge n0 r l w Hwf n wn. exists (vNe n); split.
    + apply refl_neEl.
    + apply rne; exact wn.
  - (* mpiI : irrelevant Pi stays neutral *)
    intros Ge F B w Hwf n wn. exists (vNe n); split.
    + apply refl_PiI.
    + cbn. apply t_ne; exact wn.
  - (* mpi : the entangled relevant-Pi case, supplied as a premise *)
    exact Hpi.
  - (* mU : a neutral code reflects to itself; its El is reducible as a neutral *)
    intros Ge r l h Hwf n wn. exists (vNe n); split.
    + apply refl_U.
    + cbn. split.
      * apply t_ne; exact wn.
      * exists (RedNeutral Ge (dEl (vNe n))).
        unfold rec2. clear h. destruct (lvl_of l); eapply LRne; exact wn.
Qed.

(* User-facing form: a neutral typed at a reducible type reflects to a
   REDUCIBLE term (the top-level [RedTy]/[RedTm] packaging). *)
Definition reflect_red (Hpi : reflect_pi_step)
  (Ge : senv) (T : svalty) (wfG : wf_senv Ge)
  (rt : RedTy Ge T) (n : neutral) (wn : wf_neutral Ge n T)
  : { v & (Reflect (length Ge) T n v * RedTm Ge T v)%type } :=
  let (P, H) := rt in
  let (v, pr) := @reflect_red_mut Hpi Ge T P H wfG n wn in
  existT _ v (fst pr, existT _ P (H, snd pr)).

(* ===================================================================== *)
(* ROADMAP : proving [reflect_pi_step] (the remaining normalization core).  *)
(*                                                                         *)
(* Fix [m := length Ge], [Delta := dEl (shift_val 0 1 F) :: map (shift_ty   *)
(* 0 1) Ge] (so [length Delta = S m] via [length_map]); [wf_senv Delta] by  *)
(* [wf_senv_ext] + [wf_svalty_pi_dom].  Scoping [ne_below_val m F],         *)
(* [ne_below_val (S m) B] from [wf_svalty_scoped wpi].                      *)
(*                                                                         *)
(* (1) REFLECT THE BOUND VARIABLE.  Instantiate the domain IH [shpAd] at     *)
(*     [Delta], [sg := wkn_list m], [F' := shift_val 0 1 F], with            *)
(*     [ws := wf_ssub_wkn (dEl (shift_val 0 1 F)) Hwf] and                   *)
(*     [af := Apply_val_wkn F m ..]; feed [n_var] ([nth_error Delta 0]).     *)
(*     Yields [ARG] with [Reflect (S m) (dEl (shift_val 0 1 F)) (nVar 0)     *)
(*     ARG] and [ra : redTm (shpRed PA ws af) ARG] (ARG reducible at dom).   *)
(* (2) SUBSTITUTED CODOMAIN (intrinsic).  [posApp PA ra :                    *)
(*     Apply_val (S m) (ARG :: wkn_list m) B (posTy PA ra)] is exactly       *)
(*     [refl_Pi]'s second premise; [posPack PA ra] is the codomain LRPack.   *)
(* (3) REFLECT THE ETA-BODY.  Instantiate the codomain IH [posAd] at the     *)
(*     same data with [a := ARG]; feed the neutral [nApp (shift_ne 0 1 n)    *)
(*     ARG], whose [n_app] typing uses [shift_typing] (weakened Pi),         *)
(*     [RedTm_wf] of [ra] (for [has_svalty Delta ARG (dEl (shift F))]) and   *)
(*     [Apply_reflect_cod] (bridging [ARG :: wkn_list m] over [B] to         *)
(*     [ARG :: id_list (S m)] over [shift_val 1 1 B] = [posTy PA ra]).       *)
(*     Yields [body] with [Reflect (S m) (dEl (posTy PA ra)) (nApp ..) body] *)
(*     and [redTm (posPack PA ra) body].                                     *)
(* (4) ASSEMBLE.  [v := vLam body]; [Reflect .. n (vLam body)] by [refl_Pi]  *)
(*     (premises = (1),(2),(3)).  [PiRedTmPred PA (vLam body)] needs:        *)
(*       (a) [has_svalty Ge (vLam body) (dEl (vPi F B))] by [t_lam_eta]      *)
(*           (ARG + [Apply_reflect_cod] + [RedTm_wf] of [body]). -- DONE-able *)
(*       (b) the APPLICATION CLAUSE: for arbitrary [sg1 : Delta1 <- Ge] and  *)
(*           reducible arg, the substituted lambda applied beta-reduces to a *)
(*           value reducible at [posPack PA ra1].  *** OUTSTANDING ***       *)
(*                                                                         *)
(* Obstacle for (b): the result is [body'[a :: id]] where [body'] is the     *)
(* [up sg1]-image of [body]; by the cons-composition identity                *)
(* [(a :: id) o (up sg1) = a :: sg1] this equals [body[a :: sg1]], the       *)
(* [a :: sg1]-image of a REFLECTION.  Showing it equals the reflection       *)
(* [posAd] produces at the [sg1]-instance is substitution/reflection         *)
(* COMMUTATION, whose totality at a lambda-headed substituted neutral is     *)
(* exactly the normalization content (supplied by the [posAd] IH, not by a   *)
(* prior structural lemma).  This is the genuinely entangled step; it is NOT *)
(* a separable [Apply_comp] lemma (composition through [Vapp] needs that      *)
(* beta's totality).  See plan doc (i-m-working-on-a-radiant-lemur.md).      *)
(* ===================================================================== *)

(* A Prop-level inversion helper used by the [reflect_pi_step] proof (step 0:
   [wf_senv Delta]).  Kept here because the [reflect_pi_step] goal is
   [Type]-valued and so cannot directly invert the [Prop] hypothesis [wpi]. *)
Lemma wf_svalty_pi_dom : forall Ge F B,
    wf_svalty Ge (dEl (vPi F B)) -> wf_svalty Ge (dEl F).
Proof.
  intros Ge F B H. inversion H; subst.
  match goal with He : has_svalty Ge (vPi F B) _ |- _ => inversion He; subst end.
  eapply wf_dEl; eassumption.
Qed.

(* ===================================================================== *)
(* SIMPLIFICATION (2026-06-04): the relevant-Pi case minus its sole open    *)
(* obligation.                                                              *)
(*                                                                         *)
(* Reviewing the ROADMAP above: steps (1)-(3), (4a), and the [refl_Pi]       *)
(* assembly are all dischargeable NOW from the already-proved kit            *)
(* ([wf_ssub_wkn], [Apply_val_wkn], [Apply_reflect_cod], [t_lam_eta],        *)
(* [shift_typing], [RedTm_wf]).  Only step (4b) -- the [PiRedTmPred]          *)
(* APPLICATION CLAUSE -- is genuinely open.  We therefore SHRINK the          *)
(* abstracted premise from the whole-case [reflect_pi_step] to                *)
(* [reflect_pi_app_step] below (the application clause only, handed the       *)
(* eta-body data the construction produces), and discharge everything else    *)
(* axiom-free in [reflect_pi_step_from_app].                                  *)
(*                                                                         *)
(* Correcting the ROADMAP's optimism: (4b) for an ARBITRARY well-typed        *)
(* substitution [sg] is NOT supplied by the [posAd] reflection IH alone.      *)
(* The beta-reduct is [body[a :: sg]], and [body] embeds the original         *)
(* neutral [n]; under a general [sg], [n[sg]] need not stay neutral (it may   *)
(* be a lambda), so the result is a real beta-normal value, not a reflection  *)
(* of a neutral -- it is reducible only by the semantic-application closure    *)
(* of the FULL Fundamental Lemma, with which (4b) is mutually entangled.      *)
(* That is exactly the content isolated by [reflect_pi_app_step].             *)
(* ===================================================================== *)

(* The minimal remaining obligation: the application clause of [PiRedTmPred]
   for the eta-expansion [vLam body], given the reflected eta-body data
   ([ARG]/[body] pinned by their [Reflect] derivations, and the [wkn]-instance
   domain/codomain reducibility witnesses [ra0]/[rb] that they inhabit). *)
Definition reflect_pi_app_step : Type :=
  forall Ge F B (PA : PolyRedPack Ge F B)
    (ad : PolyRedPackAdequate (@LR tl2 rec2) PA)
    (Hwf : wf_senv Ge)
    (n : neutral) (wn : wf_neutral Ge n (dEl (vPi F B)))
    (ARG body : sval)
    (ws0 : wf_ssub (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
                   (wkn_list (length Ge)) Ge)
    (af0 : Apply_val (length (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge))
                     (wkn_list (length Ge)) F (shift_val 0 1 F))
    (ra0 : redTm (shpRed PA ws0 af0) ARG)
    (Harg : Reflect (S (length Ge)) (dEl (shift_val 0 1 F)) (nVar 0) ARG)
    (Hbody : Reflect (S (length Ge)) (dEl (posTy PA ra0))
                     (nApp (shift_ne 0 1 n) ARG) body)
    (rb : redTm (posPack PA ra0) body),
    forall Delta sg a F' fsg
      (ws : wf_ssub Delta sg Ge) (af : Apply_val (length Delta) sg F F')
      (afs : Apply_val (length Delta) sg (vLam body) fsg)
      (ra : redTm (shpRed PA ws af) a),
      { v & (Vapp (length Delta) fsg a v * redTm (posPack PA ra) v)%type }.

(* Everything in the relevant-Pi case EXCEPT the application clause, proved
   axiom-free: this discharges [reflect_pi_step] from the sharper premise. *)
Lemma reflect_pi_step_from_app : reflect_pi_app_step -> reflect_pi_step.
Proof.
  intros Happ Ge F B PA wpi ad IHsh IHpos Hwf n wn.
  (* scoping of the Pi type *)
  pose proof (wf_svalty_scoped wpi) as Hsc.
  cbn [ne_below_ty ne_below_val] in Hsc. destruct Hsc as [HscF HscB].
  (* length of the extended context *)
  assert (HL : length (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
               = S (length Ge))
    by (cbn [length]; f_equal; apply length_map).
  (* wf_senv of the extended context *)
  assert (HwfD : wf_senv (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)).
  { pose proof (wf_senv_ext Hwf (wf_svalty_pi_dom wpi)) as H.
    cbn [shift_ty] in H. exact H. }
  (* the weakening substitution and its domain apply *)
  pose (ws0 := @wf_ssub_wkn Ge (dEl (shift_val 0 1 F)) Hwf).
  pose proof (@Apply_val_wkn F (length Ge) HscF) as af0.
  rewrite <- HL in af0.
  (* (1) reflect the bound variable at the (shifted) domain *)
  assert (Hvar0 : wf_neutral (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
                    (nVar 0) (dEl (shift_val 0 1 F)))
    by (apply n_var; reflexivity).
  specialize (IHsh _ (wkn_list (length Ge)) (shift_val 0 1 F) ws0 af0).
  unfold reflect_motive in IHsh.
  destruct (IHsh HwfD (nVar 0) Hvar0) as [ARG [Harg0 ra0]].
  pose proof Harg0 as Harg. rewrite HL in Harg.
  (* (2) the substituted codomain, intrinsic to the pack *)
  pose proof (posApp PA ra0) as Hpos. rewrite HL in Hpos.
  (* codomain coherence (the [t_lam_eta] / [n_app] result type) *)
  assert (HcodS : Apply_val (S (length Ge)) (ARG :: id_list (S (length Ge)))
                    (shift_val 1 1 B) (posTy PA ra0))
    by exact (@Apply_reflect_cod (length Ge) ARG B (posTy PA ra0) HscB Hpos).
  pose proof HcodS as HcodD. rewrite <- HL in HcodD.
  (* ARG is well-typed at the (shifted) domain *)
  assert (HtyARG : has_svalty (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
                     ARG (dEl (shift_val 0 1 F))).
  { apply RedTm_wf.
    exact (existT _ (redTm (shpRed PA ws0 af0)) (shpAd ad ws0 af0, ra0)). }
  (* the eta-body neutral is well-formed at the substituted codomain *)
  assert (Hnf : wf_neutral (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
                  (shift_ne 0 1 n) (dEl (vPi (shift_val 0 1 F) (shift_val 1 1 B)))).
  { pose proof (snd shift_typing Ge n (dEl (vPi F B)) wn (dEl (shift_val 0 1 F))) as H.
    cbn [shift_ty shift_val] in H. exact H. }
  assert (Happn : wf_neutral (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
                    (nApp (shift_ne 0 1 n) ARG) (dEl (posTy PA ra0))).
  { eapply n_app; [ exact Hnf | exact HtyARG | exact HcodD ]. }
  (* (3) reflect the eta-body at the substituted codomain *)
  specialize (IHpos _ (wkn_list (length Ge)) ARG (shift_val 0 1 F) ws0 af0 ra0).
  unfold reflect_motive in IHpos.
  destruct (IHpos HwfD (nApp (shift_ne 0 1 n) ARG) Happn) as [body [Hbody0 rb]].
  pose proof Hbody0 as Hbody. rewrite HL in Hbody.
  (* (4) assemble the eta-expansion [vLam body] *)
  exists (vLam body). split.
  - (* Reflect .. n (vLam body) by [refl_Pi] *)
    eapply refl_Pi; [ exact Harg | exact Hpos | exact Hbody ].
  - (* PiRedTmPred PA (vLam body) *)
    split.
    + (* (4a) typing of the eta-expansion via [t_lam_eta] *)
      eapply t_lam_eta; [ exact Harg | exact HcodS | ].
      apply RedTm_wf.
      exact (existT _ (redTm (posPack PA ra0)) (posAd ad ws0 af0 ra0, rb)).
    + (* (4b) the application clause, isolated as the sharper premise *)
      exact (Happ Ge F B PA ad Hwf n wn ARG body ws0 af0 ra0 Harg Hbody rb).
Qed.

(* User-facing form from the SHARPER premise: a neutral typed at a reducible
   type reflects to a reducible term, modulo only the application clause. *)
Definition reflect_red_app (Happ : reflect_pi_app_step)
  : forall Ge T (wfG : wf_senv Ge) (rt : RedTy Ge T) (n : neutral)
           (wn : wf_neutral Ge n T),
    { v & (Reflect (length Ge) T n v * RedTm Ge T v)%type } :=
  reflect_red (reflect_pi_step_from_app Happ).

(* ===================================================================== *)
(* Further isolation: drop the [Vapp]/[ap_lam] plumbing from the open       *)
(* obligation.  [afs : Apply_val .. sg (vLam body) fsg] forces (by the only  *)
(* applicable constructor [ap_lam]) [fsg = vLam bodysg] with                 *)
(* [Apply_val (S len) (up sg) body bodysg]; then [Vapp .. (vLam bodysg) a v] *)
(* forces (by [vapp_lam]) the beta-reduct                                    *)
(* [Apply_val len (a :: id_list len) bodysg v].  Both are structural, so the *)
(* application clause reduces to the BETA-REDUCT obligation below: the       *)
(* substituted-and-beta-reduced eta-body exists and is reducible at the       *)
(* codomain instance.  This is the textbook normalization core, free of any  *)
(* semantic-application bookkeeping. *)
(* ===================================================================== *)
Definition reflect_pi_beta_step : Type :=
  forall Ge F B (PA : PolyRedPack Ge F B)
    (ad : PolyRedPackAdequate (@LR tl2 rec2) PA)
    (Hwf : wf_senv Ge)
    (n : neutral) (wn : wf_neutral Ge n (dEl (vPi F B)))
    (ARG body : sval)
    (ws0 : wf_ssub (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
                   (wkn_list (length Ge)) Ge)
    (af0 : Apply_val (length (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge))
                     (wkn_list (length Ge)) F (shift_val 0 1 F))
    (ra0 : redTm (shpRed PA ws0 af0) ARG)
    (Harg : Reflect (S (length Ge)) (dEl (shift_val 0 1 F)) (nVar 0) ARG)
    (Hbody : Reflect (S (length Ge)) (dEl (posTy PA ra0))
                     (nApp (shift_ne 0 1 n) ARG) body)
    (rb : redTm (posPack PA ra0) body),
    forall Delta sg a F' bodysg
      (ws : wf_ssub Delta sg Ge) (af : Apply_val (length Delta) sg F F')
      (bs : Apply_val (S (length Delta)) (up sg) body bodysg)
      (ra : redTm (shpRed PA ws af) a),
      { v & (Apply_val (length Delta) (a :: id_list (length Delta)) bodysg v
             * redTm (posPack PA ra) v)%type }.

Lemma reflect_pi_app_step_from_beta : reflect_pi_beta_step -> reflect_pi_app_step.
Proof.
  intros Hbeta Ge F B PA ad Hwf n wn ARG body ws0 af0 ra0 Harg Hbody rb.
  intros Delta sg a F' fsg ws af afs ra.
  (* [afs] : applying [sg] to [vLam body] -- only [ap_lam] applies, exposing
     the substituted body [bodysg] with [Apply_val (S len) (up sg) body bodysg]. *)
  inversion afs; subst.
  match goal with
  | bs : Apply_val (S (length Delta)) (up sg) body ?bodysg |- _ =>
      destruct (Hbeta Ge F B PA ad Hwf n wn ARG body ws0 af0 ra0 Harg Hbody rb
                      Delta sg a F' bodysg ws af bs ra) as [v [Hbv Hrv]];
      exists v; split; [ apply vapp_lam; exact Hbv | exact Hrv ]
  end.
Qed.

(* The most-reduced user-facing form: reflection of a neutral into a reducible
   term, modulo only the beta-reduct (normalization) core. *)
Definition reflect_red_beta (Hbeta : reflect_pi_beta_step)
  : forall Ge T (wfG : wf_senv Ge) (rt : RedTy Ge T) (n : neutral)
           (wn : wf_neutral Ge n T),
    { v & (Reflect (length Ge) T n v * RedTm Ge T v)%type } :=
  reflect_red_app (reflect_pi_app_step_from_beta Hbeta).
