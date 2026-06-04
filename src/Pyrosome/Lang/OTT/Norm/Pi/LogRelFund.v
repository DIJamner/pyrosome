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
