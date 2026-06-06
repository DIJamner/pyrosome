(* Phase-3 PROPER: mutual reify / reflect (paper Theorem 11) connecting the
   structural neutral/normal-form conversion [conv_ne]/[conv_nf] (LogRel2Conv.v)
   to REDUCIBLE conversion [RedTmEq] (LogRel2.v).

   - REFLECT: a [conv_ne]-related pair of well-typed neutrals is reducibly
     convertible (at a reducible type); at the UNIVERSE the reflected neutral
     codes form a reducible type-conversion ([LRne]).
   - REIFY:   reducibly-convertible members are structurally convertible normal
     forms ([conv_nf]).

   This file collects the BASE + UNIVERSE cases, which are self-contained (no
   recursion through Pi members).  They are the leaves the eventual mutual Pi
   induction plugs in.  The Pi/PiI cases are the genuine mutual knot (reifying a
   function applies it to a reflected variable -> reflect at the domain;
   reflecting at a Pi recurses into the codomain pack -- well-founded on the [LR]
   derivation) and are developed separately. *)
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Universe Declaration.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply ApplyLemmas Typing Reflect Preservation ApplySubst RenTyping
  Reify ApplyConv ReifyConv
  LogRel2Conv LogRel2 LogRel2Ind LogRel2Lemmas.
Import Core.Notations.

(* ===================================================================== *)
(* REIFY (base cases): a reducible member pair reads back to structurally   *)
(* convertible normal forms.  Both are immediate from the base PERs.        *)
(* ===================================================================== *)

Lemma reify_nat : forall Ge a b, RedNatEq Ge a b -> conv_nf a b.
Proof.
  intros Ge a b H; induction H.
  - apply cnf_zero.
  - apply cnf_suc; assumption.
  - apply cnf_ne. destruct n0 as [_ c]. exact c.
Qed.

Lemma reify_neutral : forall Ge T a b, RedNeutralEq Ge T a b -> conv_nf a b.
Proof.
  intros Ge T a b H; destruct H as [n m [_ c]].
  apply cnf_ne; exact c.
Qed.

(* ===================================================================== *)
(* REFLECT (base element types): two [conv_ne]-related neutrals, well-typed *)
(* at the SAME base element type, are reducibly convertible there.  At base *)
(* element types reflection is the identity ([Reflect]'s [refl_Nat]/etc.),  *)
(* so the members are literally [vNe n], [vNe m].                           *)
(* ===================================================================== *)

Lemma reflect_nat : forall Ge n m,
    NeConv Ge (dEl vNat) n m ->
    RedTmEq Ge (dEl vNat) (dEl vNat) (vNe n) (vNe m).
Proof.
  intros Ge n m c.
  exists (RedNatEq Ge); split.
  - apply LRnat.
  - apply rne_ne; exact c.
Qed.

Lemma reflect_empty : forall Ge n m,
    NeConv Ge (dEl vEmpty) n m ->
    RedTmEq Ge (dEl vEmpty) (dEl vEmpty) (vNe n) (vNe m).
Proof.
  intros Ge n m c.
  exists (RedNeutralEq Ge (dEl vEmpty)); split.
  - apply LRempty.
  - apply rneT; exact c.
Qed.

(* SINGLE-typed: the neutral term relation lives at the LEFT code [dEl (vNe p)];
   the members [n], [m] are conv-related and typed there. *)
Lemma reflect_neEl : forall Ge n m p q r l,
    NeConv Ge (dU r l) p q ->
    NeConv Ge (dEl (vNe p)) n m ->
    RedTmEq Ge (dEl (vNe p)) (dEl (vNe q)) (vNe n) (vNe m).
Proof.
  intros Ge n m p q r l cpq cnm.
  exists (RedNeutralEq Ge (dEl (vNe p))); split.
  - apply LRne with (r:=r) (l:=l); exact cpq.
  - apply rneT; exact cnm.
Qed.

(* ===================================================================== *)
(* REFLECT (universe): two [conv_ne]-related neutral CODES are a reducible   *)
(* type-conversion -- the El-of-them is reducible via [LRne].  This is the   *)
(* substantive base case: it manufactures a NEW reducible type from a        *)
(* neutral.  It lands in [LR0]/[LR1] (the level-0/1 sub-relations of [LR2]), *)
(* selected by [lvl_of l]; either way [LRne] (which has no level guard)      *)
(* supplies the witness.                                                     *)
(* ===================================================================== *)

(* [lvl_of] never returns [tl2] -- it is [tl0] or [tl1]. *)
Lemma lvl_of_cases : forall l, (lvl_of l = tl0) + (lvl_of l = tl1).
Proof.
  intros l; destruct l as [x | n args].
  - left; reflexivity.
  - simpl. destruct (eqb n "L1"); [ right | left ]; reflexivity.
Qed.

(* The El of two [conv_ne]-related neutral CODES is a reducible TYPE-conversion
   (the type-formation companion of [reflect_U] -- its inner witness, repackaged
   at the top level [LR2] via [LRne]).  This is what lets the fundamental lemma
   FORM the reducible type [El n] from a neutral code [n]. *)
Lemma reflect_neEl_ty : forall Ge r l n m,
    NeConv Ge (dU r l) n m ->
    RedTyEq Ge (dEl (vNe n)) (dEl (vNe m)).
Proof.
  intros Ge r l n m c.
  exists (RedNeutralEq Ge (dEl (vNe n))).
  apply LRne with (r:=r) (l:=l); exact c.
Qed.

Lemma reflect_U : forall Ge r l n m,
    NeConv Ge (dU r l) n m ->
    RedTmEq Ge (dU r l) (dU r l) (vNe n) (vNe m).
Proof.
  intros Ge r l n m c.
  destruct c as [[wn wm] cnm].
  destruct (lvl_of_cases l) as [E | E].
  - (* lvl_of l = tl0 : use LRU0, witness lives in rec0 = LR0 *)
    eexists; split.
    + apply (@LRU0 tl2 LR0 LR1 Ge r l lt02 E).
    + cbn. split; [ split | ].
      * apply t_ne; exact wn.
      * apply t_ne; exact wm.
      * exists (RedNeutralEq Ge (dEl (vNe n))).
        change LR0 with (@LR tl0 LRbot LRbot).
        apply (@LRne tl0 LRbot LRbot Ge n m r l).
        repeat split; assumption.
  - (* lvl_of l = tl1 : use LRU1, witness lives in rec1 = LR1 *)
    eexists; split.
    + apply (@LRU1 tl2 LR0 LR1 Ge r l lt12 E).
    + cbn. split; [ split | ].
      * apply t_ne; exact wn.
      * apply t_ne; exact wm.
      * exists (RedNeutralEq Ge (dEl (vNe n))).
        change LR1 with (@LR tl1 LR0 LRbot).
        apply (@LRne tl1 LR0 LRbot Ge n m r l).
        repeat split; assumption.
Qed.

(* ===================================================================== *)
(* Phase-3 PROPER -- the MUTUAL reify/reflect INDUCTION (paper Theorem 11). *)
(*                                                                         *)
(* The base + universe leaves above plug into a SINGLE induction over the   *)
(* [LR] derivation ([LogRel2Ind.LR_mut]).  The relevant- and irrelevant-Pi  *)
(* cases are the genuine mutual KNOT (reifying a function applies it to a    *)
(* reflected variable -> reflect at the domain; reflecting at a Pi recurses  *)
(* into the codomain pack -> reify the domain types/members for the [∼ne]    *)
(* annotation slots), so they are kept as the two abstract premises          *)
(* [RR_pi_step] / [RR_piI_step]; EVERY other case is discharged axiom-free.  *)
(* This mirrors the proven single-sided methodology (WIP single_sided        *)
(* [LogRelFund.reflect_pi_step]): a green, axiom-free skeleton isolating      *)
(* EXACTLY the residual Pi obligations, discharged separately afterwards.     *)
(*                                                                         *)
(* The combined motive [RRCar] bundles THREE statements at a type pair       *)
(* [A,B] with relation [P]:                                                  *)
(*   REFLECT  : [NeConv]-related neutrals are [P]-related (their reflections);*)
(*   REIFY-tm : [P]-related members read back to [conv_nf];                  *)
(*   REIFY-ty : the type CODES themselves read back to [conv_nf]             *)
(*              ([conv_nf_ty]; trivial at the universe).                     *)
(* REIFY-ty feeds reflect-at-Pi's annotation slots and REFLECT feeds         *)
(* reify-at-Pi's eta variable -- hence ONE induction, not three.            *)
(*                                                                         *)
(* DESIGN (paper-faithful, RESOLVED 2026-06-06).  The conversion [conv_nf] is   *)
(* UNTYPED + purely structural (paper Def 13 [∼annot]); eta is NOT a            *)
(* conversion rule.  Instead it is BAKED INTO NORMAL FORMS by [Reflect]: a      *)
(* neutral at a relevant Pi reflects to its eta-expansion [vLam], so every       *)
(* relevant-function value is a [vLam], never a bare [vNe].  Hence REFLECT is    *)
(* stated TYPE-DIRECTED (it produces the [Reflect]-value [vn]/[vm], identity at  *)
(* base/code/universe, eta-long at relevant Pi), and REIFY-tm at [vPi] only ever *)
(* compares [vLam] vs [vLam] ([cnf_lam]) -- the [vNe]-vs-[vLam] mismatch never   *)
(* arises.  This makes the relevant-Pi REFLECT case the genuine crux (it ports   *)
(* the single-sided eta-expansion construction via [refl_Pi]/[t_lam_eta]/        *)
(* [Apply_reflect_cod]); it is NOT a trivial bare-neutral membership.            *)
(* ===================================================================== *)

(* Reify-type target: at an [El] the underlying codes are [conv_nf]; at the
   universe there is nothing structural to read back (both type indices of
   every [LR] node share a former, so the off-diagonal arms never occur). *)
Definition conv_nf_ty (A B : svalty) : Type :=
  match A, B with
  | dEl u, dEl w => conv_nf u w
  | dU _ _, dU _ _ => unit
  | _, _ => unit
  end.

(* The combined reify/reflect carrier (level-independent: no [LR] inside, so
   it survives unchanged through the finite tower).

   REFLECT is TYPE-DIRECTED: a [conv_ne]-related neutral pair reflects to the
   [Reflect]-normal values [vn]/[vm] (paper "Reflect bakes eta into normal
   forms"), which are then [P]-related.  At base/code/universe types [Reflect]
   is the identity ([refl_Nat]/[refl_U]/...), so [vn = vNe n]; at a relevant Pi
   it eta-EXPANDS ([refl_Pi] -> [vLam ...]).  This keeps every relevant-function
   value a [vLam], so REIFY-tm never faces a structural [vNe]-vs-[vLam]
   mismatch the untyped [conv_nf] cannot express. *)
(* [wf_senv Ge] is THREADED through the carrier (it is only consumed by the
   relevant-Pi case, which needs [wf_ssub_id]/[wf_ssub_wkn] to eta-expand; the
   base/universe cases ignore it).  Mirrors the single-sided [reflect_motive]'s
   leading [wf_senv Ge ->]. *)
(* REFLECT now takes a SINGLE-typed [NeConv Ge A n m] (both neutrals typed at
   the LEFT type [A], paper's [RelAtNe]/[~ne ⦂ A]) and produces the two
   type-directed reflections (left at [A], right at [B]) [P]-related.  The
   right-at-[B] reflection is structural ([Reflect] is type-directed and needs
   no typing premise); membership [P] is single-typed at [A], so the base cases
   close with NO conversion.  This is the formulation that dissolves the
   eta-variable typing wall: in [RR_pi_at] the bound var is reflected at the
   LEFT domain only ([n_var]), never manufactured at both domains. *)
Definition RRCar (Ge : senv) (A B : svalty) (P : sval -> sval -> Type) : Type :=
  wf_senv Ge ->
  ( (forall n m, NeConv Ge A n m ->
       { vn & { vm & (Reflect (length Ge) A n vn
                    * Reflect (length Ge) B m vm
                    * P vn vm)%type } })
  (* REIFY-tm (option A, NbE read-back): reducibly-convertible members read back
     (Reify, eta-long) to conv_nf-related normal forms.  UNIVERSAL form (no
     totality needed here); the eta-short-vs-eta-long mismatch that made the raw
     [conv_nf a b] FALSE is dissolved because [Reify] eta-expands at Pi. *)
  * (forall a b na nb, P a b ->
       Reify (length Ge) A a na -> Reify (length Ge) B b nb -> conv_nf na nb)
  * conv_nf_ty A B )%type.

(* Lower-tower recursion: reify/reflect already hold for a delegate relation
   [rec] (threaded, instantiated down the finite tower). *)
Definition RecRR1 (rec : RedRel) : Type :=
  forall Ge A B P, rec Ge A B P -> RRCar Ge A B P.

(* Universe REFLECT must MANUFACTURE neutral-[El] reducibility in the delegate
   relation -- it is a NEW reducible type from a neutral code, not a transport.
   Guarded by the level order so the unused tower slots ([rec = LRbot]) are
   dischargeable vacuously. *)
Definition NeElBuild (lvl lt : TypeLevel) (rec : RedRel) : Type :=
  forall Ge n m r l, TLlt lt lvl ->
    NeConv Ge (dU r l) n m ->
    { P0 : sval -> sval -> Type & rec Ge (dEl (vNe n)) (dEl (vNe m)) P0 }.

(* The relevant-Pi case (the mutual knot), abstracted at one tower level. *)
Definition RR_pi_at (lvl : TypeLevel) (rec0 rec1 : RedRel) : Type :=
  forall Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
    (wpiA : wf_svalty Ge (dEl (vPi FA BA)))
    (wpiB : wf_svalty Ge (dEl (vPi FB BB)))
    (ad : PolyRedPackAdequate (@LR lvl rec0 rec1) PA),
    (forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
            (afA : Apply_val (length Delta) sg FA FA')
            (afB : Apply_val (length Delta) sg FB FB'),
        RRCar Delta (dEl FA') (dEl FB') (redTmEq (shpRed PA ws afA afB))) ->
    (forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
            (afA : Apply_val (length Delta) sg FA FA')
            (afB : Apply_val (length Delta) sg FB FB')
            (rab : redTmEq (shpRed PA ws afA afB) a b),
        RRCar Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab))
          (redTmEq (posPack PA rab))) ->
    RRCar Ge (dEl (vPi FA BA)) (dEl (vPi FB BB)) (PiRedTmEq PA).

(* ===================================================================== *)
(* WALL DISSOLVED -- the keystone setup step for [RR_pi_at].                 *)
(*                                                                         *)
(* This is the EXACT step the two-typed [NeConv] could not perform (the      *)
(* "[has_svalty] typing-conversion wall"): reflecting the eta bound variable *)
(* [nVar 0] into the DOMAIN pack of a relevant Pi.  Under the two-typed      *)
(* encoding the domain reflect IH demanded [NeConv Delta (dEl FA') (dEl FB') *)
(* (nVar 0) (nVar 0)], i.e. [wf_neutral Delta (nVar 0)] at BOTH [dEl FA']    *)
(* AND [dEl FB'] -- impossible off-diagonal because [n_var] pins ONE context *)
(* type.  With the paper-faithful SINGLE-typed [NeConv] the premise is       *)
(* [NeConv Delta (dEl FA') (nVar 0) (nVar 0)] -- typing at the LEFT domain   *)
(* only ([n_var]) -- yet the IH still delivers BOTH eta reflections          *)
(* ([ARGn] at [dEl FA'], [ARGm] at [dEl FB']) and the domain MEMBER relating *)
(* them, which is precisely what the two-sided eta-expansion construction     *)
(* feeds to [posRed]/[posAd].  No [n_conv] is needed AT THIS STEP; the        *)
(* typing-conversion rule services escape/symmetry, not the variable.        *)
(*                                                                         *)
(* What remains of [RR_pi_at] AFTER this step is the SAME reflect/reify       *)
(* adequacy core the single-sided development reduced to and never closed     *)
(* (port of [reflect_pi_step_from_app] -> [..._beta_step] -> [..._reify_      *)
(* step]): assemble [vLam ARGn]/[vLam ARGm] ([refl_Pi], [t_lam_eta]), then    *)
(* discharge [PiRedTmEq]'s application clause by relating the beta-reduct      *)
(* [body[a::sg]] to the [posAd]-reflection of [nApp (n[sg]) (reify a)] via    *)
(* [Reflect] naturality + [conv_ne] -- the paper's Theorem 11 core (Ph5).     *)
(* That residual is what stays abstract in [RR_pi_at]; the wall that blocked  *)
(* even reaching it is gone. *)
Lemma wf_svalty_pi_dom : forall Ge F B,
    wf_svalty Ge (dEl (vPi F B)) -> wf_svalty Ge (dEl F).
Proof.
  intros Ge F B H. inversion H; subst.
  match goal with He : has_svalty Ge (vPi F B) _ |- _ => inversion He; subst end.
  eapply wf_dEl; eassumption.
Qed.

(* The weakening witnesses [ws0]/[afA0]/[afB0]/[HwfD] are exactly what the
   eta-expansion construction builds at the front-extended context (via
   [wf_ssub_wkn]/[Apply_val_wkn]/[wf_senv_ext], cf. single-sided
   [reflect_pi_step_from_app]); here they are taken as hypotheses so the lemma
   isolates the genuine content -- that the domain IH reflects the bound
   variable from a SINGLE LEFT typing yet returns BOTH eta reflections. *)
Lemma pi_bound_var_reflects :
  forall Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
    (ws0 : wf_ssub (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge)
                   (wkn_list (length Ge)) Ge)
    (afA0 : Apply_val (length (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge))
                      (wkn_list (length Ge)) FA (shift_val 0 1 FA))
    (afB0 : Apply_val (length (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge))
                      (wkn_list (length Ge)) FB (shift_val 0 1 FB))
    (HwfD : wf_senv (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge))
    (IHsh : RRCar (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge)
              (dEl (shift_val 0 1 FA)) (dEl (shift_val 0 1 FB))
              (redTmEq (shpRed PA ws0 afA0 afB0))),
    { ARGn & { ARGm &
      ( Reflect (length (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge))
                (dEl (shift_val 0 1 FA)) (nVar 0) ARGn
      * Reflect (length (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge))
                (dEl (shift_val 0 1 FB)) (nVar 0) ARGm
      * redTmEq (shpRed PA ws0 afA0 afB0) ARGn ARGm )%type } }.
Proof.
  intros Ge FA BA FB BB PA ws0 afA0 afB0 HwfD IHsh.
  (* reflect the bound variable -- typed at the LEFT domain ONLY (the wall step:
     under two-typed [NeConv] this also demanded [nVar 0 : dEl (shift FB)],
     which [n_var] cannot give off-diagonal). *)
  assert (Hvar : NeConv (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge)
                   (dEl (shift_val 0 1 FA)) (nVar 0) (nVar 0)).
  { repeat split; [ apply n_var; reflexivity | apply n_var; reflexivity | apply cne_var ]. }
  destruct (fst (fst (IHsh HwfD)) (nVar 0) (nVar 0) Hvar)
    as [ARGn [ARGm [[Hrn Hrm] rab]]].
  exists ARGn, ARGm. exact ((Hrn, Hrm), rab).
Qed.

(* The irrelevant-Pi case, abstracted: DEFERRED to Ph6 (full OTT).  REFLECT-at-
   [vPiI] is doable (members are just typings, [refl_PiI] identity) but REIFY
   at [vPiI] is NOT expressible against the structural [conv_nf] (no proof-
   irrelevance rule; [LRpiI] also relates the two sides' components by nothing).
   Kept as one abstract premise for the relevant-fragment Theorem 11. *)
Definition RR_piI_at (lvl : TypeLevel) (rec0 rec1 : RedRel) : Type :=
  forall Ge FA BA FB BB
    (wA : wf_svalty Ge (dEl (vPiI FA BA)))
    (wB : wf_svalty Ge (dEl (vPiI FB BB))),
    RRCar Ge (dEl (vPiI FA BA)) (dEl (vPiI FB BB))
      (fun f g => (has_svalty Ge f (dEl (vPiI FA BA))
                 * has_svalty Ge g (dEl (vPiI FB BB)))%type).

(* Universally-quantified premises: ONE proof at all levels discharges the
   whole tower (the relevant-Pi crux / the deferred irrelevant case). *)
Definition RR_pi_step  : Type := forall lvl rec0 rec1, RR_pi_at  lvl rec0 rec1.
Definition RR_piI_step : Type := forall lvl rec0 rec1, RR_piI_at lvl rec0 rec1.

Section RRGen.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).
  Context (HR0 : RecRR1 rec0) (HR1 : RecRR1 rec1).
  Context (HNe0 : NeElBuild lvl tl0 rec0) (HNe1 : NeElBuild lvl tl1 rec1).
  Context (Hpi : RR_pi_at lvl rec0 rec1) (HpiI : RR_piI_at lvl rec0 rec1).

  Lemma RR_gen : forall Ge A B P (H : @LR lvl rec0 rec1 Ge A B P),
      RRCar Ge A B P.
  Proof.
    intros Ge A B P H.
    induction H using LR_mut.
    - (* LRnat : reflection is the identity (refl_Nat) *)
      intros Hwf. split; [ split | ].
      + intros n m c. exists (vNe n), (vNe m). split; [ split | ].
        * apply refl_Nat.
        * apply refl_Nat.
        * apply rne_ne; exact c.
      + intros a b na nb r Hra Hrb.
        eapply Reify_conv_val; [ exact Hra | | exact (reify_nat r) | exact Hrb ].
        cbn; apply cnf_nat.
      + exact cnf_nat.
    - (* LRempty : reflection is the identity (refl_Empty) *)
      intros Hwf. split; [ split | ].
      + intros n m c. exists (vNe n), (vNe m). split; [ split | ].
        * apply refl_Empty.
        * apply refl_Empty.
        * apply rneT; exact c.
      + intros a b na nb r Hra Hrb.
        eapply Reify_conv_val; [ exact Hra | | exact (reify_neutral r) | exact Hrb ].
        cbn; apply cnf_empty.
      + exact cnf_empty.
    - (* LRne : base neutral element type (refl_neEl identity) *)
      match goal with H : NeConv _ _ _ _ |- _ => rename H into cne end.
      intros Hwf. split; [ split | ].
      + intros p q c. exists (vNe p), (vNe q). split; [ split | ].
        * apply refl_neEl.
        * apply refl_neEl.
        * apply rneT; exact c.
      + intros a b na nb r0 Hra Hrb.
        eapply Reify_conv_val; [ exact Hra | | exact (reify_neutral r0) | exact Hrb ].
        cbn. apply cnf_ne. exact (snd cne).
      + cbn. apply cnf_ne. exact (snd cne).
    - (* LRpiI : DEFERRED (irrelevant fragment) *)
      apply HpiI; assumption.
    - (* LRpi : the relevant-Pi mutual KNOT *)
      apply Hpi; assumption.
    - (* LRU0 : codes at a level-0 universe (refl_U identity) *)
      intros Hwf. split; [ split | ].
      + intros n m c. exists (vNe n), (vNe m). split; [ split | ].
        * apply refl_U.
        * apply refl_U.
        * repeat split.
          -- apply t_ne. exact (fst (fst c)).
          -- apply t_ne. exact (snd (fst c)).
          -- exact (HNe0 h c).
      + intros c d nc nd Hcd Hrc Hrd. destruct Hcd as [_ [P0 Hrec]].
        inversion Hrc; subst. inversion Hrd; subst.
        eapply ReifyTy_conv; [ eassumption | exact (snd (HR0 Hrec Hwf)) | eassumption ].
      + exact tt.
    - (* LRU1 : codes at a level-1 universe (refl_U identity) *)
      intros Hwf. split; [ split | ].
      + intros n m c. exists (vNe n), (vNe m). split; [ split | ].
        * apply refl_U.
        * apply refl_U.
        * repeat split.
          -- apply t_ne. exact (fst (fst c)).
          -- apply t_ne. exact (snd (fst c)).
          -- exact (HNe1 h c).
      + intros c d nc nd Hcd Hrc Hrd. destruct Hcd as [_ [P0 Hrec]].
        inversion Hrc; subst. inversion Hrd; subst.
        eapply ReifyTy_conv; [ eassumption | exact (snd (HR1 Hrec Hwf)) | eassumption ].
      + exact tt.
  Qed.

End RRGen.

(* ===================================================================== *)
(* Finite-tower instantiation (mirrors [LogRel2Sym]'s [LRbot]/[LR0]/[LR1]).  *)
(* ===================================================================== *)

(* [LRbot] is vacuous, so reify/reflect hold for it trivially. *)
Definition RRbot : RecRR1 LRbot.
Proof. intros Ge A B P H; destruct H. Qed.

(* A neutral-[El] reducibility builder at ANY level/delegate ([LRne] is level-
   agnostic): the substantive content of universe-reflect. *)
Definition NeElBuild_LR (lvlg lt lvl : TypeLevel) (rec0 rec1 : RedRel)
  : NeElBuild lvlg lt (@LR lvl rec0 rec1) :=
  fun Ge n m r l _ c =>
    existT _ (RedNeutralEq Ge (dEl (vNe n)))
           (@LRne lvl rec0 rec1 Ge n m r l c).

(* Vacuous builder for the OFF tower slots: the level guard is uninhabited. *)
Definition NeElBuild_vac (lvl lt : TypeLevel) (rec : RedRel)
  (no : TLlt lt lvl -> False) : NeElBuild lvl lt rec :=
  fun Ge n m r l h _ => False_rect _ (no h).

Lemma TLlt_t0_t0 : TLlt tl0 tl0 -> False. Proof. inversion 1. Qed.
Lemma TLlt_t1_t0 : TLlt tl1 tl0 -> False. Proof. inversion 1. Qed.
Lemma TLlt_t1_t1 : TLlt tl1 tl1 -> False. Proof. inversion 1. Qed.

(* The tower instances are written as [fun]-bodies (not explicit applications)
   so the bound [H : LR<k> ...] drives universe inference -- writing [LR0]/[LR1]
   explicitly in two positions would create mismatched polymorphic instances
   (same alignment discipline as [LogRel2Sym]'s [LR0_sym]/[LR1_sym]). *)
Definition RR0 (Hpi : RR_pi_step) (HpiI : RR_piI_step) : RecRR1 LR0 :=
  fun Ge A B P H =>
    RR_gen RRbot RRbot
      (@NeElBuild_vac _ _ _ TLlt_t0_t0)
      (@NeElBuild_vac _ _ _ TLlt_t1_t0)
      (Hpi _ _ _) (HpiI _ _ _) H.

(* RR0 closes the LEVEL-0 instance (rec0 = rec1 = LRbot): the abstract Pi
   premise [Hpi _ _ _] is applied at the trivial bottom universes, so the
   monomorphic bound [Hpi] aligns.  This is genuine Theorem 11 at [LR0]
   (modulo [Hpi]/[HpiI]). *)

(* ===================================================================== *)
(* UNIVERSE FINDING (2026-06-06) -- why [RR1]/[RR2] (and the top-level        *)
(* user [reflect_red]/[reify_tm]/[reify_ty]) are NOT closed from an ABSTRACT  *)
(* premise.                                                                  *)
(*                                                                          *)
(* The finite tower is UNIVERSE-POLYMORPHIC (LR0/LR1/LR2 are distinct        *)
(* polymorphic instances of [LR], the whole point of the unfolded encoding). *)
(* Closing [RR1] needs [RR_gen] at [rec0 := LR0]; that single [rec0] must be  *)
(* the SAME instance both in [HR0 : RecRR1 LR0] (= [RR0 ...], a poly constant *)
(* -> flexible) AND in the Pi premise [Hpi _ _ _ : RR_pi_at tl1 LR0 LRbot].   *)
(* But [Hpi : RR_pi_step] is a BOUND hypothesis: a bound variable is          *)
(* MONOMORPHIC, so [Hpi _ _ _] is pinned to [Hpi]'s binding universes and     *)
(* cannot be re-instantiated at [LR0]'s tower universes -> rigid-vs-rigid     *)
(* universe clash (Coq: "RR_pi_at@{..} <> RR_pi_at@{..}").  [RR0] dodges this *)
(* only because its [rec0 = LRbot] carries trivial universes.                 *)
(*                                                                          *)
(* CONSEQUENCE: the tower closes ONLY when the relevant-Pi case is a genuine  *)
(* POLYMORPHIC LEMMA (freshly instantiated per level), i.e. once the crux     *)
(* [RR_pi_at] is PROVEN (axiom-free) rather than assumed.  So discharging     *)
(* [RR_pi_at] (the eta-expansion mutual knot) is BOTH the mathematical crux   *)
(* AND the unblocker for [RR1]/[RR2]/[reflect_red]/[reify_tm]/[reify_ty];     *)
(* there is no separate universe refactor to do.  [RR_gen] + [RR0] are the    *)
(* green, axiom-free engine that the proven crux plugs straight into.         *)
(* ===================================================================== *)
(* Level-generic escape: a [P]-member at ANY [@LR lvl rec0 rec1] node is
   well-typed at both type indices.  ([RedTmEq_wf] is the [LR2] specialization;
   the recursive [LRU0]/[LRU1] cases only read typing off the code pair, so the
   proof is level-uniform.) *)
Lemma RedTmEq_wf_gen : forall lvl rec0 rec1 Ge A B a b (P : sval -> sval -> Type),
    @LR lvl rec0 rec1 Ge A B P -> P a b ->
    (has_svalty Ge a A * has_svalty Ge b B)%type.
Proof.
  intros lvl rec0 rec1 Ge A B a b P H Pab; destruct H.
  - exact (RedNatEq_wf Pab).
  - exact (RedNeutralEq_wf Pab).
  - match goal with c : NeConv _ (dU _ _) _ _ |- _ => rename c into cnm end.
    destruct Pab as [p q [[wp wq] _]]; split.
    + apply t_ne; exact wp.
    + apply t_ne. eapply n_conv; [ exact wq | apply cnf_ne; exact (snd cnm) ].
  - destruct Pab as [Hf Hg]; split; assumption.
  - destruct Pab as [[[Hf Hg] _] _]; split; assumption.
  - destruct Pab as [[Hc Hd] _]; split; assumption.
  - destruct Pab as [[Hc Hd] _]; split; assumption.
Qed.

(* ===================================================================== *)
(* CONTEXT CONVERSION: typing is stable under replacing context entries by   *)
(* [conv_nf]-related ones.  Needed two-sided: the RIGHT eta-body is produced  *)
(* in the LEFT-domain context [dEl (shift FA) :: ..] but [t_lam_eta] for the  *)
(* RIGHT Pi types it in [dEl (shift FB) :: ..]; the two differ only at the    *)
(* (convertible) front domain.                                                *)
(* ===================================================================== *)
Inductive conv_ctx : senv -> senv -> Type :=
| cc_nil : conv_ctx nil nil
| cc_dEl : forall A A' G G', conv_nf A A' -> conv_ctx G G' ->
    conv_ctx (dEl A :: G) (dEl A' :: G')
| cc_dU  : forall r l G G', conv_ctx G G' ->
    conv_ctx (dU r l :: G) (dU r l :: G').

Lemma conv_ctx_refl : forall G, conv_ctx G G.
Proof.
  induction G as [|[r l|A] G IH].
  - apply cc_nil.
  - apply cc_dU; exact IH.
  - apply cc_dEl; [ exact (fst (snd conv_refl) A) | exact IH ].
Qed.

Lemma conv_ctx_length : forall G G', conv_ctx G G' -> length G = length G'.
Proof. intros G G' c; induction c; cbn; auto. Qed.

Lemma conv_ctx_map_shift : forall G G', conv_ctx G G' ->
    conv_ctx (map (shift_ty 0 1) G) (map (shift_ty 0 1) G').
Proof.
  intros G G' c; induction c; cbn [map].
  - apply cc_nil.
  - apply cc_dEl; [ apply conv_nf_shift; assumption | assumption ].
  - apply cc_dU; assumption.
Qed.

Lemma conv_ctx_nth : forall G G' (c : conv_ctx G G') k T,
    nth_error G k = Some T ->
    { T' & ((nth_error G' k = Some T')
            * (forall Gx nn, wf_neutral Gx nn T' -> wf_neutral Gx nn T))%type }.
Proof.
  intros G G' c; induction c; intros k T He.
  - destruct k; cbn in He; discriminate He.
  - destruct k; cbn in He.
    + injection He as He; subst T. exists (dEl A'); split; [ reflexivity | ].
      intros Gx nn h. eapply n_conv; [ exact h | apply conv_nf_sym; assumption ].
    + destruct (IHc _ _ He) as [T' [He' back]]. exists T'; split; assumption.
  - destruct k; cbn in He.
    + injection He as He; subst T. exists (dU r l); split; [ reflexivity | ].
      intros Gx nn h; exact h.
    + destruct (IHc _ _ He) as [T' [He' back]]. exists T'; split; assumption.
Qed.

Lemma typing_ctx_conv :
  (forall G v T, has_svalty G v T -> forall G', conv_ctx G G' -> has_svalty G' v T)
  * (forall G n T, wf_neutral G n T -> forall G', conv_ctx G G' -> wf_neutral G' n T).
Proof.
  apply (has_neutral_mutind
    (fun G v T (_ : has_svalty G v T) => forall G', conv_ctx G G' -> has_svalty G' v T)
    (fun G n T (_ : wf_neutral G n T) => forall G', conv_ctx G G' -> wf_neutral G' n T)).
  - (* t_ne *) intros Ge n T Hn IH G' c. apply t_ne; apply IH; exact c.
  - (* t_zero *) intros Ge G' c. apply t_zero.
  - (* t_suc *) intros Ge v Hv IH G' c. apply t_suc; apply IH; exact c.
  - (* t_Nat *) intros Ge r l G' c. apply t_Nat.
  - (* t_Empty *) intros Ge r l G' c. apply t_Empty.
  - (* t_Pi *) intros Ge F B rF lF rB lB r l HF IHF HB IHB G' c.
    eapply t_Pi; [ apply IHF; exact c | apply IHB; apply cc_dEl;
      [ exact (fst (snd conv_refl) (shift_val 0 1 F)) | apply conv_ctx_map_shift; exact c ] ].
  - (* t_PiI *) intros Ge F B rF lF rB lB r l HF IHF HB IHB G' c.
    eapply t_PiI; [ apply IHF; exact c | apply IHB; apply cc_dEl;
      [ exact (fst (snd conv_refl) (shift_val 0 1 F)) | apply conv_ctx_map_shift; exact c ] ].
  - (* t_lam *) intros Ge F B b rF lF HF IHF Hb IHb G' c.
    eapply t_lam; [ apply IHF; exact c | apply IHb; apply cc_dEl;
      [ exact (fst (snd conv_refl) (shift_val 0 1 F)) | apply conv_ctx_map_shift; exact c ] ].
  - (* t_lamI *) intros Ge F B b rF lF HF IHF Hb IHb G' c.
    eapply t_lamI; [ apply IHF; exact c | apply IHb; apply cc_dEl;
      [ exact (fst (snd conv_refl) (shift_val 0 1 F)) | apply conv_ctx_map_shift; exact c ] ].
  - (* t_lam_eta *) intros Ge F B b ARG B' rF lF HF IHF HR Hap Hb IHb G' c.
    pose proof (conv_ctx_length c) as HLc.
    rewrite HLc in HR, Hap.
    eapply t_lam_eta; [ apply IHF; exact c | exact HR | exact Hap | ].
    apply IHb. apply cc_dEl;
      [ exact (fst (snd conv_refl) (shift_val 0 1 F)) | apply conv_ctx_map_shift; exact c ].
  - (* n_var *) intros Ge k T He G' c.
    destruct (@conv_ctx_nth Ge G' c k T He) as [T' [He' back]].
    apply back. apply n_var; exact He'.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l HA IHA Hs IHs G' c.
    eapply n_emptyrec; [ apply IHA; exact c | apply IHs; exact c ].
  - (* n_app *) intros Ge f F B a B' Hf IHf Ha IHa Hap G' c.
    pose proof (conv_ctx_length c) as HLc. rewrite HLc in Hap.
    eapply n_app; [ apply IHf; exact c | apply IHa; exact c | exact Hap ].
  - (* n_appI *) intros Ge f F B a B' Hf IHf Ha IHa Hap G' c.
    pose proof (conv_ctx_length c) as HLc. rewrite HLc in Hap.
    eapply n_appI; [ apply IHf; exact c | apply IHa; exact c | exact Hap ].
  - (* n_conv *) intros Ge n A B Hn IH cAB G' c.
    eapply n_conv; [ apply IH; exact c | exact cAB ].
Qed.

(* ===================================================================== *)
(* DEV: discharging RR_pi_at modulo the reify/reflect adequacy core.       *)
(* ===================================================================== *)
Section RRPiDev.
  Context (lvl : TypeLevel) (rec0 rec1 : RedRel).
  Context (Ge : senv) (FA BA FB BB : sval) (PA : PolyRedPack Ge FA BA FB BB).
  Context (wpiA : wf_svalty Ge (dEl (vPi FA BA))).
  Context (wpiB : wf_svalty Ge (dEl (vPi FB BB))).
  Context (ad : PolyRedPackAdequate (@LR lvl rec0 rec1) PA).
  Context (domIH : forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
            (afA : Apply_val (length Delta) sg FA FA')
            (afB : Apply_val (length Delta) sg FB FB'),
        RRCar Delta (dEl FA') (dEl FB') (redTmEq (shpRed PA ws afA afB))).
  Context (posIH : forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
            (afA : Apply_val (length Delta) sg FA FA')
            (afB : Apply_val (length Delta) sg FB FB')
            (rab : redTmEq (shpRed PA ws afA afB) a b),
        RRCar Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab))
          (redTmEq (posPack PA rab))).
  Context (Hwf : wf_senv Ge).

  (* Domain reify-ty leaf: conv of the (unsubstituted) domain codes via the
     domain IH at the identity substitution. *)
  Lemma dom_reify_ty : conv_nf FA FB.
  Proof.
    pose proof (@domIH Ge (id_list (length Ge)) FA FB
       (@wf_ssub_id Ge Hwf) (Apply_val_id FA (length Ge)) (Apply_val_id FB (length Ge))) as H.
    exact (snd (H Hwf)).
  Qed.

  (* --- Scoping of the two Pi codes (from wf_svalty). --- *)
  Lemma sc_A : (ne_below_val (length Ge) FA * ne_below_val (S (length Ge)) BA)%type.
  Proof.
    pose proof (wf_svalty_scoped wpiA) as H. cbn [ne_below_ty ne_below_val] in H.
    destruct H as [HF HB]; split; assumption.
  Qed.
  Lemma sc_B : (ne_below_val (length Ge) FB * ne_below_val (S (length Ge)) BB)%type.
  Proof.
    pose proof (wf_svalty_scoped wpiB) as H. cbn [ne_below_ty ne_below_val] in H.
    destruct H as [HF HB]; split; assumption.
  Qed.

  (* --- The front-extended context and its weakening data.  [Dlt] is a
     NOTATION (not a Definition) so [length Dlt] is syntactically the unfolded
     [length (dEl .. :: map .. Ge)] everywhere, and one [HL] rewrite matches
     uniformly (no fold/unfold split). --- *)
  Notation Dlt := (dEl (shift_val 0 1 FA) :: map (shift_ty 0 1) Ge).

  Lemma HL : length Dlt = S (length Ge).
  Proof. cbn [length]; f_equal; apply length_map. Qed.

  Lemma HwfD : wf_senv Dlt.
  Proof.
    pose proof (wf_senv_ext Hwf (wf_svalty_pi_dom wpiA)) as H.
    cbn [shift_ty] in H. exact H.
  Qed.

  Lemma ws0 : wf_ssub Dlt (wkn_list (length Ge)) Ge.
  Proof. exact (@wf_ssub_wkn Ge (dEl (shift_val 0 1 FA)) Hwf). Qed.

  Lemma afA0 : Apply_val (length Dlt) (wkn_list (length Ge)) FA (shift_val 0 1 FA).
  Proof. rewrite HL. apply Apply_val_wkn. exact (fst sc_A). Qed.

  Lemma afB0 : Apply_val (length Dlt) (wkn_list (length Ge)) FB (shift_val 0 1 FB).
  Proof. rewrite HL. apply Apply_val_wkn. exact (fst sc_B). Qed.

  (* The codomain reify-ty for the RAW codes -- the genuine reify/reflect
     adequacy residual (the substitution that produced posTyA/posTyB from
     BA/BB is the bound-var eta-expansion, NOT a renaming, for higher-order
     domains; see WIP/ReifyDev.v).  Shared by REFLECT and REIFY-ty. *)
  Context (Hcod : conv_nf BA BB).

  (* Domain typing premises of [t_lam_eta], recovered from the Pi codes. *)
  Lemma tyFA : exists rF lF, has_svalty Ge FA (dU rF lF).
  Proof.
    inversion wpiA; subst.
    match goal with He : has_svalty Ge (vPi FA BA) _ |- _ => inversion He; subst end.
    eexists; eexists; eassumption.
  Qed.
  Lemma tyFB : exists rF lF, has_svalty Ge FB (dU rF lF).
  Proof.
    inversion wpiB; subst.
    match goal with He : has_svalty Ge (vPi FB BB) _ |- _ => inversion He; subst end.
    eexists; eexists; eassumption.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* The eta-expansion construction: from a [NeConv]-related pair at the     *)
  (* LEFT Pi, build the two eta-long bodies and the codomain member.         *)
  (* --------------------------------------------------------------------- *)
  Lemma eta_bodies :
    forall n m (wn : wf_neutral Ge n (dEl (vPi FA BA)))
               (wm : wf_neutral Ge m (dEl (vPi FA BA)))
               (cnm : conv_ne n m),
    { ARGn & { ARGm & { body_n & { body_m & { rab : redTmEq (shpRed PA ws0 afA0 afB0) ARGn ARGm &
      ( Reflect (length Ge) (dEl (vPi FA BA)) n (vLam body_n)
      * Reflect (length Ge) (dEl (vPi FB BB)) m (vLam body_m)
      * has_svalty Ge (vLam body_n) (dEl (vPi FA BA))
      * has_svalty Ge (vLam body_m) (dEl (vPi FB BB))
      * redTmEq (posPack PA rab) body_n body_m
      * Reflect (S (length Ge)) (dEl (posTyA PA rab))
          (nApp (shift_ne 0 1 n) (shift_val 0 1 FA) (shift_val 1 1 BA) ARGn) body_n
      * Reflect (S (length Ge)) (dEl (posTyB PA rab))
          (nApp (shift_ne 0 1 m) (shift_val 0 1 FB) (shift_val 1 1 BB) ARGm) body_m )%type } } } } }.
  Proof.
    intros n m wn wm cnm.
    (* bound-variable reflection + domain member *)
    destruct (pi_bound_var_reflects PA ws0 afA0 afB0 HwfD
                (@domIH Dlt (wkn_list (length Ge)) (shift_val 0 1 FA) (shift_val 0 1 FB)
                       ws0 afA0 afB0))
      as [ARGn [ARGm [[Hargn Hargm] rab]]].
    (* domain reducibility witnesses, for RedTmEq_wf packaging *)
    pose proof (shpAd ad ws0 afA0 afB0) as domAd.
    pose proof (@RedTmEq_wf_gen lvl rec0 rec1 Dlt (dEl (shift_val 0 1 FA))
                  (dEl (shift_val 0 1 FB)) ARGn ARGm _ domAd rab) as [HtyARGn HtyARGm].
    (* domain RRCar (for reify-tm of ARGn ~ ARGm) *)
    pose proof (@domIH Dlt (wkn_list (length Ge)) (shift_val 0 1 FA) (shift_val 0 1 FB)
                  ws0 afA0 afB0 HwfD) as domRR.
    (* codomain RRCar at this domain member *)
    pose proof (@posIH Dlt (wkn_list (length Ge)) ARGn ARGm
                  (shift_val 0 1 FA) (shift_val 0 1 FB) ws0 afA0 afB0 rab HwfD) as posRR.
    (* codomain reify-ty: conv_nf (posTyA) (posTyB) *)
    pose proof (snd posRR) as HcodConv.
    (* codomain Apply witnesses (cleanly at [S (length Ge)] via pre-rewritten
       domain-applied witnesses), lifted via [Apply_reflect_cod] *)
    pose proof (posAppA PA rab) as HAppA; rewrite HL in HAppA.
    pose proof (posAppB PA rab) as HAppB; rewrite HL in HAppB.
    pose proof (Apply_reflect_cod (snd sc_A) HAppA) as HcodSA.
    pose proof (Apply_reflect_cod (snd sc_B) HAppB) as HcodSB.
    (* LEFT eta-body neutral, typed at dEl (posTyA) *)
    assert (HnL : wf_neutral Dlt (shift_ne 0 1 n)
                    (dEl (vPi (shift_val 0 1 FA) (shift_val 1 1 BA)))).
    { pose proof (snd shift_typing Ge n (dEl (vPi FA BA)) wn (dEl (shift_val 0 1 FA))) as H.
      cbn [shift_ty shift_val] in H. exact H. }
    assert (HbL : wf_neutral Dlt
              (nApp (shift_ne 0 1 n) (shift_val 0 1 FA) (shift_val 1 1 BA) ARGn)
              (dEl (posTyA PA rab))).
    { eapply n_app; [ exact HnL | exact HtyARGn | ].
      rewrite HL. exact HcodSA. }
    (* RIGHT eta-body neutral: type at dEl (posTyB) then n_conv to dEl (posTyA) *)
    assert (HnR : wf_neutral Dlt (shift_ne 0 1 m)
                    (dEl (vPi (shift_val 0 1 FB) (shift_val 1 1 BB)))).
    { pose proof (snd shift_typing Ge m (dEl (vPi FA BA)) wm (dEl (shift_val 0 1 FA))) as H.
      cbn [shift_ty shift_val] in H.
      eapply n_conv; [ exact H | ].
      apply cnf_pi; apply conv_nf_shift; [ exact dom_reify_ty | exact Hcod ]. }
    assert (HbR0 : wf_neutral Dlt
              (nApp (shift_ne 0 1 m) (shift_val 0 1 FB) (shift_val 1 1 BB) ARGm)
              (dEl (posTyB PA rab))).
    { eapply n_app; [ exact HnR | exact HtyARGm | ].
      rewrite HL. exact HcodSB. }
    assert (HbR : wf_neutral Dlt
              (nApp (shift_ne 0 1 m) (shift_val 0 1 FB) (shift_val 1 1 BB) ARGm)
              (dEl (posTyA PA rab))).
    { eapply n_conv; [ exact HbR0 | apply conv_nf_sym; exact HcodConv ]. }
    (* conv_ne of the two eta-bodies *)
    assert (HceB : conv_ne
              (nApp (shift_ne 0 1 n) (shift_val 0 1 FA) (shift_val 1 1 BA) ARGn)
              (nApp (shift_ne 0 1 m) (shift_val 0 1 FB) (shift_val 1 1 BB) ARGm)).
    { apply cne_app.
      - apply conv_ne_shift; exact cnm.
      - apply conv_nf_shift; exact dom_reify_ty.
      - apply conv_nf_shift; exact Hcod.
      - eapply Reflect_conv with (TB := dEl (shift_val 0 1 FB));
          [ exact Hargn | cbn; apply conv_nf_shift; exact dom_reify_ty
          | apply cne_var | exact Hargm ]. }
    (* reflect both eta-bodies via the codomain REFLECT *)
    destruct (fst (fst posRR) _ _ ((HbL, HbR), HceB))
      as [body_n [body_m [[Hbody_n Hbody_m] rbody]]].
    (* package the codomain members for t_lam_eta typing *)
    pose proof (posAd ad ws0 afA0 afB0 rab) as posAdq.
    pose proof (@RedTmEq_wf_gen lvl rec0 rec1 Dlt (dEl (posTyA PA rab))
                  (dEl (posTyB PA rab)) body_n body_m _ posAdq rbody) as [Htybn Htybm].
    (* convert the bound-var / eta-body reflections to [S (length Ge)] *)
    rewrite HL in Hargn, Hargm, Hbody_n, Hbody_m.
    exists ARGn, ARGm, body_n, body_m, rab.
    split; [ split; [ split; [ split; [ split; [ split | ] | ] | ] | ] | ].
    - (* Reflect n (vLam body_n) at the LEFT Pi *)
      eapply refl_Pi; [ exact Hargn | exact HAppA | exact Hbody_n ].
    - (* Reflect m (vLam body_m) at the RIGHT Pi *)
      eapply refl_Pi; [ exact Hargm | exact HAppB | exact Hbody_m ].
    - (* has_svalty Ge (vLam body_n) (dEl (vPi FA BA)) via t_lam_eta *)
      destruct tyFA as [rF [lF HtyF]].
      eapply t_lam_eta; [ exact HtyF | exact Hargn | exact HcodSA | exact Htybn ].
    - (* has_svalty Ge (vLam body_m) (dEl (vPi FB BB)) via t_lam_eta.  The body
         [body_m] was reflected in the LEFT-domain context [dEl (shift FA) :: ..]
         but [t_lam_eta] for the RIGHT Pi needs it in [dEl (shift FB) :: ..];
         bridge by context conversion ([conv_nf FA FB] = [dom_reify_ty]). *)
      destruct tyFB as [rF [lF HtyF]].
      eapply t_lam_eta; [ exact HtyF | exact Hargm | exact HcodSB | ].
      eapply (fst typing_ctx_conv _ _ _ Htybm).
      apply cc_dEl; [ apply conv_nf_shift; exact dom_reify_ty | apply conv_ctx_refl ].
    - exact rbody.
    - exact Hbody_n.
    - exact Hbody_m.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* The GENUINE residuals -- the reify/reflect adequacy core (the VR-layer  *)
  (* effort; see WIP/ReifyDev.v and ConvRelPlan).  Everything ELSE in the    *)
  (* relevant-Pi case of Theorem 11 is discharged axiom-free above/below.    *)
  (* --------------------------------------------------------------------- *)

  (* (R2) REIFY-tm: reducibly-convertible function members read back to       *)
  (* [conv_nf] (needs casing on the members + the codomain reify IH).         *)
  Lemma reify_tm_pi : forall a b na nb, PiRedTmEq PA a b ->
              Reify (length Ge) (dEl (vPi FA BA)) a na ->
              Reify (length Ge) (dEl (vPi FB BB)) b nb -> conv_nf na nb.
  Proof.
    intros a b na nb Hab Hra Hrb.
    assert (Hctx : ne_below_ctx Ge) by (intros k T HT; exact (wf_svalty_scoped (Hwf k HT))).
    destruct Hab as [[[Hta Htb] [[ba Ea] [bb Eb]]] Happm]. subst a b.
    inversion Hra; subst.
    inversion Hrb; subst.
    apply cnf_lam.
    destruct (pi_bound_var_reflects PA ws0 afA0 afB0 HwfD
                (@domIH Dlt (wkn_list (length Ge)) (shift_val 0 1 FA) (shift_val 0 1 FB)
                       ws0 afA0 afB0))
      as [ARGn [ARGm [[Hargn Hargm] rab]]].
    rewrite HL in Hargn, Hargm.
    pose proof (Reflect_det Hargn X) as HeqA; subst ARG.
    pose proof (Reflect_det Hargm X3) as HeqB; subst ARG0.
    assert (afBA : Apply_val (S (length Dlt)) (up (wkn_list (length Ge))) BA (shift_val 1 1 BA))
      by (rewrite <- shsub_0; rewrite up_shsub; rewrite HL; apply Apply_val_shift_eq; exact (snd sc_A)).
    assert (afBB : Apply_val (S (length Dlt)) (up (wkn_list (length Ge))) BB (shift_val 1 1 BB))
      by (rewrite <- shsub_0; rewrite up_shsub; rewrite HL; apply Apply_val_shift_eq; exact (snd sc_B)).
    assert (afsf : Apply_val (length Dlt) (wkn_list (length Ge)) (vLam ba) (shift_val 0 1 (vLam ba)))
      by (rewrite HL; apply Apply_val_wkn; exact (has_svalty_ne_below Hta Hctx)).
    assert (afsg : Apply_val (length Dlt) (wkn_list (length Ge)) (vLam bb) (shift_val 0 1 (vLam bb)))
      by (rewrite HL; apply Apply_val_wkn; exact (has_svalty_ne_below Htb Hctx)).
    destruct (Happm Dlt (wkn_list (length Ge)) ARGn ARGm
                (shift_val 0 1 FA) (shift_val 0 1 FB) (shift_val 1 1 BA) (shift_val 1 1 BB)
                (shift_val 0 1 (vLam ba)) (shift_val 0 1 (vLam bb))
                ws0 (RenSubst.is_ren_wkn _) afA0 afB0 afBA afBB afsf afsg rab)
      as [v [w [[HVv HVw] rvw]]].
    rewrite HL in HVv, HVw.
    pose proof (Vapp_det HVv X1) as Hv; subst v.
    pose proof (Vapp_det HVw X5) as Hw; subst w.
    pose proof (@posIH Dlt (wkn_list (length Ge)) ARGn ARGm (shift_val 0 1 FA) (shift_val 0 1 FB)
                  ws0 afA0 afB0 rab HwfD) as posRR.
    pose proof (posAppA PA rab) as HposA. rewrite HL in HposA.
    pose proof (Apply_val_det HposA X0) as HeqBA.
    pose proof (posAppB PA rab) as HposB. rewrite HL in HposB.
    pose proof (Apply_val_det HposB X4) as HeqBB.
    rewrite <- HeqBA in X2. rewrite <- HL in X2.
    rewrite <- HeqBB in X6. rewrite <- HL in X6.
    exact (snd (fst posRR) fa fa0 body body0 rvw X2 X6).
  Qed.

  (* (R3) The eta-expansion's APPLICATION CLAUSE: for the two eta-long bodies *)
  (* produced by [eta_bodies], the substituted-and-applied lambdas reduce to  *)
  (* codomain-convertible values.  This is the two-sided analog of the        *)
  (* single-sided [reflect_pi_app_step] -- the beta-reduct / RedSub-closure   *)
  (* adequacy that the single-sided development reduced to and never closed.   *)
  Definition RR_app2 : Type :=
    forall n m ARGn ARGm body_n body_m
      (rab : redTmEq (shpRed PA ws0 afA0 afB0) ARGn ARGm)
      (Hbn : Reflect (S (length Ge)) (dEl (posTyA PA rab))
               (nApp (shift_ne 0 1 n) (shift_val 0 1 FA) (shift_val 1 1 BA) ARGn) body_n)
      (Hbm : Reflect (S (length Ge)) (dEl (posTyB PA rab))
               (nApp (shift_ne 0 1 m) (shift_val 0 1 FB) (shift_val 1 1 BB) ARGm) body_m)
      (rbody : redTmEq (posPack PA rab) body_n body_m),
    forall Delta sg a b FA' FB' BA' BB' fsg gsg
      (ws : wf_ssub Delta sg Ge) (rn : is_ren sg)
      (afA : Apply_val (length Delta) sg FA FA')
      (afB : Apply_val (length Delta) sg FB FB')
      (afBA : Apply_val (S (length Delta)) (up sg) BA BA')
      (afBB : Apply_val (S (length Delta)) (up sg) BB BB')
      (afsf : Apply_val (length Delta) sg (vLam body_n) fsg)
      (afsg : Apply_val (length Delta) sg (vLam body_m) gsg)
      (rab' : redTmEq (shpRed PA ws afA afB) a b),
      { v & { w & ( Vapp (length Delta) FA' BA' fsg a v
                  * Vapp (length Delta) FB' BB' gsg b w
                  * redTmEq (posPack PA rab') v w )%type } }.
  Context (Happ : RR_app2).

  (* The relevant-Pi case of Theorem 11, MODULO the two residuals [Hcod] (R1)
     and [Happ] (R3).  (R2) reify-tm is now PROVEN axiom-free above
     ([reify_tm_pi]).  All the eta-expansion construction, both [t_lam_eta]
     typings, the context-conversion bridge, the domain reify-ty, and the
     Pi-code reify-ty are discharged. *)
  Lemma RR_pi_case : RRCar Ge (dEl (vPi FA BA)) (dEl (vPi FB BB)) (PiRedTmEq PA).
  Proof.
    intros _. split; [ split | ].
    - (* REFLECT *)
      intros n m Hnm. destruct Hnm as [[wn wm] cnm].
      destruct (eta_bodies wn wm cnm)
        as [ARGn [ARGm [body_n [body_m [rab
             [[[[[[Hrefn Hrefm] Htyn] Htym] rbody] Hbn] Hbm]]]]]].
      exists (vLam body_n), (vLam body_m). split; [ split | ].
      + exact Hrefn.
      + exact Hrefm.
      + (* the [P]-member [PiRedTmEq PA (vLam body_n) (vLam body_m)]: the two
           [is_lam] gates are trivial since the eta-expansion yields lambdas. *)
        refine (((_, _), (_, _)), _).
        * exact Htyn.
        * exact Htym.
        * eexists; reflexivity.
        * eexists; reflexivity.
        * exact (@Happ n m ARGn ARGm body_n body_m rab Hbn Hbm rbody).
    - (* REIFY-tm *) exact reify_tm_pi.
    - (* REIFY-ty *) cbn. apply cnf_pi; [ exact dom_reify_ty | exact Hcod ].
  Qed.

End RRPiDev.

(* ===================================================================== *)
(* PACKAGING: [RR_pi_at] (the abstract relevant-Pi premise of [RR_gen])      *)
(* reduced to the three reify/reflect-adequacy residuals.                    *)
(* ===================================================================== *)

(* The residual relevant-Pi obligation: at every Pi node, given the two IHs   *)
(* and [wf_senv], supply (R1) the codomain reify-ty [conv_nf BA BB] and (R3)  *)
(* the eta-expansion application clause.  ((R2) reify-tm is now PROVEN inside  *)
(* [RR_pi_case] via [reify_tm_pi].)  These are the genuine VR-layer core (see  *)
(* ReifyDev.v); EVERYTHING else in the relevant-Pi case is discharged by       *)
(* [RR_pi_case]. *)
Definition RR_pi_res (lvl : TypeLevel) (rec0 rec1 : RedRel) : Type :=
  forall Ge FA BA FB BB (PA : PolyRedPack Ge FA BA FB BB)
    (wpiA : wf_svalty Ge (dEl (vPi FA BA)))
    (wpiB : wf_svalty Ge (dEl (vPi FB BB)))
    (ad : PolyRedPackAdequate (@LR lvl rec0 rec1) PA)
    (domIH : forall Delta sg FA' FB' (ws : wf_ssub Delta sg Ge)
            (afA : Apply_val (length Delta) sg FA FA')
            (afB : Apply_val (length Delta) sg FB FB'),
        RRCar Delta (dEl FA') (dEl FB') (redTmEq (shpRed PA ws afA afB)))
    (posIH : forall Delta sg a b FA' FB' (ws : wf_ssub Delta sg Ge)
            (afA : Apply_val (length Delta) sg FA FA')
            (afB : Apply_val (length Delta) sg FB FB')
            (rab : redTmEq (shpRed PA ws afA afB) a b),
        RRCar Delta (dEl (posTyA PA rab)) (dEl (posTyB PA rab))
          (redTmEq (posPack PA rab)))
    (Hwf : wf_senv Ge),
    ( conv_nf BA BB
    * RR_app2 PA wpiA wpiB Hwf )%type.

Lemma RR_pi_at_from_res : forall lvl rec0 rec1,
    RR_pi_res lvl rec0 rec1 -> RR_pi_at lvl rec0 rec1.
Proof.
  intros lvl rec0 rec1 Hres Ge FA BA FB BB PA wpiA wpiB ad domIH posIH Hwf.
  destruct (Hres Ge FA BA FB BB PA wpiA wpiB ad domIH posIH Hwf)
    as [Hcod Happ].
  exact (@RR_pi_case lvl rec0 rec1 Ge FA BA FB BB PA wpiA wpiB ad
           domIH posIH Hwf Hcod Happ Hwf).
Qed.

