Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Typing Preservation ApplySubst RenSubst.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* TYPING PRESERVATION UNDER A RENAMING (the universe-typed fragment).      *)
(*                                                                         *)
(* The renaming-stability presheaf ([LR_ren_gen]) must rename the typing    *)
(* side-conditions carried by [LR]: [wf_svalty Ge (dEl (vPi FA BA))] for    *)
(* [LRpi]/[LRpiI], [has_svalty Ge c (dU r l)] for [LRU], and [NeConv Ge     *)
(* (dU r l) n m] (= [wf_neutral] at the universe) for [LRne].  All of these *)
(* type a TYPE CODE at the universe [dU r l] (or a variable at [dU]).       *)
(*                                                                         *)
(* The universe-typed fragment is renamed CLEANLY: as in [typing_scoped],   *)
(* restricting the [has_svalty]/[wf_neutral] motives to [T = dU r l]         *)
(* discharges [t_lam]/[t_lam_eta]/[n_emptyrec]/[n_app]/[n_appI] (whose       *)
(* conclusions are [dEl _]) by [discriminate], so neither the [Reflect]      *)
(* premise of [t_lam_eta] nor the codomain [Apply_val] of [n_app] -- the     *)
(* two places that would need WELL-SCOPEDNESS of an un-recorded annotation   *)
(* -- is ever reached.  (Renaming a TERM at a [dEl (vPi ..)] type, the       *)
(* [has_svalty f] component of [PiRedTmEq], is NOT covered here; it needs    *)
(* "well-typed => well-scoped", which the current [t_lam]/[t_lam_eta] rules  *)
(* block by not recording the domain's typing -- see the header note in      *)
(* WIP/NEXT_SESSION.md / ConvRelPlan.md.)                                    *)
(* ===================================================================== *)

(* A renaming [rho] is a context map [Ge -> Ge'] when each variable's type is
   relocated to the [rho]-image position, renamed. *)
Definition ren_ctx (rho : list nat) (Ge Ge' : senv) : Prop :=
  forall k T, nth_error Ge k = Some T ->
    nth_error Ge' (renm rho k) = Some (ren_ty rho T).

(* [ren_ty] commutes with the cutoff-0 weakening shift on types. *)
Lemma ren_ty_shift_comm0 : forall rho T,
    ren_ty (up_renl rho) (shift_ty 0 1 T) = shift_ty 0 1 (ren_ty rho T).
Proof.
  intros rho T. destruct T as [r l | e].
  - reflexivity.
  - cbn [shift_ty ren_ty]. f_equal. apply ren_shift_comm0_val.
Qed.

(* Extending a context map under a binder ([dEl F] domain head). *)
Lemma ren_ctx_up_dEl : forall rho Ge Ge' F,
    ren_ctx rho Ge Ge' ->
    ren_ctx (up_renl rho)
      (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
      (dEl (shift_val 0 1 (ren_val rho F)) :: map (shift_ty 0 1) Ge').
Proof.
  intros rho Ge Ge' F Hctx k T Hnth. destruct k as [|k'].
  - cbn [nth_error] in Hnth. injection Hnth as <-.
    rewrite renm_up_0. cbn [nth_error ren_ty]. f_equal. f_equal.
    symmetry. apply ren_shift_comm0_val.
  - cbn [nth_error] in Hnth. rewrite nth_error_map in Hnth.
    destruct (nth_error Ge k') as [T0|] eqn:E; cbn [option_map] in Hnth; [|discriminate].
    injection Hnth as <-.
    rewrite renm_up_S. cbn [nth_error]. rewrite nth_error_map.
    rewrite (Hctx k' T0 E). cbn [option_map]. f_equal.
    symmetry. apply ren_ty_shift_comm0.
Qed.

(* The universe-typed fragment renames cleanly (mutual with [wf_neutral]). *)
Lemma ren_typing_dU :
  (forall Ge v T, has_svalty Ge v T ->
     forall r l, T = dU r l ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> has_svalty Ge' (ren_val rho v) (dU r l))
  * (forall Ge n T, wf_neutral Ge n T ->
     forall r l, T = dU r l ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> wf_neutral Ge' (ren_ne rho n) (dU r l)).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => forall r l, T = dU r l ->
       forall Ge' rho, ren_ctx rho Ge Ge' -> has_svalty Ge' (ren_val rho v) (dU r l))
    (fun Ge n T _ => forall r l, T = dU r l ->
       forall Ge' rho, ren_ctx rho Ge Ge' -> wf_neutral Ge' (ren_ne rho n) (dU r l))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn r l Heq Ge' rho Hctx.
    cbn [ren_val]. apply t_ne. exact (IHn r l Heq Ge' rho Hctx).
  - (* t_zero *) intros Ge r l Heq Ge' rho Hctx. discriminate Heq.
  - (* t_suc *) intros Ge v hv IHv r l Heq Ge' rho Hctx. discriminate Heq.
  - (* t_Nat *) intros Ge r l r0 l0 Heq Ge' rho Hctx. cbn [ren_val]. apply t_Nat.
  - (* t_Empty *) intros Ge r l r0 l0 Heq Ge' rho Hctx. cbn [ren_val]. apply t_Empty.
  - (* t_Pi *) intros Ge F B rF lF rB lB r l hF IHF hB IHB r0 l0 Heq Ge' rho Hctx.
    cbn [ren_val]. eapply t_Pi.
    + exact (IHF rF lF eq_refl Ge' rho Hctx).
    + exact (IHB rB lB eq_refl _ (up_renl rho) (ren_ctx_up_dEl F Hctx)).
  - (* t_PiI *) intros Ge F B rF lF rB lB r l hF IHF hB IHB r0 l0 Heq Ge' rho Hctx.
    cbn [ren_val]. eapply t_PiI.
    + exact (IHF rF lF eq_refl Ge' rho Hctx).
    + exact (IHB rB lB eq_refl _ (up_renl rho) (ren_ctx_up_dEl F Hctx)).
  - (* t_lam *) intros Ge F B b rF lF hF IHF hb IHb r l Heq Ge' rho Hctx. discriminate Heq.
  - (* t_lamI *) intros Ge F B b hb IHb r l Heq Ge' rho Hctx. discriminate Heq.
  - (* t_lam_eta *) intros Ge F B b ARG B' rF lF hF IHF HR Hap hb IHb r l Heq Ge' rho Hctx.
    discriminate Heq.
  - (* n_var *) intros Ge k T He r l Heq Ge' rho Hctx. subst T.
    cbn [ren_ne]. apply n_var. exact (Hctx k (dU r l) He).
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr r0 l0 Heq Ge' rho Hctx.
    discriminate Heq.
  - (* n_app *) intros Ge f F B a B' hf IHf ha IHa Hap r l Heq Ge' rho Hctx.
    discriminate Heq.
  - (* n_appI *) intros Ge f F B a B' hf IHf ha IHa Hap r l Heq Ge' rho Hctx.
    discriminate Heq.
Qed.

Definition has_svalty_dU_ren {Ge v r l} (H : has_svalty Ge v (dU r l)) :=
  fst ren_typing_dU Ge v (dU r l) H r l eq_refl.
Definition wf_neutral_dU_ren {Ge n r l} (H : wf_neutral Ge n (dU r l)) :=
  snd ren_typing_dU Ge n (dU r l) H r l eq_refl.

(* Well-formedness of a TYPE is preserved under a context renaming. *)
Lemma wf_svalty_ren : forall Ge T, wf_svalty Ge T ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> wf_svalty Ge' (ren_ty rho T).
Proof.
  intros Ge T H Ge' rho Hctx. destruct H as [Ge r l | Ge e r l He].
  - cbn [ren_ty]. apply wf_dU.
  - cbn [ren_ty]. eapply wf_dEl.
    eapply (fst ren_typing_dU); [ exact He | reflexivity | exact Hctx ].
Qed.
