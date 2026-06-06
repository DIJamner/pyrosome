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
  Domain Apply Typing Preservation ApplySubst RenSubst LogRel2Conv.
Import Core.Notations.

Notation term := (@term string).

(* Stability of structural conversion under a general renaming [ren_val]/
   [ren_ne] (the variable case maps [nVar k] to [nVar (renm rho k)] on both
   sides).  Needed by the [n_conv] case of [ren_typing]. *)
Lemma conv_ren :
  (forall a b, conv_nf a b -> forall rho, conv_nf (ren_val rho a) (ren_val rho b))
  * (forall n m, conv_ne n m -> forall rho, conv_ne (ren_ne rho n) (ren_ne rho m)).
Proof.
  apply (conv_mutind
    (fun a b (_ : conv_nf a b) => forall rho, conv_nf (ren_val rho a) (ren_val rho b))
    (fun n m (_ : conv_ne n m) => forall rho, conv_ne (ren_ne rho n) (ren_ne rho m))).
  - intros n m _ IH rho. cbn [ren_val]. apply cnf_ne. apply IH.
  - intros rho. apply cnf_zero.
  - intros v w _ IH rho. cbn [ren_val]. apply cnf_suc. apply IH.
  - intros rho. apply cnf_nat.
  - intros rho. apply cnf_empty.
  - intros F B F' B' _ IHF _ IHB rho. cbn [ren_val]. apply cnf_pi; [ apply IHF | apply IHB ].
  - intros F B F' B' _ IHF _ IHB rho. cbn [ren_val]. apply cnf_piI; [ apply IHF | apply IHB ].
  - intros b b' _ IH rho. cbn [ren_val]. apply cnf_lam. apply IH.
  - intros b b' _ IH rho. cbn [ren_val]. apply cnf_lamI. apply IH.
  - intros k rho. cbn [ren_ne]. apply cne_var.
  - intros rA lA A scrut A' scrut' _ IHA _ IHs rho. cbn [ren_ne].
    apply cne_emptyrec; [ apply IHA | apply IHs ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa rho. cbn [ren_ne].
    apply cne_app; [ apply IHf | apply IHF | apply IHB | apply IHa ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa rho. cbn [ren_ne].
    apply cne_appI; [ apply IHf | apply IHF | apply IHB | apply IHa ].
Qed.

Definition conv_nf_ren : forall a b, conv_nf a b -> forall rho,
    conv_nf (ren_val rho a) (ren_val rho b) := fst conv_ren.
Definition conv_ne_ren : forall n m, conv_ne n m -> forall rho,
    conv_ne (ren_ne rho n) (ren_ne rho m) := snd conv_ren.

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
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  - (* t_lamI *) intros Ge F B b rF lF hF IHF hb IHb r l Heq Ge' rho Hctx. discriminate Heq.
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
  - (* n_conv *) intros Ge n A B w IH cAB r l Heq Ge' rho Hctx. discriminate Heq.
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

(* ===================================================================== *)
(* WELL-TYPED => WELL-SCOPED (all types).                                   *)
(*                                                                         *)
(* The [t_lam]/[t_lamI]/[t_lam_eta] rules now record the domain typing      *)
(* [has_svalty Ge F (dU rF lF)], so a function value's domain annotation is *)
(* recoverably scoped.  This unblocks the full scopedness lemma (the        *)
(* [dU]-restricted [typing_scoped] in ApplySubst.v was the previous best).  *)
(*                                                                         *)
(* Asymmetry of the motives: VALUES ([has_svalty]) get only the VALUE-side  *)
(* [ne_below_val] -- their type-side is never consumed by another case's    *)
(* IH, and dropping it lets [t_lam_eta] go through with no [B]/[ARG]         *)
(* reasoning.  NEUTRALS ([wf_neutral]) carry BOTH sides, because [n_app]/    *)
(* [n_appI] recover the [(F,B)] annotation scopedness from the FUNCTION'S    *)
(* type [dEl (vPi F B)] (its type-side), and [n_emptyrec]/the codomain need  *)
(* the result type [dEl B'] scoped (via [Apply_val_ne_below]).              *)
(* The context precondition [ne_below_ctx] feeds [n_var]'s type-side.        *)
(* ===================================================================== *)

(* Every entry of [Ge] is scoped below the FULL length (entries are shifted
   uniformly in this absolute/environment-free representation). *)
Definition ne_below_ctx (Ge : senv) : Prop :=
  forall k T, nth_error Ge k = Some T -> ne_below_ty (length Ge) T.

(* Extending a well-scoped context under a (scoped) [dEl F] binder head. *)
Lemma ne_below_ctx_up_dEl : forall Ge F,
    ne_below_ctx Ge -> ne_below_val (length Ge) F ->
    ne_below_ctx (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge).
Proof.
  intros Ge F Hctx HF k T Hnth. cbn [length]. rewrite length_map.
  destruct k as [|k'].
  - cbn [nth_error] in Hnth. injection Hnth as <-.
    cbn [ne_below_ty]. apply ne_below_shift_val. exact HF.
  - cbn [nth_error] in Hnth. rewrite nth_error_map in Hnth.
    destruct (nth_error Ge k') as [T0|] eqn:E; cbn [option_map] in Hnth; [|discriminate].
    injection Hnth as <-. apply (fst ne_below_shift). exact (Hctx k' T0 E).
Qed.

Lemma typing_ne_below :
  (forall Ge v T, has_svalty Ge v T ->
     ne_below_ctx Ge -> ne_below_val (length Ge) v)
  * (forall Ge n T, wf_neutral Ge n T ->
     ne_below_ctx Ge -> ne_below_ne (length Ge) n /\ ne_below_ty (length Ge) T).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => ne_below_ctx Ge -> ne_below_val (length Ge) v)
    (fun Ge n T _ => ne_below_ctx Ge ->
       ne_below_ne (length Ge) n /\ ne_below_ty (length Ge) T)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn Hctx. cbn [ne_below_val]. exact (proj1 (IHn Hctx)).
  - (* t_zero *) intros Ge Hctx. exact I.
  - (* t_suc *) intros Ge v hv IHv Hctx. cbn [ne_below_val]. exact (IHv Hctx).
  - (* t_Nat *) intros Ge r l Hctx. exact I.
  - (* t_Empty *) intros Ge r l Hctx. exact I.
  - (* t_Pi *) intros Ge F B rF lF rB lB r l hF IHF hB IHB Hctx.
    cbn [ne_below_val]. split.
    + exact (IHF Hctx).
    + pose proof (IHB (ne_below_ctx_up_dEl F Hctx (IHF Hctx))) as IH.
      cbn [length] in IH. rewrite length_map in IH. exact IH.
  - (* t_PiI *) intros Ge F B rF lF rB lB r l hF IHF hB IHB Hctx.
    cbn [ne_below_val]. split.
    + exact (IHF Hctx).
    + pose proof (IHB (ne_below_ctx_up_dEl F Hctx (IHF Hctx))) as IH.
      cbn [length] in IH. rewrite length_map in IH. exact IH.
  - (* t_lam *) intros Ge F B b rF lF hF IHF hb IHb Hctx.
    cbn [ne_below_val].
    pose proof (IHb (ne_below_ctx_up_dEl F Hctx (IHF Hctx))) as IH.
    cbn [length] in IH. rewrite length_map in IH. exact IH.
  - (* t_lamI *) intros Ge F B b rF lF hF IHF hb IHb Hctx.
    cbn [ne_below_val].
    pose proof (IHb (ne_below_ctx_up_dEl F Hctx (IHF Hctx))) as IH.
    cbn [length] in IH. rewrite length_map in IH. exact IH.
  - (* t_lam_eta *) intros Ge F B b ARG B' rF lF hF IHF HR Hap hb IHb Hctx.
    cbn [ne_below_val].
    pose proof (IHb (ne_below_ctx_up_dEl F Hctx (IHF Hctx))) as IH.
    cbn [length] in IH. rewrite length_map in IH. exact IH.
  - (* n_var *) intros Ge k T He Hctx. split.
    + cbn [ne_below_ne]. apply (proj1 (nth_error_Some Ge k)). rewrite He. discriminate.
    + exact (Hctx k T He).
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr Hctx. split.
    + cbn [ne_below_ne]. split; [ exact (IHA Hctx) | exact (proj1 (IHscr Hctx)) ].
    + cbn [ne_below_ty]. exact (IHA Hctx).
  - (* n_app *) intros Ge f F B a B' hf IHf ha IHa Hap Hctx.
    destruct (IHf Hctx) as [Hnef HtyF]. cbn [ne_below_ty ne_below_val] in HtyF.
    destruct HtyF as [HneF HneB]. split.
    + cbn [ne_below_ne]. repeat split;
        [ exact Hnef | exact HneF | exact HneB | exact (IHa Hctx) ].
    + cbn [ne_below_ty]. eapply Apply_val_ne_below;
        [ exact Hap | exact HneB | apply sub_below_beta; [ Lia.lia | exact (IHa Hctx) ] ].
  - (* n_appI *) intros Ge f F B a B' hf IHf ha IHa Hap Hctx.
    destruct (IHf Hctx) as [Hnef HtyF]. cbn [ne_below_ty ne_below_val] in HtyF.
    destruct HtyF as [HneF HneB]. split.
    + cbn [ne_below_ne]. repeat split;
        [ exact Hnef | exact HneF | exact HneB | exact (IHa Hctx) ].
    + cbn [ne_below_ty]. eapply Apply_val_ne_below;
        [ exact Hap | exact HneB | apply sub_below_beta; [ Lia.lia | exact (IHa Hctx) ] ].
  - (* n_conv *) intros Ge n A B w IH cAB Hctx. split.
    + exact (proj1 (IH Hctx)).
    + cbn [ne_below_ty] in *.
      exact (conv_ty_eta_ne_below cAB (proj2 (IH Hctx))).
Qed.

(* Convenience projections (the [dU]-restricted [has_svalty_scoped]/
   [wf_neutral_scoped] in ApplySubst.v are the universe-only specializations). *)
Definition has_svalty_ne_below {Ge v T} (H : has_svalty Ge v T) :=
  fst typing_ne_below Ge v T H.
Definition wf_neutral_ne_below {Ge n T} (H : wf_neutral Ge n T) :=
  snd typing_ne_below Ge n T H.

(* ===================================================================== *)
(* TYPING PRESERVATION UNDER A RENAMING (all types).                        *)
(*                                                                         *)
(* Generalizes [ren_typing_dU] to every type.  Preconditions: the type [T]  *)
(* is scoped ([ne_below_ty]) -- needed for the [t_lam_eta] codomain [B] and  *)
(* domain [F] which the rules record only partially -- and the context is    *)
(* scoped ([ne_below_ctx]) -- so neutral sub-derivations recover their own   *)
(* type's scopedness via [typing_ne_below].  The renaming is given BOTH as a  *)
(* context map ([ren_ctx]) and as a level bound ([ren_ok rho (S (length Ge)) *)
(* (length Ge')]), matching [Reflect_ren]/[Apply_val_ren_commute], which want *)
(* the bound one level above the source (the [t_lam_eta]/[n_app] codomains    *)
(* live under a binder).                                                     *)
(* ===================================================================== *)
(* The [Vapp] projections of the RenSubst commutation/scoping engines. *)
Definition Vapp_ren := snd (fst Apply_ren_commute).
Definition Vapp_ne_below' := snd (fst Apply_ne_below).

(* [ne_below] transports along a [ren_ok] renaming.  [t_lam_eta] has no
   ne_below side-conditions so [ren_typing] never needed this; the [ctm_eta]
   side-conditions of [conv_ty_eta] must be re-established over the target ctx. *)
Lemma ne_below_ren_val : forall v N rho m2,
    ne_below_val N v -> ren_ok rho N m2 -> ne_below_val m2 (ren_val rho v).
Proof.
  intros v N rho m2 Hv Hok.
  refine (Apply_val_ne_below (ren_is_Apply_val v m2 rho) Hv _).
  intros k Hk. rewrite ren_sub_nth. cbn [ne_below_val ne_below_ne].
  apply Hok; exact Hk.
Qed.

(* ===================================================================== *)
(* [conv_eta_ren] : the eta-closed conversion is stable under RENAMING.    *)
(* The [ctm_eta] case = [t_lam_eta]'s ren case + two [Vapp_ren] premises +  *)
(* re-establishing the ne_below side-conds over the target ctx via          *)
(* [ne_below_ren_val].  Consumed by [ren_typing]'s [n_conv] case below.     *)
(* (Migrated from WIP/ConvEtaProto.v.)                                       *)
(* ===================================================================== *)
Lemma conv_eta_ren :
  (forall Ge A B, conv_ty_eta Ge A B ->
     ne_below_val (length Ge) A -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       conv_ty_eta Ge' (ren_val rho A) (ren_val rho B))
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     ne_below_ty (length Ge) T -> ne_below_val (length Ge) a -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       conv_tm_eta Ge' (ren_ty rho T) (ren_val rho a) (ren_val rho b))
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     ne_below_ty (length Ge) T -> ne_below_ne (length Ge) n -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       conv_ne_eta Ge' (ren_ty rho T) (ren_ne rho n) (ren_ne rho m)).
Proof.
  apply conv_eta_mutind.
  - (* cte_nat *) intros Ge HA Hctx Ge' rho Hren Hok. cbn [ren_val]. apply cte_nat.
  - (* cte_empty *) intros Ge HA Hctx Ge' rho Hren Hok. cbn [ren_val]. apply cte_empty.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB HA Hctx Ge' rho Hren Hok.
    cbn [ren_val] in *. destruct HA as [HFn HBn]. apply cte_pi.
    + exact (IHF HFn Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ cbn [length]; rewrite length_map; exact HBn
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFn ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB HA Hctx Ge' rho Hren Hok.
    cbn [ren_val] in *. destruct HA as [HFn HBn]. apply cte_piI.
    + exact (IHF HFn Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ cbn [length]; rewrite length_map; exact HBn
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFn ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* cte_ne *) intros Ge n n' r l _ IH HA Hctx Ge' rho Hren Hok.
    cbn [ren_val] in *. eapply cte_ne.
    pose proof (IH I HA Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty] in IH'. exact IH'.
  - (* cte_refl *) intros Ge A HA Hctx Ge' rho Hren Hok. apply cte_refl.
  - (* cte_sym *) intros Ge A B d IH HA Hctx Ge' rho Hren Hok.
    apply cte_sym.
    exact (IH (proj2 (proj1 conv_eta_ne_below_iff Ge B A d) HA) Hctx Ge' rho Hren Hok).
  - (* cte_trans *) intros Ge A B C dAB IH1 dBC IH2 HA Hctx Ge' rho Hren Hok.
    eapply cte_trans.
    + exact (IH1 HA Hctx Ge' rho Hren Hok).
    + exact (IH2 (proj1 (proj1 conv_eta_ne_below_iff Ge A B dAB) HA) Hctx Ge' rho Hren Hok).
  - (* ctm_ne_nat *) intros Ge n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_ne_nat.
    pose proof (IH I Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_ne_empty *) intros Ge n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_ne_empty.
    pose proof (IH I Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_ne_el *) intros Ge cc n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_ne_el.
    pose proof (IH HT Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_zero *) intros Ge HT Ha Hctx Ge' rho Hren Hok. cbn [ren_val ren_ty]. apply ctm_zero.
  - (* ctm_suc *) intros Ge v v' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_suc.
    pose proof (IH I Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_code *) intros Ge r l cc cc' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_code. exact (IH Ha Hctx Ge' rho Hren Hok).
  - (* ctm_eta *)
    intros Ge F B f g ARG B' fa ga nbF nbf nbg HR Hap Hfa Hga _Hcod IHcod HT Hf Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. cbn [ne_below_ty ne_below_val] in HT. destruct HT as [HFt HBt].
    assert (Hokc : ren_ok rho (length Ge) (length Ge'))
      by (apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]).
    assert (HARG : ne_below_val (S (length Ge)) ARG)
      by (eapply Reflect_scoped;
          [ exact HR | cbn [ne_below_ty]; apply ne_below_shift_val; exact HFt
          | cbn [ne_below_ne]; Lia.lia ]).
    assert (Hsf : ne_below_val (S (length Ge)) (shift_val 0 1 f))
      by (apply ne_below_shift_val; exact nbf).
    assert (Hsg : ne_below_val (S (length Ge)) (shift_val 0 1 g))
      by (apply ne_below_shift_val; exact nbg).
    assert (HsF : ne_below_val (S (length Ge)) (shift_val 0 1 F))
      by (apply ne_below_shift_val; exact HFt).
    assert (HB' : ne_below_val (S (length Ge)) B')
      by (eapply Apply_val_ne_below;
          [ exact Hap | apply ne_below_shift_val; exact HBt
          | apply sub_below_beta; [ Lia.lia | exact HARG ] ]).
    assert (HsB : ne_below_val (S (S (length Ge))) (shift_val 1 1 B))
      by (apply ne_below_shift_val; exact HBt).
    assert (Hfanb : ne_below_val (S (length Ge)) fa)
      by (exact (Vapp_ne_below' Hfa Hsf HARG HsF HsB)).
    eapply ctm_eta.
    + (* nbF' *) eapply ne_below_ren_val; [ exact nbF | exact Hokc ].
    + (* nbf' *) eapply ne_below_ren_val; [ exact nbf | exact Hokc ].
    + (* nbg' *) eapply ne_below_ren_val; [ exact nbg | exact Hokc ].
    + (* Reflect *)
      pose proof (Reflect_ren HR
                    ltac:(cbn [ne_below_ty]; apply ne_below_shift_val; exact HFt)
                    ltac:(cbn [ne_below_ne]; Lia.lia)
                    (ren_ok_up Hok)) as HRr.
      cbn [ren_ty ren_ne ren_val] in HRr.
      rewrite renm_up_0, ren_shift_comm0_val in HRr. exact HRr.
    + (* Apply_val *)
      pose proof (@Apply_val_ren_commute
                    (S (length Ge)) (ARG :: id_list (S (length Ge)))
                    (shift_val 1 1 B) B' Hap
                    (S (S (length Ge)))
                    ltac:(apply ne_below_shift_val; exact HBt)
                    ltac:(apply sub_below_beta; [ Lia.lia | exact HARG ])
                    (S (length Ge')) (up_renl (up_renl rho)) (up_renl rho)
                    (ren_val (up_renl rho) ARG :: id_list (S (length Ge')))
                    (ren_ok_up Hok)
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (S (length Ge))); [ exact (ren_ok_up Hok) | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr.
      rewrite ren_shift_comm1_val in Hapr. exact Hapr.
    + (* Vapp fa *)
      pose proof (@Vapp_ren _ _ _ _ _ _ Hfa (S (length Ge)) Hsf HARG ltac:(Lia.lia)
                    (S (length Ge')) (up_renl rho) (ren_ok_up Hok)) as Hfar.
      cbn [ren_val] in Hfar.
      rewrite !ren_shift_comm0_val, ren_shift_comm1_val in Hfar. exact Hfar.
    + (* Vapp ga *)
      pose proof (@Vapp_ren _ _ _ _ _ _ Hga (S (length Ge)) Hsg HARG ltac:(Lia.lia)
                    (S (length Ge')) (up_renl rho) (ren_ok_up Hok)) as Hgar.
      cbn [ren_val] in Hgar.
      rewrite !ren_shift_comm0_val, ren_shift_comm1_val in Hgar. exact Hgar.
    + (* codomain conv *)
      eapply IHcod;
        [ cbn [ne_below_ty length]; rewrite length_map; exact HB'
        | cbn [length]; rewrite length_map; exact Hfanb
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFt ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. apply ctm_piI_ne.
    pose proof (IH HT Ha Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* ctm_lamI *) intros Ge F B b b' _ IH HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty] in *. cbn [ne_below_ty ne_below_val] in HT. destruct HT as [HFt HBt].
    cbn [ne_below_val] in Ha.
    apply ctm_lamI.
    eapply IH;
      [ cbn [ne_below_ty length]; rewrite length_map; exact HBt
      | cbn [length]; rewrite length_map; exact Ha
      | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HFt ]
      | apply ren_ctx_up_dEl; exact Hren
      | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* ctm_refl *) intros Ge T a HT Ha Hctx Ge' rho Hren Hok. apply ctm_refl.
  - (* ctm_sym *) intros Ge T a b d IH HT Ha Hctx Ge' rho Hren Hok.
    apply ctm_sym.
    exact (IH HT (proj2 (proj1 (proj2 conv_eta_ne_below_iff) Ge T b a d HT) Ha)
              Hctx Ge' rho Hren Hok).
  - (* ctm_trans *) intros Ge T a b cc dAB IH1 dBC IH2 HT Ha Hctx Ge' rho Hren Hok.
    eapply ctm_trans.
    + exact (IH1 HT Ha Hctx Ge' rho Hren Hok).
    + exact (IH2 HT (proj1 (proj1 (proj2 conv_eta_ne_below_iff) Ge T a b dAB HT) Ha)
                Hctx Ge' rho Hren Hok).
  - (* ctm_conv *) intros Ge A B a b dtm IHtm dty IHty HT Ha Hctx Ge' rho Hren Hok.
    cbn [ren_ty] in *.
    assert (HnA : ne_below_val (length Ge) A)
      by (exact (proj2 (proj1 conv_eta_ne_below_iff Ge A B dty) HT)).
    eapply ctm_conv.
    + exact (IHtm HnA Ha Hctx Ge' rho Hren Hok).
    + exact (IHty HnA Hctx Ge' rho Hren Hok).
  - (* cne_eta_var *) intros Ge k T He HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne]. apply cne_eta_var. exact (Hren k T He).
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty ren_val] in *. cbn [ne_below_ne] in Hn. destruct Hn as [HnA Hns].
    apply cne_eta_emptyrec.
    + exact (IHA HnA Hctx Ge' rho Hren Hok).
    + pose proof (IHs I Hns Hctx Ge' rho Hren Hok) as IH'. cbn [ren_ty ren_val] in IH'. exact IH'.
  - (* cne_eta_app *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty ren_val] in *. cbn [ne_below_ne] in Hn.
    destruct Hn as (Hnf & HnF & HnB & Hna).
    eapply cne_eta_app.
    + (* f *) pose proof (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ])
                            Hnf Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + (* F *) exact (IHF HnF Hctx Ge' rho Hren Hok).
    + (* B *) eapply IHB;
        [ cbn [length]; rewrite length_map; exact HnB
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HnF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
    + (* a *) pose proof (IHa ltac:(cbn [ne_below_ty]; exact HnF) Hna Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + (* Apply Bres *)
      pose proof (@Apply_val_ren_commute
                    (length Ge) (a :: id_list (length Ge)) B Bres Hap
                    (S (length Ge)) HnB
                    ltac:(apply sub_below_beta; [ Lia.lia | exact Hna ])
                    (length Ge') (up_renl rho) rho
                    (ren_val rho a :: id_list (length Ge'))
                    ltac:(apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ])
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr. exact Hapr.
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty ren_val] in *. cbn [ne_below_ne] in Hn.
    destruct Hn as (Hnf & HnF & HnB & Hna).
    eapply cne_eta_appI.
    + pose proof (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ])
                            Hnf Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + exact (IHF HnF Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ cbn [length]; rewrite length_map; exact HnB
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HnF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
    + pose proof (IHa ltac:(cbn [ne_below_ty]; exact HnF) Hna Hctx Ge' rho Hren Hok) as IH'.
      cbn [ren_ty ren_val] in IH'. exact IH'.
    + pose proof (@Apply_val_ren_commute
                    (length Ge) (a :: id_list (length Ge)) B Bres Hap
                    (S (length Ge)) HnB
                    ltac:(apply sub_below_beta; [ Lia.lia | exact Hna ])
                    (length Ge') (up_renl rho) rho
                    (ren_val rho a :: id_list (length Ge'))
                    ltac:(apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ])
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr. exact Hapr.
  - (* cne_refl *) intros Ge T n HT Hn Hctx Ge' rho Hren Hok. apply cne_refl.
  - (* cne_sym *) intros Ge T n m d IH HT Hn Hctx Ge' rho Hren Hok.
    apply cne_sym.
    exact (IH HT (proj2 (proj2 (proj2 conv_eta_ne_below_iff) Ge T m n d HT) Hn)
              Hctx Ge' rho Hren Hok).
  - (* cne_trans *) intros Ge T n m p dAB IH1 dBC IH2 HT Hn Hctx Ge' rho Hren Hok.
    eapply cne_trans.
    + exact (IH1 HT Hn Hctx Ge' rho Hren Hok).
    + exact (IH2 HT (proj1 (proj2 (proj2 conv_eta_ne_below_iff) Ge T n m dAB HT) Hn)
                Hctx Ge' rho Hren Hok).
Qed.

Definition conv_ty_eta_ren : forall Ge A B, conv_ty_eta Ge A B ->
    ne_below_val (length Ge) A -> ne_below_ctx Ge ->
    forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
      conv_ty_eta Ge' (ren_val rho A) (ren_val rho B) :=
  proj1 conv_eta_ren.

Lemma ren_typing :
  (forall Ge v T, has_svalty Ge v T ->
     ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       has_svalty Ge' (ren_val rho v) (ren_ty rho T))
  * (forall Ge n T, wf_neutral Ge n T ->
     ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
     forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
       wf_neutral Ge' (ren_ne rho n) (ren_ty rho T)).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
       forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
         has_svalty Ge' (ren_val rho v) (ren_ty rho T))
    (fun Ge n T _ => ne_below_ty (length Ge) T -> ne_below_ctx Ge ->
       forall Ge' rho, ren_ctx rho Ge Ge' -> ren_ok rho (S (length Ge)) (length Ge') ->
         wf_neutral Ge' (ren_ne rho n) (ren_ty rho T))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val]. apply t_ne. exact (IHn Hty Hctx Ge' rho Hren Hok).
  - (* t_zero *) intros Ge Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. apply t_zero.
  - (* t_suc *) intros Ge v hv IHv Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. apply t_suc. exact (IHv I Hctx Ge' rho Hren Hok).
  - (* t_Nat *) intros Ge r l Hty Hctx Ge' rho Hren Hok. cbn [ren_val ren_ty]. apply t_Nat.
  - (* t_Empty *) intros Ge r l Hty Hctx Ge' rho Hren Hok. cbn [ren_val ren_ty]. apply t_Empty.
  - (* t_Pi *) intros Ge F B rF lF rB lB r l hF IHF hB IHB Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. eapply t_Pi.
    + exact (IHF I Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ exact I | apply ne_below_ctx_up_dEl; [ exact Hctx | exact (has_svalty_scoped hF) ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* t_PiI *) intros Ge F B rF lF rB lB r l hF IHF hB IHB Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. eapply t_PiI.
    + exact (IHF I Hctx Ge' rho Hren Hok).
    + eapply IHB;
        [ exact I | apply ne_below_ctx_up_dEl; [ exact Hctx | exact (has_svalty_scoped hF) ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* t_lam *) intros Ge F B b rF lF hF IHF hb IHb Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. cbn [ne_below_ty ne_below_val] in Hty. destruct Hty as [HF HB].
    eapply t_lam.
    + exact (IHF I Hctx Ge' rho Hren Hok).
    + eapply IHb;
        [ cbn [ne_below_ty length]; rewrite length_map; exact HB
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* t_lamI *) intros Ge F B b rF lF hF IHF hb IHb Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. cbn [ne_below_ty ne_below_val] in Hty. destruct Hty as [HF HB].
    eapply t_lamI.
    + exact (IHF I Hctx Ge' rho Hren Hok).
    + eapply IHb;
        [ cbn [ne_below_ty length]; rewrite length_map; exact HB
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* t_lam_eta *) intros Ge F B b ARG B' rF lF hF IHF HR Hap hb IHb Hty Hctx Ge' rho Hren Hok.
    cbn [ren_val ren_ty]. cbn [ne_below_ty ne_below_val] in Hty. destruct Hty as [HF HB].
    assert (HARG : ne_below_val (S (length Ge)) ARG)
      by (eapply Reflect_scoped;
          [ exact HR | cbn [ne_below_ty]; apply ne_below_shift_val; exact HF
          | cbn [ne_below_ne]; Lia.lia ]).
    assert (HB' : ne_below_val (S (length Ge)) B')
      by (eapply Apply_val_ne_below;
          [ exact Hap | apply ne_below_shift_val; exact HB
          | apply sub_below_beta; [ Lia.lia | exact HARG ] ]).
    eapply t_lam_eta.
    + exact (IHF I Hctx Ge' rho Hren Hok).
    + (* Reflect premise via Reflect_ren *)
      pose proof (Reflect_ren HR
                    ltac:(cbn [ne_below_ty]; apply ne_below_shift_val; exact HF)
                    ltac:(cbn [ne_below_ne]; Lia.lia)
                    (ren_ok_up Hok)) as HRr.
      cbn [ren_ty ren_ne ren_val] in HRr.
      rewrite renm_up_0, ren_shift_comm0_val in HRr. exact HRr.
    + (* codomain Apply via Apply_val_ren_commute *)
      pose proof (@Apply_val_ren_commute
                    (S (length Ge)) (ARG :: id_list (S (length Ge)))
                    (shift_val 1 1 B) B' Hap
                    (S (S (length Ge)))
                    ltac:(apply ne_below_shift_val; exact HB)
                    ltac:(apply sub_below_beta; [ Lia.lia | exact HARG ])
                    (S (length Ge')) (up_renl (up_renl rho)) (up_renl rho)
                    (ren_val (up_renl rho) ARG :: id_list (S (length Ge')))
                    (ren_ok_up Hok)
                    ltac:(eapply RenShSc_beta;
                            [ Lia.lia | apply ren_ok_le with (N := S (S (length Ge))); [ exact (ren_ok_up Hok) | Lia.lia ]
                            | apply ren_is_Apply_val ])) as Hapr.
      rewrite ren_shift_comm1_val in Hapr. exact Hapr.
    + (* body *)
      eapply IHb;
        [ cbn [ne_below_ty length]; rewrite length_map; exact HB'
        | apply ne_below_ctx_up_dEl; [ exact Hctx | exact HF ]
        | apply ren_ctx_up_dEl; exact Hren
        | cbn [length]; rewrite !length_map; apply ren_ok_up; exact Hok ].
  - (* n_var *) intros Ge k T He Hty Hctx Ge' rho Hren Hok.
    cbn [ren_ne]. apply n_var. exact (Hren k T He).
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr Hty Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_val ren_ty]. eapply n_emptyrec.
    + exact (IHA I Hctx Ge' rho Hren Hok).
    + exact (IHscr I Hctx Ge' rho Hren Hok).
  - (* n_app *) intros Ge f F B a B' hf IHf ha IHa Hap Hty Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty].
    destruct (wf_neutral_ne_below hf Hctx) as [Hnef Htyf].
    cbn [ne_below_ty ne_below_val] in Htyf. destruct Htyf as [HF HB].
    pose proof (has_svalty_ne_below ha Hctx) as Ha. cbn [ne_below_ty] in Ha.
    eapply n_app.
    + exact (IHf (conj HF HB) Hctx Ge' rho Hren Hok).
    + exact (IHa HF Hctx Ge' rho Hren Hok).
    + exact (@Apply_val_ren_commute
               (length Ge) (a :: id_list (length Ge)) B B' Hap
               (S (length Ge)) HB
               ltac:(apply sub_below_beta; [ Lia.lia | exact Ha ])
               (length Ge') (up_renl rho) rho
               (ren_val rho a :: id_list (length Ge')) Hok
               ltac:(eapply RenShSc_beta;
                       [ Lia.lia | apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]
                       | apply ren_is_Apply_val ])).
  - (* n_appI *) intros Ge f F B a B' hf IHf ha IHa Hap Hty Hctx Ge' rho Hren Hok.
    cbn [ren_ne ren_ty].
    destruct (wf_neutral_ne_below hf Hctx) as [Hnef Htyf].
    cbn [ne_below_ty ne_below_val] in Htyf. destruct Htyf as [HF HB].
    pose proof (has_svalty_ne_below ha Hctx) as Ha. cbn [ne_below_ty] in Ha.
    eapply n_appI.
    + exact (IHf (conj HF HB) Hctx Ge' rho Hren Hok).
    + exact (IHa HF Hctx Ge' rho Hren Hok).
    + exact (@Apply_val_ren_commute
               (length Ge) (a :: id_list (length Ge)) B B' Hap
               (S (length Ge)) HB
               ltac:(apply sub_below_beta; [ Lia.lia | exact Ha ])
               (length Ge') (up_renl rho) rho
               (ren_val rho a :: id_list (length Ge')) Hok
               ltac:(eapply RenShSc_beta;
                       [ Lia.lia | apply ren_ok_le with (N := S (length Ge)); [ exact Hok | Lia.lia ]
                       | apply ren_is_Apply_val ])).
  - (* n_conv *) intros Ge n A B w IH cAB HtyB Hctx Ge' rho Hren Hok.
    assert (HtyA : ne_below_ty (length Ge) (dEl A)).
    { cbn [ne_below_ty] in *. exact (conv_ty_eta_ne_below_rev cAB HtyB). }
    cbn [ren_ty]. eapply n_conv.
    + exact (IH HtyA Hctx Ge' rho Hren Hok).
    + exact (conv_ty_eta_ren cAB HtyA Hctx Hren Hok).
Qed.
