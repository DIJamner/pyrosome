Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply ApplyLemmas Typing ApplySubst Preservation LogRel.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Renaming algebra for the [is_ren] predicate that gates [PiRedTmPred]'s   *)
(* application clause.  A renaming is a substitution all of whose entries   *)
(* are variable-neutrals ([is_ren] in LogRel.v).  These structural facts    *)
(* are what [reflect_red] and the validity layer use to discharge the       *)
(* clause's renaming hypothesis (the FL applies at [id_list]; reflection    *)
(* under a binder uses [up]/[wkn_list]).                                    *)
(* ===================================================================== *)

Lemma is_ren_nil : is_ren [].
Proof. exists []. reflexivity. Qed.

(* The tail of a renaming is a renaming. *)
Lemma is_ren_tl : forall {h t}, is_ren (h :: t) -> is_ren t.
Proof.
  intros h t [rho Heq]. destruct rho as [|r rs]; cbn in Heq; [ discriminate | ].
  injection Heq as _ Ht. exists rs. exact Ht.
Qed.

(* Consing a variable-neutral onto a renaming is a renaming. *)
Lemma is_ren_cons : forall k t, is_ren t -> is_ren (vNe (nVar k) :: t).
Proof.
  intros k t [rho Heq]. exists (k :: rho). cbn [map]. rewrite Heq. reflexivity.
Qed.

Lemma is_ren_id : forall n, is_ren (id_list n).
Proof. intro n. exists (seq 0 n). reflexivity. Qed.

Lemma is_ren_wkn : forall n, is_ren (wkn_list n).
Proof.
  intro n. exists (map S (seq 0 n)). unfold wkn_list. rewrite map_map. reflexivity.
Qed.

Lemma is_ren_up : forall s, is_ren s -> is_ren (up s).
Proof.
  intros s [rho Heq]. subst s. exists (0 :: map S rho).
  unfold up. cbn [map]. f_equal.
  rewrite !map_map. apply map_ext. intro k.
  cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

(* Reading a renaming at any index returns a variable-neutral. *)
Lemma ren_nth_var : forall sg, is_ren sg ->
    forall k, { j & nth_default (vNe (nVar k)) sg k = vNe (nVar j) }.
Proof.
  intros sg [rho ->] k. unfold nth_default. rewrite nth_error_map.
  destruct (nth_error rho k) as [j|]; cbn [option_map].
  - exists j; reflexivity.
  - exists k; reflexivity.
Qed.

(* ===================================================================== *)
(* Under a RENAMING, [Apply_*] is TOTAL and preserves neutrality.          *)
(*                                                                         *)
(* The key structural fact behind the renaming-gated Pi clause: applying a  *)
(* renaming never creates a beta redex (a variable head maps to a variable  *)
(* head, so every [Vapp]/[VappI] stays in its [vapp_ne]/[vappI_ne] case).   *)
(* Hence substitution is structurally terminating on ALL values, and a       *)
(* neutral maps to a neutral.  Proof by [sval_mutind]; the binder cases use  *)
(* [is_ren_up].                                                              *)
(* ===================================================================== *)
Lemma ren_Apply_total :
  (forall T m sg, is_ren sg -> { T' & Apply_ty m sg T T' })
  * ((forall v m sg, is_ren sg -> { v' & Apply_val m sg v v' })
  *  (forall nn m sg, is_ren sg -> { n' & Apply_ne m sg nn (vNe n') })).
Proof.
  apply (sval_mutind
    (fun T  => forall m sg, is_ren sg -> { T' & Apply_ty  m sg T  T' })
    (fun v  => forall m sg, is_ren sg -> { v' & Apply_val m sg v  v' })
    (fun nn => forall m sg, is_ren sg -> { n' & Apply_ne  m sg nn (vNe n') })).
  - (* dU *) intros r l m sg Hr. exists (dU r l). apply ap_dU.
  - (* dEl *) intros e IHe m sg Hr. destruct (IHe m sg Hr) as [e' He].
    exists (dEl e'). apply ap_dEl; exact He.
  - (* vNe *) intros nn IHnn m sg Hr. destruct (IHnn m sg Hr) as [n' Hn].
    exists (vNe n'). apply ap_ne; exact Hn.
  - (* vZero *) intros m sg Hr. exists vZero. apply ap_zero.
  - (* vSuc *) intros v IHv m sg Hr. destruct (IHv m sg Hr) as [v' Hv].
    exists (vSuc v'). apply ap_suc; exact Hv.
  - (* vNat *) intros m sg Hr. exists vNat. apply ap_nat.
  - (* vEmpty *) intros m sg Hr. exists vEmpty. apply ap_empty.
  - (* vPi *) intros F IHF B IHB m sg Hr.
    destruct (IHF m sg Hr) as [F' HF].
    destruct (IHB (S m) (up sg) (is_ren_up Hr)) as [B' HB].
    exists (vPi F' B'). apply ap_pi; [ exact HF | exact HB ].
  - (* vPiI *) intros F IHF B IHB m sg Hr.
    destruct (IHF m sg Hr) as [F' HF].
    destruct (IHB (S m) (up sg) (is_ren_up Hr)) as [B' HB].
    exists (vPiI F' B'). apply ap_piI; [ exact HF | exact HB ].
  - (* vLam *) intros b IHb m sg Hr.
    destruct (IHb (S m) (up sg) (is_ren_up Hr)) as [b' Hb].
    exists (vLam b'). apply ap_lam; exact Hb.
  - (* vLamI *) intros b IHb m sg Hr.
    destruct (IHb (S m) (up sg) (is_ren_up Hr)) as [b' Hb].
    exists (vLamI b'). apply ap_lamI; exact Hb.
  - (* nVar *) intros k m sg Hr. destruct (ren_nth_var Hr k) as [j Hj].
    exists (nVar j). rewrite <- Hj. apply ap_var.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m sg Hr.
    destruct (IHA m sg Hr) as [A' HA].
    destruct (IHscr m sg Hr) as [s' Hs].
    exists (nEmptyrec rA lA A' s'). apply ap_emptyrec; [ exact HA | exact Hs ].
  - (* nApp *) intros f IHf a IHa m sg Hr.
    destruct (IHf m sg Hr) as [nf' Hf].
    destruct (IHa m sg Hr) as [a' Ha].
    exists (nApp nf' a'). eapply ap_app; [ exact Hf | exact Ha | apply vapp_ne ].
  - (* nAppI *) intros f IHf a IHa m sg Hr.
    destruct (IHf m sg Hr) as [nf' Hf].
    destruct (IHa m sg Hr) as [a' Ha].
    exists (nAppI nf' a'). eapply ap_appI; [ exact Hf | exact Ha | apply vappI_ne ].
Qed.

Definition ren_Apply_ty_total  := fst ren_Apply_total.
Definition ren_Apply_val_total := fst (snd ren_Apply_total).
Definition ren_Apply_ne_total  := snd (snd ren_Apply_total).

(* ===================================================================== *)
(* Renaming substitution COMPOSITION.                                      *)
(*                                                                         *)
(* For RENAMINGS, [Apply_*] composes: applying [s1] then [s2] equals        *)
(* applying the pointwise composite [s3].  The general [Apply] composition  *)
(* is NOT separable (composing through a [Vapp]-at-lambda needs that beta's  *)
(* totality, which is the normalization content); but a renaming never       *)
(* creates a beta ([ren_Apply_total]), so for renamings composition is a     *)
(* clean structural induction on the first derivation.  This is what         *)
(* [Reflect] naturality under renamings and the validity-layer reflect/      *)
(* reify bridge use to transport the eta-body under a renaming.              *)
(* ===================================================================== *)

(* The composite substitution relation: [sg3] is the pointwise [sg2]-image of
   [sg1] (entry k of sg3 = sg2 applied to entry k of sg1).  Default-correct
   thanks to the [vNe (nVar k)] read default matching [ap_var]. *)
Definition RenSub (m2 : nat) (sg2 sg1 sg3 : ssub) : Type :=
  forall k, Apply_val m2 sg2 (nth_default (vNe (nVar k)) sg1 k)
                             (nth_default (vNe (nVar k)) sg3 k).

(* Reading [up sg] at a successor index = shift of the underlying read. *)
Lemma up_nth_S : forall sg k,
    nth_default (vNe (nVar (S k))) (up sg) (S k)
    = shift_val 0 1 (nth_default (vNe (nVar k)) sg k).
Proof.
  intros sg k. unfold up. rewrite nth_default_cons_S. unfold nth_default.
  rewrite nth_error_map. destruct (nth_error sg k) as [e|] eqn:E; cbn [option_map].
  - reflexivity.
  - cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

(* [up] preserves the composite relation. *)
Lemma RenSub_up : forall m2 sg2 sg1 sg3,
    RenSub m2 sg2 sg1 sg3 -> RenSub (S m2) (up sg2) (up sg1) (up sg3).
Proof.
  intros m2 sg2 sg1 sg3 H k. destruct k as [|k'].
  - (* head: both read [vNe (nVar 0)]; up sg2 maps it to itself *)
    unfold up, nth_default. cbn [nth_error].
    apply ap_ne. change (vNe (nVar 0)) with (nth_default (vNe (nVar 0)) (up sg2) 0) at 2.
    apply ap_var.
  - (* tail: shift both sides and use Apply_val_shift0 *)
    rewrite !up_nth_S. apply Apply_val_shift0. apply H.
Qed.

(* Under a renaming the output of [Apply_ne] is a neutral (no beta). *)
Lemma ren_Apply_ne_isNe : forall m s n v,
    is_ren s -> Apply_ne m s n v -> { n' & v = vNe n' }.
Proof.
  intros m s n v Hr H. destruct (ren_Apply_ne_total n m Hr) as [n' Hn'].
  pose proof (Apply_ne_det H Hn') as ->. exists n'; reflexivity.
Qed.

(* Renaming substitution composition: [Apply_*] through [s1] then [s2] equals
   [Apply_*] through the composite [s3] (when [s1] is a renaming, so step 1
   never creates a beta).  By induction on the FIRST derivation, inverting the
   second.

   NOTE: [s2] need NOT be a renaming.  The induction only ever uses [is_ren s1]
   (via [ren_Apply_ne_isNe] in the app cases, to expose the [vapp_ne] shape);
   every value flowing into the second substitution is already a step-1 output,
   which is neutral wherever a head could otherwise beta-reduce.  So this is the
   stronger RENAMING-THEN-ARBITRARY composition — exactly the shape
   [Reflect_ren]'s Pi case needs ([b[up sg]] then [as :: id_list]), which is why
   no separate [Apply_ren_commute] is required. *)
Lemma Apply_ren_comp :
  (forall m1 s1 T T', Apply_ty m1 s1 T T' ->
     is_ren s1 -> forall m2 s2 s3 T'', RenSub m2 s2 s1 s3 ->
       Apply_ty m2 s2 T' T'' -> Apply_ty m2 s3 T T'')
  * (forall m1 s1 v v', Apply_val m1 s1 v v' ->
       is_ren s1 -> forall m2 s2 s3 v'', RenSub m2 s2 s1 s3 ->
         Apply_val m2 s2 v' v'' -> Apply_val m2 s3 v v'')
  * (forall m1 s1 n v, Apply_ne m1 s1 n v ->
       is_ren s1 -> forall m2 s2 s3 v'', RenSub m2 s2 s1 s3 ->
         Apply_val m2 s2 v v'' -> Apply_ne m2 s3 n v'')
  * (forall m vf a v, Vapp m vf a v -> unit)
  * (forall m vf a v, VappI m vf a v -> unit).
Proof.
  refine (Apply_mutind
    (fun m1 s1 T T' _ => is_ren s1 -> forall m2 s2 s3 T'',
       RenSub m2 s2 s1 s3 -> Apply_ty m2 s2 T' T'' -> Apply_ty m2 s3 T T'')
    (fun m1 s1 v v' _ => is_ren s1 -> forall m2 s2 s3 v'',
       RenSub m2 s2 s1 s3 -> Apply_val m2 s2 v' v'' -> Apply_val m2 s3 v v'')
    (fun m1 s1 n v _ => is_ren s1 -> forall m2 s2 s3 v'',
       RenSub m2 s2 s1 s3 -> Apply_val m2 s2 v v'' -> Apply_ne m2 s3 n v'')
    (fun _ _ _ _ _ => unit)
    (fun _ _ _ _ _ => unit)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m1 s1 r l Hr1 m2 s2 s3 T'' Hrs H2.
    inversion H2; subst. apply ap_dU.
  - (* ap_dEl *) intros m1 s1 e e' He IHe Hr1 m2 s2 s3 T'' Hrs H2.
    inversion H2; subst. apply ap_dEl. eapply IHe; eauto.
  - (* ap_ne *) intros m1 s1 n v Hn IHn Hr1 m2 s2 s3 v'' Hrs H2.
    apply ap_ne. eapply IHn; eauto.
  - (* ap_zero *) intros m1 s1 Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_zero.
  - (* ap_suc *) intros m1 s1 v v' Hv IHv Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_suc. eapply IHv; eauto.
  - (* ap_nat *) intros m1 s1 Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_nat.
  - (* ap_empty *) intros m1 s1 Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_empty.
  - (* ap_pi *) intros m1 s1 F F' B B' HF IHF HB IHB Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_pi.
    + eapply IHF; eauto.
    + eapply IHB;
        [ exact (is_ren_up Hr1) | exact (RenSub_up Hrs) | eassumption ].
  - (* ap_piI *) intros m1 s1 F F' B B' HF IHF HB IHB Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_piI.
    + eapply IHF; eauto.
    + eapply IHB;
        [ exact (is_ren_up Hr1) | exact (RenSub_up Hrs) | eassumption ].
  - (* ap_lam *) intros m1 s1 b b' Hb IHb Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_lam.
    eapply IHb;
      [ exact (is_ren_up Hr1) | exact (RenSub_up Hrs) | eassumption ].
  - (* ap_lamI *) intros m1 s1 b b' Hb IHb Hr1 m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_lamI.
    eapply IHb;
      [ exact (is_ren_up Hr1) | exact (RenSub_up Hrs) | eassumption ].
  - (* ap_var *) intros m1 s1 k Hr1 m2 s2 s3 v'' Hrs H2.
    pose proof (Hrs k) as Hk.
    pose proof (Apply_val_det H2 Hk) as ->. apply ap_var.
  - (* ap_emptyrec *) intros m1 s1 rA lA A A' scrut scrut' HA IHA Hsc IHsc Hr1
      m2 s2 s3 v'' Hrs H2.
    inversion H2; subst.
    match goal with Hne : Apply_ne m2 s2 (nEmptyrec _ _ _ _) _ |- _ => inversion Hne; subst end.
    apply ap_emptyrec.
    + eapply IHA; eauto.
    + eapply IHsc; eauto. apply ap_ne; eassumption.
  - (* ap_app *) intros m1 s1 f vf a a' v Hf IHf Ha IHa Hvapp IHvapp Hr1
      m2 s2 s3 v'' Hrs H2.
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hne : Apply_ne m2 s2 (nApp _ _) _ |- _ => inversion Hne; subst end.
    eapply ap_app.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHa; eauto.
    + eassumption.
  - (* ap_appI *) intros m1 s1 f vf a a' v Hf IHf Ha IHa Hvapp IHvapp Hr1
      m2 s2 s3 v'' Hrs H2.
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hne : Apply_ne m2 s2 (nAppI _ _) _ |- _ => inversion Hne; subst end.
    eapply ap_appI.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHa; eauto.
    + eassumption.
  - (* vapp_lam *) intros; exact tt.
  - (* vapp_ne *) intros; exact tt.
  - (* vappI_lam *) intros; exact tt.
  - (* vappI_ne *) intros; exact tt.
Qed.

Definition Apply_ty_ren_comp  := fst (fst (fst (fst Apply_ren_comp))).
Definition Apply_val_ren_comp := snd (fst (fst (fst Apply_ren_comp))).
Definition Apply_ne_ren_comp  := snd (fst (fst Apply_ren_comp)).

(* ===================================================================== *)
(* SCOPED renaming composition + the beta-merge it powers.                 *)
(*                                                                         *)
(* The unconditional [RenSub] composite is UNSOUND for the merge we need    *)
(* ([a :: id_list] AFTER [up sg]): for [length sg <= k], [up sg] pads with   *)
(* the shifted-identity [vNe (nVar (S k))] forever, while [a :: id_list]     *)
(* un-shifts it back to [vNe (nVar k)] — they can never agree for unbounded  *)
(* [k].  But the values we compose ([body], a reflection) are SCOPED, so     *)
(* they only read indices below their bound; a [RenSub] restricted to        *)
(* in-range [k] suffices.  This scoped composition, plus the [a :: sg]       *)
(* witness, is exactly the body substitution in [reflect_pi_beta_step]:       *)
(* [body[up sg][a :: id_list]] = [body[a :: sg]].                           *)
(* ===================================================================== *)

(* In-range composite: [sg3] is the [sg2]-image of [sg1], for indices [< N]. *)
Definition RenSubSc (N m2 : nat) (sg2 sg1 sg3 : ssub) : Type :=
  forall k, k < N ->
    Apply_val m2 sg2 (nth_default (vNe (nVar k)) sg1 k)
                     (nth_default (vNe (nVar k)) sg3 k).

Lemma RenSubSc_up : forall N m2 sg2 sg1 sg3,
    RenSubSc N m2 sg2 sg1 sg3 -> RenSubSc (S N) (S m2) (up sg2) (up sg1) (up sg3).
Proof.
  intros N m2 sg2 sg1 sg3 H k Hk. destruct k as [|k'].
  - unfold up, nth_default. cbn [nth_error].
    apply ap_ne. change (vNe (nVar 0)) with (nth_default (vNe (nVar 0)) (up sg2) 0) at 2.
    apply ap_var.
  - rewrite !up_nth_S. apply Apply_val_shift0. apply H. Lia.lia.
Qed.

(* Scoped renaming-then-arbitrary composition: identical to [Apply_ren_comp]
   but the composite [RenSub] need only hold below the scope bound [N] of the
   value being substituted.  (The [Vapp]/[VappI] motives stay [unit] — [s1] is
   still a renaming, so the first derivation never betas.) *)
Lemma Apply_ren_comp_sc :
  (forall m1 s1 T T', Apply_ty m1 s1 T T' ->
     is_ren s1 -> forall N, ne_below_ty N T -> forall m2 s2 s3 T'',
       RenSubSc N m2 s2 s1 s3 -> Apply_ty m2 s2 T' T'' -> Apply_ty m2 s3 T T'')
  * (forall m1 s1 v v', Apply_val m1 s1 v v' ->
       is_ren s1 -> forall N, ne_below_val N v -> forall m2 s2 s3 v'',
         RenSubSc N m2 s2 s1 s3 -> Apply_val m2 s2 v' v'' -> Apply_val m2 s3 v v'')
  * (forall m1 s1 n v, Apply_ne m1 s1 n v ->
       is_ren s1 -> forall N, ne_below_ne N n -> forall m2 s2 s3 v'',
         RenSubSc N m2 s2 s1 s3 -> Apply_val m2 s2 v v'' -> Apply_ne m2 s3 n v'')
  * (forall m vf a v, Vapp m vf a v -> unit)
  * (forall m vf a v, VappI m vf a v -> unit).
Proof.
  refine (Apply_mutind
    (fun m1 s1 T T' _ => is_ren s1 -> forall N, ne_below_ty N T -> forall m2 s2 s3 T'',
       RenSubSc N m2 s2 s1 s3 -> Apply_ty m2 s2 T' T'' -> Apply_ty m2 s3 T T'')
    (fun m1 s1 v v' _ => is_ren s1 -> forall N, ne_below_val N v -> forall m2 s2 s3 v'',
       RenSubSc N m2 s2 s1 s3 -> Apply_val m2 s2 v' v'' -> Apply_val m2 s3 v v'')
    (fun m1 s1 n v _ => is_ren s1 -> forall N, ne_below_ne N n -> forall m2 s2 s3 v'',
       RenSubSc N m2 s2 s1 s3 -> Apply_val m2 s2 v v'' -> Apply_ne m2 s3 n v'')
    (fun _ _ _ _ _ => unit)
    (fun _ _ _ _ _ => unit)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m1 s1 r l Hr1 N Hne m2 s2 s3 T'' Hrs H2.
    inversion H2; subst. apply ap_dU.
  - (* ap_dEl *) intros m1 s1 e e' He IHe Hr1 N Hne m2 s2 s3 T'' Hrs H2.
    cbn [ne_below_ty] in Hne. inversion H2; subst. apply ap_dEl. eapply IHe; eauto.
  - (* ap_ne *) intros m1 s1 n v Hn IHn Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_val] in Hne. apply ap_ne. eapply IHn; eauto.
  - (* ap_zero *) intros m1 s1 Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_zero.
  - (* ap_suc *) intros m1 s1 v v' Hv IHv Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_val] in Hne. inversion H2; subst. apply ap_suc. eapply IHv; eauto.
  - (* ap_nat *) intros m1 s1 Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_nat.
  - (* ap_empty *) intros m1 s1 Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    inversion H2; subst. apply ap_empty.
  - (* ap_pi *) intros m1 s1 F F' B B' HF IHF HB IHB Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB].
    inversion H2; subst. apply ap_pi.
    + eapply IHF; eauto.
    + eapply IHB;
        [ exact (is_ren_up Hr1) | exact HneB | exact (RenSubSc_up Hrs) | eassumption ].
  - (* ap_piI *) intros m1 s1 F F' B B' HF IHF HB IHB Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB].
    inversion H2; subst. apply ap_piI.
    + eapply IHF; eauto.
    + eapply IHB;
        [ exact (is_ren_up Hr1) | exact HneB | exact (RenSubSc_up Hrs) | eassumption ].
  - (* ap_lam *) intros m1 s1 b b' Hb IHb Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_val] in Hne. inversion H2; subst. apply ap_lam.
    eapply IHb;
      [ exact (is_ren_up Hr1) | exact Hne | exact (RenSubSc_up Hrs) | eassumption ].
  - (* ap_lamI *) intros m1 s1 b b' Hb IHb Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_val] in Hne. inversion H2; subst. apply ap_lamI.
    eapply IHb;
      [ exact (is_ren_up Hr1) | exact Hne | exact (RenSubSc_up Hrs) | eassumption ].
  - (* ap_var *) intros m1 s1 k Hr1 N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_ne] in Hne.
    pose proof (Hrs k Hne) as Hk.
    pose proof (Apply_val_det H2 Hk) as ->. apply ap_var.
  - (* ap_emptyrec *) intros m1 s1 rA lA A A' scrut scrut' HA IHA Hsc IHsc Hr1
      N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_ne] in Hne. destruct Hne as [HneA Hnesc].
    inversion H2; subst.
    match goal with Hn2 : Apply_ne m2 s2 (nEmptyrec _ _ _ _) _ |- _ => inversion Hn2; subst end.
    apply ap_emptyrec.
    + eapply IHA; eauto.
    + eapply IHsc; eauto. apply ap_ne; eassumption.
  - (* ap_app *) intros m1 s1 f vf a a' v Hf IHf Ha IHa Hvapp IHvapp Hr1
      N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_ne] in Hne. destruct Hne as [Hnef Hnea].
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hn2 : Apply_ne m2 s2 (nApp _ _) _ |- _ => inversion Hn2; subst end.
    eapply ap_app.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHa; eauto.
    + eassumption.
  - (* ap_appI *) intros m1 s1 f vf a a' v Hf IHf Ha IHa Hvapp IHvapp Hr1
      N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_ne] in Hne. destruct Hne as [Hnef Hnea].
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hn2 : Apply_ne m2 s2 (nAppI _ _) _ |- _ => inversion Hn2; subst end.
    eapply ap_appI.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHa; eauto.
    + eassumption.
  - (* vapp_lam *) intros; exact tt.
  - (* vapp_ne *) intros; exact tt.
  - (* vappI_lam *) intros; exact tt.
  - (* vappI_ne *) intros; exact tt.
Qed.

Definition Apply_val_ren_comp_sc := snd (fst (fst (fst Apply_ren_comp_sc))).

(* The composite [a :: sg] of [up sg] then [a :: id_list]: head goes to [a]
   (the bound variable receives [a]); each tail entry [up sg @ S k] =
   [shift_val 0 1 (sg @ k)] is un-shifted by [a :: id_list] back to [sg @ k]
   (via [Apply_val_cancel] + [Apply_val_id]), since [sg @ k] is scoped in
   [Delta] (it is [has_svalty Delta] by [wf_ssub]).  Scoped to [< S (length Ge)]
   — all body indices land in [sg]'s range. *)
Lemma RenSubSc_beta : forall Delta sg Ge a,
    is_ren sg -> wf_ssub Delta sg Ge ->
    RenSubSc (S (length Ge)) (length Delta)
             (a :: id_list (length Delta)) (up sg) (a :: sg).
Proof.
  intros Delta sg Ge a Hr [Hlen Hwf] k Hk. destruct k as [|k'].
  - (* head: up sg @ 0 = vNe(nVar 0); a :: sg @ 0 = a. *)
    unfold up, nth_default. cbn [nth_error].
    apply ap_ne.
    change a with (nth_default (vNe (nVar 0)) (a :: id_list (length Delta)) 0) at 2.
    apply ap_var.
  - (* tail: shift_val 0 1 (sg @ k') un-shifted by a :: id_list back to sg @ k'. *)
    rewrite up_nth_S. rewrite nth_default_cons_S.
    assert (Hk' : k' < length Ge) by Lia.lia.
    assert (Hkl : k' < length sg) by (rewrite Hlen; exact Hk').
    (* normalize the two differing read-defaults (in range, so irrelevant) *)
    rewrite (nth_default_irrel sg (vNe (nVar k')) (vNe (nVar 0)) Hkl).
    rewrite (nth_default_irrel sg (vNe (nVar (S k'))) (vNe (nVar 0)) Hkl).
    (* sg @ k' is well-typed in Delta, hence scoped below length Delta *)
    assert (Hsome : { T & nth_error Ge k' = Some T }).
    { destruct (nth_error Ge k') as [T|] eqn:E.
      - exists T; reflexivity.
      - exfalso. apply nth_error_None in E. Lia.lia. }
    destruct Hsome as [T HT].
    destruct (Hwf k' T HT) as [T' [Hap Hhas]].
    pose proof (has_svalty_scoped Hhas) as Hsc.
    pose proof (InsAt_base (id_list (length Delta)) a) as Hins.
    rewrite id_list_length in Hins.
    exact (Apply_val_cancel Hsc Hins (Apply_val_id _ _)).
Qed.

(* The body substitution merge for [reflect_pi_beta_step]:
   [body[up sg]] then beta by [a :: id_list] equals [body[a :: sg]]. *)
Lemma Apply_beta_merge : forall Delta sg Ge a body bodysg v,
    is_ren sg -> wf_ssub Delta sg Ge ->
    ne_below_val (S (length Ge)) body ->
    Apply_val (S (length Delta)) (up sg) body bodysg ->
    Apply_val (length Delta) (a :: id_list (length Delta)) bodysg v ->
    Apply_val (length Delta) (a :: sg) body v.
Proof.
  intros Delta sg Ge a body bodysg v Hr Hws Hne Hbs Hsecond.
  eapply (Apply_val_ren_comp_sc Hbs (is_ren_up Hr) Hne);
    [ exact (RenSubSc_beta a Hr Hws) | exact Hsecond ].
Qed.

