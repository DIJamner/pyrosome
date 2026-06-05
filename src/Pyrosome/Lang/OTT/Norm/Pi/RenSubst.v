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
  Domain Apply ApplyLemmas Typing Preservation ApplySubst.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Renaming algebra for the [is_ren] predicate (LogRel2.v) that gates the   *)
(* application clause of [PiRedTmEq].  Ported (with the [(F,B)] neutral      *)
(* annotations) from the retired single-sided                               *)
(* WIP/OTT_LogRel_single_sided/LogRelRen.v; this is the substitution/        *)
(* renaming infrastructure that the two-sided RENAMING STABILITY presheaf    *)
(* (LR2 over renamings) reuses.  Independent of any [LogRel*] development --  *)
(* purely structural facts about [Apply_*] under variable-only substitutions.*)
(* ===================================================================== *)

(* [is_ren] lives in LogRel2.v but is a purely syntactic predicate; restate
   it here so this file does not depend on the relation layer. *)
Definition is_ren (sg : ssub) : Type :=
  { rho : list nat & sg = map (fun k => vNe (nVar k)) rho }.

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
(* Applying a renaming never creates a beta redex (a variable head maps to  *)
(* a variable head, so every [Vapp]/[VappI] stays in its [vapp_ne]/         *)
(* [vappI_ne] case): substitution is structurally terminating on ALL        *)
(* values, and a neutral maps to a neutral.  Proof by [sval_mutind]; the     *)
(* binder cases use [is_ren_up].  This is the totality witness that general  *)
(* substitutions lack (and that PER transitivity needs but cannot get).      *)
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
  - (* nApp -- F renamed at the cutoff, B under one binder ([up sg]) *)
    intros f IHf F IHF B IHB a IHa m sg Hr.
    destruct (IHf m sg Hr) as [nf' Hf].
    destruct (IHF m sg Hr) as [F' HF].
    destruct (IHB (S m) (up sg) (is_ren_up Hr)) as [B' HB].
    destruct (IHa m sg Hr) as [a' Ha].
    exists (nApp nf' F' B' a').
    eapply ap_app; [ exact Hf | exact HF | exact HB | exact Ha | apply vapp_ne ].
  - (* nAppI *)
    intros f IHf F IHF B IHB a IHa m sg Hr.
    destruct (IHf m sg Hr) as [nf' Hf].
    destruct (IHF m sg Hr) as [F' HF].
    destruct (IHB (S m) (up sg) (is_ren_up Hr)) as [B' HB].
    destruct (IHa m sg Hr) as [a' Ha].
    exists (nAppI nf' F' B' a').
    eapply ap_appI; [ exact Hf | exact HF | exact HB | exact Ha | apply vappI_ne ].
Qed.

Definition ren_Apply_ty_total  := fst ren_Apply_total.
Definition ren_Apply_val_total := fst (snd ren_Apply_total).
Definition ren_Apply_ne_total  := snd (snd ren_Apply_total).

(* ===================================================================== *)
(* Scope monotonicity + Apply-preserves-scope.                             *)
(*                                                                         *)
(* Shifting at any cutoff extends the scope by one; scope is monotone in    *)
(* the level; applying a substitution whose [<N] entries are scoped at the  *)
(* target level [m] sends an [<N]-scoped value to an [m]-scoped one.        *)
(* ===================================================================== *)

(* Shifting at any cutoff extends the scope by one. *)
Lemma ne_below_shift :
  (forall T m c, ne_below_ty m T -> ne_below_ty (S m) (shift_ty c 1 T))
  * ((forall v m c, ne_below_val m v -> ne_below_val (S m) (shift_val c 1 v))
  *  (forall n m c, ne_below_ne m n -> ne_below_ne (S m) (shift_ne c 1 n))).
Proof.
  apply (sval_mutind
    (fun T  => forall m c, ne_below_ty  m T -> ne_below_ty  (S m) (shift_ty  c 1 T))
    (fun v  => forall m c, ne_below_val m v -> ne_below_val (S m) (shift_val c 1 v))
    (fun nn => forall m c, ne_below_ne  m nn -> ne_below_ne  (S m) (shift_ne  c 1 nn)));
    try (intros; exact I).
  - (* dEl *) intros e IHe m c H. apply IHe; exact H.
  - (* vNe *) intros nn IHnn m c H. apply IHnn; exact H.
  - (* vSuc *) intros v IHv m c H. apply IHv; exact H.
  - (* vPi *) intros F IHF B IHB m c [HF HB]. split; [ apply IHF | apply IHB ]; assumption.
  - (* vPiI *) intros F IHF B IHB m c [HF HB]. split; [ apply IHF | apply IHB ]; assumption.
  - (* vLam *) intros b IHb m c H. apply IHb; exact H.
  - (* vLamI *) intros b IHb m c H. apply IHb; exact H.
  - (* nVar *) intros k m c H. cbn [ne_below_ne] in H. cbn [shift_ne].
    destruct (Nat.ltb k c); cbn [ne_below_ne]; Lia.lia.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m c [HA Hs].
    split; [ apply IHA | apply IHscr ]; assumption.
  - (* nApp -- F at cutoff [c], B at [S c] *)
    intros f IHf F IHF B IHB a IHa m c H. cbn [ne_below_ne] in H |- *.
    destruct H as (Hf & HF & HB & Ha).
    repeat split; [ apply IHf | apply IHF | apply IHB | apply IHa ]; assumption.
  - (* nAppI *)
    intros f IHf F IHF B IHB a IHa m c H. cbn [ne_below_ne] in H |- *.
    destruct H as (Hf & HF & HB & Ha).
    repeat split; [ apply IHf | apply IHF | apply IHB | apply IHa ]; assumption.
Qed.

Definition ne_below_shift_val := fst (snd ne_below_shift).
Definition ne_below_shift_ne  := snd (snd ne_below_shift).

(* Scope monotonicity. *)
Lemma ne_below_mono :
  (forall T m, ne_below_ty m T -> forall P, m <= P -> ne_below_ty P T)
  * ((forall v m, ne_below_val m v -> forall P, m <= P -> ne_below_val P v)
  *  (forall n m, ne_below_ne m n -> forall P, m <= P -> ne_below_ne P n)).
Proof.
  apply (sval_mutind
    (fun T  => forall m, ne_below_ty  m T -> forall P, m <= P -> ne_below_ty  P T)
    (fun v  => forall m, ne_below_val m v -> forall P, m <= P -> ne_below_val P v)
    (fun nn => forall m, ne_below_ne  m nn -> forall P, m <= P -> ne_below_ne  P nn));
    try (intros; exact I).
  - intros e IHe m H P HP. apply (IHe m); assumption.
  - intros nn IHnn m H P HP. apply (IHnn m); assumption.
  - intros v IHv m H P HP. apply (IHv m); assumption.
  - intros F IHF B IHB m [HF HB] P HP. split; [ apply (IHF m) | apply (IHB (S m)) ]; auto; Lia.lia.
  - intros F IHF B IHB m [HF HB] P HP. split; [ apply (IHF m) | apply (IHB (S m)) ]; auto; Lia.lia.
  - intros b IHb m H P HP. apply (IHb (S m)); [ exact H | Lia.lia ].
  - intros b IHb m H P HP. apply (IHb (S m)); [ exact H | Lia.lia ].
  - intros k m H P HP. cbn [ne_below_ne] in *. Lia.lia.
  - intros rA lA A IHA scrut IHscr m [HA Hs] P HP.
    split; [ apply (IHA m) | apply (IHscr m) ]; assumption.
  - (* nApp *) intros f IHf F IHF B IHB a IHa m H P HP.
    cbn [ne_below_ne] in H |- *. destruct H as (Hf & HF & HB & Ha).
    repeat split;
      [ apply (IHf m Hf P HP) | apply (IHF m HF P HP)
      | apply (IHB (S m) HB (S P)); Lia.lia | apply (IHa m Ha P HP) ].
  - (* nAppI *) intros f IHf F IHF B IHB a IHa m H P HP.
    cbn [ne_below_ne] in H |- *. destruct H as (Hf & HF & HB & Ha).
    repeat split;
      [ apply (IHf m Hf P HP) | apply (IHF m HF P HP)
      | apply (IHB (S m) HB (S P)); Lia.lia | apply (IHa m Ha P HP) ].
Qed.

Definition ne_below_val_mono := fst (snd ne_below_mono).

(* A substitution whose [<N] entries are scoped at the target level [m]. *)
Definition sub_below (N m : nat) (s : ssub) : Prop :=
  forall k, k < N -> ne_below_val m (nth_default (vNe (nVar k)) s k).

Lemma sub_below_up : forall N m s,
    sub_below N m s -> sub_below (S N) (S m) (up s).
Proof.
  intros N m s H k Hk. destruct k as [|k'].
  - replace (nth_default (vNe (nVar 0)) (up s) 0) with (vNe (nVar 0))
      by (unfold up, nth_default; reflexivity).
    cbn [ne_below_val ne_below_ne]. Lia.lia.
  - rewrite nth_default_up. apply ne_below_shift_val. apply H. Lia.lia.
Qed.

Lemma sub_below_beta : forall N m a, N <= m -> ne_below_val m a ->
    sub_below (S N) m (a :: id_list m).
Proof.
  intros N m a HNm Ha k Hk. destruct k as [|k'].
  - unfold nth_default; cbn [nth_error]. exact Ha.
  - rewrite nth_default_cons_S.
    assert (Hk'm : k' < m) by Lia.lia.
    rewrite (id_list_nth_any m k'), (@ltbT k' m Hk'm).
    cbn [ne_below_val ne_below_ne]. exact Hk'm.
Qed.

(* Apply preserves scoping: a scoped value under a scoped substitution lands
   on an [m]-scoped value (the neutral output is a value, possibly not a
   neutral after a beta). *)
Lemma Apply_ne_below :
  (forall m s T T', Apply_ty m s T T' ->
     forall N, ne_below_ty N T -> sub_below N m s -> ne_below_ty m T')
  * (forall m s v v', Apply_val m s v v' ->
       forall N, ne_below_val N v -> sub_below N m s -> ne_below_val m v')
  * (forall m s n v, Apply_ne m s n v ->
        forall N, ne_below_ne N n -> sub_below N m s -> ne_below_val m v)
  * (forall m F B vf a v, Vapp m F B vf a v ->
        ne_below_val m vf -> ne_below_val m a ->
        ne_below_val m F -> ne_below_val (S m) B -> ne_below_val m v)
  * (forall m F B vf a v, VappI m F B vf a v ->
        ne_below_val m vf -> ne_below_val m a ->
        ne_below_val m F -> ne_below_val (S m) B -> ne_below_val m v).
Proof.
  refine (Apply_mutind
    (fun m s T T' _ => forall N, ne_below_ty N T -> sub_below N m s -> ne_below_ty m T')
    (fun m s v v' _ => forall N, ne_below_val N v -> sub_below N m s -> ne_below_val m v')
    (fun m s n v _  => forall N, ne_below_ne N n -> sub_below N m s -> ne_below_val m v)
    (fun m F B vf a v _ => ne_below_val m vf -> ne_below_val m a ->
       ne_below_val m F -> ne_below_val (S m) B -> ne_below_val m v)
    (fun m F B vf a v _ => ne_below_val m vf -> ne_below_val m a ->
       ne_below_val m F -> ne_below_val (S m) B -> ne_below_val m v)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m s r l N _ _. exact I.
  - (* ap_dEl *) intros m s e e' He IHe N Hne Hsub. cbn [ne_below_ty] in *. apply (IHe N); assumption.
  - (* ap_ne *) intros m s n v Hn IHn N Hne Hsub. cbn [ne_below_val] in Hne. apply (IHn N); assumption.
  - (* ap_zero *) intros; exact I.
  - (* ap_suc *) intros m s v v' Hv IHv N Hne Hsub. cbn [ne_below_val] in *. apply (IHv N); assumption.
  - (* ap_nat *) intros; exact I.
  - (* ap_empty *) intros; exact I.
  - (* ap_pi *) intros m s F F' B B' HF IHF HB IHB N Hne Hsub.
    cbn [ne_below_val] in Hne |- *. destruct Hne as [HneF HneB]. split.
    + apply (IHF N); assumption.
    + apply (IHB (S N)); [ exact HneB | apply sub_below_up; exact Hsub ].
  - (* ap_piI *) intros m s F F' B B' HF IHF HB IHB N Hne Hsub.
    cbn [ne_below_val] in Hne |- *. destruct Hne as [HneF HneB]. split.
    + apply (IHF N); assumption.
    + apply (IHB (S N)); [ exact HneB | apply sub_below_up; exact Hsub ].
  - (* ap_lam *) intros m s b b' Hb IHb N Hne Hsub.
    cbn [ne_below_val] in Hne |- *.
    apply (IHb (S N)); [ exact Hne | apply sub_below_up; exact Hsub ].
  - (* ap_lamI *) intros m s b b' Hb IHb N Hne Hsub.
    cbn [ne_below_val] in Hne |- *.
    apply (IHb (S N)); [ exact Hne | apply sub_below_up; exact Hsub ].
  - (* ap_var *) intros m s k N Hne Hsub. cbn [ne_below_ne] in Hne.
    apply Hsub; exact Hne.
  - (* ap_emptyrec *) intros m s rA lA A A' scrut scrut' HA IHA Hsc IHsc N Hne Hsub.
    cbn [ne_below_ne] in Hne. destruct Hne as [HneA Hnesc].
    cbn [ne_below_val ne_below_ne]. split.
    + apply (IHA N); assumption.
    + pose proof (IHsc N Hnesc Hsub) as Hv. cbn [ne_below_val] in Hv. exact Hv.
  - (* ap_app *) intros m s f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp N Hne Hsub.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    refine (IHvapp (IHf N Hnef Hsub) (IHa N Hnea Hsub) (IHF N HneF Hsub) _).
    apply (IHB (S N)); [ exact HneB | apply sub_below_up; exact Hsub ].
  - (* ap_appI *) intros m s f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp N Hne Hsub.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    refine (IHvapp (IHf N Hnef Hsub) (IHa N Hnea Hsub) (IHF N HneF Hsub) _).
    apply (IHB (S N)); [ exact HneB | apply sub_below_up; exact Hsub ].
  - (* vapp_lam *) intros m F B b a v Hbeta IHbeta Hnevf Hnea HneF HneB.
    cbn [ne_below_val] in Hnevf.
    apply (IHbeta (S m)); [ exact Hnevf | apply sub_below_beta; [ Lia.lia | exact Hnea ] ].
  - (* vapp_ne *) intros m F B n a Hnevf Hnea HneF HneB.
    cbn [ne_below_val ne_below_ne] in *. repeat split; assumption.
  - (* vappI_lam *) intros m F B b a v Hbeta IHbeta Hnevf Hnea HneF HneB.
    cbn [ne_below_val] in Hnevf.
    apply (IHbeta (S m)); [ exact Hnevf | apply sub_below_beta; [ Lia.lia | exact Hnea ] ].
  - (* vappI_ne *) intros m F B n a Hnevf Hnea HneF HneB.
    cbn [ne_below_val ne_below_ne] in *. repeat split; assumption.
Qed.

Definition Apply_ty_ne_below  := fst (fst (fst (fst Apply_ne_below))).
Definition Apply_val_ne_below := snd (fst (fst (fst Apply_ne_below))).
Definition Apply_ne_ne_below  := snd (fst (fst Apply_ne_below)).

(* ===================================================================== *)
(* Renaming substitution COMPOSITION.                                      *)
(*                                                                         *)
(* For RENAMINGS, [Apply_*] composes: applying [s1] then [s2] equals        *)
(* applying the pointwise composite [s3].  General composition is NOT       *)
(* separable (a [Vapp]-at-lambda needs beta totality = the normalization    *)
(* content); but a renaming never creates a beta ([ren_Apply_total]), so a   *)
(* clean structural induction on the FIRST derivation goes through.  [s2]    *)
(* need NOT be a renaming -- only [s1] -- so this is the stronger RENAMING-  *)
(* THEN-ARBITRARY composition the presheaf's Pi case needs.                  *)
(* ===================================================================== *)

(* The composite substitution relation: entry k of [sg3] = [sg2] applied to
   entry k of [sg1] (default-correct via the [vNe (nVar k)] read default). *)
Definition RenSub (m2 : nat) (sg2 sg1 sg3 : ssub) : Type :=
  forall k, Apply_val m2 sg2 (nth_default (vNe (nVar k)) sg1 k)
                             (nth_default (vNe (nVar k)) sg3 k).

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
    rewrite !nth_default_up. apply Apply_val_shift0. apply H.
Qed.

(* Under a renaming the output of [Apply_ne] is a neutral (no beta). *)
Lemma ren_Apply_ne_isNe : forall m s n v,
    is_ren s -> Apply_ne m s n v -> { n' & v = vNe n' }.
Proof.
  intros m s n v Hr H. destruct (ren_Apply_ne_total n m Hr) as [n' Hn'].
  pose proof (Apply_ne_det H Hn') as ->. exists n'; reflexivity.
Qed.

(* Renaming-then-arbitrary composition: [Apply_*] through [s1] then [s2]
   equals [Apply_*] through the composite [s3].  By induction on the FIRST
   derivation, inverting the second; the app cases expose the [vapp_ne] shape
   via [ren_Apply_ne_isNe], so no beta arises. *)
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
  * (forall m F B vf a v, Vapp m F B vf a v -> unit)
  * (forall m F B vf a v, VappI m F B vf a v -> unit).
Proof.
  refine (Apply_mutind
    (fun m1 s1 T T' _ => is_ren s1 -> forall m2 s2 s3 T'',
       RenSub m2 s2 s1 s3 -> Apply_ty m2 s2 T' T'' -> Apply_ty m2 s3 T T'')
    (fun m1 s1 v v' _ => is_ren s1 -> forall m2 s2 s3 v'',
       RenSub m2 s2 s1 s3 -> Apply_val m2 s2 v' v'' -> Apply_val m2 s3 v v'')
    (fun m1 s1 n v _ => is_ren s1 -> forall m2 s2 s3 v'',
       RenSub m2 s2 s1 s3 -> Apply_val m2 s2 v v'' -> Apply_ne m2 s3 n v'')
    (fun _ _ _ _ _ _ _ => unit)
    (fun _ _ _ _ _ _ _ => unit)
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
  - (* ap_app -- compose head f, domain F, codomain B (under [up]), arg a *)
    intros m1 s1 f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp Hr1
      m2 s2 s3 v'' Hrs H2.
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hne : Apply_ne m2 s2 (nApp _ _ _ _) _ |- _ => inversion Hne; subst end.
    eapply ap_app.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHF; eauto.
    + eapply IHB; [ exact (is_ren_up Hr1) | exact (RenSub_up Hrs) | eassumption ].
    + eapply IHa; eauto.
    + eassumption.
  - (* ap_appI *)
    intros m1 s1 f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp Hr1
      m2 s2 s3 v'' Hrs H2.
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hne : Apply_ne m2 s2 (nAppI _ _ _ _) _ |- _ => inversion Hne; subst end.
    eapply ap_appI.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHF; eauto.
    + eapply IHB; [ exact (is_ren_up Hr1) | exact (RenSub_up Hrs) | eassumption ].
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
