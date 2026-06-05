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
  Domain Apply ApplyLemmas Typing Preservation ApplySubst Reflect.
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

(* ===================================================================== *)
(* SCOPED renaming composition.                                            *)
(*                                                                         *)
(* Identical to [Apply_ren_comp] but the composite [RenSub] need only hold  *)
(* below the scope bound [N] of the value being substituted.  This is the   *)
(* variant the presheaf uses, since every real value is scoped (the         *)
(* unscoped composite is unsound past the scope bound -- [up sg] pads with   *)
(* the shifted identity forever while [a :: id_list] un-shifts it back).     *)
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
  - rewrite !nth_default_up. apply Apply_val_shift0. apply H. Lia.lia.
Qed.

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
  * (forall m F B vf a v, Vapp m F B vf a v -> unit)
  * (forall m F B vf a v, VappI m F B vf a v -> unit).
Proof.
  refine (Apply_mutind
    (fun m1 s1 T T' _ => is_ren s1 -> forall N, ne_below_ty N T -> forall m2 s2 s3 T'',
       RenSubSc N m2 s2 s1 s3 -> Apply_ty m2 s2 T' T'' -> Apply_ty m2 s3 T T'')
    (fun m1 s1 v v' _ => is_ren s1 -> forall N, ne_below_val N v -> forall m2 s2 s3 v'',
       RenSubSc N m2 s2 s1 s3 -> Apply_val m2 s2 v' v'' -> Apply_val m2 s3 v v'')
    (fun m1 s1 n v _ => is_ren s1 -> forall N, ne_below_ne N n -> forall m2 s2 s3 v'',
       RenSubSc N m2 s2 s1 s3 -> Apply_val m2 s2 v v'' -> Apply_ne m2 s3 n v'')
    (fun _ _ _ _ _ _ _ => unit)
    (fun _ _ _ _ _ _ _ => unit)
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
  - (* ap_app *) intros m1 s1 f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp Hr1
      N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hn2 : Apply_ne m2 s2 (nApp _ _ _ _) _ |- _ => inversion Hn2; subst end.
    eapply ap_app.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHF; eauto.
    + eapply IHB; [ exact (is_ren_up Hr1) | exact HneB | exact (RenSubSc_up Hrs) | eassumption ].
    + eapply IHa; eauto.
    + eassumption.
  - (* ap_appI *) intros m1 s1 f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp Hr1
      N Hne m2 s2 s3 v'' Hrs H2.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    destruct (ren_Apply_ne_isNe Hr1 Hf) as [nf' ->].
    inversion Hvapp; subst.
    inversion H2; subst.
    match goal with Hn2 : Apply_ne m2 s2 (nAppI _ _ _ _) _ |- _ => inversion Hn2; subst end.
    eapply ap_appI.
    + eapply IHf; eauto. apply ap_ne; eassumption.
    + eapply IHF; eauto.
    + eapply IHB; [ exact (is_ren_up Hr1) | exact HneB | exact (RenSubSc_up Hrs) | eassumption ].
    + eapply IHa; eauto.
    + eassumption.
  - (* vapp_lam *) intros; exact tt.
  - (* vapp_ne *) intros; exact tt.
  - (* vappI_lam *) intros; exact tt.
  - (* vappI_ne *) intros; exact tt.
Qed.

Definition Apply_ty_ren_comp_sc  := fst (fst (fst (fst Apply_ren_comp_sc))).
Definition Apply_val_ren_comp_sc := snd (fst (fst (fst Apply_ren_comp_sc))).
Definition Apply_ne_ren_comp_sc  := snd (fst (fst Apply_ren_comp_sc)).

(* ===================================================================== *)
(* SYNTACTIC renaming by an index list [rho : list nat].                    *)
(*                                                                         *)
(* The relational [Apply_*] form cannot NAME a renamed value inside a       *)
(* motive, which is exactly what "Apply commutes with renaming"            *)
(* ([Apply_ren_commute]) needs (it must existentially produce the          *)
(* substituted codomain of a beta step).  We therefore reify the renaming   *)
(* as a total function on values ([ren_val]/[ren_ne]/[ren_ty]), mirroring   *)
(* [shift_val] with the index map [renm rho] (identity past the end of      *)
(* [rho]) and [up_renl] under binders, and prove it AGREES with applying    *)
(* the substitution [ren_sub rho] ([map (vNe o nVar) rho], i.e. the         *)
(* [is_ren] witness).  Ported with the [(F,B)] neutral annotations          *)
(* ([nApp]/[nAppI] now carry domain [F] and codomain [B]).                  *)
(* ===================================================================== *)

(* The tail-of-[up] read identity (used by [RenShSc_up]). *)
Lemma up_nth_S : forall sg k,
    nth_default (vNe (nVar (S k))) (up sg) (S k)
    = shift_val 0 1 (nth_default (vNe (nVar k)) sg k).
Proof.
  intros sg k. unfold up. rewrite nth_default_cons_S. unfold nth_default.
  rewrite nth_error_map. destruct (nth_error sg k) as [e|] eqn:E; cbn [option_map].
  - reflexivity.
  - cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

Definition renm (rho : list nat) (k : nat) : nat := nth_default k rho k.
Definition up_renl (rho : list nat) : list nat := 0 :: map S rho.
Definition ren_sub (rho : list nat) : ssub := map (fun k => vNe (nVar k)) rho.

Fixpoint ren_val (rho : list nat) (v : sval) : sval :=
  match v with
  | vNe n => vNe (ren_ne rho n)
  | vZero => vZero
  | vSuc v' => vSuc (ren_val rho v')
  | vNat => vNat
  | vEmpty => vEmpty
  | vPi F B => vPi (ren_val rho F) (ren_val (up_renl rho) B)
  | vPiI F B => vPiI (ren_val rho F) (ren_val (up_renl rho) B)
  | vLam b => vLam (ren_val (up_renl rho) b)
  | vLamI b => vLamI (ren_val (up_renl rho) b)
  end
with ren_ne (rho : list nat) (n : neutral) : neutral :=
  match n with
  | nVar k => nVar (renm rho k)
  | nEmptyrec rA lA A s => nEmptyrec rA lA (ren_val rho A) (ren_ne rho s)
  | nApp f F B a =>
      nApp (ren_ne rho f) (ren_val rho F) (ren_val (up_renl rho) B) (ren_val rho a)
  | nAppI f F B a =>
      nAppI (ren_ne rho f) (ren_val rho F) (ren_val (up_renl rho) B) (ren_val rho a)
  end.

Definition ren_ty (rho : list nat) (T : svalty) : svalty :=
  match T with
  | dU r l => dU r l
  | dEl e => dEl (ren_val rho e)
  end.

(* [ren_sub] is an [is_ren] witness. *)
Lemma is_ren_ren_sub : forall rho, is_ren (ren_sub rho).
Proof. intro rho. exists rho. reflexivity. Qed.

(* Reading the renaming substitution at [k] yields the [renm]-relocated var. *)
Lemma ren_sub_nth : forall rho k,
    nth_default (vNe (nVar k)) (ren_sub rho) k = vNe (nVar (renm rho k)).
Proof.
  intros rho k. unfold ren_sub, renm, nth_default. rewrite nth_error_map.
  destruct (nth_error rho k) as [j|]; reflexivity.
Qed.

Lemma renm_up_0 : forall rho, renm (up_renl rho) 0 = 0.
Proof. intro rho. reflexivity. Qed.

Lemma renm_up_S : forall rho k, renm (up_renl rho) (S k) = S (renm rho k).
Proof.
  intros rho k. unfold renm, up_renl, nth_default. cbn [nth_error].
  rewrite nth_error_map. destruct (nth_error rho k); reflexivity.
Qed.

(* [up] of the renaming substitution is the substitution of the lifted list. *)
Lemma up_ren_sub : forall rho, up (ren_sub rho) = ren_sub (up_renl rho).
Proof.
  intro rho. unfold up, ren_sub, up_renl. cbn [map]. f_equal.
  rewrite !map_map. apply map_ext. intro k.
  cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

(* [ren_val] AGREES with applying the renaming substitution [ren_sub rho]. *)
Lemma ren_is_Apply :
  (forall T m rho, Apply_ty m (ren_sub rho) T (ren_ty rho T))
  * ((forall v m rho, Apply_val m (ren_sub rho) v (ren_val rho v))
  *  (forall n m rho, Apply_ne m (ren_sub rho) n (vNe (ren_ne rho n)))).
Proof.
  apply (sval_mutind
    (fun T  => forall m rho, Apply_ty  m (ren_sub rho) T (ren_ty rho T))
    (fun v  => forall m rho, Apply_val m (ren_sub rho) v (ren_val rho v))
    (fun nn => forall m rho, Apply_ne  m (ren_sub rho) nn (vNe (ren_ne rho nn)))).
  - (* dU *) intros r l m rho. apply ap_dU.
  - (* dEl *) intros e IHe m rho. apply ap_dEl. apply IHe.
  - (* vNe *) intros nn IHnn m rho. apply ap_ne. apply IHnn.
  - (* vZero *) intros m rho. apply ap_zero.
  - (* vSuc *) intros v IHv m rho. apply ap_suc. apply IHv.
  - (* vNat *) intros m rho. apply ap_nat.
  - (* vEmpty *) intros m rho. apply ap_empty.
  - (* vPi *) intros F IHF B IHB m rho. cbn [ren_val]. apply ap_pi.
    + apply IHF.
    + rewrite up_ren_sub. apply IHB.
  - (* vPiI *) intros F IHF B IHB m rho. cbn [ren_val]. apply ap_piI.
    + apply IHF.
    + rewrite up_ren_sub. apply IHB.
  - (* vLam *) intros b IHb m rho. cbn [ren_val]. apply ap_lam.
    rewrite up_ren_sub. apply IHb.
  - (* vLamI *) intros b IHb m rho. cbn [ren_val]. apply ap_lamI.
    rewrite up_ren_sub. apply IHb.
  - (* nVar *) intros k m rho. cbn [ren_ne].
    rewrite <- (ren_sub_nth rho k). apply ap_var.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m rho. cbn [ren_ne ren_val].
    apply ap_emptyrec; [ apply IHA | apply IHscr ].
  - (* nApp *) intros f IHf F IHF B IHB a IHa m rho. cbn [ren_ne ren_val].
    eapply ap_app;
      [ apply IHf | apply IHF | rewrite up_ren_sub; apply IHB | apply IHa | apply vapp_ne ].
  - (* nAppI *) intros f IHf F IHF B IHB a IHa m rho. cbn [ren_ne ren_val].
    eapply ap_appI;
      [ apply IHf | apply IHF | rewrite up_ren_sub; apply IHB | apply IHa | apply vappI_ne ].
Qed.

Definition ren_is_Apply_ty  := fst ren_is_Apply.
Definition ren_is_Apply_val := fst (snd ren_is_Apply).
Definition ren_is_Apply_ne  := snd (snd ren_is_Apply).

(* The renamed image is UNIQUE: any [Apply] by a renaming substitution lands
   on the syntactic [ren_*] (by determinism). *)
Lemma Apply_ren_eq :
  (forall m rho T T', Apply_ty m (ren_sub rho) T T' -> T' = ren_ty rho T)
  * ((forall m rho v v', Apply_val m (ren_sub rho) v v' -> v' = ren_val rho v)
  *  (forall m rho n v', Apply_ne m (ren_sub rho) n v' -> v' = vNe (ren_ne rho n))).
Proof.
  repeat split.
  - intros m rho T T' H. exact (Apply_ty_det H (ren_is_Apply_ty T m rho)).
  - intros m rho v v' H. exact (Apply_val_det H (ren_is_Apply_val v m rho)).
  - intros m rho n v' H. exact (Apply_ne_det H (ren_is_Apply_ne n m rho)).
Qed.

(* ===================================================================== *)
(* SCOPED renaming-conjugation [RenShSc], the renaming analogue of          *)
(* [ShiftSub] for "Apply commutes with renaming".  Carries TWO index maps   *)
(* [rho_b] (input/binder side) and [rho_v] (output side); they coincide      *)
(* except inside a beta step (the [cb]/[cv] split).                          *)
(* ===================================================================== *)

Definition RenShSc (N m2 : nat) (rho_b rho_v : list nat) (s s2 : ssub) : Type :=
  forall k, k < N ->
    Apply_val m2 (ren_sub rho_v) (nth_default (vNe (nVar k)) s k)
             (nth_default (vNe (nVar (renm rho_b k))) s2 (renm rho_b k)).

(* The renaming maps the [< N] indices into the target level [m2]. *)
Definition ren_ok (rho : list nat) (N m2 : nat) : Prop :=
  forall k, k < N -> renm rho k < m2.

Lemma ren_ok_up : forall rho N m2,
    ren_ok rho N m2 -> ren_ok (up_renl rho) (S N) (S m2).
Proof.
  intros rho N m2 H k Hk. destruct k as [|k'].
  - rewrite renm_up_0. Lia.lia.
  - rewrite renm_up_S. assert (renm rho k' < m2) by (apply H; Lia.lia). Lia.lia.
Qed.

Lemma ren_ok_le : forall rho N N' m2, ren_ok rho N m2 -> N' <= N -> ren_ok rho N' m2.
Proof. intros rho N N' m2 H Hle k Hk. apply H. Lia.lia. Qed.

Lemma RenShSc_up : forall N m2 rho_b rho_v s s2,
    RenShSc N m2 rho_b rho_v s s2 ->
    RenShSc (S N) (S m2) (up_renl rho_b) (up_renl rho_v) (up s) (up s2).
Proof.
  intros N m2 rho_b rho_v s s2 H k Hk. destruct k as [|k'].
  - (* head: both read [vNe (nVar 0)] *)
    rewrite renm_up_0.
    replace (nth_default (vNe (nVar 0)) (up s) 0) with (vNe (nVar 0))
      by (unfold up, nth_default; reflexivity).
    replace (nth_default (vNe (nVar 0)) (up s2) 0) with (vNe (nVar 0))
      by (unfold up, nth_default; reflexivity).
    apply ap_ne.
    change (vNe (nVar 0)) with (nth_default (vNe (nVar 0)) (ren_sub (up_renl rho_v)) 0).
    apply ap_var.
  - (* tail: shift both reads and use [Apply_val_shift0] *)
    rewrite renm_up_S, !up_nth_S, <- up_ren_sub.
    apply Apply_val_shift0. apply H. Lia.lia.
Qed.

(* The beta conjugate: pushing [rho] through [a :: id_list m] yields
   [ren_a :: id_list m2].  Input side reads through [up_renl rho]. *)
Lemma RenShSc_beta : forall N m m2 rho a ren_a,
    N <= m -> ren_ok rho N m2 ->
    Apply_val m2 (ren_sub rho) a ren_a ->
    RenShSc (S N) m2 (up_renl rho) rho (a :: id_list m) (ren_a :: id_list m2).
Proof.
  intros N m m2 rho a ren_a HNm Hok Ha k Hk. destruct k as [|k'].
  - (* head: read [a] / [ren_a] *)
    rewrite renm_up_0.
    unfold nth_default; cbn [nth_error]. exact Ha.
  - (* tail: [id_list m @ k'] relocates to [id_list m2 @ (rho k')] *)
    rewrite renm_up_S, !nth_default_cons_S.
    assert (Hk'm : k' < m) by Lia.lia.
    rewrite (id_list_nth_any m k'), (@ltbT k' m Hk'm).
    assert (Hrk : renm rho k' < m2) by (apply Hok; Lia.lia).
    rewrite (id_list_nth_any m2 (renm rho k')), (@ltbT (renm rho k') m2 Hrk).
    apply ap_ne.
    rewrite <- (ren_sub_nth rho k'). apply ap_var.
Qed.

(* The [wkn_list] codomain conjugate (the [refl_Pi] analogue of
   [RenShSc_beta]): pushing [rho] through [ARG :: wkn_list m] gives
   [ARG2 :: wkn_list m2]. *)
Lemma RenShSc_wkn : forall N m m2 rho ARG ARG2,
    N <= m -> ren_ok rho N m2 ->
    Apply_val (S m2) (ren_sub (up_renl rho)) ARG ARG2 ->
    RenShSc (S N) (S m2) (up_renl rho) (up_renl rho)
            (ARG :: wkn_list m) (ARG2 :: wkn_list m2).
Proof.
  intros N m m2 rho ARG ARG2 HNm Hok HARG k Hk. destruct k as [|k'].
  - rewrite renm_up_0. unfold nth_default; cbn [nth_error]. exact HARG.
  - rewrite renm_up_S, !nth_default_cons_S.
    assert (Hk'm : k' < m) by Lia.lia.
    rewrite (wkn_list_nth_lt (vNe (nVar (S k'))) Hk'm).
    assert (Hrk : renm rho k' < m2) by (apply Hok; Lia.lia).
    rewrite (wkn_list_nth_lt (vNe (nVar (S (renm rho k')))) Hrk).
    apply ap_ne.
    replace (vNe (nVar (S (renm rho k'))))
      with (nth_default (vNe (nVar (S k'))) (ren_sub (up_renl rho)) (S k'))
      by (rewrite ren_sub_nth, renm_up_S; reflexivity).
    apply ap_var.
Qed.

(* [ARG :: wkn_list m] is [S m]-scoped when [ARG] is. *)
Lemma sub_below_wkn : forall N m ARG, N <= m -> ne_below_val (S m) ARG ->
    sub_below (S N) (S m) (ARG :: wkn_list m).
Proof.
  intros N m ARG HNm HARG k Hk. destruct k as [|k'].
  - unfold nth_default; cbn [nth_error]. exact HARG.
  - rewrite nth_default_cons_S.
    assert (Hk'm : k' < m) by Lia.lia.
    rewrite (wkn_list_nth_lt (vNe (nVar (S k'))) Hk'm).
    cbn [ne_below_val ne_below_ne]. Lia.lia.
Qed.

(* ===================================================================== *)
(* APPLY COMMUTES WITH RENAMING -- the renaming analogue of                 *)
(* [Apply_shift_commute], and the engine of [Reflect_ren]'s [refl_Pi]       *)
(* codomain step.  Conclusion is SYNTACTIC ([ren_*]); proof stays           *)
(* relational ([RenShSc_up]/[RenShSc_beta] for binder/beta, [Apply_val_det] *)
(* against [ren_is_Apply_val] for [ap_var], [Apply_ne_below] for the [Vapp] *)
(* input scopes).  [(F,B)] annotations are threaded through [ap_app]/        *)
(* [ap_appI] and the [Vapp]/[VappI] motives.                                *)
(* ===================================================================== *)
Lemma Apply_ren_commute :
  (forall m s T T', Apply_ty m s T T' ->
     forall N, ne_below_ty N T -> sub_below N m s ->
     forall m2 rho_b rho_v s2, ren_ok rho_v (S m) m2 -> RenShSc N m2 rho_b rho_v s s2 ->
       Apply_ty m2 s2 (ren_ty rho_b T) (ren_ty rho_v T'))
  * (forall m s v v', Apply_val m s v v' ->
       forall N, ne_below_val N v -> sub_below N m s ->
       forall m2 rho_b rho_v s2, ren_ok rho_v (S m) m2 -> RenShSc N m2 rho_b rho_v s s2 ->
         Apply_val m2 s2 (ren_val rho_b v) (ren_val rho_v v'))
  * (forall m s n v, Apply_ne m s n v ->
       forall N, ne_below_ne N n -> sub_below N m s ->
       forall m2 rho_b rho_v s2, ren_ok rho_v (S m) m2 -> RenShSc N m2 rho_b rho_v s s2 ->
         Apply_ne m2 s2 (ren_ne rho_b n) (ren_val rho_v v))
  * (forall m F B vf a v, Vapp m F B vf a v ->
       forall N, ne_below_val N vf -> ne_below_val N a -> N <= m ->
       forall m2 rho, ren_ok rho (S m) m2 ->
         Vapp m2 (ren_val rho F) (ren_val (up_renl rho) B)
              (ren_val rho vf) (ren_val rho a) (ren_val rho v))
  * (forall m F B vf a v, VappI m F B vf a v ->
       forall N, ne_below_val N vf -> ne_below_val N a -> N <= m ->
       forall m2 rho, ren_ok rho (S m) m2 ->
         VappI m2 (ren_val rho F) (ren_val (up_renl rho) B)
               (ren_val rho vf) (ren_val rho a) (ren_val rho v)).
Proof.
  refine (Apply_mutind
    (fun m s T T' _ => forall N, ne_below_ty N T -> sub_below N m s ->
       forall m2 rho_b rho_v s2, ren_ok rho_v (S m) m2 -> RenShSc N m2 rho_b rho_v s s2 ->
         Apply_ty m2 s2 (ren_ty rho_b T) (ren_ty rho_v T'))
    (fun m s v v' _ => forall N, ne_below_val N v -> sub_below N m s ->
       forall m2 rho_b rho_v s2, ren_ok rho_v (S m) m2 -> RenShSc N m2 rho_b rho_v s s2 ->
         Apply_val m2 s2 (ren_val rho_b v) (ren_val rho_v v'))
    (fun m s n v _ => forall N, ne_below_ne N n -> sub_below N m s ->
       forall m2 rho_b rho_v s2, ren_ok rho_v (S m) m2 -> RenShSc N m2 rho_b rho_v s s2 ->
         Apply_ne m2 s2 (ren_ne rho_b n) (ren_val rho_v v))
    (fun m F B vf a v _ => forall N, ne_below_val N vf -> ne_below_val N a -> N <= m ->
       forall m2 rho, ren_ok rho (S m) m2 ->
         Vapp m2 (ren_val rho F) (ren_val (up_renl rho) B)
              (ren_val rho vf) (ren_val rho a) (ren_val rho v))
    (fun m F B vf a v _ => forall N, ne_below_val N vf -> ne_below_val N a -> N <= m ->
       forall m2 rho, ren_ok rho (S m) m2 ->
         VappI m2 (ren_val rho F) (ren_val (up_renl rho) B)
               (ren_val rho vf) (ren_val rho a) (ren_val rho v))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m s r l N Hne Hsub m2 rho_b rho_v s2 Hok Hrs. apply ap_dU.
  - (* ap_dEl *) intros m s e e' He IHe N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_ty] in Hne. cbn [ren_ty]. apply ap_dEl.
    eapply IHe; eassumption.
  - (* ap_ne (val) *) intros m s n v Hn IHn N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_ne.
    eapply IHn; eassumption.
  - (* ap_zero *) intros m s N Hne Hsub m2 rho_b rho_v s2 Hok Hrs. apply ap_zero.
  - (* ap_suc *) intros m s v v' Hv IHv N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_suc.
    eapply IHv; eassumption.
  - (* ap_nat *) intros m s N Hne Hsub m2 rho_b rho_v s2 Hok Hrs. apply ap_nat.
  - (* ap_empty *) intros m s N Hne Hsub m2 rho_b rho_v s2 Hok Hrs. apply ap_empty.
  - (* ap_pi *) intros m s F F' B B' HF IHF HB IHB N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB]. cbn [ren_val]. apply ap_pi.
    + eapply IHF; eassumption.
    + eapply IHB;
        [ exact HneB | apply sub_below_up; exact Hsub
        | apply ren_ok_up; exact Hok | apply RenShSc_up; exact Hrs ].
  - (* ap_piI *) intros m s F F' B B' HF IHF HB IHB N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_val] in Hne. destruct Hne as [HneF HneB]. cbn [ren_val]. apply ap_piI.
    + eapply IHF; eassumption.
    + eapply IHB;
        [ exact HneB | apply sub_below_up; exact Hsub
        | apply ren_ok_up; exact Hok | apply RenShSc_up; exact Hrs ].
  - (* ap_lam *) intros m s b b' Hb IHb N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_lam.
    eapply IHb;
      [ exact Hne | apply sub_below_up; exact Hsub
      | apply ren_ok_up; exact Hok | apply RenShSc_up; exact Hrs ].
  - (* ap_lamI *) intros m s b b' Hb IHb N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_val] in Hne. cbn [ren_val]. apply ap_lamI.
    eapply IHb;
      [ exact Hne | apply sub_below_up; exact Hsub
      | apply ren_ok_up; exact Hok | apply RenShSc_up; exact Hrs ].
  - (* ap_var *) intros m s k N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_ne] in Hne. cbn [ren_ne].
    pose proof (Apply_val_det (Hrs k Hne)
                  (ren_is_Apply_val (nth_default (vNe (nVar k)) s k) m2 rho_v)) as Heq.
    rewrite <- Heq. apply ap_var.
  - (* ap_emptyrec *) intros m s rA lA A A' scrut scrut' HA IHA Hsc IHsc
      N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_ne] in Hne. destruct Hne as [HneA Hnesc].
    cbn [ren_ne ren_val]. apply ap_emptyrec.
    + eapply IHA; eassumption.
    + eapply IHsc; eassumption.
  - (* ap_app *) intros m s f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp
      N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    cbn [ren_ne]. eapply ap_app.
    + eapply IHf; eassumption.
    + eapply IHF; eassumption.
    + eapply IHB;
        [ exact HneB | apply sub_below_up; exact Hsub
        | apply ren_ok_up; exact Hok | apply RenShSc_up; exact Hrs ].
    + eapply IHa; eassumption.
    + eapply IHvapp;
        [ eapply Apply_ne_ne_below; eassumption
        | eapply Apply_val_ne_below; eassumption
        | reflexivity | exact Hok ].
  - (* ap_appI *) intros m s f vf F F' B B' a a' v Hf IHf HF IHF HB IHB Ha IHa Hvapp IHvapp
      N Hne Hsub m2 rho_b rho_v s2 Hok Hrs.
    cbn [ne_below_ne] in Hne. destruct Hne as (Hnef & HneF & HneB & Hnea).
    cbn [ren_ne]. eapply ap_appI.
    + eapply IHf; eassumption.
    + eapply IHF; eassumption.
    + eapply IHB;
        [ exact HneB | apply sub_below_up; exact Hsub
        | apply ren_ok_up; exact Hok | apply RenShSc_up; exact Hrs ].
    + eapply IHa; eassumption.
    + eapply IHvapp;
        [ eapply Apply_ne_ne_below; eassumption
        | eapply Apply_val_ne_below; eassumption
        | reflexivity | exact Hok ].
  - (* vapp_lam *) intros m F B b a v Hbeta IHbeta N Hnevf Hnea HNm m2 rho Hok.
    cbn [ne_below_val] in Hnevf. cbn [ren_val]. apply vapp_lam.
    eapply IHbeta.
    + exact Hnevf.
    + apply sub_below_beta; [ exact HNm | eapply ne_below_val_mono; eassumption ].
    + exact Hok.
    + apply RenShSc_beta;
        [ exact HNm | eapply ren_ok_le; [ exact Hok | Lia.lia ] | apply ren_is_Apply_val ].
  - (* vapp_ne *) intros m F B n a N Hnevf Hnea HNm m2 rho Hok.
    cbn [ren_val ren_ne]. apply vapp_ne.
  - (* vappI_lam *) intros m F B b a v Hbeta IHbeta N Hnevf Hnea HNm m2 rho Hok.
    cbn [ne_below_val] in Hnevf. cbn [ren_val]. apply vappI_lam.
    eapply IHbeta.
    + exact Hnevf.
    + apply sub_below_beta; [ exact HNm | eapply ne_below_val_mono; eassumption ].
    + exact Hok.
    + apply RenShSc_beta;
        [ exact HNm | eapply ren_ok_le; [ exact Hok | Lia.lia ] | apply ren_is_Apply_val ].
  - (* vappI_ne *) intros m F B n a N Hnevf Hnea HNm m2 rho Hok.
    cbn [ren_val ren_ne]. apply vappI_ne.
Qed.

Definition Apply_ty_ren_commute  := fst (fst (fst (fst Apply_ren_commute))).
Definition Apply_val_ren_commute := snd (fst (fst (fst Apply_ren_commute))).
Definition Apply_ne_ren_commute  := snd (fst (fst Apply_ren_commute)).

(* ===================================================================== *)
(* Renaming commutes with the cutoff-0 and cutoff-1 weakening shifts.        *)
(* At cutoff 0 / 1 it falls out of DETERMINISM: both sides are the image of  *)
(* [shift_val c 1 v] under [up^c (ren_sub rho)] -- the renamed side via       *)
(* [ren_is_Apply] + [up_ren_sub], the shifted side via [Apply_val_shiftc]     *)
(* with [ShiftSub_up]^c (ShiftSub_0_up).  Because [ren_sub (up_renl rho)] is   *)
(* itself an [up], the cutoff-1 [ShiftSub] chains from the cutoff-0 one (no   *)
(* genuine [ins_renl] insertion is needed).  Both feed [Reflect_ren]'s        *)
(* [refl_Pi] spine ([shift 0 F], [shift 1 B], [shift 0 n]).                    *)
(* ===================================================================== *)

Lemma Apply_ne_shift0 : forall m s n v, Apply_ne m s n v ->
    Apply_ne (S m) (up s) (shift_ne 0 1 n) (shift_val 0 1 v).
Proof.
  intros m s n v H.
  exact (snd (fst (fst Apply_shift_commute)) m s n v H 0 0 (up s)
              (ShiftSub_0_up s) (Nat.le_0_l m)).
Qed.

Lemma ren_shift_comm0_val : forall rho v,
    ren_val (up_renl rho) (shift_val 0 1 v) = shift_val 0 1 (ren_val rho v).
Proof.
  intros rho v.
  pose proof (ren_is_Apply_val (shift_val 0 1 v) 1 (up_renl rho)) as H1.
  rewrite <- up_ren_sub in H1.
  pose proof (Apply_val_shift0 (ren_is_Apply_val v 0 rho)) as H2.
  exact (Apply_val_det H1 H2).
Qed.

Lemma ren_shift_comm0_ne : forall rho n,
    ren_ne (up_renl rho) (shift_ne 0 1 n) = shift_ne 0 1 (ren_ne rho n).
Proof.
  intros rho n.
  pose proof (ren_is_Apply_ne (shift_ne 0 1 n) 1 (up_renl rho)) as H1.
  rewrite <- up_ren_sub in H1.
  pose proof (Apply_ne_shift0 (ren_is_Apply_ne n 0 rho)) as H2.
  cbn [shift_val] in H2.
  pose proof (Apply_ne_det H1 H2) as Heq. injection Heq as Heq'. exact Heq'.
Qed.

(* Cutoff-1 commute: [ren_sub (up_renl rho)] is an [up], so the cutoff-1
   [ShiftSub] is [ShiftSub_up] of the cutoff-0 [ShiftSub_0_up]. *)
Lemma ren_shift_comm1_val : forall rho v,
    ren_val (up_renl (up_renl rho)) (shift_val 1 1 v)
    = shift_val 1 1 (ren_val (up_renl rho) v).
Proof.
  intros rho v.
  pose proof (ren_is_Apply_val (shift_val 1 1 v) 2 (up_renl (up_renl rho))) as H1.
  pose proof (ren_is_Apply_val v 1 (up_renl rho)) as Hbase.
  rewrite <- up_ren_sub in Hbase.
  pose proof (Apply_val_shiftc Hbase
                (ShiftSub_up (ShiftSub_0_up (ren_sub rho))) (le_n 1)) as H2.
  rewrite !up_ren_sub in H2.
  exact (Apply_val_det H1 H2).
Qed.

(* ===================================================================== *)
(* Type-directed reflection produces SCOPED values ([Reflect_scoped]) and    *)
(* commutes with renamings ([Reflect_ren]).  The [refl_Pi] spine now carries  *)
(* the [(F,B)] annotations [shift 0 F], [shift 1 B] alongside the head        *)
(* [shift 0 n], handled by [ren_shift_comm0_val]/[ren_shift_comm1_val].       *)
(* ===================================================================== *)

Lemma Reflect_scoped : forall m T n v, Reflect m T n v ->
    ne_below_ty m T -> ne_below_ne m n -> ne_below_val m v.
Proof.
  induction 1 as [ m r l n | m n | m n | m c0 n | m F B n
    | m F B n ARG B' body Harg IHarg Hb Hbody IHbody ]; intros HT Hn.
  - exact Hn.
  - exact Hn.
  - exact Hn.
  - exact Hn.
  - exact Hn.
  - cbn [ne_below_ty ne_below_val] in HT. destruct HT as [HF HB]. cbn [ne_below_val].
    assert (HARG : ne_below_val (S m) ARG).
    { apply IHarg;
        [ cbn [ne_below_ty]; apply ne_below_shift_val; exact HF
        | cbn [ne_below_ne]; Lia.lia ]. }
    assert (HB' : ne_below_val (S m) B').
    { eapply Apply_val_ne_below;
        [ exact Hb | exact HB | apply sub_below_wkn; [ Lia.lia | exact HARG ] ]. }
    apply IHbody;
      [ cbn [ne_below_ty]; exact HB'
      | cbn [ne_below_ne]; repeat split;
        [ apply ne_below_shift_ne; exact Hn
        | apply ne_below_shift_val; exact HF
        | apply ne_below_shift_val; exact HB
        | exact HARG ] ].
Qed.

Lemma Reflect_ren : forall m T n v, Reflect m T n v ->
    ne_below_ty m T -> ne_below_ne m n ->
    forall m2 rho, ren_ok rho (S m) m2 ->
      Reflect m2 (ren_ty rho T) (ren_ne rho n) (ren_val rho v).
Proof.
  induction 1 as [ m r l n | m n | m n | m c0 n | m F B n
    | m F B n ARG B' body Harg IHarg Hb Hbody IHbody ];
    intros HT Hn m2 rho Hok.
  - cbn [ren_ty ren_val]. apply refl_U.
  - cbn [ren_ty ren_val]. apply refl_Nat.
  - cbn [ren_ty ren_val]. apply refl_Empty.
  - cbn [ren_ty ren_val ren_ne]. apply refl_neEl.
  - cbn [ren_ty ren_val]. apply refl_PiI.
  - (* refl_Pi *)
    cbn [ne_below_ty ne_below_val] in HT. destruct HT as [HF HB].
    cbn [ne_below_ne] in Hn.
    cbn [ren_ty ren_val].
    assert (HARG : ne_below_val (S m) ARG)
      by (eapply Reflect_scoped;
          [ exact Harg | cbn [ne_below_ty]; apply ne_below_shift_val; exact HF
          | cbn [ne_below_ne]; Lia.lia ]).
    eapply refl_Pi.
    + (* (1) domain reflection *)
      pose proof (IHarg ltac:(cbn [ne_below_ty]; apply ne_below_shift_val; exact HF)
                        ltac:(cbn [ne_below_ne]; Lia.lia)
                        (S m2) (up_renl rho) (ren_ok_up Hok)) as IH1.
      cbn [ren_ty ren_ne] in IH1. rewrite renm_up_0 in IH1.
      rewrite ren_shift_comm0_val in IH1. exact IH1.
    + (* (2) codomain apply via Apply_val_ren_commute *)
      eapply Apply_val_ren_commute.
      * exact Hb.
      * exact HB.
      * apply sub_below_wkn; [ Lia.lia | exact HARG ].
      * apply ren_ok_up; exact Hok.
      * apply RenShSc_wkn;
          [ Lia.lia | eapply ren_ok_le; [ exact Hok | Lia.lia ] | apply ren_is_Apply_val ].
    + (* (3) spine reflection *)
      assert (HB' : ne_below_val (S m) B')
        by (eapply Apply_val_ne_below;
            [ exact Hb | exact HB | apply sub_below_wkn; [ Lia.lia | exact HARG ] ]).
      pose proof (IHbody
                    ltac:(cbn [ne_below_ty]; exact HB')
                    ltac:(cbn [ne_below_ne]; repeat split;
                            [ apply ne_below_shift_ne; exact Hn
                            | apply ne_below_shift_val; exact HF
                            | apply ne_below_shift_val; exact HB
                            | exact HARG ])
                    (S m2) (up_renl rho) (ren_ok_up Hok)) as IH2.
      cbn [ren_ty ren_ne] in IH2.
      rewrite ren_shift_comm0_ne, ren_shift_comm0_val, ren_shift_comm1_val in IH2.
      exact IH2.
Qed.
