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
  Domain Apply ApplyLemmas Reflect EvalRel Typing.
Import Core.Notations.

(* ===================================================================== *)
(* Preservation / soundness of the Pi-extended typed relational evaluator *)
(* (EvalRel.v) against the semantic typing of the value domain (Typing.v).*)
(*                                                                        *)
(* The headline result [eval_rel_preserves_typing] : if [e] evaluates to  *)
(* [v] at semantic type [T] in semantic context [Ge], then [v] genuinely  *)
(* has semantic type [T].  It is proved by the 4-way mutual induction      *)
(* [eval_mutind] over the typed evaluator.  The intricate ingredient that  *)
(* the binder fragment forces is the DEPENDENT SUBSTITUTION LEMMA          *)
(* [subst_typed]: the relational hereditary substitution [Apply_*]         *)
(* preserves typing, INCLUDING the [Vapp]/beta step.  Its proof needs that *)
(* substitution commutes with the cutoff shift [shift_*] (so that going    *)
(* under a binder via [up] preserves [wf_ssub]).                           *)
(* ===================================================================== *)

Section Preservation.
  Notation term := (@term string).

  (* The (relational) substitution-typing judgment.  A substitution
     [sg : Delta <- Gamma] is well-typed when its length matches and each
     entry has, at [Delta], the type obtained by applying [sg] to the
     corresponding [Gamma]-type. *)
  Definition wf_ssub (Delta : senv) (sg : ssub) (Gamma : senv) : Prop :=
    length sg = length Gamma /\
    (forall k T T', nth_error Gamma k = Some T ->
       Apply_ty (length Delta) sg T T' ->
       has_svalty Delta (nth_default (vNe (nVar 0)) sg k) T').

  Definition wf_senv (Ge : senv) : Prop :=
    forall k T, nth_error Ge k = Some T -> wf_svalty Ge T.

End Preservation.

(* ===================================================================== *)
(* Part 0 : shift algebra (cutoff-indexed renaming).                       *)
(* ===================================================================== *)

(* [Nat.ltb] reflection helpers. *)
Lemma ltbT : forall k c, k < c -> Nat.ltb k c = true.
Proof. intros k c H. apply Nat.ltb_lt; exact H. Qed.
Lemma ltbF : forall k c, c <= k -> Nat.ltb k c = false.
Proof. intros k c H. apply Nat.ltb_ge; exact H. Qed.
Lemma ltb_true : forall k c, Nat.ltb k c = true -> k < c.
Proof. intros k c H. apply Nat.ltb_lt; exact H. Qed.
Lemma ltb_false : forall k c, Nat.ltb k c = false -> c <= k.
Proof. intros k c H. apply Nat.ltb_ge; exact H. Qed.

(* Composition of two shifts at related cutoffs (the classic
   renaming-commutes-with-renaming identity): for [c1 <= c2],
     shift c1 (shift c2 x) = shift (S c2) (shift c1 x).
   Going under a binder bumps BOTH cutoffs, preserving [c1 <= c2]. *)
Lemma shift_shift_comm :
  (forall T c1 c2, c1 <= c2 ->
     shift_ty c1 1 (shift_ty c2 1 T) = shift_ty (S c2) 1 (shift_ty c1 1 T))
  * ((forall v c1 c2, c1 <= c2 ->
       shift_val c1 1 (shift_val c2 1 v) = shift_val (S c2) 1 (shift_val c1 1 v))
  *  (forall n c1 c2, c1 <= c2 ->
       shift_ne c1 1 (shift_ne c2 1 n) = shift_ne (S c2) 1 (shift_ne c1 1 n))).
Proof.
  apply (sval_mutind
    (fun T => forall c1 c2, c1 <= c2 ->
       shift_ty c1 1 (shift_ty c2 1 T) = shift_ty (S c2) 1 (shift_ty c1 1 T))
    (fun v => forall c1 c2, c1 <= c2 ->
       shift_val c1 1 (shift_val c2 1 v) = shift_val (S c2) 1 (shift_val c1 1 v))
    (fun n => forall c1 c2, c1 <= c2 ->
       shift_ne c1 1 (shift_ne c2 1 n) = shift_ne (S c2) 1 (shift_ne c1 1 n))).
  - (* dU *) intros; reflexivity.
  - (* dEl *) intros e IHe c1 c2 Hle. cbn. f_equal. exact (IHe c1 c2 Hle).
  - (* vNe *) intros n IHn c1 c2 Hle. cbn. f_equal. exact (IHn c1 c2 Hle).
  - (* vZero *) intros; reflexivity.
  - (* vSuc *) intros v IHv c1 c2 Hle. cbn. f_equal. exact (IHv c1 c2 Hle).
  - (* vNat *) intros; reflexivity.
  - (* vEmpty *) intros; reflexivity.
  - (* vPi *) intros F IHF B IHB c1 c2 Hle. cbn.
    f_equal; [ exact (IHF c1 c2 Hle) | apply (IHB (S c1) (S c2)); Lia.lia ].
  - (* vPiI *) intros F IHF B IHB c1 c2 Hle. cbn.
    f_equal; [ exact (IHF c1 c2 Hle) | apply (IHB (S c1) (S c2)); Lia.lia ].
  - (* vLam *) intros b IHb c1 c2 Hle. cbn. f_equal. apply (IHb (S c1) (S c2)); Lia.lia.
  - (* vLamI *) intros b IHb c1 c2 Hle. cbn. f_equal. apply (IHb (S c1) (S c2)); Lia.lia.
  - (* nVar *) intros k c1 c2 Hle. cbn [shift_ne]. f_equal.
    (* reduce the INNER shift (cutoff c2 on the left, c1 on the right) first,
       so the outer comparison becomes a literal [_ <? _] we can rewrite. *)
    destruct (Nat.ltb k c2) eqn:E2; cbn -[Nat.ltb].
    + (* k < c2 : LHS inner = k *)
      apply ltb_true in E2.
      destruct (Nat.ltb k c1) eqn:E1; cbn -[Nat.ltb].
      * (* k < c1 *) apply ltb_true in E1.
        rewrite (@ltbT k (S c2)) by Lia.lia. reflexivity.
      * (* c1 <= k *) apply ltb_false in E1.
        rewrite (@ltbT (k + 1) (S c2)) by Lia.lia. reflexivity.
    + (* c2 <= k : LHS inner = k+1 *)
      apply ltb_false in E2.
      destruct (Nat.ltb k c1) eqn:E1; cbn -[Nat.ltb].
      * (* k < c1 : impossible, since c1 <= c2 <= k *)
        apply ltb_true in E1. exfalso; Lia.lia.
      * (* c1 <= k *) apply ltb_false in E1.
        rewrite (@ltbF (k + 1) c1) by Lia.lia.
        rewrite (@ltbF (k + 1) (S c2)) by Lia.lia. reflexivity.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr c1 c2 Hle. cbn.
    f_equal; [ exact (IHA c1 c2 Hle) | exact (IHscr c1 c2 Hle) ].
  - (* nApp *) intros f IHf a IHa c1 c2 Hle. cbn.
    f_equal; [ exact (IHf c1 c2 Hle) | exact (IHa c1 c2 Hle) ].
  - (* nAppI *) intros f IHf a IHa c1 c2 Hle. cbn.
    f_equal; [ exact (IHf c1 c2 Hle) | exact (IHa c1 c2 Hle) ].
Qed.

(* The cutoff-0 specialization used below. *)
Lemma shift_val_comm0 : forall v c,
    shift_val 0 1 (shift_val c 1 v) = shift_val (S c) 1 (shift_val 0 1 v).
Proof. intros v c. apply (fst (snd shift_shift_comm)). Lia.lia. Qed.

(* A mapped list read at [i], with a default that is the image of [d]. *)
Lemma nth_default_map_f : forall (f : sval -> sval) (d : sval) (l : ssub) i,
    nth_default (f d) (map f l) i = f (nth_default d l i).
Proof.
  intros f d l i. unfold nth_default. rewrite nth_error_map.
  destruct (nth_error l i); reflexivity.
Qed.

Lemma nth_default_cons_S : forall (d x : sval) (l : ssub) i,
    nth_default d (x :: l) (S i) = nth_default d l i.
Proof. intros. unfold nth_default. cbn [nth_error]. reflexivity. Qed.

(* In-range reads are independent of the default. *)
Lemma nth_default_irrel : forall (l : ssub) (k : nat) (d1 d2 : sval),
    k < length l -> nth_default d1 l k = nth_default d2 l k.
Proof.
  intros l k d1 d2 Hlt. unfold nth_default.
  assert (He : nth_error l k <> None) by (rewrite nth_error_Some; exact Hlt).
  destruct (nth_error l k); [ reflexivity | contradiction ].
Qed.

(* ===================================================================== *)
(* Part 1 : substitution commutes with the cutoff shift.                  *)
(*                                                                        *)
(* The DEPENDENT SUBSTITUTION lemma's engine.  We need: applying a        *)
(* substitution and then shifting equals lifting the substitution and     *)
(* applying it.  The binder traversal forces a TWO-CUTOFF invariant:      *)
(* [cb] is the cutoff on the input (domain) side, [cv] on the output      *)
(* (codomain/value) side.  They coincide everywhere EXCEPT the beta step, *)
(* where the lambda body is reached at input-cutoff [S cv] but the result *)
(* still lives at value-cutoff [cv].                                       *)
(* ===================================================================== *)

Definition sh (c k : nat) : nat := if Nat.ltb k c then k else S k.

Lemma sh_S : forall c k, sh (S c) (S k) = S (sh c k).
Proof.
  intros c k. unfold sh.
  destruct (Nat.ltb (S k) (S c)) eqn:E1; destruct (Nat.ltb k c) eqn:E2.
  - reflexivity.
  - apply ltb_true in E1. apply ltb_false in E2. exfalso. Lia.lia.
  - apply ltb_false in E1. apply ltb_true in E2. exfalso. Lia.lia.
  - reflexivity.
Qed.

(* [s2] is the (cb-input / cv-output) lift of [s]: reading [s2] at the
   cb-shifted index returns the cv-shift of reading [s]. *)
Definition ShiftSub (cb cv : nat) (s s2 : ssub) : Prop :=
  forall k, nth_default (vNe (nVar (sh cb k))) s2 (sh cb k)
            = shift_val cv 1 (nth_default (vNe (nVar k)) s k).

(* Lifting under a binder preserves the invariant (bumps both cutoffs). *)
Lemma ShiftSub_up : forall cb cv s s2,
    ShiftSub cb cv s s2 -> ShiftSub (S cb) (S cv) (up s) (up s2).
Proof.
  intros cb cv s s2 H k. destruct k as [|k'].
  - (* binder variable: sh (S cb) 0 = 0 *)
    unfold sh. cbn [Nat.ltb]. unfold up. unfold nth_default. cbn [nth_error]. reflexivity.
  - rewrite sh_S.
    unfold up. unfold nth_default. cbn [nth_error]. rewrite !nth_error_map.
    specialize (H k'). unfold nth_default in H.
    destruct (nth_error s2 (sh cb k')) as [w2|] eqn:E2;
    destruct (nth_error s k') as [w|] eqn:E; cbn [option_map] in H |- *.
    + (* both in range *) rewrite H. apply shift_val_comm0.
    + (* s2 Some, s None : H equates w2 to the shift of [s]'s default *)
      rewrite H. rewrite (shift_val_comm0 (vNe (nVar k')) cv). f_equal.
      cbn. do 2 f_equal. Lia.lia.
    + (* s2 None, s Some : defaults differ by one shift; reconcile via H *)
      rewrite <- (shift_val_comm0 w cv). rewrite <- H.
      cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
    + (* both out of range : reconcile the two cutoff defaults via H *)
      cbn [shift_val shift_ne] in H |- *.
      injection H as Hsh. do 2 f_equal. rewrite Hsh.
      destruct (Nat.ltb k' cv) eqn:E1.
      * apply ltb_true in E1. rewrite (@ltbT (S k') (S cv)) by Lia.lia. reflexivity.
      * apply ltb_false in E1. rewrite (@ltbF (S k') (S cv)) by Lia.lia. Lia.lia.
Qed.

(* The beta lift: substituting [a :: id_list m] then shifting at [cv]
   equals substituting [shift cv a :: id_list (S m)] with the body reached
   at input-cutoff [S cv].  (Requires [cv <= m].) *)
(* The k-th element of [id_list n] is [vNe (nVar k)] for ANY default. *)
Lemma id_list_nth_any : forall n k d,
    nth_default d (id_list n) k = if Nat.ltb k n then vNe (nVar k) else d.
Proof.
  intros n k d. destruct (Nat.ltb k n) eqn:E.
  - apply ltb_true in E.
    erewrite nth_default_irrel;
      [ apply id_list_nth | rewrite id_list_length; exact E ].
  - apply ltb_false in E.
    unfold nth_default.
    destruct (nth_error (id_list n) k) eqn:He; [ | reflexivity ].
    exfalso.
    assert (Hnone : nth_error (id_list n) k = None)
      by (apply nth_error_None; rewrite id_list_length; exact E).
    rewrite Hnone in He. discriminate.
Qed.

Lemma sh_lt : forall cv k m, cv <= m -> k < m -> sh cv k < S m.
Proof. intros cv k m H1 H2. unfold sh. destruct (Nat.ltb k cv); Lia.lia. Qed.

Lemma ShiftSub_beta : forall m a cv, cv <= m ->
    ShiftSub (S cv) cv (a :: id_list m) (shift_val cv 1 a :: id_list (S m)).
Proof.
  intros m a cv Hcm k. destruct k as [|k'].
  - (* k = 0 : sh (S cv) 0 = 0 (0 < S cv); s reads head [a] *)
    unfold sh. cbn [Nat.ltb]. unfold nth_default. cbn [nth_error]. reflexivity.
  - (* k = S k' : sh (S cv) (S k') = S (sh cv k') *)
    rewrite sh_S. rewrite !nth_default_cons_S.
    rewrite !id_list_nth_any.
    destruct (Nat.ltb k' m) eqn:E2; [ apply ltb_true in E2 | apply ltb_false in E2 ].
    + (* k' < m : both sides reduce to [vNe (nVar (sh cv k'))] up to [S]/[+1] *)
      rewrite (@ltbT (sh cv k') (S m)) by (apply sh_lt; [ exact Hcm | exact E2 ]).
      unfold sh. cbn [shift_val shift_ne].
      destruct (Nat.ltb k' cv); do 2 f_equal; Lia.lia.
    + (* k' >= m >= cv : both out of range *)
      assert (Hs : sh cv k' = S k')
        by (unfold sh; rewrite (@ltbF k' cv) by Lia.lia; reflexivity).
      rewrite Hs. rewrite (@ltbF (S k') (S m)) by Lia.lia.
      cbn [shift_val shift_ne]. rewrite (@ltbF (S k') cv) by Lia.lia.
      do 2 f_equal. Lia.lia.
Qed.

(* The commutation lemma, by induction on the [Apply_*] derivation.
   [Vapp]/[VappI] use the diagonal [cb = cv = c] (a value, not a domain
   element, is being applied); the beta step then reaches the lambda body
   off-diagonal via [ShiftSub_beta]. *)
Lemma Apply_shift_commute :
  (forall m s T T', Apply_ty m s T T' ->
     forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
       Apply_ty (S m) s2 (shift_ty cb 1 T) (shift_ty cv 1 T'))
  * (forall m s v v', Apply_val m s v v' ->
       forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
         Apply_val (S m) s2 (shift_val cb 1 v) (shift_val cv 1 v'))
  * (forall m s n v, Apply_ne m s n v ->
       forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
         Apply_ne (S m) s2 (shift_ne cb 1 n) (shift_val cv 1 v))
  * (forall m vf a v, Vapp m vf a v ->
       forall c, c <= m ->
         Vapp (S m) (shift_val c 1 vf) (shift_val c 1 a) (shift_val c 1 v))
  * (forall m vf a v, VappI m vf a v ->
       forall c, c <= m ->
         VappI (S m) (shift_val c 1 vf) (shift_val c 1 a) (shift_val c 1 v)).
Proof.
  refine (Apply_mutind
    (fun m s T T' _ => forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
       Apply_ty (S m) s2 (shift_ty cb 1 T) (shift_ty cv 1 T'))
    (fun m s v v' _ => forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
       Apply_val (S m) s2 (shift_val cb 1 v) (shift_val cv 1 v'))
    (fun m s n v _ => forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
       Apply_ne (S m) s2 (shift_ne cb 1 n) (shift_val cv 1 v))
    (fun m vf a v _ => forall c, c <= m ->
       Vapp (S m) (shift_val c 1 vf) (shift_val c 1 a) (shift_val c 1 v))
    (fun m vf a v _ => forall c, c <= m ->
       VappI (S m) (shift_val c 1 vf) (shift_val c 1 a) (shift_val c 1 v))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ap_dU *) intros m s r l cb cv s2 Hss Hc. cbn. apply ap_dU.
  - (* ap_dEl *) intros m s e e' He IHe cb cv s2 Hss Hc. cbn. apply ap_dEl. exact (IHe cb cv s2 Hss Hc).
  - (* ap_ne *) intros m s n v Hn IHn cb cv s2 Hss Hc. cbn. apply ap_ne. exact (IHn cb cv s2 Hss Hc).
  - (* ap_zero *) intros; cbn; apply ap_zero.
  - (* ap_suc *) intros m s v v' Hv IHv cb cv s2 Hss Hc. cbn. apply ap_suc. exact (IHv cb cv s2 Hss Hc).
  - (* ap_nat *) intros; cbn; apply ap_nat.
  - (* ap_empty *) intros; cbn; apply ap_empty.
  - (* ap_pi *) intros m s F F' B B' HF IHF HB IHB cb cv s2 Hss Hc. cbn.
    apply ap_pi.
    + exact (IHF cb cv s2 Hss Hc).
    + apply (IHB (S cb) (S cv) (up s2)); [ apply ShiftSub_up; exact Hss | Lia.lia ].
  - (* ap_piI *) intros m s F F' B B' HF IHF HB IHB cb cv s2 Hss Hc. cbn.
    apply ap_piI.
    + exact (IHF cb cv s2 Hss Hc).
    + apply (IHB (S cb) (S cv) (up s2)); [ apply ShiftSub_up; exact Hss | Lia.lia ].
  - (* ap_lam *) intros m s b b' Hb IHb cb cv s2 Hss Hc. cbn.
    apply ap_lam. apply (IHb (S cb) (S cv) (up s2)); [ apply ShiftSub_up; exact Hss | Lia.lia ].
  - (* ap_lamI *) intros m s b b' Hb IHb cb cv s2 Hss Hc. cbn.
    apply ap_lamI. apply (IHb (S cb) (S cv) (up s2)); [ apply ShiftSub_up; exact Hss | Lia.lia ].
  - (* ap_var *) intros m s k cb cv s2 Hss Hc. cbn -[Nat.ltb].
    replace (if Nat.ltb k cb then k else k + 1) with (sh cb k)
      by (unfold sh; destruct (Nat.ltb k cb); [ reflexivity | f_equal; Lia.lia ]).
    rewrite <- (Hss k). apply ap_var.
  - (* ap_emptyrec *) intros m s rA lA A A' scrut scrut' HA IHA Hsc IHsc cb cv s2 Hss Hc. cbn.
    apply ap_emptyrec.
    + exact (IHA cb cv s2 Hss Hc).
    + pose proof (IHsc cb cv s2 Hss Hc) as IH. cbn in IH. exact IH.
  - (* ap_app *) intros m s f vf a a' v Hf IHf Ha IHa Hvapp IHvapp cb cv s2 Hss Hc. cbn.
    eapply ap_app.
    + exact (IHf cb cv s2 Hss Hc).
    + exact (IHa cb cv s2 Hss Hc).
    + exact (IHvapp cv Hc).
  - (* ap_appI *) intros m s f vf a a' v Hf IHf Ha IHa Hvapp IHvapp cb cv s2 Hss Hc. cbn.
    eapply ap_appI.
    + exact (IHf cb cv s2 Hss Hc).
    + exact (IHa cb cv s2 Hss Hc).
    + exact (IHvapp cv Hc).
  - (* vapp_lam *) intros m b a v Hbeta IHbeta c Hc. cbn.
    apply vapp_lam.
    exact (IHbeta (S c) c (shift_val c 1 a :: id_list (S m)) (@ShiftSub_beta m a c Hc) Hc).
  - (* vapp_ne *) intros m n a c Hc. cbn. apply vapp_ne.
  - (* vappI_lam *) intros m b a v Hbeta IHbeta c Hc. cbn.
    apply vappI_lam.
    exact (IHbeta (S c) c (shift_val c 1 a :: id_list (S m)) (@ShiftSub_beta m a c Hc) Hc).
  - (* vappI_ne *) intros m n a c Hc. cbn. apply vappI_ne.
Qed.

(* The corollary used by the substitution lemma's binder cases: applying
   [s] then shifting at cutoff 0 equals lifting via [up] and applying.  *)
Lemma ShiftSub_0_up : forall s, ShiftSub 0 0 s (up s).
Proof.
  intros s k.
  assert (Hsh : sh 0 k = S k) by reflexivity.
  unfold ShiftSub. rewrite Hsh.
  unfold up, nth_default. cbn [nth_error]. rewrite nth_error_map.
  destruct (nth_error s k) eqn:E; cbn.
  - reflexivity.
  - do 2 f_equal. Lia.lia.
Qed.

Lemma Apply_ty_shift0 : forall m s T T', Apply_ty m s T T' ->
    Apply_ty (S m) (up s) (shift_ty 0 1 T) (shift_ty 0 1 T').
Proof.
  intros m s T T' H.
  exact (fst (fst (fst (fst Apply_shift_commute))) m s T T' H 0 0 (up s) (ShiftSub_0_up s) (Nat.le_0_l m)).
Qed.

Lemma Apply_val_shift0 : forall m s v v', Apply_val m s v v' ->
    Apply_val (S m) (up s) (shift_val 0 1 v) (shift_val 0 1 v').
Proof.
  intros m s v v' H.
  exact (snd (fst (fst (fst Apply_shift_commute))) m s v v' H 0 0 (up s) (ShiftSub_0_up s) (Nat.le_0_l m)).
Qed.

(* ===================================================================== *)
(* STATUS (this session): head-shift convention corrected; commutation    *)
(* engine proved.  What remains, and why.                                  *)
(*                                                                         *)
(* A previous attempt at this file ended with a BLOCKER claiming the       *)
(* dependent substitution lemma was unprovable because [Pi/Typing.v]       *)
(* stored a Pi binder's domain type UN-shifted ([dEl F]) while shifting    *)
(* the tail, which is not closed under weakening.  That diagnosis was      *)
(* correct, but the conclusion ("out of scope") was not: the fix is simply *)
(* to store the binder head SHIFTED ([dEl (shift_val 0 1 F)]), exactly as  *)
(* [Reflect.v]/[ev_env_ext]/[ev_hd]/[ev_wkn]/[ev_snoc] ALREADY do.  This    *)
(* session made [Pi/Typing.v] ([t_Pi]/[t_PiI]/[t_lam]/[t_lamI]) and        *)
(* [Pi/EvalRel.v] ([ev_Pi]/[ev_PiI]/[ev_lam]/[ev_lamI]) use the shifted    *)
(* head; [Pi/Determinism.v] rebuilds unchanged.  (The un-shifted [ev_Pi]/  *)
(* [ev_lam] was in fact a latent bug: a codomain that mentions its own     *)
(* binder via [hd] reflects at [ev_hd]'s shifted-head env, so it could not *)
(* have typed under the old convention.)                                   *)
(*                                                                         *)
(* PROVED ABOVE (all [Qed], axiom-free): the shift algebra                 *)
(* [shift_shift_comm], the relational substitution-commutes-with-shift     *)
(* engine [Apply_shift_commute] (the genuinely intricate, binder- and      *)
(* beta-aware core, with its [ShiftSub]/[ShiftSub_up]/[ShiftSub_beta]       *)
(* invariant), and the cutoff-0 corollaries [Apply_ty_shift0] /            *)
(* [Apply_val_shift0].  These are the reusable ingredients the dependent   *)
(* substitution lemma needs.  (The earlier version of this file never      *)
(* compiled: [shift_shift_comm]'s [nVar] case, [ShiftSub_up], the          *)
(* [Apply_mutind] tuple associativity, and several implicit-argument /     *)
(* [cbn]-over-[Nat.ltb] issues were all broken; they are fixed here.)      *)
(*                                                                         *)
(* REMAINING:                                                              *)
(*  1. Generalized weakening at an arbitrary cutoff [c] (insert a context  *)
(*     entry at de Bruijn level [c], shifting entries at [c]).  The         *)
(*     front-insertion form alone is not strong enough to go under the Pi  *)
(*     binder in its own induction; the standard fix is to carry the       *)
(*     cutoff [c] in the motive.  With the shifted-head convention this     *)
(*     now goes through (the [t_Pi] reshuffle is exactly [shift_shift_comm *)
(*     0 <= c]).  This unblocks [wf_ssub_up]: under the corrected           *)
(*     convention its head obligation reduces to [has_svalty                *)
(*     (dEl (shift F') :: _) (vNe (nVar 0)) (dEl (shift F'))], i.e. [n_var] *)
(*     at index 0 -- trivially true, where the old convention made it      *)
(*     [dEl F = dEl (F[up sg])], FALSE.                                     *)
(*  2. The dependent substitution lemma [subst_has_svalty] for every       *)
(*     NON-application case (structural induction on [Apply], using         *)
(*     [wf_ssub_up] in the binder cases), and [vapp_typed] for the neutral *)
(*     ([vapp_ne]) case (immediate from [n_app]).                          *)
(*  3. THE GENUINE KERNEL (research-grade, matches the project memo's       *)
(*     "totality / logical relations" blocker): the [n_app] case of        *)
(*     [subst_has_svalty] must type the result of substituting into a       *)
(*     neutral application whose head [f[sg]] has become a [vLam]           *)
(*     (hereditary beta).  Typing [f[sg]] needs the SUBSTITUTED function    *)
(*     type [Pi (F[sg]) (B[up sg])], whose existence is exactly totality    *)
(*     of substitution on the (dependent) type codes -- which for the Pi   *)
(*     fragment with universes is a normalization-flavoured argument, not  *)
(*     a structural one.  This is the one obstacle the head-shift fix does *)
(*     NOT remove; it is the same blocker that gates [ModelOk]'s [app_rel]  *)
(*     cong/by for the integrated model.                                   *)
(* ===================================================================== *)
