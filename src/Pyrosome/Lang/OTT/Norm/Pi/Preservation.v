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
     corresponding [Gamma]-type.  The clause is stated to PRODUCE the
     substituted type [T'] (with its [Apply_ty] witness), rather than to
     consume an arbitrary one: this is what makes [wf_ssub_up] provable
     using only the forward shift-commutation [Apply_ty_shift0] (no need
     for an un-shift inversion, hence no appeal to totality).  The
     consuming form is recovered at use sites by determinism of [Apply]. *)
  (* [Apply_ty] is [Type]-valued (it carries the substitution derivation),
     so [wf_ssub] lives in [Type] and uses [sigT]/[prod] rather than
     [ex]/[and]. *)
  Definition wf_ssub (Delta : senv) (sg : ssub) (Gamma : senv) : Type :=
    (length sg = length Gamma) *
    (forall k T, nth_error Gamma k = Some T ->
       { T' & (Apply_ty (length Delta) sg T T')
              * has_svalty Delta (nth_default (vNe (nVar 0)) sg k) T' })%type.

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

(* Named [Apply_val] projection of the commutation engine (so implicit-arg
   inference works at use sites, unlike the anonymous tuple projection). *)
Lemma Apply_val_shiftc : forall m s v v', Apply_val m s v v' ->
    forall cb cv s2, ShiftSub cb cv s s2 -> cv <= m ->
      Apply_val (S m) s2 (shift_val cb 1 v) (shift_val cv 1 v').
Proof. exact (snd (fst (fst (fst Apply_shift_commute)))). Qed.

(* ===================================================================== *)
(* Part 1b : weakening of type-directed reflection ([Reflect_weaken]).     *)
(*                                                                        *)
(* Inserting a binder at cutoff [c] commutes with [Reflect]: the reflected *)
(* value is just shifted.  Needed by the [t_lam_eta] case of              *)
(* [weaken_typing] (the eta-typing rule carries a [Reflect] premise that    *)
(* must travel under the inserted binder).  The [refl_Pi] case threads the  *)
(* shift through the codomain's [wkn_list] substitution via the commutation *)
(* engine, which needs the [wkn_list]-cons [ShiftSub] below.                *)
(* ===================================================================== *)

Lemma wkn_list_is_map : forall n, wkn_list n = map (shift_val 0 1) (id_list n).
Proof.
  intro n. unfold wkn_list, id_list. rewrite map_map. apply map_ext.
  intro k. cbn [shift_val shift_ne Nat.ltb Nat.leb]. do 2 f_equal. Lia.lia.
Qed.

(* [wkn_list] reads, split into clean in-range / out-of-range forms (no [if],
   so the downstream [ShiftSub] proof avoids match-collapse fragility). *)
Lemma wkn_list_nth_lt : forall n k d, k < n ->
    nth_default d (wkn_list n) k = vNe (nVar (S k)).
Proof.
  intros n k d Hk.
  rewrite <- (nth_default_cons_S d (vNe (nVar 0)) (wkn_list n) k).
  rewrite snoc_wkn_hd_list, id_list_nth_any, (@ltbT (S k) (S n)) by Lia.lia.
  reflexivity.
Qed.

Lemma wkn_list_nth_ge : forall n k d, n <= k ->
    nth_default d (wkn_list n) k = d.
Proof.
  intros n k d Hk. unfold nth_default.
  assert (Hn : nth_error (wkn_list n) k = None)
    by (apply nth_error_None; rewrite wkn_list_length; exact Hk).
  rewrite Hn. reflexivity.
Qed.

(* The [wkn_list] analogue of [ShiftSub_beta]: lifting the [a :: wkn_list m]
   substitution through a cutoff-[S c] shift (on BOTH sides — a value, not a
   domain element, is being shifted) extends to [shift a :: wkn_list (S m)]. *)
Lemma ShiftSub_wkn_cons : forall m a c, c <= m ->
    ShiftSub (S c) (S c) (a :: wkn_list m) (shift_val (S c) 1 a :: wkn_list (S m)).
Proof.
  intros m a c Hcm k. destruct k as [|k'].
  - (* k = 0 : sh (S c) 0 = 0, both read the head *)
    unfold sh. cbn [Nat.ltb]. unfold nth_default. cbn [nth_error]. reflexivity.
  - (* k = S k' : sh (S c) (S k') = S (sh c k') *)
    rewrite sh_S. rewrite !nth_default_cons_S.
    destruct (Nat.ltb k' m) eqn:Em;
      [ apply ltb_true in Em | apply ltb_false in Em ].
    + (* k' < m : both in range *)
      rewrite wkn_list_nth_lt by (apply sh_lt; [ exact Hcm | exact Em ]).
      rewrite wkn_list_nth_lt by exact Em.
      cbn [shift_val shift_ne]. unfold sh.
      destruct (Nat.ltb k' c) eqn:E3.
      * apply ltb_true in E3. rewrite (@ltbT (S k') (S c)) by Lia.lia. reflexivity.
      * apply ltb_false in E3. rewrite (@ltbF (S k') (S c)) by Lia.lia.
        do 2 f_equal. Lia.lia.
    + (* k' >= m >= c : both out of range *)
      assert (Hs : sh c k' = S k')
        by (unfold sh; rewrite (@ltbF k' c) by Lia.lia; reflexivity).
      rewrite Hs.
      rewrite wkn_list_nth_ge by Lia.lia.
      rewrite wkn_list_nth_ge by Lia.lia.
      cbn [shift_val shift_ne]. rewrite (@ltbF (S k') (S c)) by Lia.lia.
      do 2 f_equal. Lia.lia.
Qed.

Lemma Reflect_weaken : forall m T n v, Reflect m T n v ->
    forall c, c <= m ->
      Reflect (S m) (shift_ty c 1 T) (shift_ne c 1 n) (shift_val c 1 v).
Proof.
  induction 1 as [ m r l n | m n | m n | m c0 n | m F B n
    | m F B n ARG B' body Harg IHarg Hb Hbody IHbody ]; intros c Hc.
  - cbn. apply refl_U.
  - cbn. apply refl_Nat.
  - cbn. apply refl_Empty.
  - cbn. apply refl_neEl.
  - cbn. apply refl_PiI.
  - cbn [shift_ty shift_val shift_ne].
    eapply refl_Pi.
    + (* (1) reflect the bound variable at the shifted domain *)
      pose proof (IHarg (S c) ltac:(Lia.lia)) as IH.
      cbn [shift_ty shift_val shift_ne] in IH.
      rewrite shift_val_comm0. exact IH.
    + (* (2) thread the shift through the codomain substitution *)
      exact (Apply_val_shiftc Hb (@ShiftSub_wkn_cons m ARG c Hc) ltac:(Lia.lia)).
    + (* (3) reflect the eta-body at the shifted codomain *)
      pose proof (IHbody (S c) ltac:(Lia.lia)) as IH.
      cbn [shift_ty shift_val shift_ne] in IH.
      rewrite ((snd (snd shift_shift_comm)) n 0 c (Nat.le_0_l c)). exact IH.
Qed.

(* ===================================================================== *)
(* Part 2 : weakening at an arbitrary cutoff (insertion under binders).    *)
(*                                                                        *)
(* Front-insertion weakening is not strong enough to recurse under the Pi  *)
(* binder; the motive must carry the cutoff [c].  [wk_ctx c T0 Ge] inserts *)
(* [T0] at de Bruijn level [c] and shifts every existing entry's free      *)
(* variables at [c].  The [t_Pi] reshuffle is exactly [shift_shift_comm]   *)
(* with [0 <= c], and the [n_app] case is [Apply_shift_commute] driven by  *)
(* [ShiftSub_beta].                                                        *)
(* ===================================================================== *)

Lemma nth_error_firstn_lt : forall A (l : list A) c k,
    k < c -> nth_error (firstn c l) k = nth_error l k.
Proof.
  intros A l c. revert l. induction c as [|c IH]; intros l k Hk; [ Lia.lia | ].
  destruct l as [|x l]; cbn; [ destruct k; reflexivity | ].
  destruct k as [|k]; [ reflexivity | cbn; apply IH; Lia.lia ].
Qed.

Lemma nth_error_skipn_add : forall A (l : list A) c j,
    nth_error (skipn c l) j = nth_error l (c + j).
Proof.
  intros A l c. revert l. induction c as [|c IH]; intros l j; [ reflexivity | ].
  destruct l as [|x l]; cbn; [ destruct j; reflexivity | apply IH ].
Qed.

Lemma map_firstn : forall A B (f : A -> B) c l,
    map f (firstn c l) = firstn c (map f l).
Proof.
  intros A B f c. induction c as [|c IH]; intros l; [ reflexivity | ].
  destruct l as [|x l]; cbn; [ reflexivity | f_equal; apply IH ].
Qed.

Lemma map_skipn : forall A B (f : A -> B) c l,
    map f (skipn c l) = skipn c (map f l).
Proof.
  intros A B f c. induction c as [|c IH]; intros l; [ reflexivity | ].
  destruct l as [|x l]; cbn; [ reflexivity | apply IH ].
Qed.

Definition wk_ctx (c : nat) (T0 : svalty) (Ge : senv) : senv :=
  map (shift_ty c 1) (firstn c Ge) ++ T0 :: map (shift_ty c 1) (skipn c Ge).

Lemma wk_ctx_length : forall c T0 Ge,
    c <= length Ge -> length (wk_ctx c T0 Ge) = S (length Ge).
Proof.
  intros c T0 Ge Hc. unfold wk_ctx.
  rewrite length_app. cbn [length]. rewrite !length_map.
  rewrite firstn_length, skipn_length. Lia.lia.
Qed.

Lemma wk_ctx_nth_lt : forall c T0 Ge k T,
    k < c -> c <= length Ge -> nth_error Ge k = Some T ->
    nth_error (wk_ctx c T0 Ge) k = Some (shift_ty c 1 T).
Proof.
  intros c T0 Ge k T Hk Hc He. unfold wk_ctx.
  rewrite nth_error_app1 by (rewrite length_map, firstn_length; Lia.lia).
  rewrite nth_error_map, nth_error_firstn_lt by exact Hk. rewrite He. reflexivity.
Qed.

Lemma wk_ctx_nth_ge : forall c T0 Ge k T,
    c <= k -> c <= length Ge -> nth_error Ge k = Some T ->
    nth_error (wk_ctx c T0 Ge) (S k) = Some (shift_ty c 1 T).
Proof.
  intros c T0 Ge k T Hk Hc He. unfold wk_ctx.
  rewrite nth_error_app2 by (rewrite length_map, firstn_length; Lia.lia).
  rewrite length_map, firstn_length.
  replace (S k - Nat.min c (length Ge)) with (S (k - c))
    by (rewrite Nat.min_l by Lia.lia; Lia.lia).
  cbn [nth_error]. rewrite nth_error_map, nth_error_skipn_add.
  replace (c + (k - c)) with k by Lia.lia. rewrite He. reflexivity.
Qed.

(* Weakening commutes with map-shift, modulo a cutoff bump (the engine of
   the binder reshuffle). *)
Lemma map_shift_S_comm : forall c l,
    map (shift_ty (S c) 1) (map (shift_ty 0 1) l)
    = map (shift_ty 0 1) (map (shift_ty c 1) l).
Proof.
  intros c l. rewrite !map_map. apply map_ext. intro x.
  symmetry. apply (fst shift_shift_comm). Lia.lia.
Qed.

Lemma wk_ctx_under_binder : forall c T0 F Ge,
    wk_ctx (S c) (shift_ty 0 1 T0) (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge)
    = dEl (shift_val 0 1 (shift_val c 1 F)) :: map (shift_ty 0 1) (wk_ctx c T0 Ge).
Proof.
  intros c T0 F Ge. unfold wk_ctx.
  cbn [firstn skipn map app].
  rewrite map_app. cbn [map].
  rewrite <- !map_firstn, <- !map_skipn.
  rewrite !map_shift_S_comm.
  f_equal.
  - cbn [shift_ty]. f_equal. symmetry. apply (fst (snd shift_shift_comm)). Lia.lia.
Qed.

Lemma weaken_typing :
  (forall Ge v T, has_svalty Ge v T ->
     forall c T0, c <= length Ge ->
       has_svalty (wk_ctx c T0 Ge) (shift_val c 1 v) (shift_ty c 1 T))
  * (forall Ge n T, wf_neutral Ge n T ->
     forall c T0, c <= length Ge ->
       wf_neutral (wk_ctx c T0 Ge) (shift_ne c 1 n) (shift_ty c 1 T)).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => forall c T0, c <= length Ge ->
       has_svalty (wk_ctx c T0 Ge) (shift_val c 1 v) (shift_ty c 1 T))
    (fun Ge n T _ => forall c T0, c <= length Ge ->
       wf_neutral (wk_ctx c T0 Ge) (shift_ne c 1 n) (shift_ty c 1 T))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn c T0 Hc. cbn. apply t_ne. exact (IHn c T0 Hc).
  - (* t_zero *) intros Ge c T0 Hc. cbn. apply t_zero.
  - (* t_suc *) intros Ge v hv IHv c T0 Hc. cbn. apply t_suc. exact (IHv c T0 Hc).
  - (* t_Nat *) intros Ge r l c T0 Hc. cbn. apply t_Nat.
  - (* t_Empty *) intros Ge r l c T0 Hc. cbn. apply t_Empty.
  - (* t_Pi *) intros Ge F B rF lF rB lB r l hF IHF hB IHB c T0 Hc. cbn.
    eapply t_Pi.
    + exact (IHF c T0 Hc).
    + pose proof (IHB (S c) (shift_ty 0 1 T0)
                   ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
      rewrite wk_ctx_under_binder in IH. exact IH.
  - (* t_PiI *) intros Ge F B rF lF rB lB r l hF IHF hB IHB c T0 Hc. cbn.
    eapply t_PiI.
    + exact (IHF c T0 Hc).
    + pose proof (IHB (S c) (shift_ty 0 1 T0)
                   ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
      rewrite wk_ctx_under_binder in IH. exact IH.
  - (* t_lam *) intros Ge F B b hb IHb c T0 Hc. cbn. apply t_lam.
    pose proof (IHb (S c) (shift_ty 0 1 T0)
                 ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
    rewrite wk_ctx_under_binder in IH. exact IH.
  - (* t_lamI *) intros Ge F B b hb IHb c T0 Hc. cbn. apply t_lamI.
    pose proof (IHb (S c) (shift_ty 0 1 T0)
                 ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
    rewrite wk_ctx_under_binder in IH. exact IH.
  - (* t_lam_eta *) intros Ge F B b ARG B' HR Hap Hb IHb c T0 Hc.
    cbn [shift_val shift_ty].
    assert (HL : length (wk_ctx c T0 Ge) = S (length Ge))
      by (apply wk_ctx_length; exact Hc).
    eapply t_lam_eta.
    + (* reflect the bound variable at the shifted domain *)
      rewrite HL.
      pose proof (@Reflect_weaken _ _ _ _ HR (S c) ltac:(Lia.lia)) as IH.
      cbn [shift_ty shift_val shift_ne] in IH.
      rewrite shift_val_comm0. exact IH.
    + (* thread the shift through the eta-body's codomain substitution *)
      rewrite HL.
      pose proof (Apply_val_shiftc Hap
                    (@ShiftSub_beta (S (length Ge)) ARG (S c) ltac:(Lia.lia))
                    ltac:(Lia.lia)) as IH.
      rewrite (fst (snd shift_shift_comm) B 1 (S c) ltac:(Lia.lia)). exact IH.
    + (* the body, weakened under the binder *)
      pose proof (IHb (S c) (shift_ty 0 1 T0)
                   ltac:(cbn [length]; rewrite length_map; Lia.lia)) as IH.
      rewrite wk_ctx_under_binder in IH. cbn [shift_ty] in IH. exact IH.
  - (* n_var *) intros Ge k T He c T0 Hc. cbn -[Nat.ltb].
    destruct (Nat.ltb k c) eqn:E; cbn -[Nat.ltb].
    + apply ltb_true in E. apply n_var. exact (@wk_ctx_nth_lt c T0 Ge k T E Hc He).
    + apply ltb_false in E. replace (k + 1) with (S k) by Lia.lia.
      apply n_var. exact (@wk_ctx_nth_ge c T0 Ge k T E Hc He).
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr c T0 Hc. cbn.
    eapply n_emptyrec; [ exact (IHA c T0 Hc) | exact (IHscr c T0 Hc) ].
  - (* n_app *) intros Ge f F B a B' hf IHf ha IHa Hap c T0 Hc. cbn.
    eapply n_app.
    + exact (IHf c T0 Hc).
    + exact (IHa c T0 Hc).
    + rewrite (@wk_ctx_length c T0 Ge Hc).
      exact (Apply_val_shiftc Hap (@ShiftSub_beta (length Ge) a c Hc) Hc).
  - (* n_appI *) intros Ge f F B a B' hf IHf ha IHa Hap c T0 Hc. cbn.
    eapply n_appI.
    + exact (IHf c T0 Hc).
    + exact (IHa c T0 Hc).
    + rewrite (@wk_ctx_length c T0 Ge Hc).
      exact (Apply_val_shiftc Hap (@ShiftSub_beta (length Ge) a c Hc) Hc).
Qed.

(* Front insertion (cutoff 0) : the special case used by [wf_ssub_up]. *)
Lemma shift_typing :
  (forall Ge v T, has_svalty Ge v T ->
     forall T0, has_svalty (T0 :: map (shift_ty 0 1) Ge) (shift_val 0 1 v) (shift_ty 0 1 T))
  * (forall Ge n T, wf_neutral Ge n T ->
     forall T0, wf_neutral (T0 :: map (shift_ty 0 1) Ge) (shift_ne 0 1 n) (shift_ty 0 1 T)).
Proof.
  split; intros Ge x T H T0.
  - pose proof (fst weaken_typing Ge x T H 0 T0 (Nat.le_0_l _)) as IH.
    unfold wk_ctx in IH. cbn [firstn skipn map app] in IH. exact IH.
  - pose proof (snd weaken_typing Ge x T H 0 T0 (Nat.le_0_l _)) as IH.
    unfold wk_ctx in IH. cbn [firstn skipn map app] in IH. exact IH.
Qed.

Lemma shift_wf_svalty : forall Ge T, wf_svalty Ge T ->
  forall T0, wf_svalty (T0 :: map (shift_ty 0 1) Ge) (shift_ty 0 1 T).
Proof.
  intros Ge T H T0. destruct H as [Ge r l | Ge e r l He]; cbn.
  - apply wf_dU.
  - apply (wf_dEl (r:=r) (l:=l)). exact (fst shift_typing _ _ _ He T0).
Qed.

Lemma wf_senv_nil : wf_senv [].
Proof. intros k T He. destruct k; cbn in He; discriminate He. Qed.

Lemma wf_senv_ext : forall Ge S, wf_senv Ge -> wf_svalty Ge S ->
  wf_senv (shift_ty 0 1 S :: map (shift_ty 0 1) Ge).
Proof.
  intros Ge S HG HS k T He. destruct k as [|k]; cbn [nth_error] in He.
  - injection He as He. subst T. apply (shift_wf_svalty HS).
  - rewrite nth_error_map in He.
    destruct (nth_error Ge k) as [Tk|] eqn:E; cbn in He; [|discriminate He].
    injection He as He. subst T. apply (shift_wf_svalty (HG k Tk E)).
Qed.

(* ===================================================================== *)
(* Part 3 : the structural substitutions are well-typed; in particular     *)
(* [wf_ssub_up] -- the lemma a prior note claimed impossible.              *)
(* ===================================================================== *)

Lemma wf_ssub_id : forall Ge, wf_senv Ge -> wf_ssub Ge (id_list (length Ge)) Ge.
Proof.
  intros Ge Hwf. split; [ apply id_list_length | ].
  intros k T He. exists T. split.
  - apply Apply_ty_id.
  - assert (Hk : k < length Ge)
      by (apply (proj1 (nth_error_Some Ge k)); rewrite He; discriminate).
    rewrite (nth_default_irrel (id_list (length Ge)) (vNe (nVar 0)) (vNe (nVar k)))
      by (rewrite id_list_length; exact Hk).
    rewrite id_list_nth. apply t_ne, n_var. exact He.
Qed.

Lemma wf_ssub_forget : forall Delta, wf_ssub Delta [] [].
Proof.
  intro Delta. split; [ reflexivity | ].
  intros k T He. destruct k; cbn in He; discriminate He.
Qed.

(* The key lemma: lifting a well-typed substitution under a binder.  With
   the SHIFTED-head convention the head obligation is [vNe (nVar 0)] at
   [dEl (shift F')], i.e. [n_var] at index 0 -- trivially true.  (Under the
   old un-shifted convention it was [dEl F = dEl (F[up sg])], FALSE: that
   was the recorded blocker.)  The tail uses only the FORWARD shift
   commutation [Apply_ty_shift0]/[Apply_val_shift0] and front weakening. *)
Lemma wf_ssub_up : forall Delta sg Ge F F',
    wf_ssub Delta sg Ge ->
    Apply_val (length Delta) sg F F' ->
    wf_ssub (dEl (shift_val 0 1 F') :: map (shift_ty 0 1) Delta) (up sg)
            (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge).
Proof.
  intros Delta sg Ge F F' [Hlen Hpt] HF. split.
  - cbn [length]. unfold up. cbn [length]. rewrite !length_map. rewrite Hlen. reflexivity.
  - intros k T He. cbn [length]. rewrite length_map.
    destruct k as [|k'].
    + (* head : the fresh variable, at the (shifted, substituted) domain *)
      cbn [nth_error] in He. injection He as He. subst T.
      exists (dEl (shift_val 0 1 F')). split.
      * apply ap_dEl. apply Apply_val_shift0. exact HF.
      * unfold up. cbn [nth_default nth_error].
        apply t_ne, n_var. reflexivity.
    + (* tail : weaken the original entry forward *)
      cbn [nth_error] in He. rewrite nth_error_map in He.
      destruct (nth_error Ge k') as [Tk|] eqn:E; cbn [option_map] in He;
        [ injection He as He; subst T | discriminate He ].
      destruct (Hpt k' Tk E) as [Tk' [Hap Hty]].
      exists (shift_ty 0 1 Tk'). split.
      * apply Apply_ty_shift0. exact Hap.
      * (* [k'] is in range (its type comes from [Ge]), so the default is
           irrelevant and [(up sg)[S k'] = shift (sg[k'])]. *)
        assert (Hk : k' < length sg)
          by (rewrite Hlen; apply (proj1 (nth_error_Some Ge k')); rewrite E; discriminate).
        destruct (nth_error sg k') as [w|] eqn:Es;
          [ | apply nth_error_None in Es; Lia.lia ].
        assert (Hw : nth_default (vNe (nVar 0)) sg k' = w)
          by (unfold nth_default; rewrite Es; reflexivity).
        rewrite Hw in Hty.
        unfold up. rewrite nth_default_cons_S.
        unfold nth_default. rewrite nth_error_map, Es. cbn [option_map].
        exact (fst shift_typing Delta w Tk' Hty (dEl (shift_val 0 1 F'))).
Qed.

(* ===================================================================== *)
(* STATUS (this session, continued).                                       *)
(*                                                                         *)
(* PROVED ABOVE (all [Qed], axiom-free): the generalized weakening         *)
(* [weaken_typing] (insertion at an arbitrary cutoff), its front-insertion *)
(* corollary [shift_typing], the environment lemmas, and -- the headline   *)
(* -- [wf_ssub_up], which the prior note declared impossible under the     *)
(* un-shifted convention.  With the corrected (shifted-head) convention it *)
(* is direct: the [up] head obligation is [n_var] at index 0, and the tail *)
(* uses only the forward shift commutation already established.  Also       *)
(* [wf_ssub_id] / [wf_ssub_forget].                                        *)
(*                                                                         *)
(* REMAINING: [wf_ssub_wkn] and [wf_ssub_snoc] are now PROVED in            *)
(* [ApplySubst.v] (Parts C/D); [wf_ssub_comp] (the relational analogue of   *)
(* the first-order [Norm/Preservation.v] composition lemma) is still open,  *)
(* as are the dependent substitution lemma [subst_has_svalty] + [vapp_typed]*)
(* and [eval_sound].  The one genuine obstacle is unchanged: the [n_app] /   *)
(* hereditary-beta case of [subst_has_svalty] needs totality of            *)
(* substitution on the dependent function-type codes -- a normalization-    *)
(* flavoured argument (the project memo's "totality / logical relations"    *)
(* blocker), not a structural one.  That totality is the Fundamental Lemma   *)
(* of the semantic logical relation; its supporting algebra is being built  *)
(* in [LogRelSubst.v] (e.g. [Apply_uncancel], the reverse of               *)
(* [ApplySubst.Apply_cancel]).                                              *)
(* ===================================================================== *)
