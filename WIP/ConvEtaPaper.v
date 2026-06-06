Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Reflect LogRel2Conv Typing Preservation ApplySubst RenSubst RenTyping.
Import Core.Notations.

(* ===================================================================== *)
(* PAPER-FAITHFUL PROTOTYPE (WIP, not in build).                          *)
(*                                                                         *)
(* The committed core inductive (Typing.v conv_ty_eta) is congruence +     *)
(* eta-at-Pi ONLY -- it is asymmetric (cne_eta_app's result type Bres is    *)
(* computed from the LEFT arg), so it cannot serve as the PER the LR        *)
(* neutral relation must carry.  metamltt's declarative conversion (≡,      *)
(* Declarative.v) is instead a genuine EQUIVALENCE: ConvTySym/Trans/Refl +  *)
(* ConvTmConv are CONSTRUCTORS.  This prototype validates the minimally-     *)
(* invasive port of that idea to our value domain: ADD refl/sym/trans       *)
(* (+ a term type-conversion [ctm_conv]) as CONSTRUCTORS to the existing    *)
(* de-risked inductive, keeping cne_eta_app's pinned Bres (symmetry now      *)
(* comes from the cne_sym CONSTRUCTOR, NOT from inverting Bres).            *)
(*                                                                         *)
(* VALIDATES: (i) positivity of the augmented inductive; (ii) the ne_below  *)
(* transport must become BIDIRECTIONAL (an iff) once sym is a constructor,   *)
(* and still goes through; (iii) shift stability extends to the new         *)
(* constructors (trivial closure).  ren is analogous (omitted here).        *)
(* ===================================================================== *)

Section ConvEtaPaper.
  Notation ext F Ge := (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge).

  Unset Elimination Schemes.
  Inductive cty : senv -> sval -> sval -> Prop :=
  (* congruences *)
  | xte_nat   : forall Ge, cty Ge vNat vNat
  | xte_empty : forall Ge, cty Ge vEmpty vEmpty
  | xte_pi    : forall Ge F F' B B',
      cty Ge F F' -> cty (ext F Ge) B B' -> cty Ge (vPi F B) (vPi F' B')
  | xte_piI   : forall Ge F F' B B',
      cty Ge F F' -> cty (ext F Ge) B B' -> cty Ge (vPiI F B) (vPiI F' B')
  | xte_ne    : forall Ge n n' r l,
      cne Ge (dU r l) n n' -> cty Ge (vNe n) (vNe n')
  (* equivalence closure *)
  | xte_refl  : forall Ge A, cty Ge A A
  | xte_sym   : forall Ge A B, cty Ge B A -> cty Ge A B
  | xte_trans : forall Ge A B C, cty Ge A B -> cty Ge B C -> cty Ge A C
  with ctm : senv -> svalty -> sval -> sval -> Prop :=
  | xtm_ne_nat   : forall Ge n n', cne Ge (dEl vNat) n n' ->
      ctm Ge (dEl vNat) (vNe n) (vNe n')
  | xtm_ne_empty : forall Ge n n', cne Ge (dEl vEmpty) n n' ->
      ctm Ge (dEl vEmpty) (vNe n) (vNe n')
  | xtm_ne_el    : forall Ge c n n', cne Ge (dEl (vNe c)) n n' ->
      ctm Ge (dEl (vNe c)) (vNe n) (vNe n')
  | xtm_zero  : forall Ge, ctm Ge (dEl vNat) vZero vZero
  | xtm_suc   : forall Ge v v', ctm Ge (dEl vNat) v v' ->
      ctm Ge (dEl vNat) (vSuc v) (vSuc v')
  | xtm_code  : forall Ge r l c c', cty Ge c c' -> ctm Ge (dU r l) c c'
  | xtm_eta   : forall Ge F B f g ARG B' fa ga,
      ne_below_val (length Ge) F ->
      ne_below_val (length Ge) f ->
      ne_below_val (length Ge) g ->
      Reflect (S (length Ge)) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
      Apply_val (S (length Ge)) (ARG :: id_list (S (length Ge)))
                (shift_val 1 1 B) B' ->
      Vapp (S (length Ge)) (shift_val 0 1 F) (shift_val 1 1 B)
           (shift_val 0 1 f) ARG fa ->
      Vapp (S (length Ge)) (shift_val 0 1 F) (shift_val 1 1 B)
           (shift_val 0 1 g) ARG ga ->
      ctm (ext F Ge) (dEl B') fa ga ->
      ctm Ge (dEl (vPi F B)) f g
  | xtm_piI_ne : forall Ge F B n n', cne Ge (dEl (vPiI F B)) n n' ->
      ctm Ge (dEl (vPiI F B)) (vNe n) (vNe n')
  | xtm_lamI   : forall Ge F B b b',
      ctm (ext F Ge) (dEl B) b b' ->
      ctm Ge (dEl (vPiI F B)) (vLamI b) (vLamI b')
  (* equivalence closure + type conversion *)
  | xtm_refl  : forall Ge T a, ctm Ge T a a
  | xtm_sym   : forall Ge T a b, ctm Ge T b a -> ctm Ge T a b
  | xtm_trans : forall Ge T a b c, ctm Ge T a b -> ctm Ge T b c -> ctm Ge T a c
  | xtm_conv  : forall Ge A B a b, ctm Ge (dEl A) a b -> cty Ge A B ->
      ctm Ge (dEl B) a b
  with cne : senv -> svalty -> neutral -> neutral -> Prop :=
  | xne_var : forall Ge k T, nth_error Ge k = Some T -> cne Ge T (nVar k) (nVar k)
  | xne_emptyrec : forall Ge rA lA A A' s s',
      cty Ge A A' -> cne Ge (dEl vEmpty) s s' ->
      cne Ge (dEl A) (nEmptyrec rA lA A s) (nEmptyrec rA lA A' s')
  | xne_app : forall Ge f f' F F' B B' a a' Bres,
      cne Ge (dEl (vPi F B)) f f' ->
      cty Ge F F' -> cty (ext F Ge) B B' -> ctm Ge (dEl F) a a' ->
      Apply_val (length Ge) (a :: id_list (length Ge)) B Bres ->
      cne Ge (dEl Bres) (nApp f F B a) (nApp f' F' B' a')
  | xne_appI : forall Ge f f' F F' B B' a a' Bres,
      cne Ge (dEl (vPiI F B)) f f' ->
      cty Ge F F' -> cty (ext F Ge) B B' -> ctm Ge (dEl F) a a' ->
      Apply_val (length Ge) (a :: id_list (length Ge)) B Bres ->
      cne Ge (dEl Bres) (nAppI f F B a) (nAppI f' F' B' a')
  (* equivalence closure *)
  | xne_refl  : forall Ge T n, cne Ge T n n
  | xne_sym   : forall Ge T n m, cne Ge T m n -> cne Ge T n m
  | xne_trans : forall Ge T n m p, cne Ge T n m -> cne Ge T m p -> cne Ge T n p.
  Set Elimination Schemes.

  Scheme cty_ind := Induction for cty Sort Prop
    with ctm_ind := Induction for ctm Sort Prop
    with cne_ind := Induction for cne Sort Prop.
  Combined Scheme ceta_mutind from cty_ind, ctm_ind, cne_ind.

End ConvEtaPaper.

(* ===================================================================== *)
(* KEYSTONE 1: positivity OK (the inductive above type-checked).           *)
(* ===================================================================== *)
Definition keystone_positivity Ge : cty Ge vNat vNat := xte_nat Ge.

(* ===================================================================== *)
(* KEYSTONE 2: ne_below transport is now BIDIRECTIONAL (an iff), forced by  *)
(* the [xte_sym]/[xtm_sym]/[xne_sym] constructors -- and it still goes      *)
(* through.  (The de-risked version had separate fwd/bwd lemmas; with sym   *)
(* a constructor they MUST be proved together.)                            *)
(* ===================================================================== *)
Lemma ceta_ne_below_iff :
  (forall Ge A B, cty Ge A B ->
     (ne_below_val (length Ge) A <-> ne_below_val (length Ge) B))
  /\ (forall Ge T a b, ctm Ge T a b ->
     ne_below_ty (length Ge) T ->
     (ne_below_val (length Ge) a <-> ne_below_val (length Ge) b))
  /\ (forall Ge T n m, cne Ge T n m ->
     ne_below_ty (length Ge) T ->
     (ne_below_ne (length Ge) n <-> ne_below_ne (length Ge) m)).
Proof.
  apply ceta_mutind.
  (* ---- cty ---- *)
  - (* xte_nat *) intros Ge. reflexivity.
  - (* xte_empty *) intros Ge. reflexivity.
  - (* xte_pi *) intros Ge F F' B B' _ IHF _ IHB.
    cbn [length] in IHB; rewrite length_map in IHB.
    cbn [ne_below_val]. rewrite IHF, IHB. reflexivity.
  - (* xte_piI *) intros Ge F F' B B' _ IHF _ IHB.
    cbn [length] in IHB; rewrite length_map in IHB.
    cbn [ne_below_val]. rewrite IHF, IHB. reflexivity.
  - (* xte_ne *) intros Ge n n' r l _ IH.
    cbn [ne_below_val]. apply (IH I).
  - (* xte_refl *) intros Ge A. reflexivity.
  - (* xte_sym *) intros Ge A B _ IH. symmetry. exact IH.
  - (* xte_trans *) intros Ge A B C _ IH1 _ IH2. rewrite IH1. exact IH2.
  (* ---- ctm ---- *)
  - (* xtm_ne_nat *) intros Ge n n' _ IH HT. cbn [ne_below_val]. apply (IH I).
  - (* xtm_ne_empty *) intros Ge n n' _ IH HT. cbn [ne_below_val]. apply (IH I).
  - (* xtm_ne_el *) intros Ge c n n' _ IH HT. cbn [ne_below_val]. apply (IH HT).
  - (* xtm_zero *) intros Ge HT. reflexivity.
  - (* xtm_suc *) intros Ge v v' _ IH HT. cbn [ne_below_val]. apply (IH I).
  - (* xtm_code *) intros Ge r l c c' _ IH HT. apply IH.
  - (* xtm_eta -- both members scoped by side-conditions nbf, nbg. *)
    intros Ge F B f g ARG B' fa ga _ nbf nbg _ _ _ _ _ IH HT.
    split; intros _; assumption.
  - (* xtm_piI_ne *) intros Ge F B n n' _ IH HT. cbn [ne_below_val]. apply (IH HT).
  - (* xtm_lamI *) intros Ge F B b b' _ IH HT. cbn [ne_below_val ne_below_ty] in *.
    cbn [length] in IH; rewrite length_map in IH. apply IH. exact (proj2 HT).
  - (* xtm_refl *) intros Ge T a HT. reflexivity.
  - (* xtm_sym *) intros Ge T a b _ IH HT. symmetry. apply (IH HT).
  - (* xtm_trans *) intros Ge T a b c _ IH1 _ IH2 HT. rewrite (IH1 HT). apply (IH2 HT).
  - (* xtm_conv -- type index changes dEl A -> dEl B; recover ne_below A from
       the cty A B iff so the term IH applies. *)
    intros Ge A B a b _ IHtm _ IHty HT. cbn [ne_below_ty] in HT.
    apply IHtm. cbn [ne_below_ty]. apply IHty. exact HT.
  (* ---- cne ---- *)
  - (* xne_var *) intros Ge k T He HT. reflexivity.
  - (* xne_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT.
    cbn [ne_below_ne]. rewrite (IHs I).
    (* the type code A,A' index does not affect ne_below of the neutral *)
    assert (HiffA : ne_below_val (length Ge) A <-> ne_below_val (length Ge) A') by apply IHA.
    rewrite HiffA. reflexivity.
  - (* xne_app -- per-direction; the arg-type gate [ne_below F] comes from the
       INPUT side's [nApp] components (and across via [IHF]). *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT.
    cbn [length] in IHB; rewrite length_map in IHB. cbn [ne_below_ne]. split.
    + intros (Hf & HF & HB & Ha). repeat split.
      * apply (proj1 (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [exact HF|exact HB]))); exact Hf.
      * apply (proj1 IHF); exact HF.
      * apply (proj1 IHB); exact HB.
      * apply (proj1 (IHa ltac:(cbn [ne_below_ty]; exact HF))); exact Ha.
    + intros (Hf' & HF' & HB' & Ha').
      assert (HF : ne_below_val (length Ge) F) by (apply (proj2 IHF); exact HF').
      assert (HB : ne_below_val (S (length Ge)) B) by (apply (proj2 IHB); exact HB').
      repeat split.
      * apply (proj2 (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [exact HF|exact HB]))); exact Hf'.
      * exact HF.
      * exact HB.
      * apply (proj2 (IHa ltac:(cbn [ne_below_ty]; exact HF))); exact Ha'.
  - (* xne_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT.
    cbn [length] in IHB; rewrite length_map in IHB. cbn [ne_below_ne]. split.
    + intros (Hf & HF & HB & Ha). repeat split.
      * apply (proj1 (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [exact HF|exact HB]))); exact Hf.
      * apply (proj1 IHF); exact HF.
      * apply (proj1 IHB); exact HB.
      * apply (proj1 (IHa ltac:(cbn [ne_below_ty]; exact HF))); exact Ha.
    + intros (Hf' & HF' & HB' & Ha').
      assert (HF : ne_below_val (length Ge) F) by (apply (proj2 IHF); exact HF').
      assert (HB : ne_below_val (S (length Ge)) B) by (apply (proj2 IHB); exact HB').
      repeat split.
      * apply (proj2 (IHf ltac:(cbn [ne_below_ty ne_below_val]; split; [exact HF|exact HB]))); exact Hf'.
      * exact HF.
      * exact HB.
      * apply (proj2 (IHa ltac:(cbn [ne_below_ty]; exact HF))); exact Ha'.
  - (* xne_refl *) intros Ge T n HT. reflexivity.
  - (* xne_sym *) intros Ge T n m _ IH HT. symmetry. apply (IH HT).
  - (* xne_trans *) intros Ge T n m p _ IH1 _ IH2 HT. rewrite (IH1 HT). apply (IH2 HT).
Qed.
