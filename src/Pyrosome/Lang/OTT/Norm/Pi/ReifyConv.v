Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply ApplyLemmas Reflect Reify LogRel2Conv ApplyConv.
Import Core.Notations.

(* ===================================================================== *)
(* Read-back is a CONGRUENCE for conversion (option A adequacy).            *)
(*                                                                         *)
(* [Reflect] and [Reify] map conv-related inputs to conv-related outputs.  *)
(* Proved by induction on the [Reflect] / [Reify] derivation (NOT the      *)
(* type), so the dependent-codomain non-termination never bites; the eta   *)
(* (Pi) cases use [Apply_conv] (the substitution congruence).              *)
(* ===================================================================== *)

(* Precise type conversion: [dU]/[dEl] mismatches are EMPTY (rule out the   *)
(* universe-vs-El case in the reflect base lemma). *)
Definition conv_svty (T T2 : svalty) : Type :=
  match T, T2 with
  | dEl e, dEl e2 => conv_nf e e2
  | dU _ _, dU _ _ => unit
  | _, _ => Empty_set
  end.

Definition Apply_conv_val  := snd (fst (fst (fst Apply_conv))).
Definition Apply_conv_Vapp := snd (fst Apply_conv).

(* ===================================================================== *)
(* [Reflect] preserves conversion.                                         *)
(* ===================================================================== *)
Lemma Reflect_conv : forall m TA n vn, Reflect m TA n vn ->
    forall TB n2 vm, conv_svty TA TB -> conv_ne n n2 -> Reflect m TB n2 vm ->
    conv_nf vn vm.
Proof.
  intros m TA n vn H.
  induction H as
    [ m r l n | m n | m n | m c n | m F B n
    | m F B n ARG B' body Harg IHarg Hap Hbody IHbody ];
    intros TB n2 vm Hty Hcne Href.
  - (* refl_U *) destruct TB as [r2 l2|e2]; [|destruct Hty].
    inversion Href; subst. apply cnf_ne; exact Hcne.
  - (* refl_Nat *) destruct TB as [r2 l2|e2]; [destruct Hty|].
    cbn in Hty. inversion Hty; subst. inversion Href; subst. apply cnf_ne; exact Hcne.
  - (* refl_Empty *) destruct TB as [r2 l2|e2]; [destruct Hty|].
    cbn in Hty. inversion Hty; subst. inversion Href; subst. apply cnf_ne; exact Hcne.
  - (* refl_neEl *) destruct TB as [r2 l2|e2]; [destruct Hty|].
    cbn in Hty. inversion Hty; subst. inversion Href; subst. apply cnf_ne; exact Hcne.
  - (* refl_PiI *) destruct TB as [r2 l2|e2]; [destruct Hty|].
    cbn in Hty. inversion Hty; subst. inversion Href; subst. apply cnf_ne; exact Hcne.
  - (* refl_Pi *) destruct TB as [r2 l2|e2]; [destruct Hty|].
    cbn in Hty.
    inversion Hty as [ | | | | | F0 B0 F2 B2 HconvF HconvB | | | ]; subst.
    inversion Href as [ | | | | | m0 FF BB nn AR BB' bd HAr HAp HBd ]; subst.
    (* domain reflections related *)
    assert (HARG : conv_nf ARG AR).
    { eapply (IHarg (dEl (shift_val 0 1 F2)));
        [ cbn; apply conv_nf_shift; exact HconvF
        | apply cne_var | exact HAr ]. }
    (* codomain instances related *)
    assert (HB' : conv_nf B' BB').
    { eapply Apply_conv_val;
        [ exact Hap
        | apply conv_sub_cons; [ exact HARG | apply conv_sub_refl ]
        | exact HconvB
        | exact HAp ]. }
    (* bodies related *)
    apply cnf_lam.
    eapply (IHbody (dEl BB')).
    + cbn. exact HB'.
    + apply cne_app.
      * apply conv_ne_shift; exact Hcne.
      * apply conv_nf_shift; exact HconvF.
      * apply conv_nf_shift; exact HconvB.
      * exact HARG.
    + exact HBd.
Qed.

(* ===================================================================== *)
(* [Reify] preserves conversion (the read-back congruence).                *)
(* ===================================================================== *)
Lemma Reify_conv :
  (forall m c c', ReifyTy m c c' ->
     forall c2 c2', conv_nf c c2 -> ReifyTy m c2 c2' -> conv_nf c' c2')
  * ((forall m T v nf, Reify m T v nf ->
       forall T2 v2 nf2, conv_svty T T2 -> conv_nf v v2 -> Reify m T2 v2 nf2 -> conv_nf nf nf2)
  * (forall m n n', ReifyNe m n n' ->
       forall n2 n2', conv_ne n n2 -> ReifyNe m n2 n2' -> conv_ne n' n2')).
Proof.
  apply Reify_mutind.
  - (* rty_Nat *) intros m c2 c2' Hc Hr2.
    inversion Hc; subst. inversion Hr2; subst. apply cnf_nat.
  - (* rty_Empty *) intros m c2 c2' Hc Hr2.
    inversion Hc; subst. inversion Hr2; subst. apply cnf_empty.
  - (* rty_Pi *) intros m F B F' B' HF IHF HB IHB c2 c2' Hc Hr2.
    inversion Hc; subst. inversion Hr2; subst.
    apply cnf_pi; [ eapply IHF; eassumption | eapply IHB; eassumption ].
  - (* rty_PiI *) intros m F B F' B' HF IHF HB IHB c2 c2' Hc Hr2.
    inversion Hc; subst. inversion Hr2; subst.
    apply cnf_piI; [ eapply IHF; eassumption | eapply IHB; eassumption ].
  - (* rty_ne *) intros m n n' Hn IHn c2 c2' Hc Hr2.
    inversion Hc; subst. inversion Hr2; subst. apply cnf_ne. eapply IHn; eassumption.
  - (* rfy_code *) intros m r l c c' Hc IHc T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [|destruct Hty]. inversion Hr2; subst.
    eapply IHc; eassumption.
  - (* rfy_zero *) intros m T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty. inversion Hty; subst.
    inversion Hv; subst. inversion Hr2; subst. apply cnf_zero.
  - (* rfy_suc *) intros m v v' Hv0 IHv T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty. inversion Hty; subst.
    inversion Hv; subst. inversion Hr2; subst.
    apply cnf_suc. eapply (IHv (dEl vNat)); [ apply cnf_nat | eassumption | eassumption ].
  - (* rfy_neNat *) intros m n n' Hn IHn T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty. inversion Hty; subst.
    inversion Hv; subst. inversion Hr2; subst. apply cnf_ne. eapply IHn; eassumption.
  - (* rfy_neEmpty *) intros m n n' Hn IHn T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty. inversion Hty; subst.
    inversion Hv; subst. inversion Hr2; subst. apply cnf_ne. eapply IHn; eassumption.
  - (* rfy_neEl *) intros m c n n' Hn IHn T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty. inversion Hty; subst.
    inversion Hv; subst. inversion Hr2; subst. apply cnf_ne. eapply IHn; eassumption.
  - (* rfy_PiI *) intros m F B n n' Hn IHn T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty. inversion Hty; subst.
    inversion Hv; subst. inversion Hr2; subst. apply cnf_ne. eapply IHn; eassumption.
  - (* rfy_LamI *) intros m F B b b' Hb IHb T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty.
    inversion Hty as [ | | | | | | F0 B0 F2 B2 HcF HcB | | ]; subst.
    inversion Hv; subst. inversion Hr2; subst.
    apply cnf_lamI. eapply (IHb (dEl B2)); [ cbn; exact HcB | eassumption | eassumption ].
  - (* rfy_Pi *) intros m F B f ARG B' fa body Harg Hap Hva Hbody IHbody
                   T2 v2 nf2 Hty Hv Hr2.
    destruct T2 as [r2 l2|e2]; [destruct Hty|]. cbn in Hty.
    inversion Hty as [ | | | | | F0 B0 F2 B2 HconvF HconvB | | | ]; subst.
    inversion Hr2 as [ | | | | | | | | m0 FF BB ff AR BB' fa2 bd HAr HAp HVa HBd ]; subst.
    assert (HARG : conv_nf ARG AR).
    { eapply Reflect_conv with (TB := dEl (shift_val 0 1 F2));
        [ exact Harg | cbn; apply conv_nf_shift; exact HconvF | apply cne_var | exact HAr ]. }
    assert (HB' : conv_nf B' BB').
    { eapply Apply_conv_val;
        [ exact Hap
        | apply conv_sub_cons; [ exact HARG | apply conv_sub_refl ]
        | exact HconvB | exact HAp ]. }
    assert (HFA : conv_nf fa fa2).
    { eapply Apply_conv_Vapp;
        [ exact Hva
        | apply conv_nf_shift; exact HconvF
        | apply conv_nf_shift; exact HconvB
        | apply conv_nf_shift; exact Hv
        | exact HARG | exact HVa ]. }
    apply cnf_lam. eapply (IHbody (dEl BB')); [ cbn; exact HB' | exact HFA | exact HBd ].
  - (* rne_var *) intros m k n2 n2' Hcne Hr2.
    inversion Hcne; subst. inversion Hr2; subst. apply cne_var.
  - (* rne_emptyrec *) intros m rA lA A A' s s' HA IHA Hs IHs n2 n2' Hcne Hr2.
    inversion Hcne; subst. inversion Hr2; subst.
    apply cne_emptyrec; [ eapply IHA; eassumption | eapply IHs; eassumption ].
  - (* rne_app *) intros m f f' F F' B B' a a' Hf IHf HF IHF HB IHB Ha IHa n2 n2' Hcne Hr2.
    inversion Hcne as [ | | xf xF xB xa f2 F2 B2 a2 Hcf HcF HcB Hca | ]; subst.
    inversion Hr2; subst.
    apply cne_app;
      [ eapply IHf; eassumption
      | eapply IHF; eassumption
      | eapply IHB; eassumption
      | eapply (IHa (dEl F2)); [ cbn; exact HcF | eassumption | eassumption ] ].
  - (* rne_appI *) intros m f f' F F' B B' a a' Hf IHf HF IHF HB IHB Ha IHa n2 n2' Hcne Hr2.
    inversion Hcne as [ | | | xf xF xB xa f2 F2 B2 a2 Hcf HcF HcB Hca ]; subst.
    inversion Hr2; subst.
    apply cne_appI;
      [ eapply IHf; eassumption
      | eapply IHF; eassumption
      | eapply IHB; eassumption
      | eapply (IHa (dEl F2)); [ cbn; exact HcF | eassumption | eassumption ] ].
Qed.

Definition ReifyTy_conv := fst Reify_conv.
Definition Reify_conv_val := fst (snd Reify_conv).
Definition ReifyNe_conv := snd (snd Reify_conv).
