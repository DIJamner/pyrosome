(* ====================================================================== *)
(* OTT pivot, file 3/5 (see WIP/NEXT_SESSION.md UPDATE-n .. -r).            *)
(*                                                                        *)
(* The reduction-on-syntax LOGICAL RELATION over CLOSED Pyrosome terms      *)
(* (Pyrosome ctx = []; object open-ness lives in the `env` carried by the   *)
(* sort).  This file builds the FOUNDATION shared by every variant of the   *)
(* relation, then the reducibility relation itself.                        *)
(*                                                                        *)
(* FOUNDATION (this file, lower half) — generic over `wf_lang l` and a      *)
(* principal-argument selector `pa`:                                       *)
(*   - `reds a b`     : `a` weak-head reduces (via `star whstep`) to the    *)
(*                      whnf `b`.  This is the Pyrosome-native analog of     *)
(*                      metamltt's `WfRedTy`/`WfRedTm` records, EXCEPT we    *)
(*                      do not bake in a deterministic normalizer: the whnf  *)
(*                      reached is carried existentially and SOUNDNESS comes *)
(*                      for free from `star_whstep_sound` (reduction ⊆       *)
(*                      eq_term).  Where metamltt needs `whnf_det`, we will  *)
(*                      instead use Pyrosome constructor INJECTIVITY on the  *)
(*                      common reduct (the two whnfs of one term are         *)
(*                      eq_term-equal, hence same head by sort/term          *)
(*                      injectivity), so confluence of `whstep` is never     *)
(*                      required.                                           *)
(*   - `ne_eq t a b` : `a` and `b` are NEUTRAL and `eq_term`-equal at sort   *)
(*                      `t`.  This resolves UPDATE-n's open design Q2: the   *)
(*                      pivot makes `eq_term` THE declarative equality, so   *)
(*                      neutral members are compared by `eq_term` + a        *)
(*                      "both stuck" gate, NOT by a separate `~ne`           *)
(*                      inductive (metamltt needs `~ne` only because its     *)
(*                      `≡` is declarative-only; here `eq_term` already IS    *)
(*                      declarative).                                       *)
(*                                                                        *)
(* DESIGN NOTE for the reducibility relation (built on top): OTT's Tarski    *)
(* universe has NO universe CODE (`U` is a `ty`, never an `exp`), so type    *)
(* codes are only `Nat`/`Empty`/`Pi_*`/neutrals — the impredicative         *)
(* recursion that forces metamltt's Small/Large tower is ABSENT, and the     *)
(* type-LR is a single plain inductive.  "Under a Pi binder" extends the     *)
(* object env `G` (a term-level op), so the Kripke quantification is over    *)
(* object substitutions, not Pyrosome renamings.                           *)
(* ====================================================================== *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Section WithLang.
    Context (l : lang) (wfl : wf_lang l).
    Context (pa : V -> option nat).

    Notation whstep := (whstep V l pa).
    Notation whnf := (whnf pa).
    Notation neutral := (neutral pa).

    (* ------------------------------------------------------------------ *)
    (* Reduction to weak-head normal form.                                 *)
    (* `reds a b` := `a` weak-head reduces to the whnf `b`.  Sort-erased    *)
    (* (so it can be reused at every sort head); the sort at which the      *)
    (* equation `a = b` holds is supplied separately to `reds_sound`.      *)
    (* ------------------------------------------------------------------ *)
    Definition reds (a b : term) : Prop :=
      star whstep a b /\ whnf b.

    Lemma reds_star a b : reds a b -> star whstep a b.
    Proof. intros [H _]; exact H. Qed.

    Lemma reds_whnf a b : reds a b -> whnf b.
    Proof. intros [_ H]; exact H. Qed.

    (* A whnf reduces (in zero steps) to itself. *)
    Lemma reds_refl a : whnf a -> reds a a.
    Proof. intro H; split; [ constructor | exact H ]. Qed.

    (* Soundness: a reduction-to-whnf is an `eq_term` at any sort at which
       the source is well typed (reduction ⊆ eq_term, for free). *)
    Lemma reds_sound a b t
      : wf_term l [] a t -> reds a b -> eq_term l [] t a b.
    Proof.
      intros Hwf [Hstar _].
      eapply star_whstep_sound; eauto.
    Qed.

    (* Subject reduction for reduction-to-whnf. *)
    Lemma reds_wf a b t
      : wf_term l [] a t -> reds a b -> wf_term l [] b t.
    Proof.
      intros Hwf [Hstar _].
      eapply star_whstep_wf; eauto.
    Qed.

    (* Determinism UP TO CONVERSION: the two whnfs reached from one well-typed
       term are `eq_term`-equal.  This is the Pyrosome-native replacement for
       metamltt's syntactic `whnf_det` — it needs only soundness (reduction ⊆
       eq_term), never confluence of `whstep`.  The LR inversions that metamltt
       does by `whnf_det` we do by combining this with sort/term constructor
       INJECTIVITY on `b1 = b2` (up to eq_term). *)
    Lemma reds_eq a b1 b2 t
      : wf_term l [] a t -> reds a b1 -> reds a b2 -> eq_term l [] t b1 b2.
    Proof.
      intros Hwf Hr1 Hr2.
      eapply eq_term_trans.
      - eapply eq_term_sym; eapply reds_sound; eauto.
      - eapply reds_sound; eauto.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* Neutral equality.  Two terms are "neutral-equal" at sort `t` when    *)
    (* both are stuck (neutral) and they are `eq_term`-equal.  This is the   *)
    (* base PER carried by the Ne case of the LR (cf. metamltt `~ne`, but    *)
    (* delegated to the project's existing declarative equality).           *)
    (* ------------------------------------------------------------------ *)
    Definition ne_eq (t : sort) (a b : term) : Prop :=
      neutral a /\ neutral b /\ eq_term l [] t a b.

    Lemma ne_eq_l t a b : ne_eq t a b -> neutral a.
    Proof. intros (H & _ & _); exact H. Qed.

    Lemma ne_eq_r t a b : ne_eq t a b -> neutral b.
    Proof. intros (_ & H & _); exact H. Qed.

    Lemma ne_eq_conv t a b : ne_eq t a b -> eq_term l [] t a b.
    Proof. intros (_ & _ & H); exact H. Qed.

    (* `ne_eq` is symmetric and transitive (a PER), inheriting both from
       `eq_term`; reflexivity holds for any well-typed neutral. *)
    Lemma ne_eq_sym t a b : ne_eq t a b -> ne_eq t b a.
    Proof.
      intros (Ha & Hb & Hc); repeat split; eauto using eq_term_sym with lang_core.
    Qed.

    Lemma ne_eq_trans t a b c : ne_eq t a b -> ne_eq t b c -> ne_eq t a c.
    Proof.
      intros (Ha & Hb & Hab) (Hb' & Hc & Hbc); repeat split;
        eauto using eq_term_trans with lang_core.
    Qed.

    Lemma ne_eq_refl t a : neutral a -> wf_term l [] a t -> ne_eq t a a.
    Proof.
      intros Hn Hwf; repeat split; eauto using eq_term_refl with lang_core.
    Qed.

  End WithLang.

End WithVar.
