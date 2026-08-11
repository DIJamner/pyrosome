Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf
  Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.Values.
Import Core.Notations.

(* =====================================================================
   Rz: REALIZATION, AND THE TEST THAT THE *-ERASURE IS SOUND.

   Soundness of the value layer cannot be [eqt e v]: [*] is not a term of
   [ott_dtt] and has no sort (design.md section 14d).  It becomes a
   realization relation [Rz G i A v e] -- "the value [v] realizes the term
   [e]" -- and the fact the endgame turns on is

     Rz_eqt : Rz G i A v e1 -> Rz G i A v e2 -> eqt (sExp G i A) e1 e2

   "two terms with the same value are provably equal".  That is where
   proof irrelevance is spent, and it is the CHEAPEST REFUTATION of the
   whole [*] design: if it fails, the erasure is wrong.  It needs neither
   [Nrm] nor the weakening layer, so it is proved here, first.

   IT GOES THROUGH.  [Rz_eqt] below is [Qed], axiom-free.

   WHY THIS IS NOT A LOCAL CONCERN (design.md section 14e).  [*] is
   reachable from a CODE by a chain of entirely well-typed steps: a code
   can be an [Id], [Id]'s endpoints are relevant ELEMENTS, a relevant
   element can be an [Emptyrec] or an [app_rel] at an irrelevant domain,
   and both carry [*].  Section 14a's counterexample is one instance.
   [rz_id] is in the block below precisely so that this chain is exercised
   and not assumed away.

   SCOPE, stated honestly.  Every TYPE argument is held fixed between the
   value and the term: [rz_emptyrec] varies only the erased argument, and
   [rz_id] only the two endpoints.  That is not a hidden assumption about
   the theory, it is a restriction on which pairs this relation relates,
   and it is what keeps the relation single-sorted -- letting a type
   argument vary makes the conclusion's SORT vary with it, which needs a
   realization relation on types as well.  [app_rel] is left out of the
   block for exactly that reason (its conclusion sort mentions its
   argument), and is covered instead by the standalone
   [app_rel_star_eqt] below.  Both erasable positions of (E2) are
   therefore discharged; what is deferred is only their propagation
   through varying type indices.
   ===================================================================== *)

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

Ltac er := solve [ apply eq_term_refl; wfa ].

(* ------------------------------------------------------------------ *)
(* Two facts [Eqns.v] and [Wf.v] were missing, because both predate the  *)
(* Id fragment (neither mentions [oIdEq] anywhere).  They are in the     *)
(* files' own idiom and cost one [wf_by] / one [cong_step] each; they    *)
(* belong upstream in Wf.v/Eqns.v whenever those are next touched.       *)
(* ------------------------------------------------------------------ *)

Lemma wf_IdEq G l A B t u
  : wft G sEnv -> wft l sLvl ->
    wft A (sCode G oRel l) -> wft B (sCode G oRel l) ->
    wft t (sElt G oRel l A) -> wft u (sElt G oRel l B) ->
    wft (oIdEq G l A B t u) (sExp G (iEl oRel oL1) (oU G oIrr oL0)).
Proof. intros; wf_by "Id". Qed.

Lemma IdEq_cong G1 G2 l1 l2 A1 A2 B1 B2 t1 t2 u1 u2
  : eqt sEnv G1 G2 -> eqt sLvl l1 l2 ->
    eqt (sCode G2 oRel l2) A1 A2 -> eqt (sCode G2 oRel l2) B1 B2 ->
    eqt (sElt G2 oRel l2 A2) t1 t2 -> eqt (sElt G2 oRel l2 B2) u1 u2 ->
    eqt (sExp G2 (iEl oRel oL1) (oU G2 oIrr oL0))
      (oIdEq G1 l1 A1 B1 t1 u1) (oIdEq G2 l2 A2 B2 t2 u2).
Proof. intros; cong_step "Id" [u1;t1;B1;A1;l1;G1] [u2;t2;B2;A2;l2;G2]. Qed.

(* [Empty] elaborates at info [rel (iota L1)]; [eq_proof_irr] wants its
   code argument at [iCode L0].  The two are equal by "next0". *)
Lemma wft_c0 G c
  : wft G sEnv ->
    wft c (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0)) ->
    wft c (sCode G oIrr oL0).
Proof.
  intros HG Hc; eapply wf_term_conv; [ exact Hc | ].
  unfold sCode, iCode; apply sExp_cong.
  - apply eq_term_refl; exact HG.
  - apply Info_cong; [ apply Rel_cong | apply eq_term_sym; apply eq_next0 ].
  - apply eq_term_refl; apply wf_U; auto using wf_Irr, wf_L0.
Qed.

(* ================================================================== *)
(* The two erasable positions of (E2), discharged directly             *)
(* ================================================================== *)

(* POSITION 2, and this is design.md section 14a VERBATIM: the two
   [Emptyrec]s it exhibits -- distinct terms, both normal at the same
   RELEVANT type -- are provably equal.  Under the old [NfET] they were a
   counterexample to injectivity; under the [*]-collapse they have the
   same value, and this lemma is why that is sound. *)
Theorem emptyrec_star_eqt G rA lA A e1 e2
  : wft G sEnv -> wft rA sRelevance -> wft lA sLvl ->
    wft A (sCode G rA lA) ->
    wft e1 (sElt G oIrr oL0 (oEmpty G)) ->
    wft e2 (sElt G oIrr oL0 (oEmpty G)) ->
    eqt (sElt G rA lA A) (oEmptyrec G rA lA A e1) (oEmptyrec G rA lA A e2).
Proof.
  intros HG HrA HlA HA He1 He2.
  apply Emptyrec_cong; try er.
  apply eq_proof_irr; auto using wf_L0.
  apply wft_c0; [ exact HG | apply wf_Empty; exact HG ].
Qed.

(* POSITION 1: two [app_rel]s at an IRRELEVANT domain differing only in
   the argument.  Kept out of the [Rz] block because its conclusion SORT
   mentions the argument. *)
Theorem app_rel_star_eqt G lF lG F B f a1 a2
  : wft G sEnv -> wft lF sLvl -> wft lG sLvl ->
    wft F (sCode G oIrr lF) ->
    wft B (sCode (oExtC G oIrr lF F) oRel lG) ->
    wft f (sElt G oRel lG (oPiRel G oIrr lF lG F B)) ->
    wft a1 (sElt G oIrr lF F) -> wft a2 (sElt G oIrr lF F) ->
    eqt (sAppRelConcl G oIrr lF lG F B a2)
      (oAppRel G oIrr lF lG F B f a1) (oAppRel G oIrr lF lG F B f a2).
Proof.
  intros HG HlF HlG HF HB Hf Ha1 Ha2.
  apply AppRel_cong; try er.
  apply eq_proof_irr; assumption.
Qed.

(* ================================================================== *)
(* The relation                                                        *)
(* ================================================================== *)

(* CONVERSION-FREE BY DESIGN.  A [rz_conv] clause inside the inductive
   would appear on BOTH sides of [Rz_eqt], and the case where the first
   derivation is a leaf and the second a conversion has no induction
   hypothesis to appeal to -- the recursion there is on the SECOND
   derivation.  Taking the conversion closure afterwards ([RzE] below)
   makes [Rz_eqt] a plain induction on the first derivation with
   [inversion] on the second, and [RzE_eqt] three lines of transitivity.

   Every clause carries the well-typedness of its TERM side, which is
   what [rz_star] needs of the OTHER derivation ([Rz_wf]) in order to
   spend proof irrelevance. *)
Inductive Rz : term -> term -> term -> term -> term -> Prop :=
(* The whole irrelevant fragment: [*] realizes EVERY well-typed term at
   an irrelevant [El].  Its only premise is well-typedness, because that
   is all "proof irrelevance" asks for. *)
| rz_star : forall G l c e,
    wft G sEnv -> wft l sLvl -> wft c (sCode G oIrr l) ->
    wft e (sElt G oIrr l c) ->
    Rz G (iEl oIrr l) (oEl G oIrr l c) oStar e
(* ---- leaves ---- *)
| rz_nat : forall G,
    wft G sEnv -> Rz G (iCode oL0) (oU G oRel oL0) (oNat G) (oNat G)
| rz_empty : forall G,
    wft G sEnv ->
    Rz G (iEl oRel oL1) (oU G oIrr oL0) (oEmpty G) (oEmpty G)
| rz_zero : forall G,
    wft G sEnv ->
    Rz G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) (oZero G) (oZero G)
(* ---- propagation ---- *)
| rz_suc : forall G n ne,
    wft G sEnv ->
    wft (oSuc G ne) (sElt G oRel oL0 (oNat G)) ->
    Rz G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) n ne ->
    Rz G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) (oSuc G n) (oSuc G ne)
(* ERASABLE POSITION 2 *)
| rz_emptyrec : forall G rA lA A e,
    wft G sEnv -> wft rA sRelevance -> wft lA sLvl ->
    wft A (sCode G rA lA) ->
    wft e (sElt G oIrr oL0 (oEmpty G)) ->
    Rz G (iEl rA lA) (oEl G rA lA A)
       (oEmptyrec G rA lA A oStar) (oEmptyrec G rA lA A e)
(* THE CHAIN OF SECTION 14e: a CODE whose element subterms may contain
   [*].  Without this clause the whole point would be assumed away. *)
| rz_id : forall G l A B t u te ue,
    wft G sEnv -> wft l sLvl ->
    wft A (sCode G oRel l) -> wft B (sCode G oRel l) ->
    wft te (sElt G oRel l A) -> wft ue (sElt G oRel l B) ->
    Rz G (iEl oRel l) (oEl G oRel l A) t te ->
    Rz G (iEl oRel l) (oEl G oRel l B) u ue ->
    Rz G (iEl oRel oL1) (oU G oIrr oL0)
       (oIdEq G l A B t u) (oIdEq G l A B te ue).

(* Each clause carries it, so this is a case analysis. *)
Lemma Rz_wf G i A v e : Rz G i A v e -> wft e (sExp G i A).
Proof.
  destruct 1.
  - assumption.
  - apply wf_Nat; assumption.
  - apply wf_Empty; assumption.
  - apply wf_Zero; assumption.
  - assumption.
  - apply wf_Emptyrec; assumption.
  - apply wf_IdEq; assumption.
Qed.

(* ================================================================== *)
(* THE TEST                                                            *)
(* ================================================================== *)

Theorem Rz_eqt G i A v e1 e2
  : Rz G i A v e1 -> Rz G i A v e2 -> eqt (sExp G i A) e1 e2.
Proof.
  intros H1; revert e2;
    induction H1 as
      [ G l c e HG Hl Hc He
      | G HG
      | G HG
      | G HG
      | G n ne HG Hne Hn IHn
      | G rA lA A e HG HrA HlA HA He
      | G l A B t u te ue HG Hl HA HB Hte Hue Ht IHt Hu IHu ];
    intros eR HR.
  (* ---- [*]: PROOF IRRELEVANCE IS SPENT HERE, and nowhere else. *)
  - apply eq_proof_irr; try assumption.
    exact (Rz_wf HR).
  (* ---- leaves: only the clause with the same value head can fire ---- *)
  - inversion HR; subst; er.
  - inversion HR; subst; er.
  - inversion HR; subst; er.
  (* ---- suc ---- *)
  - inversion HR; subst.
    apply Suc_cong; [ er | ].
    apply IHn; assumption.
  (* ---- Emptyrec: erasable position 2 ---- *)
  - inversion HR; subst.
    apply emptyrec_star_eqt; assumption.
  (* ---- Id: the section-14e chain ---- *)
  - inversion HR; subst.
    apply IdEq_cong; try er.
    + apply IHt; assumption.
    + apply IHu; assumption.
Qed.

(* ================================================================== *)
(* The conversion closure -- what the layer above actually uses         *)
(* ================================================================== *)

(* [RzE G i A v e] : [v] realizes SOME term provably equal to [e].  This
   is the form that is stable under the theory's equations, which is what
   the 28 sigma-equations need. *)
Definition RzE (G i A v e : term) : Prop :=
  exists e0, Rz G i A v e0 /\ eqt (sExp G i A) e e0.

Lemma RzE_intro G i A v e : Rz G i A v e -> RzE G i A v e.
Proof.
  intro H; exists e; split;
    [ exact H | apply eq_term_refl; exact (Rz_wf H) ].
Qed.

Lemma RzE_conv G i A v e e'
  : RzE G i A v e -> eqt (sExp G i A) e' e -> RzE G i A v e'.
Proof.
  intros [e0 [H Heq]] Heq'; exists e0; split;
    [ exact H | eapply eq_term_trans; eassumption ].
Qed.

(* [Rz_eqt] survives the closure, which is the statement the endgame
   consumes. *)
Theorem RzE_eqt G i A v e1 e2
  : RzE G i A v e1 -> RzE G i A v e2 -> eqt (sExp G i A) e1 e2.
Proof.
  intros [n1 [H1 Hq1]] [n2 [H2 Hq2]].
  eapply eq_term_trans; [ exact Hq1 | ].
  eapply eq_term_trans; [ exact (Rz_eqt H1 H2) | ].
  apply eq_term_sym; exact Hq2.
Qed.
