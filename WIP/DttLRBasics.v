Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttWf WIP.DttEqns WIP.DttNf WIP.DttLR.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 2a: the elementary interface to [RTy].

   Everything here is what can be said about the candidate relation of
   WIP/DttLR.v WITHOUT any weakening/substitution metatheory (Layer 1's
   [Wk_wf]/[NfCode_wk]/[NfCode_subst], WIP/DttNfWf.v) and without Layer
   0.5's rigidity ([NfCode_inj]/[TyOk_inj]).  Concretely:

     * the six clauses are pairwise disjoint BY HEAD SYMBOL, so each has
       an inversion ("read the candidate back") lemma;
     * hence [RTy] rebuilds [TyOk] of its own type index;
     * hence the four LEAF candidates are closed under provable equality
       of the subject, with no side conditions at all;
     * and [RTm]'s elimination direction is definitionally free.

   Two things are NOT here, and both are blocked on layers that do not
   exist yet rather than on effort; see the section headers for the exact
   obstruction.

     * [RTy_fun] (syntactic functionality).  The Pi clauses name their
       domain/codomain candidates at a CHOSEN normal representative
       ([F']/[C]), and two derivations at the same syntactic type may
       choose different ones.  Identifying them is exactly Layer 0.5's
       [NfCode_inj]/[TyOk_inj], so [RTy_fun] is proved here from those two
       statements as explicit hypotheses ([NfCodeInj]/[TyOkInj] below,
       verbatim from WIP/dtt_norm_design.md section 4).

     * [RTy_cand_eq] at the two Pi clauses.  See the header of section 3.

   STRUCTURAL NOTE.  Coq's generated [RTy_ind] has NO induction hypothesis
   in either Pi case: the recursive occurrences of [RTy] sit under [ex] and
   [and], which the scheme generator treats as non-recursive.  Section 0
   therefore builds [RTy_strong_ind] by hand as a [Fixpoint]; the guard
   condition does accept recursion through [forall]/[ex]/[and], so this is
   a plain definition and not an axiom.  Every induction below goes through
   it.
   ===================================================================== *)

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* Small glue: well-formedness out of a provable equation               *)
(* ------------------------------------------------------------------ *)

Lemma eqt_wf_l t e1 e2 : eqt t e1 e2 -> wft e1 t.
Proof.
  intro H; eapply eq_term_wf_l; try typeclasses eauto;
    [ exact ott_dtt_wf | constructor | exact H ].
Qed.

Lemma eqt_wf_r t e1 e2 : eqt t e1 e2 -> wft e2 t.
Proof.
  intro H; eapply eq_term_wf_r; try typeclasses eauto;
    [ exact ott_dtt_wf | constructor | exact H ].
Qed.

(* ================================================================== *)
(* 0. Syntactic non-confusion for the six clause indices               *)
(* ================================================================== *)

(* The clause indices are [U] against [El], and inside [El] the head of the
   code.  All of it is [con]-vs-[con] with different names, hence
   [congruence] after unfolding; each fact is named so later layers can
   reuse it. *)

Lemma oU_neq_oEl G r l G' r' l' e : oU G r l <> oEl G' r' l' e.
Proof. unfold oU, oEl; congruence. Qed.

Lemma iCode_neq_iEl l r l' : iCode l <> iEl r l'.
Proof. unfold iCode, iEl, oInfo, oNext, oIota; congruence. Qed.

Lemma oNat_neq_oEmpty G G' : oNat G <> oEmpty G'.
Proof. unfold oNat, oEmpty; congruence. Qed.

Lemma oNat_neq_oPiRel G G' rF lF lG F B : oNat G <> oPiRel G' rF lF lG F B.
Proof. unfold oNat, oPiRel; congruence. Qed.

Lemma oNat_neq_oPiIrr G G' rF lF F B : oNat G <> oPiIrr G' rF lF F B.
Proof. unfold oNat, oPiIrr; congruence. Qed.

Lemma oEmpty_neq_oPiRel G G' rF lF lG F B : oEmpty G <> oPiRel G' rF lF lG F B.
Proof. unfold oEmpty, oPiRel; congruence. Qed.

Lemma oEmpty_neq_oPiIrr G G' rF lF F B : oEmpty G <> oPiIrr G' rF lF F B.
Proof. unfold oEmpty, oPiIrr; congruence. Qed.

Lemma oPiRel_neq_oPiIrr G rF lF lG F B G' rF' lF' F' B'
  : oPiRel G rF lF lG F B <> oPiIrr G' rF' lF' F' B'.
Proof. unfold oPiRel, oPiIrr; congruence. Qed.

Lemma oRel_neq_oIrr : oRel <> oIrr.
Proof. unfold oRel, oIrr; congruence. Qed.

(* ------------------------------------------------------------------ *)
(* A variable is never one of the four canonical codes                  *)
(* ------------------------------------------------------------------ *)

(* [VarT] derives exactly two shapes.  This is what makes the [rty_var]
   clause disjoint from the four code clauses: the overlap would need a
   variable to BE [Nat]/[Empty]/[Pi_rel]/[Pi_irr] syntactically. *)
Lemma VarT_head G i A x
  : VarT G i A x ->
    (exists G0 i0 A0, x = oHd G0 i0 A0)
    \/ (exists D G0 w i0 A0 y, x = oExpSubst D G0 w i0 A0 y).
Proof. destruct 1; eauto 10. Qed.

Ltac varT_absurd H :=
  apply VarT_head in H;
  destruct H as [ (?&?&?&?) | (?&?&?&?&?&?&?) ];
  unfold oNat, oEmpty, oPiRel, oPiIrr, oHd, oExpSubst in *;
  congruence.

Lemma VarT_not_Nat G i A G0 : ~ VarT G i A (oNat G0).
Proof. intro H; varT_absurd H. Qed.

Lemma VarT_not_Empty G i A G0 : ~ VarT G i A (oEmpty G0).
Proof. intro H; varT_absurd H. Qed.

Lemma VarT_not_PiRel G i A G0 rF lF lG F B
  : ~ VarT G i A (oPiRel G0 rF lF lG F B).
Proof. intro H; varT_absurd H. Qed.

Lemma VarT_not_PiIrr G i A G0 rF lF F B
  : ~ VarT G i A (oPiIrr G0 rF lF F B).
Proof. intro H; varT_absurd H. Qed.

(* The uniform "kill the impossible branches" step of every inversion
   below: [inversion] itself discriminates the clauses whose type index has
   a different head, and the only surviving overlap is [rty_var] against a
   canonical code, which the four lemmas above rule out. *)
Ltac rty_kill :=
  try (exfalso;
       match goal with
       | [ Hx : VarT _ _ _ _ |- _ ] => varT_absurd Hx
       end).

(* ================================================================== *)
(* 1. Per-clause introduction and elimination                          *)
(* ================================================================== *)

(* ---- introduction: the canonical candidate of each leaf clause ---- *)

Lemma RTy_U_i G r l
  : EnvOk G -> RelNf r -> LvlNf l -> RTy G (iCode l) (oU G r l) (HasNfCode G r l).
Proof. intros; apply rty_U; try assumption; reflexivity. Qed.

Lemma RTy_nat_i G
  : EnvOk G ->
    RTy G (iEl oRel oL0) (oEl G oRel oL0 (oNat G))
        (HasNf G (iEl oRel oL0) (oEl G oRel oL0 (oNat G))).
Proof. intros; apply rty_nat; try assumption; reflexivity. Qed.

Lemma RTy_empty_i G
  : EnvOk G ->
    RTy G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G))
        (HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G))).
Proof. intros; apply rty_empty; try assumption; reflexivity. Qed.

Lemma RTy_var_i G r l c
  : VarT G (iCode l) (oU G r l) c ->
    RTy G (iEl r l) (oEl G r l c) (HasNe G (iEl r l) (oEl G r l c)).
Proof. intros; apply rty_var; try assumption; reflexivity. Qed.

(* ---- elimination: read the candidate back ---- *)

Lemma RTy_U_e G r l P c
  : RTy G (iCode l) (oU G r l) P -> (P c <-> HasNfCode G r l c).
Proof. intro H; inversion H; subst; auto; rty_kill. Qed.

Lemma RTy_nat_e G P e
  : RTy G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) P ->
    (P e <-> HasNf G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e).
Proof. intro H; inversion H; subst; auto; rty_kill. Qed.

Lemma RTy_empty_e G P e
  : RTy G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) P ->
    (P e <-> HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e).
Proof. intro H; inversion H; subst; auto; rty_kill. Qed.

Lemma RTy_var_e G r l c P e
  : VarT G (iCode l) (oU G r l) c ->
    RTy G (iEl r l) (oEl G r l c) P ->
    (P e <-> HasNe G (iEl r l) (oEl G r l c) e).
Proof. intros Hx H; inversion H; subst; auto; rty_kill. Qed.

(* The two Pi clauses hand back the domain/codomain candidate FAMILIES
   together with the reading of [P].  [Pd]/[Pc] are constructor parameters,
   so they can only be produced existentially. *)

Lemma RTy_pi_rel_e G rF lF lG F B P
  : RTy G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) P ->
    exists (Pd : term -> term -> term -> Prop)
           (Pc : term -> term -> term -> term -> Prop),
      RelNf rF /\ LvlNf lF /\ LvlNf lG
      /\ NfCode G rF lF F
      /\ NfCode (oExtC G rF lF F) oRel lG B
      /\ (forall D w, Wk D G w -> EnvOk D ->
            exists F', NfCode D rF lF F'
                    /\ eqt (sCode D rF lF) (wkCode D G w rF lF F) F'
                    /\ RTy D (iEl rF lF) (oEl D rF lF F') (Pd D w))
      /\ (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
            exists C, TyOk D (iEl oRel lG) C
                   /\ eqt (sTy D (iEl oRel lG))
                          (codAtRel D G rF lF lG F B w a) C
                   /\ RTy D (iEl oRel lG) C (Pc D w a))
      /\ (forall e, P e <->
            (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
               Pc D w a (appAtRel D G rF lF lG F B w e a))).
Proof.
  intro H; inversion H; subst; rty_kill;
    do 2 eexists; repeat apply conj; eassumption.
Qed.

Lemma RTy_pi_irr_e G rF lF F B P
  : RTy G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) P ->
    exists (Pd : term -> term -> term -> Prop)
           (Pc : term -> term -> term -> term -> Prop),
      RelNf rF /\ LvlNf lF
      /\ NfCode G rF lF F
      /\ NfCode (oExtC G rF lF F) oIrr oL0 B
      /\ (forall D w, Wk D G w -> EnvOk D ->
            exists F', NfCode D rF lF F'
                    /\ eqt (sCode D rF lF) (wkCode D G w rF lF F) F'
                    /\ RTy D (iEl rF lF) (oEl D rF lF F') (Pd D w))
      /\ (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
            exists C, TyOk D (iEl oIrr oL0) C
                   /\ eqt (sTy D (iEl oIrr oL0))
                          (codAtIrr D G rF lF F B w a) C
                   /\ RTy D (iEl oIrr oL0) C (Pc D w a))
      /\ (forall e, P e <->
            (HasNf G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e
             /\ forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
                  Pc D w a (appAtIrr D G rF lF F B w e a))).
Proof.
  intro H; inversion H; subst; rty_kill;
    do 2 eexists; repeat apply conj; eassumption.
Qed.

(* ================================================================== *)
(* 4. [RTy] rebuilds well-formedness of its own type index             *)
(* ================================================================== *)

(* Each clause's premises are exactly what [TyOk]/[NfCode] need, so this is
   a one-step case analysis -- no induction, no Layer-1 input. *)
Theorem RTy_TyOk G i A P : RTy G i A P -> TyOk G i A.
Proof.
  destruct 1;
    eauto using tyok_U, tyok_El, nfcode_nat, nfcode_empty, nfcode_var,
                nfcode_pi_rel, nfcode_pi_irr.
Qed.

(* ================================================================== *)
(* 2. The induction principle [RTy] actually needs                     *)
(* ================================================================== *)

(* Coq's [RTy_ind] gives NO induction hypothesis in the two Pi cases: the
   recursive occurrences of [RTy] there sit under [ex] and [and] (a
   "nested" position), and the scheme generator omits IHs for those.  The
   guard condition, however, does accept recursion through
   [forall]/[ex]/[and], so the principle can simply be written out as a
   [Fixpoint].  This is an ordinary definition -- no axiom, no
   well-founded recursion, no [Acc] -- and it is what every induction over
   [RTy] in this development (and in the layers above) must use.

   The only difference from [RTy_ind] is the extra [Pr ...] conjunct in the
   two nested premises of each Pi case. *)

Section StrongInd.
  Context (Pr : term -> term -> term -> (term -> Prop) -> Prop).

  Context
    (H_U : forall G r l P,
        EnvOk G -> RelNf r -> LvlNf l ->
        (forall c, P c <-> HasNfCode G r l c) ->
        Pr G (iCode l) (oU G r l) P)
    (H_nat : forall G P,
        EnvOk G ->
        (forall e, P e <-> HasNf G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e) ->
        Pr G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) P)
    (H_empty : forall G P,
        EnvOk G ->
        (forall e, P e <-> HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e) ->
        Pr G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) P)
    (H_var : forall G r l c P,
        VarT G (iCode l) (oU G r l) c ->
        (forall e, P e <-> HasNe G (iEl r l) (oEl G r l c) e) ->
        Pr G (iEl r l) (oEl G r l c) P)
    (H_pi_rel : forall G rF lF lG F B P Pd Pc,
        RelNf rF -> LvlNf lF -> LvlNf lG ->
        NfCode G rF lF F ->
        NfCode (oExtC G rF lF F) oRel lG B ->
        (forall D w, Wk D G w -> EnvOk D ->
           exists F', NfCode D rF lF F'
                   /\ eqt (sCode D rF lF) (wkCode D G w rF lF F) F'
                   /\ RTy D (iEl rF lF) (oEl D rF lF F') (Pd D w)
                   /\ Pr D (iEl rF lF) (oEl D rF lF F') (Pd D w)) ->
        (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
           exists C, TyOk D (iEl oRel lG) C
                  /\ eqt (sTy D (iEl oRel lG)) (codAtRel D G rF lF lG F B w a) C
                  /\ RTy D (iEl oRel lG) C (Pc D w a)
                  /\ Pr D (iEl oRel lG) C (Pc D w a)) ->
        (forall e, P e <->
           (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
              Pc D w a (appAtRel D G rF lF lG F B w e a))) ->
        Pr G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) P)
    (H_pi_irr : forall G rF lF F B P Pd Pc,
        RelNf rF -> LvlNf lF ->
        NfCode G rF lF F ->
        NfCode (oExtC G rF lF F) oIrr oL0 B ->
        (forall D w, Wk D G w -> EnvOk D ->
           exists F', NfCode D rF lF F'
                   /\ eqt (sCode D rF lF) (wkCode D G w rF lF F) F'
                   /\ RTy D (iEl rF lF) (oEl D rF lF F') (Pd D w)
                   /\ Pr D (iEl rF lF) (oEl D rF lF F') (Pd D w)) ->
        (forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
           exists C, TyOk D (iEl oIrr oL0) C
                  /\ eqt (sTy D (iEl oIrr oL0)) (codAtIrr D G rF lF F B w a) C
                  /\ RTy D (iEl oIrr oL0) C (Pc D w a)
                  /\ Pr D (iEl oIrr oL0) C (Pc D w a)) ->
        (forall e, P e <->
           (HasNf G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e
            /\ forall D w a, Wk D G w -> EnvOk D -> Pd D w a ->
                 Pc D w a (appAtIrr D G rF lF F B w e a))) ->
        Pr G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) P).

  Fixpoint RTy_strong_ind G i A P (H : RTy G i A P) {struct H} : Pr G i A P :=
    match H in RTy G0 i0 A0 P0 return Pr G0 i0 A0 P0 with
    | @rty_U G r l P HG Hr Hl Hiff => @H_U G r l P HG Hr Hl Hiff
    | @rty_nat G P HG Hiff => @H_nat G P HG Hiff
    | @rty_empty G P HG Hiff => @H_empty G P HG Hiff
    | @rty_var G r l c P Hx Hiff => @H_var G r l c P Hx Hiff
    | @rty_pi_rel G rF lF lG F B P Pd Pc HrF HlF HlG HF HB Hd Hc Hiff =>
        @H_pi_rel G rF lF lG F B P Pd Pc HrF HlF HlG HF HB
          (fun D w Hw HD =>
             match Hd D w Hw HD with
             | ex_intro _ F' (conj h1 (conj h2 h3)) =>
                 ex_intro _ F' (conj h1 (conj h2 (conj h3 (RTy_strong_ind h3))))
             end)
          (fun D w a Hw HD Ha =>
             match Hc D w a Hw HD Ha with
             | ex_intro _ C (conj h1 (conj h2 h3)) =>
                 ex_intro _ C (conj h1 (conj h2 (conj h3 (RTy_strong_ind h3))))
             end)
          Hiff
    | @rty_pi_irr G rF lF F B P Pd Pc HrF HlF HF HB Hd Hc Hiff =>
        @H_pi_irr G rF lF F B P Pd Pc HrF HlF HF HB
          (fun D w Hw HD =>
             match Hd D w Hw HD with
             | ex_intro _ F' (conj h1 (conj h2 h3)) =>
                 ex_intro _ F' (conj h1 (conj h2 (conj h3 (RTy_strong_ind h3))))
             end)
          (fun D w a Hw HD Ha =>
             match Hc D w a Hw HD Ha with
             | ex_intro _ C (conj h1 (conj h2 h3)) =>
                 ex_intro _ C (conj h1 (conj h2 (conj h3 (RTy_strong_ind h3))))
             end)
          Hiff
    end.

End StrongInd.

(* ================================================================== *)
(* 3. Candidates are closed under provable equality of the subject      *)
(* ================================================================== *)

(* [HasNf]/[HasNe]/[HasNfCode] are stated UP TO [eq_term] already, so at
   the four leaf clauses closure is one use of transitivity and needs no
   side condition whatever.
   -- see the header of section 3b for the two Pi clauses. *)

Definition CandEq (G i A : term) (P : term -> Prop) : Prop :=
  forall e e', P e -> eqt (sExp G i A) e e' -> P e'.

Lemma HasNf_eq G i A e e'
  : HasNf G i A e -> eqt (sExp G i A) e e' -> HasNf G i A e'.
Proof.
  intros [n [Hn Heq]] Heq'; exists n; split; [ exact Hn | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact Heq' | exact Heq ].
Qed.

Lemma HasNe_eq G i A e e'
  : HasNe G i A e -> eqt (sExp G i A) e e' -> HasNe G i A e'.
Proof.
  intros [n [Hn Heq]] Heq'; exists n; split; [ exact Hn | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact Heq' | exact Heq ].
Qed.

Lemma HasNfCode_eq G r l c c'
  : HasNfCode G r l c -> eqt (sCode G r l) c c' -> HasNfCode G r l c'.
Proof.
  intros [n [Hn Heq]] Heq'; exists n; split; [ exact Hn | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact Heq' | exact Heq ].
Qed.

Lemma RTy_cand_eq_U G r l P
  : RTy G (iCode l) (oU G r l) P -> CandEq G (iCode l) (oU G r l) P.
Proof.
  intros H e e' He Heq.
  apply (RTy_U_e e' H).
  eapply HasNfCode_eq; [ apply (RTy_U_e e H); exact He | exact Heq ].
Qed.

Lemma RTy_cand_eq_nat G P
  : RTy G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) P ->
    CandEq G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) P.
Proof.
  intros H e e' He Heq.
  apply (RTy_nat_e e' H).
  eapply HasNf_eq; [ apply (RTy_nat_e e H); exact He | exact Heq ].
Qed.

Lemma RTy_cand_eq_empty G P
  : RTy G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) P ->
    CandEq G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) P.
Proof.
  intros H e e' He Heq.
  apply (RTy_empty_e e' H).
  eapply HasNe_eq; [ apply (RTy_empty_e e H); exact He | exact Heq ].
Qed.

Lemma RTy_cand_eq_var G r l c P
  : VarT G (iCode l) (oU G r l) c ->
    RTy G (iEl r l) (oEl G r l c) P ->
    CandEq G (iEl r l) (oEl G r l c) P.
Proof.
  intros Hx H e e' He Heq.
  apply (RTy_var_e e' Hx H).
  eapply HasNe_eq; [ apply (RTy_var_e e Hx H); exact He | exact Heq ].
Qed.
