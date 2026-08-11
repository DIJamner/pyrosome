Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Tools.ComputeWf Tools.Matches
  Tools.EGraph.ComputeWf.
From Pyrosome.Lang Require Import Subst.
From Pyrosome.Lang.OTT Require Import Base Nat Pi SubstCommute ProofIrr.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 0: the target language and its vocabulary.

   The analogue of Gluing/Stlc/Syntax.v for the dependent theory of
   src/Pyrosome/Lang/OTT/.

   TARGET LANGUAGE.  [ott_dtt] is

       ott_proofirr_el ++ ott_subst_commute ++ ott_pi ++ ott_nat ++ ott_base
         ++ subst_ott ++ ott_info                                  (74 rules)

   i.e. Lang/OTT's Tarski-universe core (U/El, two levels, relevance
   tags), the parameterized substitution calculus, Nat/zero/suc/Empty/
   Emptyrec, dependent Pi (relevant + irrelevant) with beta, ETA, and
   the substitution commutations, and definitional proof irrelevance
   (Lang/OTT/ProofIrr.v's [ott_proofirr_el] -- the El-sorted rule, stated
   over a universe code "c" : #"U" #"irr" "l" rather than a bare type
   metavariable, since a bare-type-metavariable statement gives the rigid
   model's [rceq_term] a refutable USkel obligation; see ProofIrr.v for
   the full explanation).

   Census: 32 term_rule, 33 term_eq_rule, 9 sort_rule, 0 sort_eq_rule.

   [ott_subst_commute] (src/Pyrosome/Lang/OTT/SubstCommute.v) supplies the
   four substitution commutations Lang/OTT/Pi.v and Lang/OTT/Nat.v never
   had -- "app_rel subst", "app_irr subst", "lam_irr subst" and
   "Emptyrec subst".  Without them those terms are STUCK under an explicit
   substitution, normal forms are not stable under weakening, and the
   normalization statement is false.  Upstream, "lam_irr subst" and
   "app_irr subst" are subsumed by Lang/OTT/ProofIrr.v, which is out of
   scope here; "app_rel subst" is derivable from eta and beta but is much
   cheaper as a rule.
   The last figure is the single most consequential fact about this
   language: it has NO sort equations at all.  Sorts are indexed by TERMS
   ([ty G i], [exp G i A]) and all "type equality" of the object theory is
   term equality at the sort [ty].  Consequently the [csort_by] obligation
   of CutTModel_ok is VACUOUS.

   Unlike the earlier draft of this development, [ott_pi] is taken WHOLE:
   Lang/OTT/Pi.v now discharges "Pi_rel eta" with [push_rule] rather than
   [push_rule_todo], so the language is axiom-free and eta is available.
   Eta is not a decoration -- it is what makes reification type-directed
   and escape/reflect a single mutual induction (see WIP/dtt_norm_design.md
   section 7).

   SHAPES.  Every constructor's argument order below was read off the
   COMPILED language (rule contexts are stored most-recent-first and [con]'s
   argument list follows that order), not off the surface notation.  Note in
   particular:
     - [snoc]'s con list is [v;g;A;i;G';G]  (v BEFORE g, unlike the STLC
       language where it was [v;A;g;G';G]);
     - [hd], [wkn], [id], [forget], [emp] carry their index arguments in the
       con list even though their [args] fields are empty;
     - [Empty] and [Pi_irr] are elaborated at info [rel (iota L1)], while
       [Nat] is elaborated at info [rel (next L0)] -- the two are equal only
       via the "next0" equation.
   ===================================================================== *)

Notation term := (@Term.term string).
Notation sort := (@Term.sort string).
Notation ctx := (@Term.ctx string).
Notation lang := (@Rule.lang string).

(* ------------------------------------------------------------------ *)
(* The language                                                         *)
(* ------------------------------------------------------------------ *)

Definition ott_dtt : lang := Eval vm_compute in
  (ott_proofirr_el ++ ott_subst_commute ++ ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info).

Lemma ott_dtt_wf : wf_lang ott_dtt.
Proof. compute_wf_lang. Qed.

(* ------------------------------------------------------------------ *)
(* Sorts                                                                *)
(* ------------------------------------------------------------------ *)

Definition sRelevance : sort := scon "relevance" [].
Definition sLvl : sort := scon "lvl" [].
Definition sTlvl : sort := scon "tlvl" [].
Definition sInfo : sort := scon "tyinfo" [].
Definition sLtl (a b : term) : sort := scon "ltl" [b; a].
Definition sEnv : sort := scon "env" [].
Definition sSub (G G' : term) : sort := scon "sub" [G'; G].
Definition sTy (G i : term) : sort := scon "ty" [i; G].
Definition sExp (G i A : term) : sort := scon "exp" [A; i; G].

(* ------------------------------------------------------------------ *)
(* Term constructors                                                    *)
(* ------------------------------------------------------------------ *)

(* --- ott_info: relevance / levels / type-levels / the bundle --- *)
Definition oRel : term := con "rel" [].
Definition oIrr : term := con "irr" [].
Definition oL0 : term := con "L0" [].
Definition oL1 : term := con "L1" [].
Definition oLt01 : term := con "L0<L1" [].
Definition oIota (l : term) : term := con "iota" [l].
Definition oInf : term := con "inf" [].
Definition oNext (l : term) : term := con "next" [l].
Definition oInfo (r l : term) : term := con "info" [l; r].

(* --- subst_ott: the substitution calculus, parameterized by tyinfo --- *)
Definition oEmp : term := con "emp" [].
Definition oExt (G i A : term) : term := con "ext" [A; i; G].
Definition oId (G : term) : term := con "id" [G].
Definition oForget (G : term) : term := con "forget" [G].
Definition oCmp (G1 G2 G3 f g : term) : term := con "cmp" [g; f; G3; G2; G1].
Definition oTySubst (G G' g i A : term) : term :=
  con "ty_subst" [A; i; g; G'; G].
Definition oExpSubst (G G' g i A v : term) : term :=
  con "exp_subst" [v; A; i; g; G'; G].
Definition oSnoc (G G' i A g v : term) : term := con "snoc" [v; g; A; i; G'; G].
Definition oWkn (G i A : term) : term := con "wkn" [A; i; G].
Definition oHd (G i A : term) : term := con "hd" [A; i; G].

(* --- ott_base: the Tarski universe --- *)
Definition oU (G r l : term) : term := con "U" [l; r; G].
Definition oEl (G r l e : term) : term := con "El" [e; l; r; G].

(* --- ott_nat --- *)
Definition oNat (G : term) : term := con "Nat" [G].
Definition oZero (G : term) : term := con "zero" [G].
Definition oSuc (G n : term) : term := con "suc" [n; G].
Definition oEmpty (G : term) : term := con "Empty" [G].
Definition oEmptyrec (G rA lA A e : term) : term :=
  con "Emptyrec" [e; A; lA; rA; G].

(* --- ott_pi --- *)
Definition oPiRel (G rF lF lG F B : term) : term :=
  con "Pi_rel" [B; F; lG; lF; rF; G].
Definition oPiIrr (G rF lF F B : term) : term :=
  con "Pi_irr" [B; F; lF; rF; G].
Definition oLamRel (G rF lF lG F B t : term) : term :=
  con "lam_rel" [t; B; F; lG; lF; rF; G].
Definition oLamIrr (G rF lF F B t : term) : term :=
  con "lam_irr" [t; B; F; lF; rF; G].
Definition oAppRel (G rF lF lG F B f a : term) : term :=
  con "app_rel" [a; f; B; F; lG; lF; rF; G].
Definition oAppIrr (G rF lF F B f a : term) : term :=
  con "app_irr" [a; f; B; F; lF; rF; G].

(* ------------------------------------------------------------------ *)
(* Derived abbreviations that recur in the rules' conclusion sorts       *)
(* ------------------------------------------------------------------ *)

(* The info of a code at level [l]: [rel, next l]. *)
Definition iCode (l : term) : term := oInfo oRel (oNext l).
(* The info of an element of a type at relevance [r], level [l]. *)
Definition iEl (r l : term) : term := oInfo r (oIota l).

(* [sCode G r l] : the sort of codes for [r,l]-types in [G]. *)
Definition sCode (G r l : term) : sort := sExp G (iCode l) (oU G r l).
(* [sEl G r l e] : the sort of elements of the type named by the code [e]. *)
Definition sElt (G r l e : term) : sort := sExp G (iEl r l) (oEl G r l e).

(* The context extension by the type named by a code (the shape every binder
   rule uses): [ext G (info rF (iota lF)) (El G rF lF F)]. *)
Definition oExtC (G rF lF F : term) : term :=
  oExt G (iEl rF lF) (oEl G rF lF F).

(* The instantiating substitution [<id, a> : sub G (extC G rF lF F)], as it
   appears in [app_rel]'s conclusion sort. *)
Definition oInst (G rF lF F a : term) : term :=
  oSnoc G G (iEl rF lF) (oEl G rF lF F) (oId G) a.

(* [app_rel]'s conclusion sort, verbatim from the compiled rule (with the
   argument [a] left abstract). *)
Definition sAppRelConcl (G rF lF lG F B a : term) : sort :=
  sExp G (iEl oRel lG)
    (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
       (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B)).

Definition sAppIrrConcl (G rF lF F B a : term) : sort :=
  sExp G (iEl oIrr oL0)
    (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a)
       (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B)).

(* The lifting of [g : sub G G'] under a binder of code [F] (the "under'"
   of the compiled substitution commutations):
     <cmp (wkn (extC G rF lF F[g])) g , hd> : sub (extC G ...) (extC G' ...) *)
Definition oLift (G G' g rF lF F : term) : term :=
  let Fg := oExpSubst G G' g (iCode lF) (oU G' rF lF) F in
  let GF := oExtC G rF lF Fg in
  oSnoc GF G' (iEl rF lF) (oEl G' rF lF F)
    (oCmp GF G G' (oWkn G (iEl rF lF) (oEl G rF lF Fg)) g)
    (oHd G (iEl rF lF) (oEl G rF lF Fg)).

(* ------------------------------------------------------------------ *)
(* Index normal forms                                                   *)
(*                                                                      *)
(* [relevance] and [lvl] are rigid (no equations, two closed constructors *)
(* each).  [tlvl] has the two equations "next0" ([next L0 = iota L1]) and *)
(* "next1" ([next L1 = inf]); its normal forms are therefore exactly      *)
(* [iota L0], [iota L1], [inf] -- a THREE-element set.  [tyinfo] has one  *)
(* constructor, so its normal forms are the six [info r n].              *)
(* ------------------------------------------------------------------ *)

Inductive RelNf : term -> Prop :=
| relnf_rel : RelNf oRel
| relnf_irr : RelNf oIrr.

Inductive LvlNf : term -> Prop :=
| lvlnf_L0 : LvlNf oL0
| lvlnf_L1 : LvlNf oL1.

Inductive TlvlNf : term -> Prop :=
| tlvlnf_iota : forall l, LvlNf l -> TlvlNf (oIota l)
| tlvlnf_inf : TlvlNf oInf.

Inductive InfoNf : term -> Prop :=
| infonf : forall r n, RelNf r -> TlvlNf n -> InfoNf (oInfo r n).

(* The normalizer.  [next L0 = iota L1] and [next L1 = inf] are the only
   tlvl equations, so this is a one-step rewrite. *)
(* Matched on the ARGUMENT-LIST SHAPE first and only then on the head symbol
   (via [eqb], not a literal string pattern), exactly as [RVarr]/[RSub] do in
   the STLC development: it keeps the case analyses in the proofs below to a
   fixed, small number of [destruct]s. *)
Definition ntlvl (n : term) : term :=
  match n with
  | con nm [l] =>
      if eqb nm "next" then
        match l with
        | con nl [] =>
            if eqb nl "L0" then oIota oL1
            else if eqb nl "L1" then oInf
            else n
        | _ => n
        end
      else n
  | _ => n
  end.

Definition ninfo (i : term) : term :=
  match i with
  | con nm [n; r] => if eqb nm "info" then oInfo r (ntlvl n) else i
  | _ => i
  end.

Lemma ntlvl_iota l : ntlvl (oIota l) = oIota l.
Proof. reflexivity. Qed.

Lemma ntlvl_inf : ntlvl oInf = oInf.
Proof. reflexivity. Qed.

Lemma ntlvl_next0 : ntlvl (oNext oL0) = oIota oL1.
Proof. reflexivity. Qed.

Lemma ntlvl_next1 : ntlvl (oNext oL1) = oInf.
Proof. reflexivity. Qed.

Lemma ntlvl_nf n : TlvlNf n -> ntlvl n = n.
Proof. destruct 1; reflexivity. Qed.

Lemma ntlvl_TlvlNf_iota l : LvlNf l -> TlvlNf (ntlvl (oIota l)).
Proof. intro; rewrite ntlvl_iota; constructor; assumption. Qed.

Lemma ntlvl_TlvlNf_next l : LvlNf l -> TlvlNf (ntlvl (oNext l)).
Proof.
  destruct 1; [ rewrite ntlvl_next0 | rewrite ntlvl_next1 ];
    repeat constructor.
Qed.

Lemma ninfo_oInfo r n : ninfo (oInfo r n) = oInfo r (ntlvl n).
Proof. reflexivity. Qed.

Lemma ninfo_nf i : InfoNf i -> ninfo i = i.
Proof.
  destruct 1 as [r n Hr Hn].
  rewrite ninfo_oInfo, (ntlvl_nf Hn); reflexivity.
Qed.

Lemma ninfo_InfoNf r n : RelNf r -> TlvlNf n -> InfoNf (ninfo (oInfo r n)).
Proof.
  intros Hr Hn; rewrite ninfo_oInfo, (ntlvl_nf Hn); constructor; assumption.
Qed.
