Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.Ceq Pyrosome.Gluing.Dtt.ModelStruct.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4c: the [cterm_cong] and [cterm_by]
   obligations for the INDEX FRAGMENT of [ott_dtt].

   The index fragment is [ott_info]: the nine term rules

       rel  irr  L0  L1  L0<L1  iota  inf  next  info

   and the three equations that live over them

       next0 ([next L0 = iota L1])   next1 ([next L1 = inf])
       ltl_irr (proof irrelevance for [ltl])

   No environment, substitution, type or term appears anywhere in this
   fragment, so it is completely independent of Layers 1-3; it is proved
   here against src/Pyrosome/Gluing/Dtt/Ceq.v's contract alone (the
   dependency on ModelStruct.v is the shared [rule_pin] tactic and nothing
   mathematical).

   WHAT THE CONTRACT HAS TO SUPPLY, AND WHY IT IS ENOUGH.

   [relevance] and [lvl] are RIGID -- two closed nullary constructors each
   and no equations -- so [ceq_relevance]/[ceq_lvl] are plain syntactic
   equality plus [RelNf]/[LvlNf].  That is exactly the right strength for
   the two congruences that consume them: [cong_iota] and [cong_next] both
   need their argument's [LvlNf] to know which of the two [ntlvl] branches
   fires, and they need the argument's SYNTACTIC equality to conclude that
   the two [ntlvl]s agree.  An [eq_term]-only clause at [lvl] would not do:
   [ntlvl] is a syntactic function, and there is no reason a priori for two
   provably-equal levels to have equal [ntlvl (next _)].  (They do, since
   [lvl] is rigid -- but proving that is Layer 0.5's rigidity work, which
   the contract sidesteps by carrying [LvlNf] directly.)

   [ceq_tlvl]'s "equal [ntlvl] + [TlvlNf] of it" then turned out to be
   exactly enough, in both directions:

   - as a HYPOTHESIS ([cong_info]): the [ntlvl] equation is what makes the
     two [ninfo]s agree, and the [TlvlNf] is what feeds [infonf].  Nothing
     else about the tlvl argument is used.
   - as a CONCLUSION ([cong_iota]/[cong_next], [by_next0]/[by_next1]): the
     normalizer's one-step-rewrite definition (src/Pyrosome/Gluing/Dtt/Syntax.v) reduces
     each goal to [ntlvl_iota]/[ntlvl_next0]/[ntlvl_next1] plus a [LvlNf]
     case split -- packaged already as [ntlvl_TlvlNf_iota] and
     [ntlvl_TlvlNf_next].

   And [ceq_tyinfo]'s "equal [ninfo] + [InfoNf]" is enough for [cong_info],
   the only rule that concludes at [tyinfo]: [ninfo] is defined by pushing
   [ntlvl] under [info], so both conjuncts are [ninfo_oInfo] followed by the
   corresponding conjunct of the tlvl argument.

   [ltl] is proof-irrelevant, so [ceq_ltl] carries the [eq_term] and
   nothing else; [ltl_irr] is then literally the [eq_ltl_irr] instance,
   and its four well-formedness side conditions come from the [ltl]
   arguments' clauses ([eqt_wf_l]/[eqt_wf_r]) and from [LvlNf_wf] on the
   two rigid level arguments.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* A.  The nine congruences                                            *)
(* ================================================================== *)

(* ---- the five nullary formers ---------------------------------- *)

Lemma cong_rel : Ceq_term sRelevance oRel oRel.
Proof. apply ceq_relevance; constructor. Qed.

Lemma cong_irr : Ceq_term sRelevance oIrr oIrr.
Proof. apply ceq_relevance; constructor. Qed.

Lemma cong_L0 : Ceq_term sLvl oL0 oL0.
Proof. apply ceq_lvl; constructor. Qed.

Lemma cong_L1 : Ceq_term sLvl oL1 oL1.
Proof. apply ceq_lvl; constructor. Qed.

(* [ltl] is proof-irrelevant, so its clause is the bare equation. *)
Lemma cong_lt01 : Ceq_term (sLtl oL0 oL1) oLt01 oLt01.
Proof. apply ceq_ltl, Lt01_cong. Qed.

Lemma cong_inf : Ceq_term sTlvl oInf oInf.
Proof.
  apply ceq_tlvl;
    [ apply Inf_cong
    | reflexivity
    | rewrite ntlvl_inf; constructor ].
Qed.

(* ---- the two unary tlvl formers -------------------------------- *)

(* [Ceq_lvl_e] hands back SYNTACTIC equality of the argument, so the
   [ntlvl] equation is [reflexivity] after the substitution; the [LvlNf]
   it also hands back is what picks the [ntlvl] branch. *)
Lemma cong_iota l1 l2
  : Ceq_term sLvl l1 l2 -> Ceq_term sTlvl (oIota l1) (oIota l2).
Proof.
  intro H; apply Ceq_lvl_e in H as [-> Hnf].
  apply ceq_tlvl;
    [ apply Iota_cong; apply eq_term_refl; apply LvlNf_wf; exact Hnf
    | reflexivity
    | apply ntlvl_TlvlNf_iota; exact Hnf ].
Qed.

(* THE INTERESTING ONE.  [ntlvl (next l)] is [iota L1] when [l] is [L0] and
   [inf] when [l] is [L1], so both the equation and the [TlvlNf] need the
   argument's [LvlNf] -- and the equation additionally needs the two
   arguments to be the SAME level, which is precisely the syntactic
   conjunct of [ceq_lvl].  Both are packaged in [ntlvl_TlvlNf_next]. *)
Lemma cong_next l1 l2
  : Ceq_term sLvl l1 l2 -> Ceq_term sTlvl (oNext l1) (oNext l2).
Proof.
  intro H; apply Ceq_lvl_e in H as [-> Hnf].
  apply ceq_tlvl;
    [ apply Next_cong; apply eq_term_refl; apply LvlNf_wf; exact Hnf
    | reflexivity
    | apply ntlvl_TlvlNf_next; exact Hnf ].
Qed.

(* ---- the bundle ------------------------------------------------- *)

(* [ninfo] pushes [ntlvl] under [info], so each conjunct of [ceq_tyinfo]
   is [ninfo_oInfo] followed by the matching conjunct of [ceq_tlvl] (and,
   for [InfoNf], the [RelNf] of the rigid relevance argument). *)
Lemma cong_info r1 r2 n1 n2
  : Ceq_term sRelevance r1 r2 -> Ceq_term sTlvl n1 n2 ->
    Ceq_term sInfo (oInfo r1 n1) (oInfo r2 n2).
Proof.
  intros Hr Hn.
  apply Ceq_relevance_e in Hr as [-> Hrnf].
  apply Ceq_tlvl_e in Hn as (Hq & Heq & Hnf).
  apply ceq_tyinfo.
  - apply Info_cong;
      [ apply eq_term_refl; apply RelNf_wf; exact Hrnf | exact Hq ].
  - rewrite !ninfo_oInfo, Heq; reflexivity.
  - rewrite ninfo_oInfo; constructor; assumption.
Qed.

(* ================================================================== *)
(* B.  The three equations                                             *)
(* ================================================================== *)

(* Both tlvl equations have EMPTY rule contexts, so the [cterm_by]
   obligation delivers nothing and demands the closed instance. *)

Lemma by_next0 : Ceq_term sTlvl (oNext oL0) (oIota oL1).
Proof.
  apply ceq_tlvl;
    [ apply eq_next0
    | rewrite ntlvl_next0, ntlvl_iota; reflexivity
    | rewrite ntlvl_next0; repeat constructor ].
Qed.

Lemma by_next1 : Ceq_term sTlvl (oNext oL1) oInf.
Proof.
  apply ceq_tlvl;
    [ apply eq_next1
    | rewrite ntlvl_next1, ntlvl_inf; reflexivity
    | rewrite ntlvl_next1; constructor ].
Qed.

(* [ltl_irr] equates ANY two inhabitants of [ltl a b], so the [ceq_ltl]
   clause -- which carries only the equation -- is discharged by the
   equation itself.  The four well-formedness side conditions are the
   only content. *)
Lemma by_ltl_irr a b p1 p2
  : LvlNf a -> LvlNf b -> wft p1 (sLtl a b) -> wft p2 (sLtl a b) ->
    Ceq_term (sLtl a b) p1 p2.
Proof.
  intros Ha Hb H1 H2.
  apply ceq_ltl, eq_ltl_irr; auto using LvlNf_wf.
Qed.

(* ================================================================== *)
(* C.  The dispatchers                                                 *)
(* ================================================================== *)

(* Both are stated in exactly the shape of the corresponding
   [CutTModel_ok] field, with the rule name restricted to the fragment.
   The name is pinned FIRST and the rule looked up afterwards, so each case
   costs ONE rule rather than a 32-way (resp. 32-way) disjunction of all of
   them -- [rule_pin], src/Pyrosome/Gluing/Dtt/ModelStruct.v, which also
   reads the argument list off [ceq_args] and turns the class projections
   back into [Ceq_term]. *)

Lemma idx_cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    (name = "rel" \/ name = "irr" \/ name = "L0" \/ name = "L1"
     \/ name = "L0<L1" \/ name = "iota" \/ name = "inf" \/ name = "next"
     \/ name = "info") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; rule_pin.
  - (* rel *) apply cong_rel.
  - (* irr *) apply cong_irr.
  - (* L0 *) apply cong_L0.
  - (* L1 *) apply cong_L1.
  - (* L0<L1 *) apply cong_lt01.
  - (* iota *) apply cong_iota; assumption.
  - (* inf *) apply cong_inf.
  - (* next *) apply cong_next; assumption.
  - (* info *) apply cong_info; assumption.
Qed.

Lemma idx_by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    (name = "next0" \/ name = "next1" \/ name = "ltl_irr") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hname Hargs.
  destruct Hname as [-> | [-> | ->]]; rule_pin.
  - (* next0 *) apply by_next0.
  - (* next1 *) apply by_next1.
  - (* ltl_irr: the two level arguments are rigid, the two [ltl] arguments
       supply the well-formedness of the two sides. *)
    repeat match goal with
           | [ H : Ceq_term _ _ _ |- _ ] =>
               first [ apply Ceq_lvl_e in H as [? ?]
                     | apply Ceq_ltl_e in H ]
           end;
      subst.
    apply by_ltl_irr; eauto using eqt_wf_l, eqt_wf_r.
Qed.
