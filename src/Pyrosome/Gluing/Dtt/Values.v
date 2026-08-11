Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
(* [Require EXPORT]: [oStar] and the weakening relation live in WkRel.v
   (see the note there on why the dependency runs this way), and everything
   downstream of Values.v wants both. *)
Require Import Pyrosome.Gluing.Dtt.Syntax.
Require Export Pyrosome.Gluing.Dtt.WkRel.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1 (REVISED): *-COLLAPSED VALUES.

   This file replaces the judgements of src/Pyrosome/Gluing/Dtt/NormalForms.v
   ([EnvOk]/[TyOk]/[NfCode]/[NeCode]/[VarT]/[NeET]/[NfET]) with the value
   predicates of design.md sections 13 and 14.  Two things change, and both are
   forced by the Id fragment:

   (1) THE IRRELEVANT FRAGMENT HAS ONE VALUE, [*].  Reification is
       type-directed and every type class is justified by one equation of
       [ott_dtt]: [Pi_rel] by "Pi_rel eta", and EVERY irrelevant type by
       "proof irrelevance", which reifies to the single token [oStar].
       Proof irrelevance is the eta rule of the irrelevant fragment.
       REDUCTION never dispatches on relevance; only reification does,
       exactly as it already dispatches on [Nat] vs [Pi_rel].

       This is what makes [Val_inj] (provably-equal *-collapsed values are
       syntactically equal) TRUE where [NfET_inj] was FALSE: design.md
       section 14a exhibits two distinct [Emptyrec]s over provably-equal
       irrelevant arguments, both [NfET] at the same relevant type.  Here
       both are the SAME term, [Emptyrec G rA lA A *].

   (2) NAMED REPRESENTATIVES BECOME COMPUTED ONES.  Where NormalForms.v wrote

         ... -> TyOk (oExt G i A) i A' -> eqt ... A' -> VarT (oExt G i A) i A' ...

       i.e. "A' is SOME normal type provably equal to A[wkn]", this file
       writes the COMPUTED representative [wkTy G i A A].  Likewise
       [neet_app_rel]'s named [C] becomes [oEl G oRel lG (instC ...)].
       That is design.md section 4b's declined alternative, now mandatory:
       with an [eq_term]-named representative the judgements are not
       functional, and Layer 0.5 -- which used to supply uniqueness of the
       naming -- is refutable once [Id] is in the language (section 12e).

       [wkTy] and [instC] are SECTION PARAMETERS here.  Their definitions are
       the subject of the weakening/instantiation layer; see the T3 note at
       the end of this file and WIP-scratch WkVal for the state of play.
       Nothing in this file depends on how they are defined -- only the
       clauses that name a representative mention them, and they mention them
       only in an index position.

   THE GRAMMAR (design.md section 14b):

     Vcode ::= var | Nat | Empty | Pi_rel rF lF lG Vcode Vcode
             | Pi_irr rF lF Vcode Vcode
             | Id l Vcode Vcode Vel Vel                       (STUCK only)
     Vty   ::= U D r l | El D r l Vcode
     Vel   ::= (at El _ irr _)                 *
             | (at El _ rel L0 Nat)            zero | suc Vel | Vne
             | (at El _ rel lG Pi_rel)         lam_rel ... Vel
             | (at El _ rel l  Vcode-neutral)  Vne
     Vne   ::= var | app_rel rF lF lG Vcode Vcode Vne Vel
             | Emptyrec rA lA Vcode *

   Relative to NormalForms.v: [nfet_ne_empty], [nfet_lam_irr],
   [neet_app_irr] and [neet_idcong] are GONE (all subsumed by [*] -- an
   [Idcong] is a proof, and the value of a proof is [*]), and with them
   [oIdcongTy]; one clause [val_irr] replaces them all.  The five [NeCode]
   clauses are kept verbatim, with [NfET] premises becoming [Val] premises:
   they are the complete stuck-analysis for [Id] (design.md section 12b) and
   they are correct.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

Section WithReps.

  (* THE [wkTy] PARAMETER IS GONE.  It named the value form of a weakened
     type, and a variable's type is always a weakened one; it is now the
     relation [WkRel.WkTy], whose determinism ([WkRel.Wk_det]) is what makes
     the naming functional.  That is decision (a) of WkVal.v's trailer,
     discharged: relation plus determinism, not a Gallina [Fixpoint], which
     the guard checker refuses on this syntax.

     [instC] survives, and is the last parameter.  It is the value form of
     [B[<id,a>]], for [B] a value code at level [lG] over [oExtC G rF lF F]
     and [a] a value at [El G rF lF F]; it is used ONLY as the type index of
     an [app_rel] neutral.  It retires the same way [wkTy] just did, into
     the instantiation relation, once that block exists. *)
  Context (instC : term -> term -> term -> term -> term -> term -> term -> term).

(* ------------------------------------------------------------------ *)
(* The mutual block                                                     *)
(* ------------------------------------------------------------------ *)

Inductive ValEnv : term -> Prop :=
| valenv_emp : ValEnv oEmp
| valenv_ext : forall G i A, ValEnv G -> ValTy G i A -> ValEnv (oExt G i A)

(* [ValTy G i A] : [A] is a value type of sort [ty G i].  The info index is
   determined by the type: [iCode l] for a universe, [iEl r l] for an [El].
   Infos are NOT normalized here (the language is not uniform about which
   side of "next0" it lands on -- [Nat] elaborates at [info rel (next L0)]
   but [Empty] at [info rel (iota L1)]), so each canonical form is pinned to
   the info its own former uses. *)
with ValTy : term -> term -> term -> Prop :=
| valty_U : forall G r l,
    ValEnv G -> RelNf r -> LvlNf l -> ValTy G (iCode l) (oU G r l)
| valty_El : forall G r l c,
    ValCode G r l c -> ValTy G (iEl r l) (oEl G r l c)

(* [ValCode G r l c] : [c] is a value code, i.e. a value at [U G r l].
   Codes are NOT collapsed even at [r = irr]: [U G irr l] is the type of
   irrelevant CODES, and it is not itself proof-irrelevant -- proof
   irrelevance is an [El]-sorted rule.  This is what keeps [ValCode_inj]
   meaningful, and it is why the [Id] fragment (whose codes contain relevant
   ELEMENTS) forces the element layer to be injective too. *)
with ValCode : term -> term -> term -> term -> Prop :=
| valcode_nat : forall G,
    ValEnv G -> ValCode G oRel oL0 (oNat G)
| valcode_empty : forall G,
    ValEnv G -> ValCode G oIrr oL0 (oEmpty G)
| valcode_pi_rel : forall G rF lF lG F B,
    RelNf rF -> LvlNf lF -> LvlNf lG ->
    ValCode G rF lF F ->
    ValCode (oExtC G rF lF F) oRel lG B ->
    ValCode G oRel lG (oPiRel G rF lF lG F B)
| valcode_pi_irr : forall G rF lF F B,
    RelNf rF -> LvlNf lF ->
    ValCode G rF lF F ->
    ValCode (oExtC G rF lF F) oIrr oL0 B ->
    ValCode G oIrr oL0 (oPiIrr G rF lF F B)
| valcode_ne : forall G r l c,
    NeCode G r l c -> ValCode G r l c

(* [NeCode G r l c] : a code no computation rule of [ott_dtt] can reduce.
   Before the Id fragment this was exactly "a variable"; [Id] adds a second
   way for a code to be stuck.

   These five clauses are the complete stuck analysis of design.md section
   12b, KEPT VERBATIM from NormalForms.v (only the element premises change,
   from [NfET] to [Val]).  An [Id] reduces as soon as both of its codes are
   canonical: distinct heads clash to [Empty], two [Pi_rel]s go to funext or
   (on mismatched domain indices) to [Empty], and two [Nat]s dispatch on the
   endpoints.  So it is stuck exactly when a CODE is neutral, or when both
   codes are [Nat] and an ENDPOINT is neutral.

   Note the indices: [Id] lands at [irr, L0] while its two code arguments are
   RELEVANT, and the only neutral code at a relevant index is a variable --
   so [necode_id_l]/[necode_id_r] do not recurse into further [Id]s. *)
with NeCode : term -> term -> term -> term -> Prop :=
| necode_var : forall G r l c,
    ValVar G (iCode l) (oU G r l) c -> NeCode G r l c
| necode_id_l : forall G l A B t u,
    NeCode G oRel l A -> ValCode G oRel l B ->
    Val G (iEl oRel l) (oEl G oRel l A) t ->
    Val G (iEl oRel l) (oEl G oRel l B) u ->
    NeCode G oIrr oL0 (oIdEq G l A B t u)
| necode_id_r : forall G l A B t u,
    ValCode G oRel l A -> NeCode G oRel l B ->
    Val G (iEl oRel l) (oEl G oRel l A) t ->
    Val G (iEl oRel l) (oEl G oRel l B) u ->
    NeCode G oIrr oL0 (oIdEq G l A B t u)
| necode_id_nat_l : forall G t u,
    ValNe G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) t ->
    Val G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) u ->
    NeCode G oIrr oL0 (oIdEq G oL0 (oNat G) (oNat G) t u)
| necode_id_nat_r : forall G t u,
    Val G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) t ->
    ValNe G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) u ->
    NeCode G oIrr oL0 (oIdEq G oL0 (oNat G) (oNat G) t u)

(* [ValVar G i A x] : [x] is an object-level variable of the value type [A].
   The meta-context is empty, so object-level variables are [hd] and its
   [wkn]-shifts.

   THE FUNCTIONAL POINT.  NormalForms.v's [vart_hd]/[vart_wkn] took the
   representative [A'] as an EXTRA ARGUMENT pinned by an [eq_term] premise
   -- "SOME normal type provably equal to [A[wkn]]".  Here it is pinned by
   [WkRel.WkTy], which is DETERMINISTIC ([WkRel.Wk_det]), so [A'] is THE
   weakening and not merely one of them.  The distinction is the whole of
   design.md section 13's turn to functional content.

   Note also that the type ANNOTATION carried by the term itself is exactly
   the premise's index [A], so the term is determined by [x] and the binding
   alone -- no choice is made anywhere.

   These two clauses are [WkRel.VarTy]'s two clauses plus the value-hood
   side conditions; [ValVar_VarTy] below is the erasure. *)
with ValVar : term -> term -> term -> term -> Prop :=
| valvar_hd : forall G i A A',
    ValEnv G -> ValTy G i A ->
    WkTy (oExt G i A) G (oWkn G i A) i A A' ->
    ValVar (oExt G i A) i A' (oHd G i A)
| valvar_wkn : forall G i A x j B A',
    ValVar G i A x -> ValTy G j B ->
    WkTy (oExt G j B) G (oWkn G j B) i A A' ->
    ValVar (oExt G j B) i A'
           (oExpSubst (oExt G j B) G (oWkn G j B) i A x)

(* [ValNe G i A e] : [e] is neutral at the value type [A].  No conversion
   clause: the representative of an eliminator's result type is COMPUTED at
   the construction site.

   The two clauses that used to exist for the irrelevant fragment
   ([neet_app_irr], [neet_idcong]) are gone: both conclude at an irrelevant
   [El], where the only value is [*].

   The erasable positions of design.md section 14c (E2) are visible here and
   nowhere else.  (E2) says that the ONLY irrelevant-typed subterms sitting in
   relevant positions are [app_rel]'s [a] when [rF = irr], and [Emptyrec]'s
   [e]; this was checked mechanically over the compiled language, Id fragment
   included.  The first is handled by [valne_app_rel]'s premise
   [Val G (iEl rF lF) ... a], which at [rF = oIrr] forces [a = oStar] by
   [val_irr] (see [Val_irr_star] below).  The second is handled by writing
   [oStar] LITERALLY in [valne_emptyrec]. *)
with ValNe : term -> term -> term -> term -> Prop :=
| valne_var : forall G i A x,
    ValVar G i A x -> ValNe G i A x
| valne_app_rel : forall G rF lF lG F B f a,
    ValCode G rF lF F ->
    ValCode (oExtC G rF lF F) oRel lG B ->
    ValNe G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) f ->
    Val G (iEl rF lF) (oEl G rF lF F) a ->
    ValNe G (iEl oRel lG) (oEl G oRel lG (instC G rF lF F a lG B))
          (oAppRel G rF lF lG F B f a)
| valne_emptyrec : forall G rA lA A,
    ValCode G rA lA A ->
    ValNe G (iEl rA lA) (oEl G rA lA A) (oEmptyrec G rA lA A oStar)

(* [Val G i A v] : [v] is the value of type [A].  Dispatched by [A]'s head,
   exhaustively over [ValTy]:

     A = U G r l                     -> a value code
     A = El G irr l c,  ANY c        -> *                     <-- proof irr
     A = El G rel L0 (Nat G)         -> zero | suc | neutral
     A = El G rel lG (Pi_rel ...)    -> lam_rel ONLY          <-- eta
     A = El G rel l  c,  c neutral   -> neutral

   [Empty] and [Pi_irr] no longer appear: they are irrelevant codes, so they
   are covered -- with [Id] and every irrelevant neutral -- by the single
   clause [val_irr].  That is (E1) (design.md section 14c), proved as
   [ValCode_irr_shape] below. *)
with Val : term -> term -> term -> term -> Prop :=
| val_code : forall G r l c,
    ValCode G r l c -> Val G (iCode l) (oU G r l) c
| val_irr : forall G l c,
    ValCode G oIrr l c -> Val G (iEl oIrr l) (oEl G oIrr l c) oStar
| val_zero : forall G,
    ValEnv G -> Val G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) (oZero G)
| val_suc : forall G n,
    Val G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) n ->
    Val G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) (oSuc G n)
| val_ne_nat : forall G e,
    ValNe G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e ->
    Val G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e
| val_ne : forall G l c e,
    NeCode G oRel l c ->
    ValNe G (iEl oRel l) (oEl G oRel l c) e ->
    Val G (iEl oRel l) (oEl G oRel l c) e
| val_lam_rel : forall G rF lF lG F B t,
    RelNf rF -> LvlNf lF -> LvlNf lG ->
    ValCode G rF lF F ->
    ValCode (oExtC G rF lF F) oRel lG B ->
    Val (oExtC G rF lF F) (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B) t ->
    Val G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B))
        (oLamRel G rF lF lG F B t).

Scheme ValEnv_min := Minimality for ValEnv Sort Prop
  with ValTy_min := Minimality for ValTy Sort Prop
  with ValCode_min := Minimality for ValCode Sort Prop
  with NeCode_min := Minimality for NeCode Sort Prop
  with ValVar_min := Minimality for ValVar Sort Prop
  with ValNe_min := Minimality for ValNe Sort Prop
  with Val_min := Minimality for Val Sort Prop.

Combined Scheme Val_mutind from
  ValEnv_min, ValTy_min, ValCode_min, NeCode_min, ValVar_min, ValNe_min,
  Val_min.

(* ------------------------------------------------------------------ *)
(* (E1) and the *-collapse                                              *)
(* ------------------------------------------------------------------ *)

(* (E1), design.md section 14c: [El G irr l c] covers exactly [Empty],
   [Pi_irr], [Id] and irrelevant neutral codes -- [Nat] and [Pi_rel] being
   the only relevant canonical codes.  [Id] and the irrelevant variables are
   the two [NeCode] cases, so the disjunction has three arms. *)
Lemma ValCode_irr_shape G l c
  : ValCode G oIrr l c ->
    (l = oL0 /\ c = oEmpty G)
    \/ (exists rF lF F B, l = oL0 /\ c = oPiIrr G rF lF F B)
    \/ NeCode G oIrr l c.
Proof.
  (* [inversion] discharges [valcode_nat] and [valcode_pi_rel] itself:
     their relevance index is [oRel = con "rel" []], and [oIrr] is a
     different [con], so the two are separated by [discriminate]. *)
  inversion 1; subst; eauto 10.
Qed.

(* The *-collapse itself: at an irrelevant [El] there is exactly one value,
   and it is [*].  This is the whole content of design.md section 14b, and it
   is what makes [Val_inj] provable where [NfET_inj] was false. *)
Lemma Val_irr_star G l c v
  : Val G (iEl oIrr l) (oEl G oIrr l c) v -> v = oStar.
Proof.
  inversion 1; subst; try reflexivity; exfalso; discriminate.
Qed.

(* The converse: [*] IS a value at every irrelevant [El] of a value code.
   Together with [Val_irr_star] this says the irrelevant fragment's value set
   is the singleton [{*}]. *)
Lemma Val_irr_intro G l c
  : ValCode G oIrr l c -> Val G (iEl oIrr l) (oEl G oIrr l c) oStar.
Proof. apply val_irr. Qed.

(* (E2) in the form the value layer uses it: an [app_rel] at an IRRELEVANT
   domain has [*] as its argument.  (E2) proper -- "the only irrelevant-typed
   subterms in relevant positions are [app_rel]'s [a] and [Emptyrec]'s [e]" --
   is a statement about the compiled language, not about these judgements; it
   was checked mechanically (design.md section 14c) and is what licenses the
   grammar above.  What is left to check here is that the grammar really does
   collapse both positions, and it does: [Emptyrec]'s argument is the literal
   [oStar] of [valne_emptyrec], and [app_rel]'s is this lemma. *)
Lemma ValNe_app_rel_irr_arg G lF lG F B f a
  : ValNe G (iEl oRel lG) (oEl G oRel lG (instC G oIrr lF F a lG B))
          (oAppRel G oIrr lF lG F B f a) ->
    ValCode G oIrr lF F ->
    a = oStar.
Proof.
  intros H HF; inversion H; subst;
    (* [valne_emptyrec] is discharged by [inversion] itself; what is left is
       [valne_var] (a variable is not an [app_rel]) and the real case. *)
    [ exfalso; match goal with Hv : ValVar _ _ _ _ |- _ => inversion Hv end
    | eapply Val_irr_star; eassumption ].
Qed.

(* ------------------------------------------------------------------ *)
(* Syntactic shape lemmas                                               *)
(*                                                                      *)
(* RESCUED from src/Pyrosome/Gluing/Dtt/Inj.v (which is deleted with the  *)
(* rest of Layer 0.5, design.md section 12e).  [VarT_shape] was the only  *)
(* lemma in that file with no dependence on the rigid model; the rest is  *)
(* stated over [ICode]/[ITy]/[IEnv] and goes with them.                   *)
(* ------------------------------------------------------------------ *)

(* The subject of a [ValVar] is an [oHd] or a [wkn]-substituted variable.
   (Inj.v:216, [VarT_shape], transposed to [ValVar].) *)
Lemma ValVar_shape G i A x : ValVar G i A x ->
  (exists G0 i0 A0, x = oHd G0 i0 A0)
  \/ (exists G0 j B i0 A0 y,
         x = oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y).
Proof. destruct 1; [ left | right ]; eauto 10. Qed.

(* A value variable is a variable, forgetting value-hood.  This is the
   bridge that lets the weakening layer's [VarTy]-indexed facts be used on
   [ValVar]-indexed ones. *)
Lemma ValVar_VarTy G i A x : ValVar G i A x -> VarTy G i A x.
Proof.
  induction 1;
    [ eapply varty_hd; eassumption | eapply varty_wkn; eassumption ].
Qed.

(* Hence a value variable's type is determined by its context and itself --
   [WkRel.Wk_det]'s fourth conjunct, transported. *)
Lemma ValVar_type_unique G i1 A1 i2 A2 x
  : ValVar G i1 A1 x -> ValVar G i2 A2 x -> i1 = i2 /\ A1 = A2.
Proof.
  intros H1 H2;
    exact (VarTy_det (ValVar_VarTy H1) (ValVar_VarTy H2)).
Qed.

(* The same, one level up: a [ValNe] is a variable, an [app_rel] or an
   [Emptyrec].  (The [NeET_shape]-like helper the old development never
   needed, because [NeET] had four more clauses.) *)
Lemma ValNe_shape G i A e : ValNe G i A e ->
  (exists G0 i0 A0, e = oHd G0 i0 A0)
  \/ (exists G0 j B i0 A0 y,
         e = oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y)
  \/ (exists G0 rF lF lG F B f a, e = oAppRel G0 rF lF lG F B f a)
  \/ (exists G0 rA lA A0, e = oEmptyrec G0 rA lA A0 oStar).
Proof.
  destruct 1.
  - destruct (ValVar_shape H) as [ H0 | H0 ]; [ left | right; left ]; exact H0.
  - right; right; left; eauto 10.
  - right; right; right; eauto 10.
Qed.

(* A neutral code is a variable or a stuck [Id]. *)
Lemma NeCode_shape G r l c : NeCode G r l c ->
  ValVar G (iCode l) (oU G r l) c
  \/ (exists l0 A B t u, c = oIdEq G l0 A B t u).
Proof. destruct 1; [ left | right .. ]; eauto 10. Qed.

End WithReps.

(* =====================================================================
   WHAT IS LEFT PARAMETRIC, AND WHY.

   [instC] is the last parameter.  It is needed only as the type index of
   [valne_app_rel]: an application's result type is [B[<id,a>]], and the
   value layer must name THE instantiation.

   IT DOES NOT RETIRE THE WAY [wkTy] JUST DID, and the difference is not
   one of degree.  WEAKENING NEVER CREATES A REDEX -- it only shifts -- so
   WkRel.v is purely structural, which is why it was cheap.
   INSTANTIATION SUBSTITUTES A VALUE FOR A VARIABLE, and a value in a
   neutral's head position turns that neutral into a redex.  So the
   instantiation relation must EVALUATE, and it is therefore not a sibling
   of the weakening relation but a fragment of the normalizer itself.

   Where exactly, in this grammar.  Substituting the element [a] into a
   value CODE [B] over [oExtC G rF lF F] is structural at [Nat], [Empty],
   [Pi_rel], [Pi_irr] and at code VARIABLES -- a code variable's type is a
   universe, and the de Bruijn-0 variable of [oExtC G rF lF F] has type
   [El _ rF lF F[wkn]], which is an [El], so a code variable is NEVER the
   one being substituted and always merely strips.  Likewise an [Id] stuck
   on a neutral CODE stays stuck, for the same reason.  The one place it
   breaks is [necode_id_nat_l]/[_r]: there the stuck endpoint is an
   ELEMENT at [El _ rel L0 (Nat _)], it CAN be the de Bruijn-0 variable
   (when [F] is [Nat]), and substituting [zero] or [suc n] for it fires
   "Id-Nat-00"/"-0S"/"-SS".  Symmetrically, an endpoint [app_rel … f a]
   whose head [f] is the 0-variable becomes a beta-redex when a [lam_rel]
   is substituted.

   This is design.md section 14d confirmed from the substitution side, and
   it is exactly what the Id fragment costs: NfWk.v:3139's [NfCode_csubst]
   -- "the code grammar is a free algebra closed under substitution
   STRUCTURALLY", NormalForms.v:66 -- was true only because pre-Id codes
   contain no elements.

   So the instantiation block needs the semantic operations as well as the
   substitution ones: an application judgement (beta) and an Id judgement
   (the whole section-12b computation table).  Estimated at five or six
   mutual judgements, i.e. the factorization survives; the growth is in
   CLAUSES, not in judgements.
   ===================================================================== *)
