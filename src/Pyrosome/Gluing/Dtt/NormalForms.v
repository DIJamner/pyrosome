Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1: eta-long normal forms.

   The analogue of the "LAYER 1" half of Gluing/Stlc/NormalForms.v.  Three
   things differ from the simply-typed case, and each is forced.

   (1) ONE MUTUAL BLOCK, SIX JUDGEMENTS.  In STLC [TyOk]/[EnvOk] are two
       independent inductives over closed syntax, because a type there is
       built from [unit] and [->] alone.  Here a type is [El G r l c] for a
       normal CODE c, and codes contain neutrals, which contain normal
       terms.  So environments, types, codes, variables, neutrals and
       normals are one block.

   (2) NORMAL FORMS ARE ETA-LONG.  [ott_dtt] contains "Pi_rel eta", so a
       neutral at a [Pi_rel] type is NOT normal -- its normal form is its
       eta-expansion.  Concretely: [NfET] has no neutral clause at
       [El _ rel _ (Pi_rel ...)]; the only normal there is a [lam_rel].
       [Pi_irr] keeps a neutral clause, because "Pi_irr eta" is not a rule
       of [ott_pi] (upstream it is subsumed by proof irrelevance, and
       ProofIrr is out of scope here).

       Two STLC clauses disappear as a consequence.  [nee_lamapp] (a normal
       function value applied to a neutral argument is stuck) existed only
       because SimpleVSTLC is call-by-value and its beta fires when both
       sides are [ret]s; "Pi_rel beta" fires for an arbitrary argument, and
       there is no value/expression split in [ott_dtt] at all.

   (3) NEUTRALS AND VARIABLES CARRY A *NAMED* NORMAL TYPE.  [app_rel]'s
       result type is [(El B)[<id,a>]] and a variable's type is [A[wkn]];
       neither is a normal type.  Rather than index the judgements by
       arbitrary types (which would force a conversion clause, and with it
       an inversion problem), each such clause takes the normal
       representative [C]/[A'] as an extra argument together with the
       [eq_term] that identifies it.  Existence of the representative is
       Layer 1's business ([TyOk_wk], [NfCode_wk], [NfCode_subst]);
       UNIQUENESS is Layer 0.5's ([TyOk_inj]).

       That [NfCode_subst] is provable at all -- normal codes are closed
       under substitution -- is the structural fact the whole development
       rests on: no eliminator of [ott_dtt] has a universe as its result
       type ([app_rel]/[app_irr]/[Emptyrec] all land in an [El]), so the
       only NEUTRAL codes are variables and the code grammar

           c ::= x | Nat G | Empty G | Pi_rel G rF lF lG c c | Pi_irr G rF lF c c

       is a free algebra closed under substitution structurally.  See
       WIP/dtt_norm_design.md section 2.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

Inductive EnvOk : term -> Prop :=
| envok_emp : EnvOk oEmp
| envok_ext : forall G i A, EnvOk G -> TyOk G i A -> EnvOk (oExt G i A)

(* [TyOk G i A] : [A] is a normal type of sort [ty G i].  The info index is
   determined by the type: [iCode l] for a universe, [iEl r l] for an [El].
   Infos are NOT normalized here (the language itself is not uniform about
   which side of "next0" it lands on -- [Nat] is elaborated at
   [info rel (next L0)] but [Empty] at [info rel (iota L1)]), so each
   canonical form is pinned to the info its own former uses and the
   mismatches are paid for by a [wf_term_conv] in the typing lemmas. *)
with TyOk : term -> term -> term -> Prop :=
| tyok_U : forall G r l,
    EnvOk G -> RelNf r -> LvlNf l -> TyOk G (iCode l) (oU G r l)
| tyok_El : forall G r l c,
    NfCode G r l c -> TyOk G (iEl r l) (oEl G r l c)

(* [NfCode G r l c] : [c] is a normal code, i.e. a normal element of
   [U G r l].  The neutral clause is a VARIABLE and nothing else (see the
   header). *)
with NfCode : term -> term -> term -> term -> Prop :=
| nfcode_nat : forall G,
    EnvOk G -> NfCode G oRel oL0 (oNat G)
| nfcode_empty : forall G,
    EnvOk G -> NfCode G oIrr oL0 (oEmpty G)
| nfcode_pi_rel : forall G rF lF lG F B,
    RelNf rF -> LvlNf lF -> LvlNf lG ->
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oRel lG B ->
    NfCode G oRel lG (oPiRel G rF lF lG F B)
| nfcode_pi_irr : forall G rF lF F B,
    RelNf rF -> LvlNf lF ->
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oIrr oL0 B ->
    NfCode G oIrr oL0 (oPiIrr G rF lF F B)
| nfcode_var : forall G r l c,
    VarT G (iCode l) (oU G r l) c -> NfCode G r l c

(* [VarT G i A x] : [x] is an object-level variable of the normal type [A].
   The meta-context is empty, so object-level variables are [hd] and its
   [wkn]-shifts, exactly as in the STLC development; [cterm_var] is
   therefore vacuous.  [A'] is the named normal form of [A[wkn]]. *)
with VarT : term -> term -> term -> term -> Prop :=
| vart_hd : forall G i A A',
    EnvOk G -> TyOk G i A ->
    TyOk (oExt G i A) i A' ->
    eqt (sTy (oExt G i A) i)
        (oTySubst (oExt G i A) G (oWkn G i A) i A) A' ->
    VarT (oExt G i A) i A' (oHd G i A)
| vart_wkn : forall G i A x j B A',
    VarT G i A x -> TyOk G j B ->
    TyOk (oExt G j B) i A' ->
    eqt (sTy (oExt G j B) i)
        (oTySubst (oExt G j B) G (oWkn G j B) i A) A' ->
    VarT (oExt G j B) i A'
         (oExpSubst (oExt G j B) G (oWkn G j B) i A x)

(* [NeET G i A e] : [e] is neutral at the normal type [A].  Note there is no
   conversion clause: the normal representative of an eliminator's result
   type is supplied at the construction site. *)
with NeET : term -> term -> term -> term -> Prop :=
| neet_var : forall G i A x,
    VarT G i A x -> NeET G i A x
| neet_app_rel : forall G rF lF lG F B f a C,
    NeET G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) f ->
    NfET G (iEl rF lF) (oEl G rF lF F) a ->
    TyOk G (iEl oRel lG) C ->
    eqt (sTy G (iEl oRel lG))
        (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a) (iEl oRel lG)
                  (oEl (oExtC G rF lF F) oRel lG B))
        C ->
    NeET G (iEl oRel lG) C (oAppRel G rF lF lG F B f a)
| neet_app_irr : forall G rF lF F B f a C,
    NeET G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) f ->
    NfET G (iEl rF lF) (oEl G rF lF F) a ->
    TyOk G (iEl oIrr oL0) C ->
    eqt (sTy G (iEl oIrr oL0))
        (oTySubst G (oExtC G rF lF F) (oInst G rF lF F a) (iEl oIrr oL0)
                  (oEl (oExtC G rF lF F) oIrr oL0 B))
        C ->
    NeET G (iEl oIrr oL0) C (oAppIrr G rF lF F B f a)
(* [Emptyrec]'s argument is at [El _ irr L0 (Empty _)], where there is no
   introduction form at all, so every normal there is neutral. *)
| neet_emptyrec : forall G rA lA A e,
    NfCode G rA lA A ->
    NeET G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e ->
    NeET G (iEl rA lA) (oEl G rA lA A) (oEmptyrec G rA lA A e)

(* [NfET G i A e] : [e] is an ETA-LONG normal term of the normal type [A].
   The clauses are dispatched by [A]'s head, and the dispatch is exhaustive
   over [TyOk]:

     A = U G r l                    -> a normal code
     A = El G rel L0 (Nat G)        -> zero | suc | neutral
     A = El G irr L0 (Empty G)      -> neutral
     A = El G r l x,  x a variable  -> neutral
     A = El G rel lG (Pi_rel ...)   -> lam_rel ONLY            <-- eta
     A = El G irr L0 (Pi_irr ...)   -> lam_irr | neutral       <-- no eta *)
with NfET : term -> term -> term -> term -> Prop :=
| nfet_code : forall G r l c,
    NfCode G r l c -> NfET G (iCode l) (oU G r l) c
| nfet_zero : forall G,
    EnvOk G -> NfET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) (oZero G)
| nfet_suc : forall G n,
    NfET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) n ->
    NfET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) (oSuc G n)
| nfet_ne_nat : forall G e,
    NeET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e ->
    NfET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e
| nfet_ne_empty : forall G e,
    NeET G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e ->
    NfET G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e
| nfet_ne_var : forall G r l c e,
    VarT G (iCode l) (oU G r l) c ->
    NeET G (iEl r l) (oEl G r l c) e ->
    NfET G (iEl r l) (oEl G r l c) e
| nfet_lam_rel : forall G rF lF lG F B t,
    RelNf rF -> LvlNf lF -> LvlNf lG ->
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oRel lG B ->
    NfET (oExtC G rF lF F) (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B) t ->
    NfET G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B))
         (oLamRel G rF lF lG F B t)
| nfet_lam_irr : forall G rF lF F B t,
    RelNf rF -> LvlNf lF ->
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oIrr oL0 B ->
    NfET (oExtC G rF lF F) (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B) t ->
    NfET G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B))
         (oLamIrr G rF lF F B t)
| nfet_ne_pi_irr : forall G rF lF F B e,
    NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oIrr oL0 B ->
    NeET G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e ->
    NfET G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e.

Scheme EnvOk_min := Minimality for EnvOk Sort Prop
  with TyOk_min := Minimality for TyOk Sort Prop
  with NfCode_min := Minimality for NfCode Sort Prop
  with VarT_min := Minimality for VarT Sort Prop
  with NeET_min := Minimality for NeET Sort Prop
  with NfET_min := Minimality for NfET Sort Prop.

Combined Scheme Nf_mutind from
  EnvOk_min, TyOk_min, NfCode_min, VarT_min, NeET_min, NfET_min.

(* ------------------------------------------------------------------ *)
(* Weakenings                                                           *)
(* ------------------------------------------------------------------ *)

(* [Wk D G w] : [w : sub D G] is a weakening.  A purely SYNTACTIC class --
   no clause mentions reducibility -- which is what lets Layer 2's Kripke
   quantifier range over it without circularity.

   As in the STLC development the class must be closed under going under a
   binder ([wk_lift]), because the [exp_subst lam_rel] equation rewrites
   [w[lam A e]] to [lam A[w] (e[<w o wkn, hd>])] and the lifted substitution
   is a [snoc], not a [wkn]-composite.  Unlike STLC, lifting must also
   WEAKEN THE DOMAIN TYPE: [A] lives in [G], so the extended domain is
   [ext D i A'] for [A'] the normal form of [A[w]], and the head variable's
   type [A'[wkn]] agrees with what [snoc] demands ([A[wkn o w]]) only by
   "ty_subst_cmp".  So [Wk_wf] genuinely needs [wf_term_conv]. *)
Inductive Wk : term -> term -> term -> Prop :=
| wk_id : forall G, EnvOk G -> Wk G G (oId G)
| wk_ext : forall D G i A w,
    Wk D G w -> TyOk D i A ->
    Wk (oExt D i A) G (oCmp (oExt D i A) D G (oWkn D i A) w)
| wk_lift : forall D G i A A' w,
    Wk D G w -> TyOk G i A -> TyOk D i A' ->
    eqt (sTy D i) (oTySubst D G w i A) A' ->
    Wk (oExt D i A') (oExt G i A)
       (oSnoc (oExt D i A') G i A
              (oCmp (oExt D i A') D G (oWkn D i A') w)
              (oHd D i A')).

(* ------------------------------------------------------------------ *)
(* "has a normal form", up to provable equality                         *)
(*                                                                      *)
(* Everything downstream is stated in these three, never in the bare      *)
(* predicates: `e has a normal form at A` means `e is PROVABLY EQUAL to  *)
(* a canonical form at A`.  That is what discharges the 28 substitution    *)
(* equations inside the theory and keeps the model's transitivity and      *)
(* symmetry obligations nearly free.                                      *)
(* ------------------------------------------------------------------ *)

Definition HasNf (G i A e : term) : Prop :=
  exists n, NfET G i A n /\ eqt (sExp G i A) e n.

Definition HasNe (G i A e : term) : Prop :=
  exists n, NeET G i A n /\ eqt (sExp G i A) e n.

Definition HasNfCode (G r l c : term) : Prop :=
  exists c0, NfCode G r l c0 /\ eqt (sCode G r l) c c0.

Lemma HasNe_HasNf_nat G e
  : HasNe G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e ->
    HasNf G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) e.
Proof.
  intros [n [Hn Heq]]; exists n; split; [ apply nfet_ne_nat | ]; assumption.
Qed.

Lemma HasNe_HasNf_empty G e
  : HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e ->
    HasNf G (iEl oIrr oL0) (oEl G oIrr oL0 (oEmpty G)) e.
Proof.
  intros [n [Hn Heq]]; exists n; split; [ apply nfet_ne_empty | ]; assumption.
Qed.

Lemma HasNe_HasNf_var G r l c e
  : VarT G (iCode l) (oU G r l) c ->
    HasNe G (iEl r l) (oEl G r l c) e ->
    HasNf G (iEl r l) (oEl G r l c) e.
Proof.
  intros Hc [n [Hn Heq]]; exists n; split;
    [ eapply nfet_ne_var; eassumption | assumption ].
Qed.

Lemma HasNe_HasNf_pi_irr G rF lF F B e
  : NfCode G rF lF F ->
    NfCode (oExtC G rF lF F) oIrr oL0 B ->
    HasNe G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e ->
    HasNf G (iEl oIrr oL0) (oEl G oIrr oL0 (oPiIrr G rF lF F B)) e.
Proof.
  intros HF HB [n [Hn Heq]]; exists n; split;
    [ eapply nfet_ne_pi_irr; eassumption | assumption ].
Qed.

(* There is deliberately NO [HasNe_HasNf] at a [Pi_rel] type: that is
   exactly what eta forbids, and what makes reification type-directed. *)
