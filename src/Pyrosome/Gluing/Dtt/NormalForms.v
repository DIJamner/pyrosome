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
       [Pi_irr] ALSO has no neutral clause, but for a different reason:
       [ott_dtt] contains a "proof irrelevance" rule (El-sorted, from
       [ott_proofirr_el] in Lang/OTT/ProofIrr.v), and it subsumes irrelevant
       eta -- for [e] at [El G irr L0 (Pi_irr F B)], [e = lam_irr F B t]
       holds for ANY well-typed body [t], so a neutral there is not normal
       either.  The two cases are discharged asymmetrically: at [Pi_rel]
       the normal form must be THE eta-expansion of the neutral (only
       "Pi_rel eta" proves that equality), whereas at [Pi_irr] ANY normal
       inhabitant of the codomain will do (proof irrelevance equates the
       neutral to all of them at once), so [HasNf] is derived from
       [eq_proof_irr] rather than from a dedicated [NfET] clause.

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

(* ------------------------------------------------------------------ *)
(* The type an [Idcong] concludes at                                    *)
(* ------------------------------------------------------------------ *)

(* [Idcong A B b t u e] concludes at the Id between the two instantiations
   of its body:  Id (B[<id,t>]) (B[<id,u>]) (b[<id,t>]) (b[<id,u>]).
   Spelled EXACTLY as the compiled rule stores it (read off the elaborated
   language, not the surface notation): the codomain code travels at the
   info [iCode lB] and the body at [iEl oRel lB]. *)
Definition oIdcongTy (G l lB A B b t u : term) : term :=
  let X := oExtC G oRel l A in
  oIdEq G lB
    (oExpSubst G X (oInst G oRel l A t) (iCode lB) (oU X oRel lB) B)
    (oExpSubst G X (oInst G oRel l A u) (iCode lB) (oU X oRel lB) B)
    (oExpSubst G X (oInst G oRel l A t) (iEl oRel lB) (oEl X oRel lB B) b)
    (oExpSubst G X (oInst G oRel l A u) (iEl oRel lB) (oEl X oRel lB B) b).

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
| nfcode_ne : forall G r l c,
    NeCode G r l c -> NfCode G r l c

(* [NeCode G r l c] : [c] is a NEUTRAL code -- a code that no computation
   rule of [ott_dtt] can reduce.  Before the Id fragment this was exactly
   "a variable", and [NfCode] had [nfcode_var] instead; [Id] adds a second
   way for a code to be stuck, so the notion is broken out.

   The clauses are the complete stuck analysis of section 12b of
   Gluing/Dtt/design.md.  An [Id] reduces as soon as both of its codes are
   canonical: distinct heads clash to [Empty], two [Pi_rel]s go to funext
   or (on mismatched domain indices) to [Empty], and two [Nat]s dispatch on
   the endpoints.  So it is stuck exactly when a CODE is neutral, or when
   both codes are [Nat] and an ENDPOINT is neutral. *)
with NeCode : term -> term -> term -> term -> Prop :=
| necode_var : forall G r l c,
    VarT G (iCode l) (oU G r l) c -> NeCode G r l c

(* Stuck on a neutral code.  Note the indices: [Id] lands at [irr, L0],
   while its two code arguments are RELEVANT, and the only neutral code at
   a relevant index is a variable -- so these clauses do not recurse into
   further [Id]s. *)
| necode_id_l : forall G l A B t u,
    NeCode G oRel l A -> NfCode G oRel l B ->
    NfET G (iEl oRel l) (oEl G oRel l A) t ->
    NfET G (iEl oRel l) (oEl G oRel l B) u ->
    NeCode G oIrr oL0 (oIdEq G l A B t u)
| necode_id_r : forall G l A B t u,
    NfCode G oRel l A -> NeCode G oRel l B ->
    NfET G (iEl oRel l) (oEl G oRel l A) t ->
    NfET G (iEl oRel l) (oEl G oRel l B) u ->
    NeCode G oIrr oL0 (oIdEq G l A B t u)

(* Stuck on a neutral endpoint, both codes being [Nat].  No other pair of
   canonical codes can be stuck. *)
| necode_id_nat_l : forall G t u,
    NeET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) t ->
    NfET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) u ->
    NeCode G oIrr oL0 (oIdEq G oL0 (oNat G) (oNat G) t u)
| necode_id_nat_r : forall G t u,
    NfET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) t ->
    NeET G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) u ->
    NeCode G oIrr oL0 (oIdEq G oL0 (oNat G) (oNat G) t u)

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
(* [Idcong] is neutral UNCONDITIONALLY -- there is no premise on the shape
   of its body [b].  That is what makes reification at an Id type work; see
   section 12d of design.md.  The alternative (neutral only when [b] is
   neutral, with a structural recursion supplying the normal form
   otherwise) does not close: at a [lam_rel] body the reduced type needs a
   congruence in TWO variables at once, which the single-binder [Idcong]
   cannot express and which cannot be assembled from two one-variable
   congruences without a cast.  Being unconditionally neutral, its normal
   form is instead whatever its TYPE dictates, and the existing
   type-directed machinery supplies it: at a [Pi_irr] (the unit
   proposition, or a funext Pi) it eta-expands by proof irrelevance and the
   body [Idcong ... . a1 . a2 . p] is [app_irr] of a neutral, hence neutral
   again at the smaller inner Id; at [Empty] or a stuck Id, neutrals are
   already normal.
   As with [app_rel], the normal representative [C] of the conclusion type
   is supplied at the construction site -- here it is the normal form of
   the Id code, computed by the same structural recursion as
   [NfCode_subst], extended with the Id computation table. *)
| neet_idcong : forall G l lB A B b t u e C,
    NfCode G oRel l A ->
    NfCode (oExtC G oRel l A) oRel lB B ->
    NfET (oExtC G oRel l A) (iEl oRel lB) (oEl (oExtC G oRel l A) oRel lB B) b ->
    NfET G (iEl oRel l) (oEl G oRel l A) t ->
    NfET G (iEl oRel l) (oEl G oRel l A) u ->
    NfET G (iEl oIrr oL0) (oEl G oIrr oL0 (oIdEq G l A A t u)) e ->
    TyOk G (iEl oIrr oL0) C ->
    eqt (sTy G (iEl oIrr oL0))
        (oEl G oIrr oL0 (oIdcongTy G l lB A B b t u)) C ->
    NeET G (iEl oIrr oL0) C (oIdcong G l lB A B b t u e)

(* [NfET G i A e] : [e] is an ETA-LONG normal term of the normal type [A].
   The clauses are dispatched by [A]'s head, and the dispatch is exhaustive
   over [TyOk]:

     A = U G r l                    -> a normal code
     A = El G rel L0 (Nat G)        -> zero | suc | neutral
     A = El G irr L0 (Empty G)      -> neutral
     A = El G r l x,  x a variable  -> neutral
     A = El G rel lG (Pi_rel ...)   -> lam_rel ONLY            <-- eta
     A = El G irr L0 (Pi_irr ...)   -> lam_irr ONLY            <-- proof irr *)
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
(* At a type named by a NEUTRAL code, every normal is neutral.  Before the
   Id fragment "neutral code" meant "variable" and this clause was
   [nfet_ne_var]; it now dispatches on [NeCode], which additionally covers
   a stuck [Id].  This is the ONLY place the Id fragment touches [NfET] --
   the extension adds no normal form except neutrals. *)
| nfet_ne : forall G r l c e,
    NeCode G r l c ->
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
         (oLamIrr G rF lF F B t).

Scheme EnvOk_min := Minimality for EnvOk Sort Prop
  with TyOk_min := Minimality for TyOk Sort Prop
  with NfCode_min := Minimality for NfCode Sort Prop
  with NeCode_min := Minimality for NeCode Sort Prop
  with VarT_min := Minimality for VarT Sort Prop
  with NeET_min := Minimality for NeET Sort Prop
  with NfET_min := Minimality for NfET Sort Prop.

(* SEVEN conjuncts now, not six: every consumer of [Nf_mutind]
   (NfTyping.v, NfWk.v, LogRelCore.v) gains an [NeCode] case. *)
Combined Scheme Nf_mutind from
  EnvOk_min, TyOk_min, NfCode_min, NeCode_min, VarT_min, NeET_min, NfET_min.

(* ------------------------------------------------------------------ *)
(* Syntactic shape lemmas                                               *)
(*                                                                      *)
(* RESCUED from src/Pyrosome/Gluing/Dtt/Inj.v (deleted with the rest of  *)
(* Layer 0.5; design.md section 12e).  [VarT_shape] was the ONLY lemma   *)
(* in that file with no dependence on the rigid model of Rigid.v -- the  *)
(* other twenty-odd are stated over [ICode]/[ITy]/[IEnv]/[ISub] and go   *)
(* with them.  It lives here rather than in NfTyping.v because it is     *)
(* pure case analysis on [VarT] and needs neither Wf.v nor Eqns.v.       *)
(* ------------------------------------------------------------------ *)

(* The subject of a [VarT] is an [oHd] or a [wkn]-substituted variable.
   (Was Inj.v:216.) *)
Lemma VarT_shape G i A x : VarT G i A x ->
  (exists G0 i0 A0, x = oHd G0 i0 A0)
  \/ (exists G0 j B i0 A0 y,
         x = oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y).
Proof. destruct 1; [ left | right ]; eauto 10. Qed.

(* The [NeET] analogue: a neutral is a variable, an application, an
   [Emptyrec] or an [Idcong].  (New; the old development never needed it
   because Layer 0.5 did the corresponding work semantically.) *)
Lemma NeET_shape G i A e : NeET G i A e ->
  (exists G0 i0 A0, e = oHd G0 i0 A0)
  \/ (exists G0 j B i0 A0 y,
         e = oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y)
  \/ (exists G0 rF lF lG F B f a, e = oAppRel G0 rF lF lG F B f a)
  \/ (exists G0 rF lF F B f a, e = oAppIrr G0 rF lF F B f a)
  \/ (exists G0 rA lA A0 e0, e = oEmptyrec G0 rA lA A0 e0)
  \/ (exists G0 l lB A0 B b t u e0, e = oIdcong G0 l lB A0 B b t u e0).
Proof.
  destruct 1.
  - destruct (VarT_shape H) as [ H0 | H0 ]; [ left | right; left ]; exact H0.
  - right; right; left; eauto 10.
  - right; right; right; left; eauto 10.
  - right; right; right; right; left; eauto 10.
  - right; right; right; right; right; eauto 20.
Qed.

(* A neutral code is a variable or a stuck [Id]. *)
Lemma NeCode_shape G r l c : NeCode G r l c ->
  VarT G (iCode l) (oU G r l) c
  \/ (exists l0 A B t u, c = oIdEq G l0 A B t u).
Proof. destruct 1; [ left | right .. ]; eauto 10. Qed.

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
   "ty_subst_cmp".  So [Wk_wf] genuinely needs [wf_term_conv].

   [wk_wkn] is the BARE one-step weakening.  It is derivable up to
   [eq_term] ([wkn ; id = wkn], and [wk_ext] at [wk_id] gives the left
   side), but the theory's own "Pi_rel eta" is stated with the bare [wkn],
   so having it as a clause rather than as an equational detour is what
   lets Layer 2's escape step at [Pi_rel] apply eta directly.  Note the
   four clauses still have pairwise-distinct head symbols
   ([id]/[wkn]/[cmp]/[snoc]), so [Wk_ext_inv] stays a SYNTACTIC
   case-analysis: no clause is up to [eq_term], which is what keeps this
   class usable as Layer 2's Kripke quantifier. *)
Inductive Wk : term -> term -> term -> Prop :=
| wk_id : forall G, EnvOk G -> Wk G G (oId G)
| wk_wkn : forall D i A,
    EnvOk D -> TyOk D i A -> Wk (oExt D i A) D (oWkn D i A)
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

Lemma HasNe_HasNf_ne G r l c e
  : NeCode G r l c ->
    HasNe G (iEl r l) (oEl G r l c) e ->
    HasNf G (iEl r l) (oEl G r l c) e.
Proof.
  intros Hc [n [Hn Heq]]; exists n; split;
    [ eapply nfet_ne; eassumption | assumption ].
Qed.

(* The old name, kept as a derived form: a code variable is a neutral code. *)
Lemma HasNe_HasNf_var G r l c e
  : VarT G (iCode l) (oU G r l) c ->
    HasNe G (iEl r l) (oEl G r l c) e ->
    HasNf G (iEl r l) (oEl G r l c) e.
Proof.
  intro; apply HasNe_HasNf_ne; apply necode_var; assumption.
Qed.

(* There is deliberately NO [HasNe_HasNf] at a [Pi_rel] OR a [Pi_irr] type.
   At [Pi_rel] that is exactly what eta forbids: the normal form of a
   neutral there must be its eta-expansion, not the neutral itself, and
   only "Pi_rel eta" proves the two equal.  At [Pi_irr] the reason is
   different -- proof irrelevance, not eta -- but the conclusion is the
   same: "proof irrelevance" (see [eq_proof_irr] in Eqns.v) equates a
   neutral at [El G irr L0 (Pi_irr ...)] with EVERY well-typed [lam_irr] at
   that type, so a neutral there is never the (unique) normal form either;
   what makes reification type-directed at [Pi_irr] is deriving [HasNf]
   from [eq_proof_irr] rather than from a dedicated [NfET] clause. *)
