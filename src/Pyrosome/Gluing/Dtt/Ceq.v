Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.RSub.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4a: the model's relations.

   This file fixes the CONTRACT the [CutTModel_ok] obligations are proved
   against; it deliberately contains no obligation proofs, so the
   congruence and equation cases can be developed independently.

   Two design points carried over from Gluing/Stlc/Ceq.v, both load-bearing:

   - Every clause carries [eq_term ott_dtt [] t e1 e2].  This is the
     gluing: `has a normal form` means PROVABLY EQUAL to a canonical form,
     so the 28 substitution equations are discharged inside the theory and
     no confluence or termination argument for the sigma-calculus is
     needed.  It also makes [cterm_trans]/[cterm_sym]/[cterm_conv] nearly
     free.

   - The semantic conjunct quantifies over REDUCIBLE SUBSTITUTIONS.  It has
     to live here rather than in a separate lemma, because [cterm_cong]
     concludes about the term itself, not about a substitution instance.

   The semantic conjunct constrains only [e1]; the corresponding fact for
   [e2] is recovered from the equation, exactly as [term_sym_obligation] in
   Gluing/Stlc/ModelCong.v does.

   THREE THINGS ARE NEW relative to the simply-typed case.

   (i) [Ceq_sort] is NOT [eq].  In STLC it can be, because the sorts' index
       arguments are rigid.  Here [exp G i A] is indexed by an environment,
       a tyinfo and a TYPE, and all three carry equations.  The smallest
       witness is already in the compiled language: [Nat] is elaborated at
       info [rel (next L0)] and [Empty] at [rel (iota L1)], and those are
       equal only via `next0`.  So sort equality is defined to BE the
       bidirectional transfer of the term relation -- which is precisely
       what [cterm_conv] consumes.  The cost is paid once, in [csort_cong].

   (ii) The index sorts are handled by NORMALIZATION rather than by
       equality.  [relevance] and [lvl] are rigid (no equations, two closed
       constructors each), so plain syntactic equality is right there; but
       [tlvl] has `next0`/`next1`, so its clause compares [ntlvl], and
       [tyinfo] compares [ninfo].  [ltl] is proof-irrelevant (`ltl_irr`
       equates any two inhabitants), so its clause carries the equation and
       nothing else.

   (iii) [env] cannot be syntactic equality either -- for the same reason
       as (i): [ext G (next L0) A] and [ext G (iota L1) A] are provably
       equal environments with different syntax.  So the [env] clause says
       `has a normal environment`, and Layer 0.5's [EnvOk_inj] is what
       makes that a singleton.

   (iv) EVERY index of a semantic conjunct is quantified up to [eq_term],
       not held fixed: the environment via [RSubN] (src/Pyrosome/Gluing/Dtt/RSub.v), the
       info and the type via [RTmN]/[RTyN] (src/Pyrosome/Gluing/Dtt/LogRel.v).  This is forced,
       not stylistic.  [csort_cong] varies all three, and with any of them
       held fixed the corresponding [Ceq_sort] transfer is unprovable --
       for the info it is REFUTABLE modulo consistency, which
       src/Pyrosome/Gluing/Dtt/ModelStruct.v proves: `next0` makes [ty G (iCode L0)] and
       [ty G (iEl rel L1)] provably equal sorts whose sets of normal
       representatives are disjoint (because [TyOk] pins each former's
       info), so a transfer between them would force the closed universe
       [U irr L0] to be provably equal to the [El] of a closed relevant
       [Pi] code.  With all three quantified, both directions of every
       transfer are transitivity alone.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

Definition HasNfEnv (G : term) : Prop :=
  exists G0, EnvOk G0 /\ eqt sEnv G G0.

(* An inductive family rather than a sort-indexed match: off-diagonal sorts
   (a [Ceq_term] at a sort that is none of the nine) are then uninhabited
   for free -- there is simply no constructor whose index can reach them --
   rather than needing an explicit [False] leaf, and reading a clause back
   is [inversion] instead of decision-tree surgery. *)
Inductive Ceq_term : sort -> term -> term -> Prop :=

(* ---- the rigid index sorts ---- *)
| ceq_relevance : forall r,
    RelNf r -> Ceq_term sRelevance r r
| ceq_lvl : forall l,
    LvlNf l -> Ceq_term sLvl l l

(* ---- the index sorts with equations ---- *)
| ceq_tlvl : forall n1 n2,
    eqt sTlvl n1 n2 ->
    ntlvl n1 = ntlvl n2 ->
    TlvlNf (ntlvl n1) ->
    Ceq_term sTlvl n1 n2
| ceq_tyinfo : forall i1 i2,
    eqt sInfo i1 i2 ->
    ninfo i1 = ninfo i2 ->
    InfoNf (ninfo i1) ->
    Ceq_term sInfo i1 i2
(* [ltl] is proof-irrelevant: `ltl_irr` equates any two inhabitants, so
   there is no content to attach. *)
| ceq_ltl : forall a b p1 p2,
    eqt (sLtl a b) p1 p2 -> Ceq_term (sLtl a b) p1 p2

(* ---- environments ---- *)
| ceq_env : forall G1 G2,
    eqt sEnv G1 G2 -> HasNfEnv G1 -> Ceq_term sEnv G1 G2

(* ---- substitutions ---- *)
| ceq_sub : forall G G' g1 g2,
    eqt (sSub G G') g1 g2 ->
    (forall D h, EnvOk D -> RSubN D G h -> RSubN D G' (oCmp D G G' h g1)) ->
    Ceq_term (sSub G G') g1 g2

(* ---- types ---- *)
(* The semantic content of a type is that its every reducible instance is a
   REDUCIBLE TYPE, i.e. has a normal representative carrying a candidate.
   [RTyN] is stated up to [eq_term] in the type, so the fact transfers to
   [A2] for free. *)
| ceq_ty : forall G i A1 A2,
    eqt (sTy G i) A1 A2 ->
    (forall D g, EnvOk D -> RSubN D G g ->
       RTyN D i (oTySubst D G g i A1)) ->
    Ceq_term (sTy G i) A1 A2

(* ---- terms ---- *)
| ceq_exp : forall G i A e1 e2,
    eqt (sExp G i A) e1 e2 ->
    (forall D g, EnvOk D -> RSubN D G g ->
       RTmN D i (oTySubst D G g i A) (oExpSubst D G g i A e1)) ->
    Ceq_term (sExp G i A) e1 e2.

(* ------------------------------------------------------------------ *)
(* Clause readings                                                      *)
(*                                                                      *)
(* Downstream proofs should go through these rather than inverting        *)
(* [Ceq_term] by hand, so a change of representation stays local.         *)
(* ------------------------------------------------------------------ *)

Lemma Ceq_relevance_e r1 r2
  : Ceq_term sRelevance r1 r2 -> r1 = r2 /\ RelNf r1.
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_lvl_e l1 l2
  : Ceq_term sLvl l1 l2 -> l1 = l2 /\ LvlNf l1.
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_tlvl_e n1 n2
  : Ceq_term sTlvl n1 n2 ->
    eqt sTlvl n1 n2 /\ ntlvl n1 = ntlvl n2 /\ TlvlNf (ntlvl n1).
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_tyinfo_e i1 i2
  : Ceq_term sInfo i1 i2 ->
    eqt sInfo i1 i2 /\ ninfo i1 = ninfo i2 /\ InfoNf (ninfo i1).
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_ltl_e a b p1 p2
  : Ceq_term (sLtl a b) p1 p2 -> eqt (sLtl a b) p1 p2.
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_env_e G1 G2
  : Ceq_term sEnv G1 G2 -> eqt sEnv G1 G2 /\ HasNfEnv G1.
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_sub_e G G' g1 g2
  : Ceq_term (sSub G G') g1 g2 ->
    eqt (sSub G G') g1 g2
    /\ (forall D h, EnvOk D -> RSubN D G h -> RSubN D G' (oCmp D G G' h g1)).
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_ty_e G i A1 A2
  : Ceq_term (sTy G i) A1 A2 ->
    eqt (sTy G i) A1 A2
    /\ (forall D g, EnvOk D -> RSubN D G g -> RTyN D i (oTySubst D G g i A1)).
Proof. intro H; inversion H; subst; auto. Qed.

Lemma Ceq_exp_e G i A e1 e2
  : Ceq_term (sExp G i A) e1 e2 ->
    eqt (sExp G i A) e1 e2
    /\ (forall D g, EnvOk D -> RSubN D G g ->
          RTmN D i (oTySubst D G g i A) (oExpSubst D G g i A e1)).
Proof. intro H; inversion H; subst; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Sort equality                                                        *)
(* ------------------------------------------------------------------ *)

(* Sort equality IS the bidirectional transfer of the term relation.  This
   is deliberate: conversion is where dependent normalization usually dies,
   and rather than try to RECOVER the transfer by inverting [eq_sort]
   (which would need sort injectivity for the whole language), the relation
   is defined to carry exactly what [cterm_conv] consumes, and the cost is
   paid once, in [csort_cong].

   The language has no [sort_eq_rule]s at all, so [csort_by] is vacuous;
   [csort_trans] and [csort_sym] are transitivity of [eq_sort] plus
   composition, resp. symmetry plus a swap, one line each. *)
Definition Ceq_sort (t1 t2 : sort) : Prop :=
  eq_sort ott_dtt [] t1 t2
  /\ (forall e1 e2, Ceq_term t1 e1 e2 -> Ceq_term t2 e1 e2)
  /\ (forall e1 e2, Ceq_term t2 e1 e2 -> Ceq_term t1 e1 e2).

Lemma Ceq_sort_refl t : wf_sort ott_dtt [] t -> Ceq_sort t t.
Proof.
  intro Hwf; unfold Ceq_sort; repeat split; auto using eq_sort_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The model                                                            *)
(* ------------------------------------------------------------------ *)

(* [CutTModel]'s carriers are [Type]-valued; the [Prop]-valued relations
   above are accepted by cumulativity, exactly as Gluing/SyntacticModel.v
   does.  Keeping everything in [Prop] is what avoids the [Prop]/[Type]
   wall that stopped the earlier attempt: the single bridge in the whole
   development is [CutModelSound.v]'s [inhabited]. *)
Definition DttCM : CutTModel :=
  {|
    ceq_sort := Ceq_sort;
    ceq_term := Ceq_term;
  |}.
