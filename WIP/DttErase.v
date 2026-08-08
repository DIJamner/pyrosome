Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttNf.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 0.5a: ERASURE, the syntactic half of code
   rigidity.

   THE STRUCTURAL FACT (design section 2, visible in [DttNf.v]'s
   [NfCode]): no eliminator of [ott_dtt] has a universe as its result
   type -- [app_rel], [app_irr] and [Emptyrec] all land in an [El] -- so
   the only NEUTRAL codes are variables and normal codes form the FREE
   grammar

       c ::= x | Nat G | Empty G | Pi_rel G rF lF lG c c | Pi_irr G rF lF c c

   Everything in this file is a consequence of that: the erasure below is
   exactly the "forget the index arguments, de-Bruijn the variables" map
   of that grammar, and it is injective on normal forms.

   WHAT IS HERE.

     1. A first-order de Bruijn domain [rcode]/[rty]/[renv], with NO
        index arguments at all: erasure drops every [G], every [i], every
        [ty]/[exp] index that the concrete syntax threads through the
        constructors, keeping only the relevance/level bits and the code
        skeleton.

     2. Four erasure RELATIONS [ErEnv]/[ErTy]/[ErCode]/[ErVar], defined
        mutually and only on the Layer-1 normal syntax.  Relations rather
        than functions because the concrete syntax carries index
        arguments that erasure drops (so erasure is not injective on raw
        terms, and its inverse is not a function).

     3. [Nf_erase_total]: every Layer-1 normal object has an erasure.
        UNCONDITIONAL.

     4. [Er_fun]: erasure is functional (a normal object has at most one
        erasure).  UNCONDITIONAL.

     5. [EnvOk_erase_inj] / [TyOk_erase_inj] / [NfCode_erase_inj]:
        erasure is INJECTIVE on normal forms -- two normal objects over
        the same environment with the same erasure are syntactically
        identical.  CONDITIONAL on [WknRepUnique]; see the next section.

   THE ONE ASSUMPTION, AND WHY IT IS UNAVOIDABLE HERE.

   [VarT] (DttNf.v) names the normal representative of a weakened type:

       vart_hd : ... -> TyOk (oExt G i A) i A' ->
                 eqt (sTy (oExt G i A) i)
                     (oTySubst (oExt G i A) G (oWkn G i A) i A) A' ->
                 VarT (oExt G i A) i A' (oHd G i A)

   [A'] is pinned by that [eq_term] premise and BY NOTHING SYNTACTIC.
   And the variable term at de Bruijn index [k+1],

       oExpSubst (oExt G j B) G (oWkn G j B) i A x,

   CONTAINS the named representative [A] of the variable at index [k].
   So "erasure is injective on variables" is equivalent to "the naming is
   unique", which is [TyOk_inj] -- a fact about [eq_term], i.e. exactly
   the semantic half of code rigidity.  Purely syntactically it is not
   available: as far as this file can see, two derivations of
   [VarT G i A' x] may name different [A']s, and then the two [x]s are
   different terms with the same erasure.

   It is therefore taken as an explicit, named hypothesis

       WknRepUnique : the normal representative of ONE type's weakening
                      is unique

   -- an instance of design section 4's [TyOk_inj], and precisely what
   the rigid model supplies.  It is an ordinary [Definition ... : Prop]
   passed as an argument to the three injectivity theorems: there is no
   [Axiom], no [Admitted], and the unconditional results (2)-(4) do not
   mention it.  NB for the composing layer: closing the loop
   ([WknRepUnique] from the rigid model + these theorems = [TyOk_inj])
   needs an induction on the length of the environment, because
   [WknRepUnique] at an environment of length n is used while proving
   injectivity at that same length; see the report accompanying this
   file.

   No [eq_term] is reasoned about anywhere below -- [WknRepUnique] is
   only ever APPLIED -- and no model is built.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* =====================================================================
   1. The semantic domain: first-order de Bruijn codes and types.
   ===================================================================== *)

(* A normal code, with all index arguments erased.  [rc_var] is a de
   Bruijn INDEX (0 = the most recently bound variable); the [bool] of
   [rc_pi] is [true] for [Pi_rel], [false] for [Pi_irr]. *)
Inductive rcode : Type :=
| rc_var : nat -> rcode
| rc_nat : rcode
| rc_empty : rcode
| rc_pi : bool -> rcode -> rcode -> rcode.

(* A normal type: a universe [U r l] or an [El] of a normal code.  In
   both cases the first [bool] is the relevance ([true] = [rel]) and the
   second is the level ([true] = [L1]). *)
Inductive rty : Type :=
| rt_U : bool -> bool -> rty
| rt_El : bool -> bool -> rcode -> rty.

(* MOST-RECENT-FIRST, matching [ott]'s [ext]: the head of the list is the
   type of the variable at de Bruijn index 0. *)
Definition renv := list rty.

(* =====================================================================
   2. Erasure of the rigid index sorts.

   [relevance] and [lvl] have two closed constructors each and no
   equations, so their erasure is a bijection onto [bool].
   ===================================================================== *)

Inductive ErRel : term -> bool -> Prop :=
| errel_rel : ErRel oRel true
| errel_irr : ErRel oIrr false.

Inductive ErLvl : term -> bool -> Prop :=
| erlvl_L0 : ErLvl oL0 false
| erlvl_L1 : ErLvl oL1 true.

Lemma ErRel_fun r b1 b2 : ErRel r b1 -> ErRel r b2 -> b1 = b2.
Proof. intros H1 H2; destruct H1; inversion H2; reflexivity. Qed.

Lemma ErLvl_fun l b1 b2 : ErLvl l b1 -> ErLvl l b2 -> b1 = b2.
Proof. intros H1 H2; destruct H1; inversion H2; reflexivity. Qed.

Lemma ErRel_inj r1 r2 b : ErRel r1 b -> ErRel r2 b -> r1 = r2.
Proof. intros H1 H2; destruct H1; inversion H2; reflexivity. Qed.

Lemma ErLvl_inj l1 l2 b : ErLvl l1 b -> ErLvl l2 b -> l1 = l2.
Proof. intros H1 H2; destruct H1; inversion H2; reflexivity. Qed.

Lemma RelNf_ErRel r : RelNf r -> exists b, ErRel r b.
Proof. destruct 1; [ exists true | exists false ]; constructor. Qed.

Lemma LvlNf_ErLvl l : LvlNf l -> exists b, ErLvl l b.
Proof. destruct 1; [ exists false | exists true ]; constructor. Qed.

(* =====================================================================
   3. Erasure of environments, types, codes and variables.

   Defined ONLY on the normal syntax of Layer 1 (there is no clause for
   [ty_subst], [cmp], ... : erasure of an arbitrary term is meaningless
   and is never needed).  The four judgements are mutual because a type
   is an [El] of a code, a code may be a variable, and a variable's index
   is read off an environment of types.

   Note what [ErVar E G i A x k] does NOT say: nothing at all about [A],
   the NAMED normal representative of the variable's type.  It could not:
   see the header.  The link between [A] and [E] at slot [k] is the
   content of [WknRepUnique].
   ===================================================================== *)

Inductive ErEnv : term -> renv -> Prop :=
| erenv_emp : ErEnv oEmp []
| erenv_ext : forall G i A E T,
    ErEnv G E -> ErTy E G i A T -> ErEnv (oExt G i A) (T :: E)

(* [ErTy E G i A T] : the normal type [A] of sort [ty G i], read in the
   environment whose erasure is [E], erases to [T]. *)
with ErTy : renv -> term -> term -> term -> rty -> Prop :=
| erty_U : forall E G r l br bl,
    ErRel r br -> ErLvl l bl ->
    ErTy E G (iCode l) (oU G r l) (rt_U br bl)
| erty_El : forall E G r l c br bl n,
    ErRel r br -> ErLvl l bl -> ErCode E G r l c n ->
    ErTy E G (iEl r l) (oEl G r l c) (rt_El br bl n)

(* [ErCode E G r l c n] : the normal code [c] of sort [sCode G r l]
   erases to [n].  The five clauses are the five productions of the free
   code grammar. *)
with ErCode : renv -> term -> term -> term -> term -> rcode -> Prop :=
| ercode_nat : forall E G,
    ErCode E G oRel oL0 (oNat G) rc_nat
| ercode_empty : forall E G,
    ErCode E G oIrr oL0 (oEmpty G) rc_empty
| ercode_pi_rel : forall E G rF lF lG F B brF blF nF nB,
    ErRel rF brF -> ErLvl lF blF ->
    ErCode E G rF lF F nF ->
    ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oRel lG B nB ->
    ErCode E G oRel lG (oPiRel G rF lF lG F B) (rc_pi true nF nB)
| ercode_pi_irr : forall E G rF lF F B brF blF nF nB,
    ErRel rF brF -> ErLvl lF blF ->
    ErCode E G rF lF F nF ->
    ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oIrr oL0 B nB ->
    ErCode E G oIrr oL0 (oPiIrr G rF lF F B) (rc_pi false nF nB)
| ercode_var : forall E G r l c k,
    ErVar E G (iCode l) (oU G r l) c k ->
    ErCode E G r l c (rc_var k)

(* [ErVar E G i A x k] : [x] is the variable at de Bruijn index [k].
   [hd] is 0 and each [exp_subst (wkn ...)] layer is +1, so the index
   counts exactly the [wkn]s, i.e. the distance from the binder. *)
with ErVar : renv -> term -> term -> term -> term -> nat -> Prop :=
| ervar_hd : forall E G i A A' T,
    ErTy E G i A T ->
    ErVar (T :: E) (oExt G i A) i A' (oHd G i A) 0
| ervar_wkn : forall E G i A x j B A' TB k,
    ErVar E G i A x k ->
    ErTy E G j B TB ->
    ErVar (TB :: E) (oExt G j B) i A'
          (oExpSubst (oExt G j B) G (oWkn G j B) i A x) (S k).

Scheme ErEnv_min := Minimality for ErEnv Sort Prop
  with ErTy_min := Minimality for ErTy Sort Prop
  with ErCode_min := Minimality for ErCode Sort Prop
  with ErVar_min := Minimality for ErVar Sort Prop.

Combined Scheme Er_mutind from ErEnv_min, ErTy_min, ErCode_min, ErVar_min.

(* The environment extension a binder makes, at the erasure level. *)
Lemma ErEnv_extC E G rF lF F brF blF nF
  : ErEnv G E -> ErRel rF brF -> ErLvl lF blF -> ErCode E G rF lF F nF ->
    ErEnv (oExtC G rF lF F) (rt_El brF blF nF :: E).
Proof.
  intros; unfold oExtC; econstructor; [ eassumption | ].
  econstructor; eassumption.
Qed.

(* =====================================================================
   4. Erasure is functional.
   ===================================================================== *)

Lemma Er_fun :
  (forall G E1, ErEnv G E1 -> forall E2, ErEnv G E2 -> E1 = E2)
  /\ (forall E G i A T1, ErTy E G i A T1 -> forall T2, ErTy E G i A T2 -> T1 = T2)
  /\ (forall E G r l c n1, ErCode E G r l c n1 ->
      forall n2, ErCode E G r l c n2 -> n1 = n2)
  /\ (forall E G i A x k1, ErVar E G i A x k1 ->
      forall k2, ErVar E G i A x k2 -> k1 = k2).
Proof.
  apply Er_mutind.
  (* erenv_emp *)
  - intros E2 H; inversion H; reflexivity.
  (* erenv_ext *)
  - intros G i A E T HE IHE HT IHT E2 H; inversion H; subst.
    erewrite IHE by eassumption.
    erewrite IHT by eassumption.
    reflexivity.
  (* erty_U *)
  - intros E G r l br bl Hr Hl T2 H; inversion H; subst.
    erewrite (ErRel_fun Hr) by eassumption.
    erewrite (ErLvl_fun Hl) by eassumption.
    reflexivity.
  (* erty_El *)
  - intros E G r l c br bl n Hr Hl Hc IHc T2 H; inversion H; subst.
    erewrite (ErRel_fun Hr) by eassumption.
    erewrite (ErLvl_fun Hl) by eassumption.
    erewrite IHc by eassumption.
    reflexivity.
  (* ercode_nat *)
  - intros E G n2 H; inversion H; subst; [ reflexivity | ].
    (* the code cannot also be a variable *)
    match goal with Hv : ErVar _ _ _ _ _ _ |- _ => inversion Hv end.
  (* ercode_empty *)
  - intros E G n2 H; inversion H; subst; [ reflexivity | ].
    match goal with Hv : ErVar _ _ _ _ _ _ |- _ => inversion Hv end.
  (* ercode_pi_rel *)
  - intros E G rF lF lG F B brF blF nF nB HrF HlF HF IHF HB IHB n2 H;
      inversion H; subst.
    2:{ match goal with Hv : ErVar _ _ _ _ _ _ |- _ => inversion Hv end. }
    erewrite IHF by eassumption.
    match goal with
    | Hr : ErRel rF ?b |- _ =>
        rewrite <- (ErRel_fun HrF Hr) in *
    end.
    match goal with
    | Hl : ErLvl lF ?b |- _ =>
        rewrite <- (ErLvl_fun HlF Hl) in *
    end.
    erewrite IHB by eassumption.
    reflexivity.
  (* ercode_pi_irr *)
  - intros E G rF lF F B brF blF nF nB HrF HlF HF IHF HB IHB n2 H;
      inversion H; subst.
    2:{ match goal with Hv : ErVar _ _ _ _ _ _ |- _ => inversion Hv end. }
    erewrite IHF by eassumption.
    match goal with
    | Hr : ErRel rF ?b |- _ =>
        rewrite <- (ErRel_fun HrF Hr) in *
    end.
    match goal with
    | Hl : ErLvl lF ?b |- _ =>
        rewrite <- (ErLvl_fun HlF Hl) in *
    end.
    erewrite IHB by eassumption.
    reflexivity.
  (* ercode_var *)
  - intros E G r l c k Hv IHv n2 H; inversion H; subst;
      try (inversion Hv; fail).
    erewrite IHv by eassumption; reflexivity.
  (* ervar_hd *)
  - intros E G i A A' T HT k2 H; inversion H; subst; reflexivity.
  (* ervar_wkn *)
  - intros E G i A x j B A' TB k Hv IHv HT k2 H; inversion H; subst.
    erewrite IHv by eassumption; reflexivity.
Qed.

Definition ErEnv_fun := proj1 Er_fun.
Definition ErTy_fun := proj1 (proj2 Er_fun).
Definition ErCode_fun := proj1 (proj2 (proj2 Er_fun)).
Definition ErVar_fun := proj2 (proj2 (proj2 Er_fun)).

(* =====================================================================
   5. Small inversions on the Layer-1 judgements.
   ===================================================================== *)

(* A variable's type is always a normal type: every [VarT] clause carries
   [TyOk] of its conclusion type. *)
Lemma VarT_TyOk G i A x : VarT G i A x -> TyOk G i A.
Proof. inversion 1; assumption. Qed.

(* The relevance and level of a normal code are normal.  The variable
   case goes through [VarT_TyOk]: the type of a code variable is
   [oU G r l], whose only [TyOk] derivation is [tyok_U]. *)
Lemma NfCode_nf_indices G r l c : NfCode G r l c -> RelNf r /\ LvlNf l.
Proof.
  destruct 1; try (split; constructor; assumption).
  match goal with
  | H : VarT _ _ _ _ |- _ =>
      apply VarT_TyOk in H; inversion H; subst; split; assumption
  end.
Qed.

Lemma TyOk_U_inv G i r l
  : TyOk G i (oU G r l) -> i = iCode l /\ EnvOk G /\ RelNf r /\ LvlNf l.
Proof. inversion 1; subst; repeat split; assumption. Qed.

Lemma TyOk_El_inv G i r l c
  : TyOk G i (oEl G r l c) -> i = iEl r l /\ NfCode G r l c.
Proof. inversion 1; subst; split; [ reflexivity | assumption ]. Qed.

(* =====================================================================
   6. Totality: every normal object has an erasure.  UNCONDITIONAL.

   [NeET]/[NfET] play no role (codes never contain a neutral that is not
   a variable -- the structural fact this whole layer rests on), so their
   components are [True].
   ===================================================================== *)

Theorem Nf_erase_total :
  (forall G, EnvOk G -> exists E, ErEnv G E)
  /\ (forall G i A, TyOk G i A ->
        forall E, ErEnv G E -> exists T, ErTy E G i A T)
  /\ (forall G r l c, NfCode G r l c ->
        forall E, ErEnv G E -> exists n, ErCode E G r l c n)
  /\ (forall G i A x, VarT G i A x ->
        forall E, ErEnv G E -> exists k, ErVar E G i A x k)
  /\ (forall G i A e, NeET G i A e -> True)
  /\ (forall G i A e, NfET G i A e -> True).
Proof.
  apply Nf_mutind; try (intros; exact I).
  (* envok_emp *)
  - exists (@nil rty); constructor.
  (* envok_ext *)
  - intros G i A HG [E HE] HA IHA.
    destruct (IHA E HE) as [T HT].
    exists (T :: E); econstructor; eassumption.
  (* tyok_U *)
  - intros G r l HG IHG Hr Hl E HE.
    destruct (RelNf_ErRel Hr) as [br Hbr].
    destruct (LvlNf_ErLvl Hl) as [bl Hbl].
    exists (rt_U br bl); constructor; assumption.
  (* tyok_El *)
  - intros G r l c Hc IHc E HE.
    destruct (NfCode_nf_indices Hc) as [Hr Hl].
    destruct (RelNf_ErRel Hr) as [br Hbr].
    destruct (LvlNf_ErLvl Hl) as [bl Hbl].
    destruct (IHc E HE) as [n Hn].
    exists (rt_El br bl n); constructor; assumption.
  (* nfcode_nat *)
  - intros G HG IHG E HE; exists rc_nat; constructor.
  (* nfcode_empty *)
  - intros G HG IHG E HE; exists rc_empty; constructor.
  (* nfcode_pi_rel *)
  - intros G rF lF lG F B HrF HlF HlG HF IHF HB IHB E HE.
    destruct (RelNf_ErRel HrF) as [brF HbrF].
    destruct (LvlNf_ErLvl HlF) as [blF HblF].
    destruct (IHF E HE) as [nF HnF].
    destruct (IHB _ (ErEnv_extC HE HbrF HblF HnF)) as [nB HnB].
    exists (rc_pi true nF nB); econstructor; eassumption.
  (* nfcode_pi_irr *)
  - intros G rF lF F B HrF HlF HF IHF HB IHB E HE.
    destruct (RelNf_ErRel HrF) as [brF HbrF].
    destruct (LvlNf_ErLvl HlF) as [blF HblF].
    destruct (IHF E HE) as [nF HnF].
    destruct (IHB _ (ErEnv_extC HE HbrF HblF HnF)) as [nB HnB].
    exists (rc_pi false nF nB); econstructor; eassumption.
  (* nfcode_var *)
  - intros G r l c Hv IHv E HE.
    destruct (IHv E HE) as [k Hk].
    exists (rc_var k); constructor; assumption.
  (* vart_hd *)
  - intros G i A A' HG IHG HA IHA HA' IHA' Heq E HE.
    inversion HE; subst.
    exists 0; econstructor; eassumption.
  (* vart_wkn *)
  - intros G i A x j B A' Hx IHx HB IHB HA' IHA' Heq E HE.
    inversion HE; subst.
    match goal with H : ErEnv G ?E0 |- _ => destruct (IHx E0 H) as [k Hk] end.
    exists (S k); econstructor; eassumption.
Qed.

Definition EnvOk_erase_total := proj1 Nf_erase_total.
Definition TyOk_erase_total := proj1 (proj2 Nf_erase_total).
Definition NfCode_erase_total := proj1 (proj2 (proj2 Nf_erase_total)).
Definition VarT_erase_total := proj1 (proj2 (proj2 (proj2 Nf_erase_total))).

(* =====================================================================
   7. The semantic input.

   [WknRepUnique] : the normal representative NAMED by [vart_hd] /
   [vart_wkn] for the weakening of ONE type [A] is unique.  This is the
   instance of design section 4's [TyOk_inj] that the erasure argument
   cannot see (header).  It is stated exactly in the shape in which the
   [eq_term] premises of [DttNf.v]'s [VarT] provide their arguments, so
   using it is a bare [apply]: nothing below reasons ABOUT [eq_term].
   ===================================================================== *)

Definition WknRepUnique : Prop :=
  forall G j B i A A1 A2,
    TyOk (oExt G j B) i A1 -> TyOk (oExt G j B) i A2 ->
    eqt (sTy (oExt G j B) i)
        (oTySubst (oExt G j B) G (oWkn G j B) i A) A1 ->
    eqt (sTy (oExt G j B) i)
        (oTySubst (oExt G j B) G (oWkn G j B) i A) A2 ->
    A1 = A2.

(* =====================================================================
   8. Injectivity.

   The order of business is forced by the shape of the erasure: a
   variable's index says nothing about the code grammar, so [ErVar]
   injectivity is proved first, by induction on the INDEX (not on a
   derivation); then [ErCode] injectivity by induction on the erased
   code; then [ErTy] and [ErEnv], which are one case analysis each.
   ===================================================================== *)

(* Variables.  The two [WknRepUnique] uses are the two clauses of
   [VarT]; everything else is the observation that the index arguments
   ([G], [i], [A] inside [oHd G i A] and [oWkn G j B]) are determined by
   the SHAPE of the normal environment, which is a syntactic term. *)
Theorem VarT_erase_inj (Hwk : WknRepUnique) :
  forall k E G i1 A1 x1 i2 A2 x2,
    VarT G i1 A1 x1 -> VarT G i2 A2 x2 ->
    ErVar E G i1 A1 x1 k -> ErVar E G i2 A2 x2 k ->
    i1 = i2 /\ A1 = A2 /\ x1 = x2.
Proof.
  induction k; intros E G i1 A1 x1 i2 A2 x2 Hv1 Hv2 He1 He2.
  - (* index 0: both are [hd] of the same [ext], so the terms agree on
       the nose; the types agree by [WknRepUnique]. *)
    inversion He1; subst; inversion He2; subst.
    inversion Hv1; subst; inversion Hv2; subst.
    repeat split; [ | eapply Hwk; eassumption ]; reflexivity.
  - (* index k+1: the inner variable is determined by the induction
       hypothesis -- INCLUDING its named type, which is a subterm of the
       [exp_subst] wrapper -- and then the outer type is determined by
       [WknRepUnique]. *)
    inversion He1; subst; inversion He2; subst.
    inversion Hv1; subst; inversion Hv2; subst.
    match goal with
    | H1 : VarT ?G0 _ _ _, H2 : VarT ?G0 _ _ _,
      E1 : ErVar ?E0 ?G0 _ _ _ k, E2 : ErVar ?E0 ?G0 _ _ _ k |- _ =>
        destruct (IHk _ _ _ _ _ _ _ _ H1 H2 E1 E2) as [? [? ?]]
    end.
    subst.
    repeat split; [ reflexivity | eapply Hwk; eassumption | reflexivity ].
Qed.

(* Codes.  The generalized statement determines the relevance and the
   level as well as the code, which is what the [Pi] case needs: neither
   [rF] nor [lF] survives erasure, so they have to be recovered from the
   erased DOMAIN, and [lG] from the erased CODOMAIN. *)
Theorem NfCode_erase_inj_gen (Hwk : WknRepUnique) :
  forall n E G r1 l1 c1 r2 l2 c2,
    NfCode G r1 l1 c1 -> NfCode G r2 l2 c2 ->
    ErCode E G r1 l1 c1 n -> ErCode E G r2 l2 c2 n ->
    r1 = r2 /\ l1 = l2 /\ c1 = c2.
Proof.
  induction n; intros E G r1 l1 c1 r2 l2 c2 Hc1 Hc2 He1 He2.
  - (* rc_var: both codes are variables, and [VarT_erase_inj] applies at
       the SAME type [oU G r l] only after that theorem has supplied the
       type equality; the relevance and level are then read off it. *)
    inversion He1; subst; inversion He2; subst.
    match goal with
    | H1 : ErVar _ _ _ _ c1 n, H2 : ErVar _ _ _ _ c2 n |- _ =>
        assert (VarT G (iCode l1) (oU G r1 l1) c1) as Hv1
          by (inversion Hc1; subst; try (inversion H1; fail); assumption);
        assert (VarT G (iCode l2) (oU G r2 l2) c2) as Hv2
          by (inversion Hc2; subst; try (inversion H2; fail); assumption);
        destruct (VarT_erase_inj Hwk _ _ _ _ _ _ _ _ _ Hv1 Hv2 H1 H2)
          as [Hi [HA Hx]]
    end.
    inversion Hi; inversion HA; subst; repeat split; reflexivity.
  - (* rc_nat *)
    inversion He1; subst;
      [ | match goal with H : ErVar _ _ _ _ _ _ |- _ => inversion H end ].
    inversion He2; subst;
      [ | match goal with H : ErVar _ _ _ _ _ _ |- _ => inversion H end ].
    repeat split; reflexivity.
  - (* rc_empty *)
    inversion He1; subst;
      [ | match goal with H : ErVar _ _ _ _ _ _ |- _ => inversion H end ].
    inversion He2; subst;
      [ | match goal with H : ErVar _ _ _ _ _ _ |- _ => inversion H end ].
    repeat split; reflexivity.
  - (* rc_pi: the bool of [rc_pi] selects the clause, so the two
       derivations use the same one. *)
    inversion He1; subst;
      try (match goal with H : ErVar _ _ _ _ _ _ |- _ => inversion H; fail end);
      inversion He2; subst;
      try (match goal with H : ErVar _ _ _ _ _ _ |- _ => inversion H; fail end);
      [ | ].
    + (* Pi_rel *)
      match goal with
      | HF1 : ErCode ?E ?G ?rF1 ?lF1 ?F1 n1, HF2 : ErCode ?E ?G ?rF2 ?lF2 ?F2 n1,
        HB1 : ErCode _ _ _ _ ?B1 n2, HB2 : ErCode _ _ _ _ ?B2 n2 |- _ =>
          let HN1 := fresh in let HN2 := fresh in
          assert (NfCode G rF1 lF1 F1 /\ NfCode (oExtC G rF1 lF1 F1) oRel l1 B1)
            as HN1 by (inversion Hc1; subst;
                       [ split; assumption
                       | match goal with
                         | H : VarT _ _ _ _ |- _ => inversion H end ]);
          assert (NfCode G rF2 lF2 F2 /\ NfCode (oExtC G rF2 lF2 F2) oRel l2 B2)
            as HN2 by (inversion Hc2; subst;
                       [ split; assumption
                       | match goal with
                         | H : VarT _ _ _ _ |- _ => inversion H end ]);
          destruct HN1 as [HNF1 HNB1]; destruct HN2 as [HNF2 HNB2];
          destruct (IHn1 _ _ _ _ _ _ _ _ HNF1 HNF2 HF1 HF2) as [? [? ?]]
      end.
      subst.
      match goal with
      | H1 : ErRel ?rF ?b1, H2 : ErRel ?rF ?b2 |- _ =>
          rewrite <- (ErRel_fun H1 H2) in *
      end.
      match goal with
      | H1 : ErLvl ?lF ?b1, H2 : ErLvl ?lF ?b2 |- _ =>
          rewrite <- (ErLvl_fun H1 H2) in *
      end.
      match goal with
      | HB1 : ErCode _ _ _ _ ?B1 n2, HB2 : ErCode _ _ _ _ ?B2 n2 |- _ =>
          destruct (IHn2 _ _ _ _ _ _ _ _ HNB1 HNB2 HB1 HB2) as [? [? ?]]
      end.
      subst; repeat split; reflexivity.
    + (* Pi_irr *)
      match goal with
      | HF1 : ErCode ?E ?G ?rF1 ?lF1 ?F1 n1, HF2 : ErCode ?E ?G ?rF2 ?lF2 ?F2 n1,
        HB1 : ErCode _ _ _ _ ?B1 n2, HB2 : ErCode _ _ _ _ ?B2 n2 |- _ =>
          let HN1 := fresh in let HN2 := fresh in
          assert (NfCode G rF1 lF1 F1 /\ NfCode (oExtC G rF1 lF1 F1) oIrr oL0 B1)
            as HN1 by (inversion Hc1; subst;
                       [ split; assumption
                       | match goal with
                         | H : VarT _ _ _ _ |- _ => inversion H end ]);
          assert (NfCode G rF2 lF2 F2 /\ NfCode (oExtC G rF2 lF2 F2) oIrr oL0 B2)
            as HN2 by (inversion Hc2; subst;
                       [ split; assumption
                       | match goal with
                         | H : VarT _ _ _ _ |- _ => inversion H end ]);
          destruct HN1 as [HNF1 HNB1]; destruct HN2 as [HNF2 HNB2];
          destruct (IHn1 _ _ _ _ _ _ _ _ HNF1 HNF2 HF1 HF2) as [? [? ?]]
      end.
      subst.
      match goal with
      | H1 : ErRel ?rF ?b1, H2 : ErRel ?rF ?b2 |- _ =>
          rewrite <- (ErRel_fun H1 H2) in *
      end.
      match goal with
      | H1 : ErLvl ?lF ?b1, H2 : ErLvl ?lF ?b2 |- _ =>
          rewrite <- (ErLvl_fun H1 H2) in *
      end.
      match goal with
      | HB1 : ErCode _ _ _ _ ?B1 n2, HB2 : ErCode _ _ _ _ ?B2 n2 |- _ =>
          destruct (IHn2 _ _ _ _ _ _ _ _ HNB1 HNB2 HB1 HB2) as [? [? ?]]
      end.
      subst; repeat split; reflexivity.
Qed.

Theorem NfCode_erase_inj (Hwk : WknRepUnique) E G r l c1 c2 n
  : NfCode G r l c1 -> NfCode G r l c2 ->
    ErCode E G r l c1 n -> ErCode E G r l c2 n ->
    c1 = c2.
Proof.
  intros; destruct (NfCode_erase_inj_gen Hwk _ _ _ _ _ _ _ _
                      ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(eassumption)) as [? [? ?]];
    assumption.
Qed.

Theorem TyOk_erase_inj_gen (Hwk : WknRepUnique) E G i1 A1 i2 A2 T
  : TyOk G i1 A1 -> TyOk G i2 A2 ->
    ErTy E G i1 A1 T -> ErTy E G i2 A2 T ->
    i1 = i2 /\ A1 = A2.
Proof.
  intros Ht1 Ht2 He1 He2.
  destruct T.
  - (* rt_U: nothing but the two bits survives, and both are injective. *)
    inversion He1; subst; inversion He2; subst.
    match goal with
    | H1 : ErRel ?r1 ?b, H2 : ErRel ?r2 ?b |- _ =>
        rewrite (ErRel_inj H1 H2) in *
    end.
    match goal with
    | H1 : ErLvl ?l1 ?b, H2 : ErLvl ?l2 ?b |- _ =>
        rewrite (ErLvl_inj H1 H2) in *
    end.
    split; reflexivity.
  - (* rt_El: the code is determined by [NfCode_erase_inj]. *)
    inversion He1; subst; inversion He2; subst.
    match goal with
    | H1 : ErRel ?r1 ?b, H2 : ErRel ?r2 ?b |- _ =>
        rewrite (ErRel_inj H1 H2) in *
    end.
    match goal with
    | H1 : ErLvl ?l1 ?b, H2 : ErLvl ?l2 ?b |- _ =>
        rewrite (ErLvl_inj H1 H2) in *
    end.
    apply TyOk_El_inv in Ht1; destruct Ht1 as [_ HN1].
    apply TyOk_El_inv in Ht2; destruct Ht2 as [_ HN2].
    match goal with
    | H1 : ErCode _ _ _ _ ?c1 ?n, H2 : ErCode _ _ _ _ ?c2 ?n |- _ =>
        rewrite (NfCode_erase_inj Hwk HN1 HN2 H1 H2) in *
    end.
    split; reflexivity.
Qed.

Theorem TyOk_erase_inj (Hwk : WknRepUnique) E G i A1 A2 T
  : TyOk G i A1 -> TyOk G i A2 ->
    ErTy E G i A1 T -> ErTy E G i A2 T ->
    A1 = A2.
Proof.
  intros; destruct (TyOk_erase_inj_gen Hwk ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(eassumption)) as [? ?];
    assumption.
Qed.

Theorem EnvOk_erase_inj (Hwk : WknRepUnique) :
  forall E G1 G2, EnvOk G1 -> EnvOk G2 -> ErEnv G1 E -> ErEnv G2 E -> G1 = G2.
Proof.
  induction E; intros G1 G2 H1 H2 He1 He2.
  - inversion He1; inversion He2; subst; reflexivity.
  - inversion He1; subst; inversion He2; subst.
    inversion H1; subst; inversion H2; subst.
    match goal with
    | Ha : ErEnv ?Ga E, Hb : ErEnv ?Gb E |- _ =>
        rewrite (IHE Ga Gb ltac:(assumption) ltac:(assumption) Ha Hb) in *
    end.
    match goal with
    | Ha : ErTy E ?G ?i1 ?A1 a, Hb : ErTy E ?G ?i2 ?A2 a |- _ =>
        destruct (TyOk_erase_inj_gen Hwk ltac:(eassumption) ltac:(eassumption)
                    Ha Hb) as [? ?]
    end.
    subst; reflexivity.
Qed.
