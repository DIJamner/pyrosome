Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.NormalForms.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 0.5a: ERASURE, the syntactic half of code
   rigidity.

   THE STRUCTURAL FACT (design section 2, visible in [NormalForms.v]'s
   [NfCode]): no eliminator of [ott_dtt] has a universe as its result
   type -- [app_rel], [app_irr] and [Emptyrec] all land in an [El] -- so
   the only NEUTRAL codes are variables and normal codes form the FREE
   grammar

       c ::= x | Nat G | Empty G | Pi_rel G rF lF lG c c | Pi_irr G rF lF c c

   Everything here is a consequence of that: the erasure below is exactly
   the "forget the index arguments, de-Bruijn the variables" map of that
   grammar, and it is injective on normal forms.  The claim held up under
   the induction: no clause of [ErCode] mentions [NeET] or [NfET], and
   the only neutral that has to be handled is a variable
   ([NfCode_of_var]).

   WHAT IS HERE.

     1. A first-order de Bruijn domain [rcode]/[rty]/[renv] with no index
        arguments: erasure drops every [G], every [i], and every
        [ty]/[exp] index the concrete syntax threads through its
        constructors, keeping the relevance/level bits and the code
        skeleton.

     2. Four erasure RELATIONS [ErEnv]/[ErTy]/[ErCode]/[ErVar], defined
        mutually and only on the Layer-1 normal syntax.  Relations rather
        than functions because the syntax carries index arguments that
        erasure drops.

     3. [Nf_erase_total]: every Layer-1 normal object has an erasure.
        UNCONDITIONAL.

     4. [Er_fun]: erasure is functional -- a normal object has at most
        one erasure.  UNCONDITIONAL.

   Injectivity is NOT here: it is proved in src/Pyrosome/Gluing/Dtt/Inj.v,
   over the rigid model's own interpretation relations.

   ONE DELIBERATE DESIGN POINT, a deviation from the datatype sketched in
   the task, so read it before consuming this file.

   (A) [rc_pi] RECORDS THE DOMAIN'S RELEVANCE AND LEVEL.

       [oPiRel G rF lF lG F B] carries [rF] and [lF] as SUBTERMS, so
       injectivity has to recover them from the erasure.  They cannot be
       recovered from the erased domain [nF]: when [F] is a variable, its
       relevance and level are those of its NAMED type, which
       erasure does not see and which the environment pins down only up
       to provable equality.  So [rc_pi] carries them:

           rc_pi (pi-relevance) (domain-relevance) (domain-level)
                 (domain-code) (codomain-code)

       This costs nothing semantically -- [rt_El brF blF nF] is exactly
       the entry the binder pushes onto the environment, so the two bits
       are already present in [renv] -- and it is what lets the [Pi]
       clauses of the injectivity argument go through with NO assumption
       about variables at all.  The Pi's own level [lG] is NOT recorded:
       it is the level index of the judgement, which the statement fixes.

   WHAT [ErVar E G i A x k] DOES NOT SAY: nothing whatsoever about [A],
   the NAMED normal representative of the variable's type.  [VarT]
   (NormalForms.v) pins that representative only by an [eq_term] premise,
   which is a fact about the equational theory and therefore the business
   of the rigid model, not of this file.

   Nothing below reasons ABOUT [eq_term], and no model is built.  There is
   no [Axiom] and no [Admitted].
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* =====================================================================
   1. The semantic domain: first-order de Bruijn codes and types.
   ===================================================================== *)

(* A normal code with all index arguments erased.  [rc_var] carries a de
   Bruijn INDEX (0 = the most recently bound variable).  For [rc_pi] the
   three bools are, in order: [true] for [Pi_rel] and [false] for
   [Pi_irr]; the domain's relevance; the domain's level.  See (A) in the
   header for why the last two are there. *)
Inductive rcode : Type :=
| rc_var : nat -> rcode
| rc_nat : rcode
| rc_empty : rcode
| rc_pi : bool -> bool -> bool -> rcode -> rcode -> rcode.

(* A normal type: a universe [U r l], or an [El] of a normal code.  In
   both cases the first [bool] is the relevance ([true] = [rel]) and the
   second the level ([true] = [L1]). *)
Inductive rty : Type :=
| rt_U : bool -> bool -> rty
| rt_El : bool -> bool -> rcode -> rty.

(* MOST-RECENT-FIRST, matching [ott]'s [ext]: the head of the list is the
   erased type bound by the innermost [ext]. *)
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

   Defined ONLY on the normal syntax of Layer 1: there is no clause for
   [ty_subst], [cmp], ... -- the erasure of an arbitrary term is
   meaningless and is never needed.  The four judgements are mutual
   because a type is an [El] of a code, a code may be a variable, and a
   variable's index is read against an environment of types.

   Note what [ErVar E G i A x k] does NOT say: nothing whatsoever about
   [A], the NAMED normal representative of the variable's type.  It could
   not; see (B) in the header.
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
   erases to [n].  Five clauses for the five productions of the free code
   grammar. *)
with ErCode : renv -> term -> term -> term -> term -> rcode -> Prop :=
| ercode_nat : forall E G,
    ErCode E G oRel oL0 (oNat G) rc_nat
| ercode_empty : forall E G,
    ErCode E G oIrr oL0 (oEmpty G) rc_empty
| ercode_pi_rel : forall E G rF lF lG F B brF blF nF nB,
    ErRel rF brF -> ErLvl lF blF ->
    ErCode E G rF lF F nF ->
    ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oRel lG B nB ->
    ErCode E G oRel lG (oPiRel G rF lF lG F B) (rc_pi true brF blF nF nB)
| ercode_pi_irr : forall E G rF lF F B brF blF nF nB,
    ErRel rF brF -> ErLvl lF blF ->
    ErCode E G rF lF F nF ->
    ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oIrr oL0 B nB ->
    ErCode E G oIrr oL0 (oPiIrr G rF lF F B) (rc_pi false brF blF nF nB)
| ercode_var : forall E G r l c k,
    ErVar E G (iCode l) (oU G r l) c k ->
    ErCode E G r l c (rc_var k)

(* [ErVar E G i A x k] : [x] is the variable at de Bruijn index [k].
   [hd] is 0 and each [exp_subst (wkn ...)] layer is +1, so the index
   counts the [wkn]s, i.e. the distance from the binder. *)
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

(* The erasure of the environment extension every binder makes. *)
Lemma ErEnv_extC E G rF lF F brF blF nF
  : ErEnv G E -> ErRel rF brF -> ErLvl lF blF -> ErCode E G rF lF F nF ->
    ErEnv (oExtC G rF lF F) (rt_El brF blF nF :: E).
Proof.
  intros; unfold oExtC; econstructor; [ eassumption | ].
  econstructor; eassumption.
Qed.

(* =====================================================================
   4. Inversions.

   All of them are one [inversion] away, but stating them keeps every
   proof below free of generated hypothesis names.  "subj" = inverted on
   the shape of the SUBJECT term; the others are inverted on the shape of
   the ERASURE.

   The recurring side condition is that a variable is never a canonical
   form: [ErVar]'s subject is an [oHd] or an [oExpSubst], so an [ErVar]
   hypothesis about an [oNat]/[oEmpty]/[oPiRel]/[oPiIrr] is absurd.  That
   is [er_absurd_var]; its [VarT] analogue is [nf_absurd_var].
   ===================================================================== *)

Ltac er_absurd_var :=
  match goal with H : ErVar _ _ _ _ _ _ |- _ => solve [ inversion H ] end.

Ltac nf_absurd_var :=
  match goal with H : VarT _ _ _ _ |- _ => solve [ inversion H ] end.

(* ---- [ErEnv] ---- *)

Lemma ErEnv_emp_inv E : ErEnv oEmp E -> E = [].
Proof. inversion 1; reflexivity. Qed.

Lemma ErEnv_ext_inv G i A E
  : ErEnv (oExt G i A) E ->
    exists T E0, E = T :: E0 /\ ErEnv G E0 /\ ErTy E0 G i A T.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ErEnv_nil_inv G : ErEnv G [] -> G = oEmp.
Proof. inversion 1; reflexivity. Qed.

Lemma ErEnv_cons_inv G T E
  : ErEnv G (T :: E) ->
    exists G0 i A, G = oExt G0 i A /\ ErEnv G0 E /\ ErTy E G0 i A T.
Proof. inversion 1; subst; eauto 10. Qed.

(* ---- [ErTy], on the erasure ---- *)

Lemma ErTy_U_inv E G i A br bl
  : ErTy E G i A (rt_U br bl) ->
    exists r l, A = oU G r l /\ i = iCode l /\ ErRel r br /\ ErLvl l bl.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ErTy_El_inv E G i A br bl n
  : ErTy E G i A (rt_El br bl n) ->
    exists r l c, A = oEl G r l c /\ i = iEl r l
                  /\ ErRel r br /\ ErLvl l bl /\ ErCode E G r l c n.
Proof. inversion 1; subst; eauto 10. Qed.

(* ---- [ErTy], on the subject ---- *)

Lemma ErTy_subj_U_inv E G i G0 r l T
  : ErTy E G i (oU G0 r l) T ->
    exists br bl, T = rt_U br bl /\ ErRel r br /\ ErLvl l bl.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma ErTy_subj_El_inv E G i G0 r l c T
  : ErTy E G i (oEl G0 r l c) T ->
    exists br bl n, T = rt_El br bl n
                    /\ ErRel r br /\ ErLvl l bl /\ ErCode E G r l c n.
Proof. inversion 1; subst; eauto 10. Qed.

(* ---- [ErCode], on the erasure ---- *)

Lemma ErCode_var_inv E G r l c k
  : ErCode E G r l c (rc_var k) -> ErVar E G (iCode l) (oU G r l) c k.
Proof. inversion 1; subst; assumption. Qed.

Lemma ErCode_nat_inv E G r l c
  : ErCode E G r l c rc_nat -> r = oRel /\ l = oL0 /\ c = oNat G.
Proof. inversion 1; subst; repeat split. Qed.

Lemma ErCode_empty_inv E G r l c
  : ErCode E G r l c rc_empty -> r = oIrr /\ l = oL0 /\ c = oEmpty G.
Proof. inversion 1; subst; repeat split. Qed.

Lemma ErCode_pi_true_inv E G r l c brF blF nF nB
  : ErCode E G r l c (rc_pi true brF blF nF nB) ->
    exists rF lF F B,
      r = oRel /\ c = oPiRel G rF lF l F B
      /\ ErRel rF brF /\ ErLvl lF blF
      /\ ErCode E G rF lF F nF
      /\ ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oRel l B nB.
Proof. inversion 1; subst; eauto 20. Qed.

Lemma ErCode_pi_false_inv E G r l c brF blF nF nB
  : ErCode E G r l c (rc_pi false brF blF nF nB) ->
    exists rF lF F B,
      r = oIrr /\ l = oL0 /\ c = oPiIrr G rF lF F B
      /\ ErRel rF brF /\ ErLvl lF blF
      /\ ErCode E G rF lF F nF
      /\ ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oIrr oL0 B nB.
Proof. inversion 1; subst; eauto 20. Qed.

(* ---- [ErCode], on the subject ---- *)

Lemma ErCode_subj_nat_inv E G r l G0 n
  : ErCode E G r l (oNat G0) n -> n = rc_nat.
Proof. inversion 1; subst; try reflexivity; er_absurd_var. Qed.

Lemma ErCode_subj_empty_inv E G r l G0 n
  : ErCode E G r l (oEmpty G0) n -> n = rc_empty.
Proof. inversion 1; subst; try reflexivity; er_absurd_var. Qed.

Lemma ErCode_subj_pi_rel_inv E G r l G0 rF lF lG F B n
  : ErCode E G r l (oPiRel G0 rF lF lG F B) n ->
    exists brF blF nF nB,
      n = rc_pi true brF blF nF nB
      /\ ErRel rF brF /\ ErLvl lF blF
      /\ ErCode E G rF lF F nF
      /\ ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oRel lG B nB.
Proof. inversion 1; subst; try er_absurd_var; eauto 20. Qed.

Lemma ErCode_subj_pi_irr_inv E G r l G0 rF lF F B n
  : ErCode E G r l (oPiIrr G0 rF lF F B) n ->
    exists brF blF nF nB,
      n = rc_pi false brF blF nF nB
      /\ ErRel rF brF /\ ErLvl lF blF
      /\ ErCode E G rF lF F nF
      /\ ErCode (rt_El brF blF nF :: E) (oExtC G rF lF F) oIrr oL0 B nB.
Proof. inversion 1; subst; try er_absurd_var; eauto 20. Qed.

Lemma ErCode_subj_var_inv E G r l c n E' i A k
  : ErVar E' G i A c k -> ErCode E G r l c n ->
    exists k', n = rc_var k' /\ ErVar E G (iCode l) (oU G r l) c k'.
Proof. intros Hv Hc; destruct Hc; try solve [ inversion Hv ]; eauto. Qed.

(* ---- [ErVar] ---- *)

Lemma ErVar_0_inv E Gx i A x
  : ErVar E Gx i A x 0 ->
    exists G0 i0 A0 T E0,
      E = T :: E0 /\ Gx = oExt G0 i0 A0 /\ i = i0 /\ x = oHd G0 i0 A0.
Proof. inversion 1; subst; eauto 20. Qed.

Lemma ErVar_S_inv E Gx i A x k
  : ErVar E Gx i A x (S k) ->
    exists G0 j B A0 y TB E0,
      E = TB :: E0 /\ Gx = oExt G0 j B
      /\ x = oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i A0 y
      /\ ErVar E0 G0 i A0 y k.
Proof. inversion 1; subst; eauto 20. Qed.

Lemma ErVar_subj_hd_inv E Gx i A G0 i0 A0 k
  : ErVar E Gx i A (oHd G0 i0 A0) k -> k = 0.
Proof. inversion 1; reflexivity. Qed.

Lemma ErVar_subj_wkn_inv E Gx i A G0 j B i0 A0 x k
  : ErVar E Gx i A (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 x) k ->
    exists E0 TB k0, k = S k0 /\ E = TB :: E0 /\ ErVar E0 G0 i0 A0 x k0.
Proof. inversion 1; subst; eauto 10. Qed.

(* ---- Layer-1 judgements ---- *)

Lemma EnvOk_ext_inv G i A : EnvOk (oExt G i A) -> EnvOk G /\ TyOk G i A.
Proof. inversion 1; subst; split; assumption. Qed.

(* A variable's type is always a normal type: every [VarT] clause carries
   [TyOk] of its conclusion type. *)
Lemma VarT_TyOk G i A x : VarT G i A x -> TyOk G i A.
Proof. inversion 1; assumption. Qed.

Lemma VarT_hd_inv Gx i A G0 i0 A0
  : VarT Gx i A (oHd G0 i0 A0) ->
    Gx = oExt G0 i0 A0 /\ i = i0
    /\ TyOk (oExt G0 i0 A0) i0 A
    /\ eqt (sTy (oExt G0 i0 A0) i0)
           (oTySubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0) A.
Proof. inversion 1; subst; repeat split; assumption. Qed.

Lemma VarT_wkn_inv Gx i A G0 j B i0 A0 x
  : VarT Gx i A (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 x) ->
    Gx = oExt G0 j B /\ i = i0
    /\ VarT G0 i0 A0 x
    /\ TyOk (oExt G0 j B) i0 A
    /\ eqt (sTy (oExt G0 j B) i0)
           (oTySubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0) A.
Proof. inversion 1; subst; repeat split; assumption. Qed.

Lemma TyOk_U_inv G i r l
  : TyOk G i (oU G r l) -> i = iCode l /\ EnvOk G /\ RelNf r /\ LvlNf l.
Proof. inversion 1; subst; repeat split; assumption. Qed.

Lemma TyOk_El_inv G i r l c
  : TyOk G i (oEl G r l c) -> i = iEl r l /\ NfCode G r l c.
Proof. inversion 1; subst; split; [ reflexivity | assumption ]. Qed.

(* A normal type determines its own info index: [TyOk] pins [i] to
   [iCode l] at a universe and to [iEl r l] at an [El].  (Layer 1 does
   not normalize infos, but it does pin each canonical form to the
   spelling its own former uses, which is all that is needed here.) *)
Lemma TyOk_info_det G i1 i2 A : TyOk G i1 A -> TyOk G i2 A -> i1 = i2.
Proof. intros H1 H2; destruct H1; inversion H2; subst; reflexivity. Qed.

(* The only neutral code is a variable: if a normal code happens to have
   the shape of a variable, its derivation is [nfcode_var]. *)
Lemma NfCode_of_var G r l c E i A k
  : NfCode G r l c -> ErVar E G i A c k -> VarT G (iCode l) (oU G r l) c.
Proof. destruct 1; intro Hv; try solve [ inversion Hv ]; assumption. Qed.

Lemma NfCode_pi_rel_inv G r l G0 rF lF lG F B
  : NfCode G r l (oPiRel G0 rF lF lG F B) ->
    r = oRel /\ l = lG /\ NfCode G rF lF F
    /\ NfCode (oExtC G rF lF F) oRel lG B.
Proof.
  inversion 1; subst; try nf_absurd_var; repeat split; assumption.
Qed.

Lemma NfCode_pi_irr_inv G r l G0 rF lF F B
  : NfCode G r l (oPiIrr G0 rF lF F B) ->
    r = oIrr /\ l = oL0 /\ NfCode G rF lF F
    /\ NfCode (oExtC G rF lF F) oIrr oL0 B.
Proof.
  inversion 1; subst; try nf_absurd_var; repeat split; assumption.
Qed.

(* The relevance and level of a normal code are themselves normal.  The
   variable case goes through [VarT_TyOk]: a code variable's type is
   [oU G r l], whose only [TyOk] derivation is [tyok_U]. *)
Lemma NfCode_nf_indices G r l c : NfCode G r l c -> RelNf r /\ LvlNf l.
Proof.
  destruct 1; try (split; solve [ constructor | assumption ]).
  match goal with
  | H : VarT _ _ _ _ |- _ =>
      apply VarT_TyOk in H; apply TyOk_U_inv in H;
      destruct H as [_ [_ [? ?]]]; split; assumption
  end.
Qed.

(* =====================================================================
   5. Erasure is functional.  UNCONDITIONAL.
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
  - intros E2 H; apply ErEnv_emp_inv in H; auto.
  (* erenv_ext *)
  - intros G i A E T HE IHE HT IHT E2 H.
    apply ErEnv_ext_inv in H; destruct H as [T2 [E0 [-> [HE0 HT0]]]].
    pose proof (IHE _ HE0) as Heq; subst.
    f_equal; apply IHT; assumption.
  (* erty_U *)
  - intros E G r l br bl Hr Hl T2 H.
    apply ErTy_subj_U_inv in H; destruct H as [br2 [bl2 [-> [Hr2 Hl2]]]].
    f_equal; [ eapply ErRel_fun | eapply ErLvl_fun ]; eassumption.
  (* erty_El *)
  - intros E G r l c br bl n Hr Hl Hc IHc T2 H.
    apply ErTy_subj_El_inv in H; destruct H as [br2 [bl2 [n2 [-> [Hr2 [Hl2 Hc2]]]]]].
    f_equal; [ eapply ErRel_fun | eapply ErLvl_fun | apply IHc ]; eassumption.
  (* ercode_nat *)
  - intros E G n2 H; apply ErCode_subj_nat_inv in H; auto.
  (* ercode_empty *)
  - intros E G n2 H; apply ErCode_subj_empty_inv in H; auto.
  (* ercode_pi_rel *)
  - intros E G rF lF lG F B brF blF nF nB HrF HlF HF IHF HB IHB n2 H.
    apply ErCode_subj_pi_rel_inv in H.
    destruct H as [brF2 [blF2 [nF2 [nB2 [-> [HrF2 [HlF2 [HF2 HB2]]]]]]]].
    pose proof (IHF _ HF2) as Heq; subst nF2.
    pose proof (ErRel_fun HrF HrF2) as Heq1; subst brF2.
    pose proof (ErLvl_fun HlF HlF2) as Heq2; subst blF2.
    f_equal; apply IHB; assumption.
  (* ercode_pi_irr *)
  - intros E G rF lF F B brF blF nF nB HrF HlF HF IHF HB IHB n2 H.
    apply ErCode_subj_pi_irr_inv in H.
    destruct H as [brF2 [blF2 [nF2 [nB2 [-> [HrF2 [HlF2 [HF2 HB2]]]]]]]].
    pose proof (IHF _ HF2) as Heq; subst nF2.
    pose proof (ErRel_fun HrF HrF2) as Heq1; subst brF2.
    pose proof (ErLvl_fun HlF HlF2) as Heq2; subst blF2.
    f_equal; apply IHB; assumption.
  (* ercode_var *)
  - intros E G r l c k Hv IHv n2 H.
    destruct (ErCode_subj_var_inv Hv H) as [k2 [-> Hv2]].
    f_equal; apply IHv; assumption.
  (* ervar_hd *)
  - intros E G i A A' T HT IHT k2 H; apply ErVar_subj_hd_inv in H; auto.
  (* ervar_wkn *)
  - intros E G i A x j B A' TB k Hv IHv HT IHT k2 H.
    apply ErVar_subj_wkn_inv in H.
    destruct H as [E0 [TB2 [k0 [-> [Heq Hv2]]]]].
    inversion Heq; subst.
    f_equal; apply IHv; assumption.
Qed.

Definition ErEnv_fun := proj1 Er_fun.
Definition ErTy_fun := proj1 (proj2 Er_fun).
Definition ErCode_fun := proj1 (proj2 (proj2 Er_fun)).
Definition ErVar_fun := proj2 (proj2 (proj2 Er_fun)).

(* =====================================================================
   6. Totality: every normal object has an erasure.  UNCONDITIONAL.

   [NeET]/[NfET] play no role -- a code never contains a neutral that is
   not a variable, which is the structural fact this layer rests on -- so
   their components of the mutual scheme are [True].
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
  - intros G i A HG IHG HA IHA.
    destruct IHG as [E HE].
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
    exists (rc_pi true brF blF nF nB); econstructor; eassumption.
  (* nfcode_pi_irr *)
  - intros G rF lF F B HrF HlF HF IHF HB IHB E HE.
    destruct (RelNf_ErRel HrF) as [brF HbrF].
    destruct (LvlNf_ErLvl HlF) as [blF HblF].
    destruct (IHF E HE) as [nF HnF].
    destruct (IHB _ (ErEnv_extC HE HbrF HblF HnF)) as [nB HnB].
    exists (rc_pi false brF blF nF nB); econstructor; eassumption.
  (* nfcode_var *)
  - intros G r l c Hv IHv E HE.
    destruct (IHv E HE) as [k Hk].
    exists (rc_var k); constructor; assumption.
  (* vart_hd *)
  - intros G i A A' HG IHG HA IHA HA' IHA' Heq E HE.
    apply ErEnv_ext_inv in HE; destruct HE as [T [E0 [-> [HE0 HT0]]]].
    exists 0; econstructor; eassumption.
  (* vart_wkn *)
  - intros G i A x j B A' Hx IHx HB IHB HA' IHA' Heq E HE.
    apply ErEnv_ext_inv in HE; destruct HE as [TB [E0 [-> [HE0 HT0]]]].
    destruct (IHx E0 HE0) as [k Hk].
    exists (S k); econstructor; eassumption.
Qed.

Definition EnvOk_erase_total := proj1 Nf_erase_total.
Definition TyOk_erase_total := proj1 (proj2 Nf_erase_total).
Definition NfCode_erase_total := proj1 (proj2 (proj2 Nf_erase_total)).
Definition VarT_erase_total := proj1 (proj2 (proj2 (proj2 Nf_erase_total))).

