Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Values.
Import Core.Notations.

(* =====================================================================
   WEAKENING OF VALUES, AS A DETERMINISTIC MUTUAL RELATION.

   T3 established that weakening cannot be a Gallina [Fixpoint] on the
   annotated syntax: the recursion on the weakening [w] and the recursion
   on the subject call each other and neither argument decreases
   (WkVal.v's header quotes the guard checker).  The decreasing structure
   is the DERIVATION, so this file recurses on derivations natively --
   design.md section 13b's own notion of "functional", where determinism
   (its property (D)) is a THEOREM rather than a definitional accident.

   THE FACTORIZATION THAT MAKES THIS SMALL.  The obvious reading of
   "relational" is one enormous block containing the value judgements AND
   their weakening (13 inductives, ~56 clauses), because [Values.v]'s
   [valvar_hd] needs the weakened type as its index.  That is not
   necessary.  The weakening relation NEVER MENTIONS THE VALUE
   JUDGEMENTS -- it is syntax-directed on [w] and on the subject -- so it
   is a self-contained block that can be defined FIRST and used by
   [Values.v] as a premise.  Three judgements suffice:

     WkTy  D G w i A A'        types
     WkTm  D G w e e'          codes AND elements, in ONE judgement
     WkVar D G w i A A' x x'   variables

   [WkTm] needs no type index: every annotation a weakened code or
   element carries is already stored in the subject.  Only VARIABLES
   introduce a new annotation -- the type of the inner variable in the
   smaller context -- which is why they, and only they, are typed.
   That observation is what collapses 13 inductives to 3.

   CODES AND ELEMENTS SHARE ONE JUDGEMENT because their head symbols are
   pairwise distinct ([Nat]/[Empty]/[Pi_rel]/[Pi_irr]/[Id] against
   [zero]/[suc]/[*]/[lam_rel]/[app_rel]/[Emptyrec]/[hd]/[exp_subst]), so
   nothing is lost and determinism becomes a head-symbol argument.  This
   is also what makes the code/element mutual recursion that design.md
   section 14d calls "the real structural cost of [Id]" completely
   painless: [wktm_id] weakens an [Id]'s two codes and its two ELEMENT
   endpoints with the same relation, in one clause.

   The *-collapse is what keeps the element half short: there is no
   [lam_irr], no [app_irr] and no [Idcong] clause, because those all live
   at irrelevant [El]s where the only value is [*], and [*] weakens to
   [*] ([wktm_star]).
   ===================================================================== *)

(* The lifted weakening, verbatim from NfWk.v:141.  (WkVal.v has its own
   copy; this file deliberately does not depend on WkVal.v, which drags in
   Wf.v and Eqns.v for its equational hypotheses.) *)
Definition oLiftW (D G w i A A' : term) : term :=
  oSnoc (oExt D i A') G i A (oCmp (oExt D i A') D G (oWkn D i A') w)
    (oHd D i A').

(* ================================================================== *)
(* The block                                                           *)
(* ================================================================== *)

(* A FOURTH judgement, [VarTy], is forced, and finding out why was the
   informative part of writing this file.  The first draft had a purely
   syntactic [IsVar] side condition on the two clauses that dispatch on
   [w] alone, and left the variable's type [A] otherwise unconstrained.
   Determinism of [WkTm] is then FALSE: [wkvar_wkn] emits
   [exp_subst wkn i A x], whose annotation is [A], so the output depends
   on a type the relation never pinned down.  [VarTy G i A x] -- "[x] is a
   variable whose value type in [G] is [A]" -- pins it, and it is exactly
   [Values.v]'s [ValVar] minus the value-hood side conditions, which is
   where [Values.v]'s [wkTy] parameter goes when this is wired up. *)

Inductive WkTy : term -> term -> term -> term -> term -> term -> Prop :=
| wkty_U : forall D G w r l,
    WkTy D G w (iCode l) (oU G r l) (oU D r l)
| wkty_El : forall D G w r l c c',
    WkTm D G w c c' ->
    WkTy D G w (iEl r l) (oEl G r l c) (oEl D r l c')

with WkTm : term -> term -> term -> term -> term -> Prop :=
(* ---- codes ---- *)
| wktm_nat : forall D G w, WkTm D G w (oNat G) (oNat D)
| wktm_empty : forall D G w, WkTm D G w (oEmpty G) (oEmpty D)
| wktm_pi_rel : forall D G w rF lF lG F B F' B',
    WkTm D G w F F' ->
    WkTm (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')) B B' ->
    WkTm D G w (oPiRel G rF lF lG F B) (oPiRel D rF lF lG F' B')
| wktm_pi_irr : forall D G w rF lF F B F' B',
    WkTm D G w F F' ->
    WkTm (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')) B B' ->
    WkTm D G w (oPiIrr G rF lF F B) (oPiIrr D rF lF F' B')
(* THE STUCK-[Id] CLAUSE, and the whole of the code/element mutual
   recursion.  [A] and [B] are codes, [t] and [u] are ELEMENTS, and one
   judgement weakens all four. *)
| wktm_id : forall D G w l A B t u A' B' t' u',
    WkTm D G w A A' -> WkTm D G w B B' ->
    WkTm D G w t t' -> WkTm D G w u u' ->
    WkTm D G w (oIdEq G l A B t u) (oIdEq D l A' B' t' u')
(* ---- elements ---- *)
| wktm_zero : forall D G w, WkTm D G w (oZero G) (oZero D)
| wktm_suc : forall D G w n n',
    WkTm D G w n n' -> WkTm D G w (oSuc G n) (oSuc D n')
(* The entire irrelevant fragment, in one clause. *)
| wktm_star : forall D G w, WkTm D G w oStar oStar
| wktm_lam_rel : forall D G w rF lF lG F B t F' B' t',
    WkTm D G w F F' ->
    WkTm (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')) B B' ->
    WkTm (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')) t t' ->
    WkTm D G w (oLamRel G rF lF lG F B t) (oLamRel D rF lF lG F' B' t')
| wktm_app_rel : forall D G w rF lF lG F B f a F' B' f' a',
    WkTm D G w F F' ->
    WkTm (oExtC D rF lF F') (oExtC G rF lF F)
         (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F')) B B' ->
    WkTm D G w f f' -> WkTm D G w a a' ->
    WkTm D G w (oAppRel G rF lF lG F B f a) (oAppRel D rF lF lG F' B' f' a')
(* [Emptyrec]'s argument is [*] on both sides: it is (E2)'s second
   erasable position, and the value grammar writes it literally. *)
| wktm_emptyrec : forall D G w rA lA A A',
    WkTm D G w A A' ->
    WkTm D G w (oEmptyrec G rA lA A oStar) (oEmptyrec D rA lA A' oStar)
(* ---- variables ----

   SPLIT ON THE HEAD SYMBOL, not left as one clause over an unconstrained
   subject.  A single [wktm_var : WkVar … x x' -> WkTm D G w x x'] is
   syntactically overlapping with EVERY other clause, since [x] is a bare
   variable of the inductive, so [inversion] on [WkTm D G w (oNat G) e2]
   spawns a bogus [WkVar] subcase for each of the twelve.  Splitting on
   [oHd] / [oExpSubst] makes the whole judgement head-directed, which is
   what turns determinism into a discrimination argument. *)
| wktm_var_hd : forall D G w i A A' G0 i0 A0 x',
    WkVar D G w i A A' (oHd G0 i0 A0) x' ->
    WkTm D G w (oHd G0 i0 A0) x'
| wktm_var_wkn : forall D G w i A A' G0 j B i0 A0 y x',
    WkVar D G w i A A'
          (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y) x' ->
    WkTm D G w (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y) x'

(* [WkVar D G w i A A' x x'] : [x], a variable of value type [A] over [G],
   weakens along [w] to [x'] of value type [A'] over [D].  The five
   clauses are the four constructors of NormalForms.v's [Wk] class, with
   the lifted one split on the shape of [x] -- under a lift [hd] goes to
   [hd] and a weakened variable goes one level down.  This is exactly the
   dispatch that cannot be a [Fixpoint]. *)
with WkVar : term -> term -> term -> term -> term -> term -> term -> term
             -> Prop :=
| wkvar_id : forall G i A x,
    VarTy G i A x -> WkVar G G (oId G) i A A x x
| wkvar_wkn : forall G j B i A A' x,
    VarTy G i A x ->
    WkTy (oExt G j B) G (oWkn G j B) i A A' ->
    WkVar (oExt G j B) G (oWkn G j B) i A A' x
          (oExpSubst (oExt G j B) G (oWkn G j B) i A x)
| wkvar_cmp : forall D0 j B G w0 i A A0 A' x x0,
    WkVar D0 G w0 i A A0 x x0 ->
    WkTy (oExt D0 j B) D0 (oWkn D0 j B) i A0 A' ->
    WkVar (oExt D0 j B) G
          (oCmp (oExt D0 j B) D0 G (oWkn D0 j B) w0) i A A' x
          (oExpSubst (oExt D0 j B) D0 (oWkn D0 j B) i A0 x0)
| wkvar_lift_hd : forall D0 G0 w0 i0 A0 A0' A A',
    WkTy D0 G0 w0 i0 A0 A0' ->
    WkTy (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0 A ->
    WkTy (oExt D0 i0 A0') D0 (oWkn D0 i0 A0') i0 A0' A' ->
    WkVar (oExt D0 i0 A0') (oExt G0 i0 A0) (oLiftW D0 G0 w0 i0 A0 A0')
          i0 A A' (oHd G0 i0 A0) (oHd D0 i0 A0')
| wkvar_lift_wkn : forall D0 G0 w0 i0 A0 A0' i Ay Ay' y y' A A',
    WkVar D0 G0 w0 i Ay Ay' y y' ->
    WkTy (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i Ay A ->
    WkTy (oExt D0 i0 A0') D0 (oWkn D0 i0 A0') i Ay' A' ->
    WkVar (oExt D0 i0 A0') (oExt G0 i0 A0) (oLiftW D0 G0 w0 i0 A0 A0')
          i A A'
          (oExpSubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i Ay y)
          (oExpSubst (oExt D0 i0 A0') D0 (oWkn D0 i0 A0') i Ay' y')

(* [VarTy G i A x] : [x] is a variable whose value type in [G] is [A].
   A variable's type is always a weakened one, which is why this needs
   [WkTy] and hence belongs in the block. *)
with VarTy : term -> term -> term -> term -> Prop :=
| varty_hd : forall G i A0 A,
    WkTy (oExt G i A0) G (oWkn G i A0) i A0 A ->
    VarTy (oExt G i A0) i A (oHd G i A0)
| varty_wkn : forall G j B i A A' x,
    VarTy G i A x ->
    WkTy (oExt G j B) G (oWkn G j B) i A A' ->
    VarTy (oExt G j B) i A' (oExpSubst (oExt G j B) G (oWkn G j B) i A x).

Scheme WkTy_min := Minimality for WkTy Sort Prop
  with WkTm_min := Minimality for WkTm Sort Prop
  with WkVar_min := Minimality for WkVar Sort Prop
  with VarTy_min := Minimality for VarTy Sort Prop.

Combined Scheme Wk_mutind from WkTy_min, WkTm_min, WkVar_min, VarTy_min.

(* ================================================================== *)
(* DETERMINISM -- design.md section 13b's property (D)                 *)
(* ================================================================== *)

(* The whole argument is head symbols: no two clauses of [WkTm] can fire
   on the same subject, and no two clauses of [WkVar] on the same [w] and
   subject.  [inversion] does the discrimination and the induction
   hypotheses do the rest. *)
(* NOTE THE STRENGTHENED [WkVar] CONJUNCT: it concludes [i = i2] and
   [A = A2] as well, i.e. a variable's INPUT type is determined by its
   context and the variable itself.  That is not a bonus, it is what
   breaks the circularity.  [WkTm]'s two variable clauses quantify [i] and
   [A] existentially, so [WkTm] determinism needs variable-type uniqueness;
   proving it as a separate theorem needs [WkTy] determinism, which needs
   [WkTm] determinism.  Folding it into the same induction closes the
   loop, because at every [WkVar] clause the required uniqueness comes
   from an induction hypothesis of a SUB-derivation ([VarTy] at
   [wkvar_id]/[wkvar_wkn], [WkVar] at [wkvar_cmp]/[wkvar_lift_wkn], and
   [WkTy] at [wkvar_lift_hd]). *)
Theorem Wk_det :
  (forall D G w i A A', WkTy D G w i A A' ->
     forall A2, WkTy D G w i A A2 -> A' = A2)
  /\ (forall D G w e e', WkTm D G w e e' ->
     forall e2, WkTm D G w e e2 -> e' = e2)
  /\ (forall D G w i A A' x x', WkVar D G w i A A' x x' ->
     forall i2 A2 A2' x2, WkVar D G w i2 A2 A2' x x2 ->
       i = i2 /\ A = A2 /\ A' = A2' /\ x' = x2)
  /\ (forall G i A x, VarTy G i A x ->
     forall i2 A2, VarTy G i2 A2 x -> i = i2 /\ A = A2).
Proof.
  apply Wk_mutind; intros;
    (* (1) Drop the clause's OWN premises.  Each is paired with an
       induction hypothesis and would otherwise be matched by it, yielding
       a trivial equation and consuming the hypothesis before the second
       derivation's premise can use it. *)
    repeat match goal with
    | Hp : WkTy ?D ?G ?w ?i ?A ?X,
      _ : forall z, WkTy ?D ?G ?w ?i ?A z -> ?X = z |- _ => clear Hp
    | Hp : WkTm ?D ?G ?w ?e ?X,
      _ : forall z, WkTm ?D ?G ?w ?e z -> ?X = z |- _ => clear Hp
    | Hp : WkVar ?D ?G ?w _ _ _ ?x _,
      _ : forall a b c d, WkVar ?D ?G ?w a b c ?x d -> _ |- _ => clear Hp
    | Hp : VarTy ?G _ _ ?x,
      _ : forall a b, VarTy ?G a b ?x -> _ |- _ => clear Hp
    end;
    (* (2) Invert the second derivation.  Every judgement is head-directed
       -- in the subject for [WkTy]/[WkTm]/[VarTy], in the weakening and
       then the subject for [WkVar] -- so all but one clause dies here. *)
    match goal with
    | H : WkTy _ _ _ _ _ ?X |- _ = ?X => inversion H; subst
    | H : WkTm _ _ _ _ ?X |- _ = ?X => inversion H; subst
    | H : WkVar _ _ _ ?I ?A ?B ?x ?Y
      |- _ = ?I /\ _ = ?A /\ _ = ?B /\ _ = ?Y => inversion H; subst
    | H : VarTy _ ?I ?A ?x |- _ = ?I /\ _ = ?A => inversion H; subst
    end;
    (* (3) Feed the surviving premises to the induction hypotheses. *)
    repeat match goal with
    | IH : forall z, WkTy ?D ?G ?w ?i ?A z -> _,
      H : WkTy ?D ?G ?w ?i ?A _ |- _ => specialize (IH _ H); subst
    | IH : forall z, WkTm ?D ?G ?w ?e z -> _,
      H : WkTm ?D ?G ?w ?e _ |- _ => specialize (IH _ H); subst
    | IH : forall a b c d, WkVar ?D ?G ?w a b c ?x d -> _,
      H : WkVar ?D ?G ?w _ _ _ ?x _ |- _ =>
        specialize (IH _ _ _ _ H); destruct IH as [? [? [? ?]]]; subst
    | IH : forall a b, VarTy ?G a b ?x -> _,
      H : VarTy ?G _ _ ?x |- _ =>
        specialize (IH _ _ H); destruct IH as [? ?]; subst
    end;
    repeat split; auto.
Qed.

Definition WkTy_det := proj1 Wk_det.
Definition WkTm_det := proj1 (proj2 Wk_det).
Definition WkVar_det := proj1 (proj2 (proj2 Wk_det)).
Definition VarTy_det := proj2 (proj2 (proj2 Wk_det)).

(* A weakening derivation knows its subject is a variable of the type it
   claims.  (Used when wiring [Values.v]'s [ValVar] onto [VarTy].) *)
Lemma WkVar_VarTy D G w i A A' x x'
  : WkVar D G w i A A' x x' -> VarTy G i A x.
Proof.
  induction 1; try assumption.
  - eapply varty_hd; eassumption.
  - eapply varty_wkn; eassumption.
Qed.
