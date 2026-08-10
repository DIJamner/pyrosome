Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

(* A *cut-free*, Prop-valued, *closed* model, parameterized by an abstract type
   of terms and an abstract type of sorts.

   This is the Prop-valued analogue of Gluing/CutTModel.v's [CutTModel], but
   abstracted away from the syntactic carrier and specialized to the *closed*
   setting.  Unlike Theory/Model.v, a [ClosedModel] carries NO substitution
   structure at all (no [PreModel]/[Substable]): the point of the closed setting
   is precisely to avoid an object-level substitution law.  Concretely, compared
   to a [Model]:

   - the carrier is just a pair of types [term]/[sort] with no operations;
   - the judgments [ceq_sort]/[ceq_term] are Prop-valued (so a member carries no
     data), and they carry NO ambient context: a [ClosedModel] describes the
     equalities that hold among closed terms/sorts of its carrier;
   - [ClosedModel_ok] contains only the structural equational laws --
     transitivity, symmetry and conversion.  There is NO substitution law, NO
     congruence/axiom-instance operation (those mention a source language and are
     supplied instead, per rule, by a compiler; see
     Compilers/ClosedCompilerDefs.v), and NO variable rule (the model is closed).

   Because the judgments are Props, a [ClosedModel] can serve directly as the
   *target* of a semantics-preserving compiler whose conclusions are Props (no
   [inhabited] truncation is needed to eliminate its witnesses). *)
Section WithModelArgs.
  Context {term sort : Type}.

  Class ClosedModel :=
    {
      ceq_sort : sort -> sort -> Prop;
      ceq_term : sort -> term -> term -> Prop;
    }.

  Section WithCM.
    Context {CM : ClosedModel}.

    (* The structural equational laws.  Each lines up with a [check_proof] /
       [check_sort_proof] structural case (TreeProofs.v): ptrans, psym, pconv.
       The pcon (congruence / axiom-instance) and pvar cases are absent: the
       former are discharged per source rule by a compiler, the latter cannot
       arise in the closed setting. *)
    Class ClosedModel_ok :=
      {
        (* ptrans *)
        cterm_trans : forall t e1 e12 e2,
          ceq_term t e1 e12 -> ceq_term t e12 e2 -> ceq_term t e1 e2;
        (* psym *)
        cterm_sym : forall t e1 e2,
          ceq_term t e1 e2 -> ceq_term t e2 e1;
        (* pconv *)
        cterm_conv : forall t1 t2 e1 e2,
          ceq_sort t1 t2 -> ceq_term t1 e1 e2 -> ceq_term t2 e1 e2;

        (* sort versions (check_sort_proof) *)
        csort_trans : forall t1 t12 t2,
          ceq_sort t1 t12 -> ceq_sort t12 t2 -> ceq_sort t1 t2;
        csort_sym : forall t1 t2,
          ceq_sort t1 t2 -> ceq_sort t2 t1;
      }.

  End WithCM.

End WithModelArgs.

Arguments ClosedModel term sort : clear implicits.
Arguments ClosedModel_ok {term sort} CM.
