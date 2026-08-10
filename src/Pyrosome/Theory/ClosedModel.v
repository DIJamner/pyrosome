Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable Model.

(* A *cut-free*, Prop-valued, *closed* model, parameterized by an abstract type
   of terms and an abstract type of sorts (via a [PreModel], exactly as
   Theory/Model.v is).

   This is the Prop-valued analogue of Gluing/CutTModel.v's [CutTModel], but
   abstracted away from the syntactic carrier and specialized to the *closed*
   setting.  In particular, compared to a [Model]:

   - the judgments [ceq_sort]/[ceq_term] are Prop-valued (so a member carries no
     data), and they carry NO ambient context: a [ClosedModel] describes the
     equalities that hold among closed terms/sorts of its carrier;
   - correspondingly [ClosedModel_ok] contains only the structural equational
     laws -- transitivity, symmetry and conversion.  There is NO substitution
     law, NO congruence/axiom-instance operation (those mention a source
     language and are supplied instead, per rule, by a compiler; see
     Compilers/ClosedCompilerDefs.v), and NO variable rule (the model is closed).

   Because the judgments are Props, a [ClosedModel] can serve directly as the
   *target* of a semantics-preserving compiler whose conclusions are Props (no
   [inhabited] truncation is needed to eliminate its witnesses). *)
Section WithVar.
  Context {V : Type}.

  Notation named_list := (@named_list V).
  Notation Substable0 := (Substable0 V).
  Notation Substable := (Substable (V:=V)).

  Section WithModelArgs.
    Context {term sort : Type}.

    Local Notation ctx := (named_list sort).
    Local Notation subst := (named_list term).

    Class ClosedModel :=
      {
        cpremodel :: @PreModel V term sort;
        ceq_sort : sort -> sort -> Prop;
        ceq_term : sort -> term -> term -> Prop;
      }.

    Section WithCM.
      Context {CM : ClosedModel}.

      (* Argument equality, built pointwise from [ceq_term] exactly as
         TreeProofs.check_args_proof checks an argument list (each argument at the
         rule-context type substituted by the preceding right-hand values).  The
         index is the rule's context [c'].  This is used to state a compiler's
         per-rule obligations; it is not itself a model law. *)
      Inductive ceq_args : ctx -> list term -> list term -> Prop :=
      | ceq_args_nil : ceq_args [] [] []
      | ceq_args_cons : forall c' es1 es2,
          ceq_args c' es1 es2 ->
          forall name t e1 e2,
            ceq_term t[/with_names_from c' es2/] e1 e2 ->
            ceq_args ((name,t)::c') (e1::es1) (e2::es2).

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

End WithVar.

Arguments ClosedModel {V} term sort.
Arguments ClosedModel_ok {V term sort} CM.
