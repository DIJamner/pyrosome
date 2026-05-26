Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable Model.

(* A [Type]-valued analogue of Theory/Model.v's [Model]: the judgments
   [eq_sort]/[eq_term]/[wf_sort]/[wf_term] live in [Type] rather than [Prop], so
   that a model's derivations can carry computational content (e.g. the normal
   form attached to a term in a gluing / normalization-by-evaluation model).

   The substitution structure [PreModel] is judgment-free and is shared verbatim
   with Theory/Model.v.  Everything else mirrors Model.v with [Prop] replaced by
   [Type]; names are prefixed with [t] to coexist with the [Prop] versions. *)
Section WithVar.
  Context {V : Type}.

  Notation named_list := (@named_list V).
  Notation Substable0 := (Substable0 V).
  Notation Substable := (Substable (V:=V)).

  Section WithModelArgs.
    Context {term sort : Type}.

    Local Notation ctx := (named_list sort).
    Local Notation subst := (named_list term).

    Class TModel :=
      {
        tpremodel :: @PreModel V term sort;
        teq_sort : ctx -> sort -> sort -> Type;
        teq_term : ctx -> sort -> term -> term -> Type;
        twf_sort : ctx -> sort -> Type;
        twf_term : ctx -> term -> sort -> Type;
      }.

    Section WithTModel.
      Context {TM : TModel}.

      Inductive teq_subst (c : ctx) : ctx -> subst -> subst -> Type :=
      | teq_subst_nil : teq_subst c [] [] []
      | teq_subst_cons : forall c' s1 s2,
          teq_subst c c' s1 s2 ->
          forall name t e1 e2,
            teq_term c t[/s2/] e1 e2 ->
            teq_subst c ((name,t)::c') ((name,e1)::s1) ((name,e2)::s2).

      Inductive twf_args (c : ctx) : list term -> ctx -> Type :=
      | twf_args_nil : twf_args c [] []
      | twf_args_cons : forall s c' name e t,
          twf_term c e t[/with_names_from c' s/] ->
          twf_args c s c' ->
          twf_args c (e::s) ((name,t)::c').

      Inductive twf_ctx : ctx -> Type :=
      | twf_ctx_nil : twf_ctx []
      | twf_ctx_cons : forall name c v,
          fresh name c ->
          twf_ctx c ->
          twf_sort c v ->
          twf_ctx ((name,v)::c).

      Inductive teq_args (c : ctx) : ctx -> list term -> list term -> Type :=
      | teq_args_nil : teq_args c [] [] []
      | teq_args_cons : forall c' es1 es2,
          teq_args c c' es1 es2 ->
          forall name t e1 e2,
            teq_term c t[/with_names_from c' es2/] e1 e2 ->
            teq_args c ((name,t)::c') (e1::es1) (e2::es2).

      Inductive twf_subst c : subst -> ctx -> Type :=
      | twf_subst_nil : twf_subst c [] []
      | twf_subst_cons : forall s c' name e t,
          twf_subst c s c' ->
          twf_term c e t[/s/] ->
          twf_subst c ((name,e)::s) ((name,t)::c').

      (* The CwF laws, packaged as [Type]-valued operations.  Note in particular
         [twf_term_conv]: conversion is a transport *function*, the computational
         content a gluing model uses to coerce data along a sort equality. *)
      Class TModel_ok :=
        {
          term_substable_ok :: Substable0_ok term;
          sort_substable_ok :: Substable_ok term sort;

          teq_sort_subst : forall c s1 s2 c' t1' t2',
            twf_ctx c' ->
            teq_subst c c' s1 s2 ->
            teq_sort c' t1' t2' ->
            teq_sort c t1'[/s1/] t2'[/s2/];
          teq_sort_refl : forall c t, twf_sort c t -> teq_sort c t t;
          teq_sort_trans : forall c t1 t12 t2,
            teq_sort c t1 t12 -> teq_sort c t12 t2 -> teq_sort c t1 t2;
          teq_sort_sym : forall c t1 t2, teq_sort c t1 t2 -> teq_sort c t2 t1;

          teq_term_subst : forall c s1 s2 c' t e1 e2,
            twf_ctx c' ->
            teq_subst c c' s1 s2 ->
            teq_term c' t e1 e2 ->
            teq_term c t[/s2/] e1[/s1/] e2[/s2/];
          teq_term_refl : forall c e t, twf_term c e t -> teq_term c t e e;
          teq_term_trans : forall c t e1 e12 e2,
            teq_term c t e1 e12 -> teq_term c t e12 e2 -> teq_term c t e1 e2;
          teq_term_sym : forall c t e1 e2, teq_term c t e1 e2 -> teq_term c t e2 e1;
          teq_term_conv : forall c t t',
            teq_sort c t t' ->
            forall e1 e2, teq_term c t e1 e2 -> teq_term c t' e1 e2;

          twf_term_conv : forall c e t t',
            twf_term c e t -> teq_sort c t t' -> twf_term c e t';
          twf_term_var : forall c n t,
            In (n,t) c -> twf_term c (inj_var n) t;

          twf_sort_subst_monotonicity
          : forall c t, twf_sort c t -> twf_ctx c ->
              forall c'' s, twf_subst c'' s c -> twf_sort c'' t[/s/];
          twf_term_subst_monotonicity
          : forall c e t, twf_term c e t -> twf_ctx c ->
              forall c'' s, twf_subst c'' s c -> twf_term c'' e[/s/] t[/s/];
          twf_sort_implies_ws : forall c t, twf_sort c t -> well_scoped (map fst c) t;
          twf_term_implies_ws : forall c e t, twf_term c e t -> well_scoped (map fst c) e;
        }.

    End WithTModel.

  End WithModelArgs.

  Arguments TModel : clear implicits.
  Arguments TModel_ok {term sort} TM.

End WithVar.

Arguments TModel {V} term sort.
