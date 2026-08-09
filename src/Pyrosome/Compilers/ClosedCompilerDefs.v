Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ClosedModel.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation lang := (@lang V).

  (* A closed compiler case is a *function* from the compiled subterms to a
     target term/sort, rather than a term/sort with argument variables plus a
     substitution.  Because the case is applied directly to the compiled
     subterms, [compile] never performs an object-level substitution: the
     plumbing between subterms is done at the meta level. *)
  Variant closed_compiler_case : Type :=
    | closed_term_case (f : list term -> term)
    | closed_sort_case (f : list term -> sort).

  Definition closed_compiler := named_list closed_compiler_case.

  Existing Instance term_default.
  Existing Instance sort_default.

  Section CompileFn.
    Context (cmp : closed_compiler).

    Fixpoint compile (e : term) : term :=
      match e with
      | var x => var x
      | con n s =>
          let s' := map compile s in
          match named_list_lookup_err cmp n with
          | Some (closed_term_case f) => f s'
          | _ => default
          end
      end.

    Definition compile_sort (t : sort) : sort :=
      match t with
      | scon n s =>
          let s' := map compile s in
          match named_list_lookup_err cmp n with
          | Some (closed_sort_case f) => f s'
          | _ => default
          end
      end.

    Definition compile_args := map compile.
    Definition compile_subst (s : named_list term) := named_map compile s.
    Definition compile_ctx (c : ctx) := named_map compile_sort c.
  End CompileFn.

  (* The pullback model: a target [ClosedModel] [CM], viewed through [compile],
     is itself a [ClosedModel] over the *source* syntax.  Semantics preservation
     will be exactly the statement that this pullback satisfies the cut-free
     model laws of the source language (i.e. is a [ClosedModel_ok]). *)
  Definition compile_model (cmp : closed_compiler) (CM : ClosedModel) : ClosedModel :=
    {|
      ceq_sort t1 t2 :=
        ceq_sort (ClosedModel:=CM) (compile_sort cmp t1) (compile_sort cmp t2);
      ceq_term t e1 e2 :=
        ceq_term (ClosedModel:=CM) (compile_sort cmp t) (compile cmp e1) (compile cmp e2);
    |}.

  (* A closed compiler [cmp] preserves the semantics of source language [l] at
     ambient context [c], targeting model [CM], exactly when the pullback of [CM]
     along [cmp] is a well-formed cut-free model of [l]. *)
  Definition preserving_closed_compiler
    (cmp : closed_compiler) (l : lang) (c : ctx) (CM : ClosedModel) : Prop :=
    ClosedModel_ok l c (CM := compile_model cmp CM).

End WithVar.

Arguments closed_compiler_case : clear implicits.
Arguments closed_compiler : clear implicits.
