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
  (* Source syntax is the syntactic [term]/[sort]. *)
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation lang := (@lang V).

  (* The target of a closed compiler is an *abstract* carrier [tgt_term]/
     [tgt_sort] (as in Theory/Model.v / ClosedModel.v), equipped with a
     [PreModel] -- used to interpret source variables via [inj_var] -- and
     defaults for the (unreachable, in a well-formed compiler) lookup-failure
     cases. *)
  Section WithTarget.
    Context {tgt_term tgt_sort : Type}
            {tgt_pre : @PreModel V tgt_term tgt_sort}
            {tgt_term_default : WithDefault tgt_term}
            {tgt_sort_default : WithDefault tgt_sort}.

  (* A closed compiler case is a *function* from the compiled subterms to a
     target term/sort, rather than a term/sort with argument variables plus a
     substitution.  Because the case is applied directly to the compiled
     subterms, [compile] never performs an object-level substitution: the
     plumbing between subterms is done at the meta level. *)
  Variant closed_compiler_case : Type :=
    | closed_term_case (f : list tgt_term -> tgt_term)
    | closed_sort_case (f : list tgt_term -> tgt_sort).

  Definition closed_compiler := named_list closed_compiler_case.

  Section CompileFn.
    Context (cmp : closed_compiler).

    (* A source variable compiles to the target's injected variable; in the
       closed setting no variable actually survives to be compiled, but the
       recursion is total over all source terms. *)
    Fixpoint compile (e : term) : tgt_term :=
      match e with
      | var x => inj_var x
      | con n s =>
          let s' := map compile s in
          match named_list_lookup_err cmp n with
          | Some (closed_term_case f) => f s'
          | _ => default
          end
      end.

    Definition compile_sort (t : sort) : tgt_sort :=
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
     will be exactly the statement that the source language's equalities hold in
     this pullback. *)
  Definition compile_model (cmp : closed_compiler) (CM : @ClosedModel V tgt_term tgt_sort)
    : @ClosedModel V term sort :=
    {|
      cpremodel := @syntax_model V V_Eqb;
      ceq_sort t1 t2 :=
        CM.(ceq_sort) (compile_sort cmp t1) (compile_sort cmp t2);
      ceq_term t e1 e2 :=
        CM.(ceq_term) (compile_sort cmp t) (compile cmp e1) (compile cmp e2);
    |}.

  (* The inductive, per-rule characterization of a preserving compiler (the
     closed analogue of CompilerDefs.preserving_compiler_ext).  It walks the
     source language rule-by-rule; each constructor carries EXACTLY ONE
     obligation for that rule, phrased entirely in the target model [CM] on the
     compiled syntax.  The equational structural laws (transitivity, symmetry,
     conversion) are NOT obligations here -- they are discharged once and
     generically from [CM]'s own [ClosedModel_ok] in
     ClosedCompilers.preserving_closed_compiler_ext_sound.

     Each obligation quantifies over argument lists [s1]/[s2] related by the
     pullback's [ceq_args]: this is the analogue of the open compiler's single
     wf/eq fact, but here it must range over instantiations directly because the
     cut-free target model has no primitive substitution law to lift a single
     fact with. *)
  Inductive preserving_closed_compiler_ext
    (cmp : closed_compiler) (CM : @ClosedModel V tgt_term tgt_sort) : lang -> Prop :=
  | preserving_closed_nil : preserving_closed_compiler_ext cmp CM []
  | preserving_closed_sort_rule : forall l n c' args,
      preserving_closed_compiler_ext cmp CM l ->
      (forall s1 s2 : list term,
          ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
          ceq_sort (ClosedModel := CM)
                   (compile_sort cmp (scon n s1)) (compile_sort cmp (scon n s2))) ->
      preserving_closed_compiler_ext cmp CM ((n, sort_rule c' args) :: l)
  | preserving_closed_term_rule : forall l n c' args t,
      preserving_closed_compiler_ext cmp CM l ->
      (forall s1 s2 : list term,
          ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
          ceq_term (ClosedModel := CM)
                   (compile_sort cmp (t [/with_names_from c' s2/]))
                   (compile cmp (con n s1)) (compile cmp (con n s2))) ->
      preserving_closed_compiler_ext cmp CM ((n, term_rule c' args t) :: l)
  | preserving_closed_sort_eq_rule : forall l n c' t1 t2,
      preserving_closed_compiler_ext cmp CM l ->
      (forall s1 s2 : list term,
          ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
          ceq_sort (ClosedModel := CM)
                   (compile_sort cmp (t1 [/with_names_from c' s1/]))
                   (compile_sort cmp (t2 [/with_names_from c' s2/]))) ->
      preserving_closed_compiler_ext cmp CM ((n, sort_eq_rule c' t1 t2) :: l)
  | preserving_closed_term_eq_rule : forall l n c' e1 e2 t,
      preserving_closed_compiler_ext cmp CM l ->
      (forall s1 s2 : list term,
          ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
          ceq_term (ClosedModel := CM)
                   (compile_sort cmp (t [/with_names_from c' s2/]))
                   (compile cmp (e1 [/with_names_from c' s1/]))
                   (compile cmp (e2 [/with_names_from c' s2/]))) ->
      preserving_closed_compiler_ext cmp CM ((n, term_eq_rule c' e1 e2 t) :: l).

  End WithTarget.

End WithVar.

Arguments closed_compiler_case : clear implicits.
Arguments closed_compiler : clear implicits.
