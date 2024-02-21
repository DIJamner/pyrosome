Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  
  Section WithModel.
    Context {tgt_term tgt_sort : Type}
      {tgt_Model : @Model V tgt_term tgt_sort}
      (*TODO: should I make it so that these aren't necessary?*)
      `{WithDefault tgt_term}
      `{WithDefault tgt_sort}.

    Existing Instance tgt_Model.

    Section CompileJudgment.
      Context (compile : term -> tgt_term)
        (compile_sort : sort -> tgt_sort)
        (compile_ctx : ctx -> named_list tgt_sort)
        (compile_args : list term -> list tgt_term)
        (compile_subst : subst -> named_list tgt_term)
        (src : lang).
      
      (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
       *)
      Definition sort_wf_preserving_sem :=
        forall c t,
          wf_sort src c t ->
          wf_ctx src c ->
          Model.wf_sort (compile_ctx c) (compile_sort t).

      Definition term_wf_preserving_sem :=
        forall c e t,
          wf_term src c e t ->
          wf_ctx src c ->
          Model.wf_term (compile_ctx c) (compile e) (compile_sort t).

      Definition sort_eq_preserving_sem :=
        forall c t1 t2,
          eq_sort src c t1 t2 ->
          wf_ctx src c ->
          Model.eq_sort (compile_ctx c) (compile_sort t1) (compile_sort t2).
      
      Definition term_eq_preserving_sem :=
        forall c t e1 e2,
          eq_term src c t e1 e2 ->
          wf_ctx src c ->
          Model.eq_term (compile_ctx c) (compile_sort t) (compile e1) (compile e2).

      Definition args_wf_preserving_sem :=
        forall c s c',
          wf_args src c s c' ->
          wf_ctx src c ->
          wf_ctx src c' ->
          Model.wf_args (compile_ctx c) (compile_args s) (compile_ctx c').

      Definition subst_eq_preserving_sem :=
        forall c c' s1 s2,
          eq_subst src c c' s1 s2 ->
          wf_ctx src c ->
          wf_ctx src c' ->
          Model.eq_subst (compile_ctx c) (compile_ctx c') (compile_subst s1) (compile_subst s2).
      
      Definition args_eq_preserving_sem :=
        forall c c' s1 s2,
          eq_args src c c' s1 s2 ->
          wf_ctx src c ->
          wf_ctx src c' ->
          Model.eq_args (compile_ctx c) (compile_ctx c') (compile_args s1) (compile_args s2).
      
      Definition ctx_wf_preserving_sem :=
        forall c, wf_ctx src c -> Model.wf_ctx (compile_ctx c).

      (*Set up to match the combined scheme for the judgment inductives *)
      Definition semantics_preserving :=
        sort_eq_preserving_sem /\ term_eq_preserving_sem /\ subst_eq_preserving_sem
        /\ sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
        /\ ctx_wf_preserving_sem.

    End CompileJudgment.

  End WithModel.

End WithVar.
