Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Export Substable Model Term Rule Core.


(*TODO: should this be split differently? Model_ok for core should be in Core.v*)
Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.


  Section WithLang.
    Context (l : lang V)
            (wfl : wf_lang l).
    Notation core_model := (core_model l). 

    Instance core_model_ok : Model_ok core_model :=
      {
        term_substable_ok := substable_term_ok (V:=V);
        sort_substable_ok := substable_sort_ok (V:=V);
        eq_sort_subst := eq_sort_subst (l:=l);
        eq_sort_refl := eq_sort_refl (l:=l);
        eq_sort_trans := eq_sort_trans (l:=l);
        eq_sort_sym := eq_sort_sym (l:=l);
        eq_term_subst := eq_term_subst (l:=l);
        eq_term_refl := eq_term_refl (l:=l);
        eq_term_trans := eq_term_trans (l:=l);
        eq_term_sym := eq_term_sym (l:=l);
        eq_term_conv := eq_term_conv (l:=l);
        wf_term_conv := wf_term_conv (l:=l);
        wf_term_var := wf_term_var l;
        wf_sort_subst_monotonicity := wf_sort_subst_monotonicity wfl;
        wf_term_subst_monotonicity := wf_term_subst_monotonicity wfl;
        wf_sort_implies_ws := wf_sort_implies_ws ltac:(eauto with lang_core);
        wf_term_implies_ws := wf_term_implies_ws ltac:(eauto with lang_core);
      }.

  End WithLang.
  
  (*TODO: implement (is this defined in multicompilers.v?*)
  Axiom Eqb_list :forall {A}, Eqb A -> Eqb (list A).
  Existing Instance Eqb_list.

  Section Multicompilers.
    Context (l : lang (list V))
            (wfl : wf_lang l).

    Context (fn_names : list V).

    
    Notation named_list := (@named_list (list V)).
    Notation named_map := (@named_map (list V)).
    Notation term := (@term (list V)).
    Notation var := (@var (list V)).
    Notation con := (@con (list V)).
    Notation ctx := (@ctx (list V)).
    Notation sort := (@sort (list V)).
    Notation subst := (@subst (list V)).
    Notation rule := (@rule (list V)).
    Notation lang := (@lang (list V)).

    Notation Model := (@Model (list V) (list term) (list sort)).


    Let arity := length fn_names.

    Definition flatten_ctx : named_list (list sort) -> ctx :=
      flat_map (fun '(n,t) =>
                  map (fun '(fn, t) =>(fn::n,t)) (combine fn_names t)).

    (*TODO: double check this*)
    Fixpoint split_subst (s : named_list (list term)) : list (named_list term) :=
      match s with
      | [] => repeat [] arity
      | (n,e)::s =>
          map (fun '(e,s) => (n,e)::s) (combine e (split_subst s))
      end.

    Definition expand_args : list (list V) -> list (list V) :=
      flat_map (fun n =>
                  map (fun fn =>fn::n) fn_names).
    
    Instance list_term_subst : Substable0 (list V) (list term) :=
      {
        inj_var x := map (fun n => var (n::x)) fn_names;
        eq_term0 := fun _ => eq;
        apply_subst0 s e := map (fun '(e,s) => e[/s/]) (combine e (split_subst s));
        well_scoped0 args e :=
        length e = arity /\
          all (well_scoped (expand_args args))  e
      }.

    (* TODO
    Instance list_term_subst_ok : Substable0_ok (list term).
    Proof.
      constructor.
      all: basic_goal_prep; basic_core_crush.
      {
        unfold Substable.subst_lookup.
        induction s;
          basic_goal_prep; basic_term_crush.
        {
          subst arity.
          induction fn_names; 
            basic_goal_prep; basic_term_crush.
        }
        {
          case_match;
          basic_utils_crush.
        }
        simpl.
          
      }
      {
        inj_var x := map (fun n => var (n::x)) fn_names;
        apply_subst0 s e := map (fun '(e,s) => e[/s/]) (combine e (split_subst s));
        well_scoped0 args e :=
        length e = arity /\
          all (well_scoped (expand_args args))  e
      }.
    
    Instance list_sort_subst : Substable (list term) (list sort) :=
      {
        apply_subst s t := map (fun '(t,s) => t[/s/]) (combine t (split_subst s));
        well_scoped args t :=
        length t = arity /\
          all (well_scoped (expand_args args))  t
      }.

    (* TODO: move to Utils.v
       TODO: use this or all3?
     *)
    Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Prop)
      : list A -> list B -> list C -> Prop :=
    | Forall3_nil : Forall3 R [] [] []
    | Forall3_cons : forall (x : A) (y : B) (z : C)
                            (l : list A) (l' : list B) (l'' : list C),
        R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z :: l'').

     Instance multi_model : Model :=
      {
        term_substable := list_term_subst;
        sort_substable := list_sort_subst;
        eq_sort c t1 t2 :=
        (length t1 = arity) /\
          (length t2 = arity) /\
          (Forall2 (eq_sort l (flatten_ctx c)) t1 t2);
        eq_term c t e1 e2 :=
        (length t = arity) /\
          (length e1 = arity) /\
          (length e2 = arity) /\
          (Forall3 (eq_term l (flatten_ctx c)) t e1 e2);
        wf_sort c t :=
        (length t = arity) /\
          (Forall (wf_sort l (flatten_ctx c)) t);
        wf_term c e t :=
        (length e = arity) /\
        (length t = arity) /\
          (Forall2 (wf_term l (flatten_ctx c)) e t);
      }.
    

    Instance multi_model_ok : Model_ok multi_model.
    constructor.
    - 
    try typeclasses eauto.

    Qed.
      :=
      {
        term_substable_ok := substable_term_ok (V:=V);
        sort_substable_ok := substable_sort_ok (V:=V);
        eq_sort_subst := eq_sort_subst (l:=l);
        eq_sort_refl := eq_sort_refl (l:=l);
        eq_sort_trans := eq_sort_trans (l:=l);
        eq_sort_sym := eq_sort_sym (l:=l);
        eq_term_subst := eq_term_subst (l:=l);
        eq_term_refl := eq_term_refl (l:=l);
        eq_term_trans := eq_term_trans (l:=l);
        eq_term_sym := eq_term_sym (l:=l);
        eq_term_conv := eq_term_conv (l:=l);
        wf_term_conv := wf_term_conv (l:=l);
        wf_term_var := wf_term_var l;
        wf_sort_subst_monotonicity := wf_sort_subst_monotonicity wfl;
        wf_term_subst_monotonicity := wf_term_subst_monotonicity wfl;
        wf_sort_implies_ws := wf_sort_implies_ws ltac:(eauto with lang_core);
        wf_term_implies_ws := wf_term_implies_ws ltac:(eauto with lang_core);
      }.
     *)

    End Multicompilers.
    
  End WithVar.
