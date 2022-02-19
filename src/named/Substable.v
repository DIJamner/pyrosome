Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.

Section WithVar.
  Context (V : Type).

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).


  (* Operations for types that can be substituted into themselves *)
  Class Substable0 (A : Type) : Type :=
    {
      inj_var : V -> A;
      apply_subst0 : named_list A -> A -> A;
      well_scoped0 : list V -> A -> Prop;
    }.

  Section WithSubstable0.
    Context {A} {Substable0 : Substable0 A}.

    Notation subst := (named_list A).

    Definition id_args {B} (c : named_list B) :=
      map inj_var (map fst c).

    (*Defined as a notation so that the definition 
      does not get in the way of automation *)
    Notation id_subst c := (with_names_from c (id_args c)).
    
    Definition subst_cmp (s1 s2 : named_list A) := named_map (apply_subst0 s1) s2.

    Fixpoint ws_subst args (s : subst) : Prop :=
      match s with
      | [] => True
      | (n,e)::s' => fresh n s' /\ well_scoped0 args e /\ ws_subst args s'
      end.
    Arguments ws_subst args !s/.

    Class Substable0_ok : Type :=
      {
        subst_assoc0 : forall s1 s2 a,
          well_scoped0 (map fst s2) a ->
          apply_subst0 s1 (apply_subst0 s2 a) = apply_subst0 (subst_cmp s1 s2) a;
        subst_id0 : forall {A} (c : named_list A) a,
          (* Not necessary because of our choice of default
        well_scoped (map fst c) a ->*)
          apply_subst0 (id_subst c) a = a;
        strengthen_subst0
        : forall s a n e,
          well_scoped0 (map fst s) a ->
          fresh n s ->
          apply_subst0 ((n,e)::s) a = apply_subst0 s a;
        well_scoped_subst0 args s a
        : ws_subst args s ->
          well_scoped0 (map fst s) a ->
          well_scoped0 args (apply_subst0 s a)
      }.

    Class Substable (B : Type) : Type :=
      {
        apply_subst : subst -> B -> B;
        well_scoped : list V -> B -> Prop;
        subst_assoc : forall s1 s2 a,
          well_scoped (map fst s2) a ->
          apply_subst s1 (apply_subst s2 a) = apply_subst (subst_cmp s1 s2) a;
        subst_id : forall {B} (c : named_list B) a,
          (* Not necessary because of our choice of default
        well_scoped (map fst c) a ->*)
          apply_subst (id_subst c) a = a;
        strengthen_subst
        : forall s a n e,
          well_scoped (map fst s) a ->
          fresh n s ->
          apply_subst ((n,e)::s) a= apply_subst s a;
        well_scoped_subst args s a
        : ws_subst args s ->
          well_scoped (map fst s) a ->
          well_scoped args (apply_subst s a)
      }.

  End WithSubstable0.

  
  #[export] Instance substable0_is_substable {A} `{Substable0 A} `{Substable0_ok A}
    : Substable A :=
    {
      apply_subst := apply_subst0;
      well_scoped := well_scoped0;
      subst_assoc :=  subst_assoc0;
      subst_id := @subst_id0 _ _ _;
      strengthen_subst := strengthen_subst0;
      well_scoped_subst := well_scoped_subst0;
    }.

End WithVar.

Arguments id_args : simpl never.

(*Defined as a notation so that the definition 
does not get in the way of automation *)
Notation id_subst c := (with_names_from c (id_args c)).

Arguments Substable0_ok [V]%type_scope _%type_scope {_}.
Arguments Substable {V}%type_scope _%type_scope {_} _%type_scope.

Arguments well_scoped [V]%type_scope {A}%type_scope {_} {B}%type_scope {_} _%list_scope !_.
Arguments apply_subst [V]%type_scope {A}%type_scope {_} {B}%type_scope {_} _%list_scope !_.

(*TODO: add'l arguments, fix these hints*)
#[global] Hint Rewrite @subst_assoc : term.
#[global] Hint Rewrite @subst_id : term.
#[global] Hint Rewrite @strengthen_subst : term.
#[global] Hint Resolve well_scoped_subst : term.

Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).
