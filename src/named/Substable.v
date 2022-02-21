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

    Definition subst := (named_list A).

    Definition id_args {B} (c : named_list B) :=
      map inj_var (map fst c).

    (*Defined as a notation so that the definition 
      does not get in the way of automation *)
    Notation id_subst c := (with_names_from c (id_args c)).
    
    Definition subst_cmp (s1 s2 : subst) := named_map (apply_subst0 s1) s2.

    Fixpoint ws_subst args (s : subst) : Prop :=
      match s with
      | [] => True
      | (n,e)::s' => fresh n s' /\ well_scoped0 args e /\ ws_subst args s'
      end.
    Arguments ws_subst args !s/.

    (* TODO: make sure that using apply_subst0 here isn't a problem for automation.
       The alternative is to split Substable into defs and properties like Substable0
     *)
    Definition args_subst s (a : list A) := map (apply_subst0 s) a.
    Arguments args_subst s !a/.

    Definition ws_args args : list A -> Prop := all (well_scoped0 args).
    Arguments ws_args args !s/.

    Definition subst_lookup `{Eqb V} (s : subst) (n : V) : A :=
      named_list_lookup (inj_var n) s n.

    Arguments subst_lookup {_} !s n/.

    Class Substable0_ok : Type :=
      {
        subst_assoc0 : forall s1 s2 a,
          well_scoped0 (map fst s2) a ->
          apply_subst0 s1 (apply_subst0 s2 a) = apply_subst0 (subst_cmp s1 s2) a;
        subst_id0 : forall {B} (c : named_list B) a,
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
    
    Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).
    
    Context {Substable0_ok : Substable0_ok}.
    
    #[export] Instance substable0_is_substable
      : Substable A :=
      {
        apply_subst := apply_subst0;
        well_scoped := well_scoped0;
        subst_assoc :=  subst_assoc0;
        subst_id := @subst_id0 _;
        strengthen_subst := strengthen_subst0;
        well_scoped_subst := well_scoped_subst0;
      }.
    

    (*TODO: use separate DB*)
    Local Hint Rewrite subst_assoc0 : utils.
    Arguments subst_id0 {Substable0_ok} B%type_scope _ _.
    Local Hint Rewrite subst_id0 : utils.
    Local Hint Rewrite strengthen_subst0 : utils.
    Local Hint Resolve well_scoped_subst0 : utils.

    Lemma args_subst_assoc : forall s1 s2 a,
        ws_args (map fst s2) a ->
        args_subst s1 (args_subst s2 a)
        = args_subst (subst_cmp s1 s2) a.
    Proof.
      induction a; basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma args_subst_id
      : forall A (c : named_list A) a,
        args_subst (id_subst c) a = a.
    Proof.
      induction a; basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma args_strengthen_subst s a n e
      : ws_args (map fst s) a ->
        fresh n s ->
        args_subst ((n,e)::s) a = args_subst s a.
    Proof.
      induction a; basic_goal_prep; f_equal;
        basic_utils_crush.
    Qed.

    Lemma args_well_scoped_subst args s a
      : ws_subst args s ->
        ws_args (map fst s) a ->
        ws_args args (args_subst s a).
    Proof.
      induction a; basic_goal_prep; try case_match;
        basic_utils_crush.
    Qed.

    #[export] Instance substable_args : Substable (list A) :=
      {
        apply_subst := args_subst;
        well_scoped := ws_args;
        subst_assoc := args_subst_assoc;
        subst_id := args_subst_id;
        strengthen_subst := args_strengthen_subst;
        well_scoped_subst := args_well_scoped_subst;
      }.

    
    Lemma subst_subst_assoc : forall s1 s2 a,
        ws_subst (map fst s2) a ->
        subst_cmp s1 (subst_cmp s2 a)
        = subst_cmp (subst_cmp s1 s2) a.
    Proof.
      induction a; basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma subst_subst_id
      : forall A (c : named_list A) a,
        subst_cmp (id_subst c) a = a.
    Proof.
      induction a; basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma subst_strengthen_subst s a n e
      : ws_subst (map fst s) a ->
        fresh n s ->
        subst_cmp ((n,e)::s) a = subst_cmp s a.
    Proof.
      induction a; basic_goal_prep; f_equal;
        solve [basic_utils_crush].
    Qed.

    Lemma subst_well_scoped_subst args s a
      : ws_subst args s ->
        ws_subst (map fst s) a ->
        ws_subst args (subst_cmp s a).
    Proof.
      unfold subst_cmp.
      induction a; basic_goal_prep; try case_match;
        basic_utils_crush.
    Qed.

    
   #[export] Instance substable_subst : Substable (named_list A) :=
      {
        apply_subst := subst_cmp;
        well_scoped := ws_subst;
        subst_assoc := subst_subst_assoc;
        subst_id := subst_subst_id;
        strengthen_subst := subst_strengthen_subst;
        well_scoped_subst := subst_well_scoped_subst;
      }.
    
    Lemma with_names_from_args_subst {B} (c':named_list B) s' (s : list A)
      : with_names_from c' s[/s'/] = (with_names_from c' s)[/s'/].
    Proof.
      revert s.
      induction c';
        destruct s;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

  End WithSubstable0.


End WithVar.

Arguments id_args : simpl never.

(*Defined as a notation so that the definition 
does not get in the way of automation *)
Notation id_subst c := (with_names_from c (id_args c)).


Arguments subst_lookup [V]%type_scope {A}%type_scope {Substable0 H} !s n/.
Arguments args_subst [V]%type_scope {A}%type_scope {Substable0} s !a%list_scope/.
Arguments ws_args [V]%type_scope {A}%type_scope {Substable0} (_ !_)%list_scope/.

Arguments ws_subst [V]%type_scope {A}%type_scope {Substable0} args !s/.

Arguments Substable0_ok [V]%type_scope _%type_scope {_}.
Arguments Substable {V}%type_scope _%type_scope {_} _%type_scope.

Arguments well_scoped [V]%type_scope {A}%type_scope {_} {B}%type_scope {_} _%list_scope !_.
Arguments apply_subst [V]%type_scope {A}%type_scope {_} {B}%type_scope {_} _%list_scope !_.

Arguments args_subst [V]%type_scope {A}%type_scope {Substable0} s !a%list_scope/.
Arguments ws_args [V]%type_scope {A}%type_scope {Substable0} (_ !_)%list_scope/.
Arguments subst_id0 [V]%type_scope {A}%type_scope {Substable0 Substable0_ok} B%type_scope _ _.



(*TODO: add'l arguments, fix these hints*)
#[global] Hint Rewrite @subst_assoc : term.
#[global] Hint Rewrite @subst_id : term.
#[global] Hint Rewrite @strengthen_subst : term.
#[global] Hint Resolve well_scoped_subst : term.

Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).
