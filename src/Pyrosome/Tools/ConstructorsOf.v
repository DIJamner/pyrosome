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

  Fixpoint constructors_of (e : term) : list V :=
    match e with
    | var _ => []
    | con n s => n::(flat_map constructors_of s)
    end.

  Definition constructors_of_args := flat_map constructors_of.

  Definition constructors_of_sort (t : sort) :=
    let (n,s) := t in
    n::(flat_map constructors_of s).

  Definition constructors_of_ctx (c : ctx) :=
    flat_map constructors_of_sort (map snd c).

  Definition constructors_of_rule r :=
    match r with
    | sort_rule c _ => constructors_of_ctx c
    | term_rule c _ t =>
        constructors_of_ctx c ++ constructors_of_sort t
    | sort_eq_rule c t1 t2 => 
        constructors_of_ctx c
          ++ constructors_of_sort t1
          ++ constructors_of_sort t2
    | term_eq_rule c e1 e2 t => 
        constructors_of_ctx c
          ++ constructors_of e1
          ++ constructors_of e2
          ++ constructors_of_sort t
    end.

  Definition constructors_of_lang (l:lang) :=
    flat_map constructors_of_rule (map snd l).
    

End WithVar.

  
