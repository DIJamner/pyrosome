(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind FunctionalDB.
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

  
  Context 
      (V_map : forall A, map.map V A)
      (V_map_ok : forall A, map.ok (V_map A)).

  Notation instance := (instance V V V_map V_map).
  
  Record eqsat : Type := {
      inst : instance;
      (* maintain a map*)
      sort_map : V_map V;
    }.

  Context (succ : V -> V).
  
  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).

  Require Import Utils.Monad.
  Import Monad.StateMonad.
  
  Definition gensym {M} `{Monad M} : stateT V M V :=
    fun s => Mret (succ s, s).

  Definition writer S A : Type := list S * A.

  Instance writer_monad S : Monad (writer S) :=
    {
      Mret _ a := ([],a);
      Mbind _ _ f ma :=
        let '(l1,a) := ma in
        let '(l2,b) := f a in
        (l2++l1,b)
    }.

  Definition write {A} a : writer A unit :=
    ([a],tt).
    

  Fixpoint term_to_clauses (e : term) : stateT V (writer (atom V V * V)) V :=
    match e with
    | var x => (*TODO: how to handle vars in db? shared namespace w/ con? *)
        @! let xx <- gensym in
          let tt <- lift (write (Build_atom _ _ x [],xx)) in
          ret xx
    | con n s =>
        @! let s' <- list_Mmap term_to_clauses s in
          let ax <- gensym in
          let tt <- lift (write (Build_atom _ _ n s',ax)) in
          ret ax
    end.
  
  (* Patterns treat variables differently! *)
  Fixpoint term_pat_to_clauses (varmap : named_list V) (e : term) : stateT V (writer (atom V V * V)) V :=
    match e with
    | var x => Mret (named_list_lookup default varmap x)
    | con n s =>
        @! let s' <- list_Mmap (term_pat_to_clauses varmap) s in
          let ax <- gensym in
          let tt <- lift (write (Build_atom _ _ n s',ax)) in
          ret ax
    end.

  Definition sort_pat_to_clauses vm (t : sort) : stateT V (writer (atom V V * V)) V :=
    match t with
    | scon n s =>
        @! let s' <- list_Mmap (term_pat_to_clauses vm) s in
          let ax <- gensym in
          let tt <- lift (write (Build_atom _ _ n s',ax)) in
          ret ax
    end.

  (*TODO: is vm always empty?*)
  Fixpoint ctx_pat_to_clauses vm (c : ctx)
    : stateT V (writer (atom V V * V)) (list (V * V)) :=
    match c with
    | [] => Mret (M:=stateT V (writer (atom V V * V))) vm
    | (n,t)::c' =>
        @! let vm' <- ctx_pat_to_clauses vm c' in
          let t' <- sort_pat_to_clauses vm' t in
          let n' <- gensym in
          let _ <- lift (write (Build_atom _ _ sort_of [n'] ,t')) in
          ret (n,n')::vm'
    end.

  (*TODO: sketch full translation on paper*)
  
  (*TODO: does the wrong thing w/ vars
  Definition ctx_to_clauses

  Definition lang_rule_to_log_rule n (r : rule) : log_rule :=
    match r with
    (* TODO: what to do with the sorts?
       Include sort_of as special symbol/fn in db? might be easiest
     *)
    | term_rule c _ t =>
        (*TODO: want multiple conclusions?
          Can be immitated by chained single-conclusion rules, but at > n times cost where n is #conclusions
          e.g.:
          (n args) |-> ?x, (sort_of ?x) |-> xt :- ... t |-> xt

          alternately: want a different `default` for `sort_of`?
          Question: can I ignore/never materialize the sort? No: side conditions are defined by their sorts

          Note about Multi-conclusion rules:
          - need to have separate variables for outputs that aren't matched in the assumptions.
          General idea: assumptions generate a subst,
          future rules treat vars in the subst diff from vars out of the subst
          Can I remove the awk. in-list vs option distinction by making the clause always have the var this way?
         *)
        term_to_clauses : state V 
        Note: need fresh variable state across assumptions, conclusion?
                                                                      
      Build_log_op (concl_cons (term_to_conclusion (con n (map fst c)))... (fun x y => sort_of x y)  ]  ((ctx_to_assumptions c))

  TODO: rules to eqsat program
  TODO: sort map rebuilding
*)

End WithVar.
