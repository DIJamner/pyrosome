(*
   Based on this paper, with some deviation:
   Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker,
   Eli Rosenthal, Zachary Tatlock, and Max Willsey. 2023.
   Better Together: Unifying Datalog and Equality Saturation.
   Proc. ACM Program. Lang. 7, PLDI, Article 125 (June 2023), 25 pages.
   URL: https://doi.org/10.1145/3591239
 *)
Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind FunctionalDB Monad.
Import Monad.StateMonad.
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

  Variant extended_clause :=
    | rel_clause : atom V V -> V -> extended_clause
    | var_clause : V -> V -> extended_clause.

  (*
    Translation of rewrite into query:
    G |- e1 ~> e2 : A
    xi : Bi |- e1 ~> e2 : scon nA aj

    becomes
    to_clauses(e2, kA) |-> k1 :- to_clauses(G)
                              /\ to_clauses(A) |-> kA
                              /\ to_clauses(e1, kA) |-> k1

   to_clauses(var x, kA) := lookup(x) |-> x /\ sort_of(x,kA) [keep var map around w/ gensym, alt. multiple passes]
   to_clauses(con n ei, kA) := node n ki |-> k /\ to_clauses(ei,rulectx) |-> ki /\ sort_of(k,kA)


   Important: should dedup the queries; performance critical
   To dedup: use hashcons w/ logic vars as ptrs (in other words: maintain a set of existing nodes)
   One thing to be careful of: bound vars on rhs of |->

   Semantics of cj(x1...xn)... :- ai(x1...xn)...:
   roughly: forall x1...xn such that ai ... , add cj ...
   Note: for xk where xk in fv(c) - fv(a), choose a default (fresh) value

   For a sound (but not complete) characterization,
   forall e1, e2. DB  + c1 ... cm |= e1 = e2 -> DB + c1...cm+1 |= e1 = e2;
   and, forall x1...xn, (forall i, DB + c1 ... cm |= ai) -> |- cm+1
   TODO: address delayed rebuilding; this characterization rebuilds on every +

   *)

  Definition rel_clause' x s xx := rel_clause (Build_atom _ _ x s) xx.
  
  Fixpoint term_to_clauses (e : term) : stateT V (writer extended_clause) V :=
    match e with
    | var x => (*TODO: how to handle vars in db? shared namespace w/ con? *)
        @! let xx <- gensym in
          let tt <- lift (write (rel_clause' x [] xx)) in
          ret xx
    | con n s =>
        @! let s' <- list_Mmap term_to_clauses s in
          let ax <- gensym in
          let tt <- lift (write (rel_clause' n s' ax)) in
          ret ax
    end.
  
  (* Patterns treat variables differently! *)
  Fixpoint term_pat_to_clauses (varmap : named_list V) (e : term)
    : stateT V (writer extended_clause) V :=
    match e with
    | var x => Mret (named_list_lookup default varmap x)
    | con n s =>
        @! let s' <- list_Mmap (term_pat_to_clauses varmap) s in
          let ax <- gensym in
          let tt <- lift (write (rel_clause' n s' ax)) in
          ret ax
    end.

  Definition sort_pat_to_clauses vm (t : sort)
    : stateT V (writer extended_clause) V :=
    match t with
    | scon n s =>
        @! let s' <- list_Mmap (term_pat_to_clauses vm) s in
          let ax <- gensym in
          let tt <- lift (write (rel_clause' n s' ax)) in
          ret ax
    end.

  Fixpoint ctx_pat_to_clauses (c : ctx)
    : stateT V (writer _) (list (V * V)) :=
    match c with
    | [] => Mret (M:=stateT V (writer _)) []
    | (n,t)::c' =>
        @! let vm <- ctx_pat_to_clauses c' in
          let t' <- sort_pat_to_clauses vm t in
          let n' <- gensym in
          let _ <- lift (write (rel_clause' sort_of [n'] t')) in
          ret (n,n')::vm
    end.

  Definition term_pat_to_clauses_known_ret (varmap : named_list V) (e : term) (retV : V)
    : stateT V (writer _) unit :=
    @! let e' <- term_pat_to_clauses varmap e in
      (lift (write (var_clause e' retV))).
  
  (*TODO: use writer that appends to the end or reverse *)
  Fail Fixpoint term_pat_to_upd (varmap : named_list V) (e : term)
    : stateT V (writer log_upd) V (* ret var *) :=
    match e with
    | var x => Mret (named_list_lookup default varmap x)
    | con n s =>
        @!let args <- list_Mmap (term_pat_to_upd varmap) s in
          let i <- gensym in
          let _ <- lift (write (let_row (Build_atom n args) i)) in
          let t := sort_of n s in
          let _ <- lift (write (put_row sort_of i t)) in
          ret i
    end.
  
(*
  Definition rewrite_to_log_op c t e1 e2 :=
    let (next, clauses, c', e1', t') :=
      (@!let {stateT V (writer _)}
               c' <- ctx_pat_to_clauses c in
         let t' <- sort_pat_to_clauses c' t in
         let e1' <- term_pat_to_clauses c' e1 in
         let _ <- lift (write (Build_atom _ _ sort_of [e1'] ,t')) in
         ret (c',e1',t') 0 in
    let (next', clauses', e2') :=
      (@!let {stateT V (writer (atom V V * V))}
               e2' <- term_pat_to_clauses c' e2 in
         let _ <- lift (write (var_clause e2' e1'))in
         TODO: need to subst in both sets of clauses in case e2' not new
         Question: is this a design issue?.
       In the case that both LHS and RHS are variables, can't unify them in the conclusion.
       Solution: just add a unify x,y command
                                                                               
       (*TODO: want to add the clause e1' = e2'; how best to write that?
           could have term_pat_to_clauses take a default arg?
           - likely best: take a fn of type stateT V _ V; use gensym normally,
             const arg for a default

          ex.:  x, y : A
                P : eq x y
                ----------
                x = y : A
          *)
         let _ <- lift (write (Build_atom _ _ sort_of [e2'] ,t')) in
         ret e2') next in
    (*TODO: for optimizing queries: is equivalence (or even inclusion) of queries decidable? (might be)
      idea: query-db correspondence: run one query on the other?
      - note: consider whether this requires a completeness theorem about queries (probably doesn't)
     *)

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
*)

End WithVar.
