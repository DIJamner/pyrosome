(* An implementation of the core of egglog

   TODO: benchmark, then use plist everywhere feasible and retest
 *)
Require Import Equalities Orders Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
Require Import Tries.Canonical.

From Utils Require Import Utils Monad Natlike ArrayList ExtraMaps UnionFind.
From Utils.EGraph Require Import Defs QueryOpt.
From Utils Require TrieMap.
Import Sets.
Import StateMonad.


(*TODO: move somewhere*)
Definition Is_Some_satisfying {A} (P : A -> Prop) x :=
  match x with
  | Some x => P x
  | None => False
  end.
Notation "x <$> P" :=
  (Is_Some_satisfying P x)
    (at level 56,left associativity).

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)

      (*TODO: just extend to Natlike?*)
      (idx_succ : idx -> idx)
      (idx_zero : idx)
      (*TODO: any reason to have separate from idx?*)
      (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol).

  Notation atom := (atom idx symbol).

  Definition atom_subst (sub : named_list idx idx) (a : atom) :=
    Build_atom
      a.(atom_fn)
      (map (fun x => named_list_lookup x sub x) a.(atom_args))
      (named_list_lookup a.(atom_ret) sub a.(atom_ret)).


(* Alternate approach: consider the initial model of the theory.
   Terms added at the start form a no-premise rule, so can be ignored.
 *)
  Record model : Type :=
    {
      (* represents the quotiented idx.
         TODO: to realize the quotient, should I include a domain equiv?
         - would let me use e.g. terms as the domain
         - alternatively, I can use idx as the domain, and take the quotient
           to be implied by the non-bijectivity of constants.
       *)
      domain : Type;
      (* included to support setoids *)
      domain_eq : domain -> domain -> Prop;
      (*constants : idx -> domain; TODO: do I have any constants? *)
      interpretation : symbol -> list domain -> option domain;
    }.

  Definition eval_atom m (assignment : named_list idx m.(domain)) f args : option m.(domain) :=
    @!let args' <- list_Mmap (named_list_lookup_err assignment) args in
      (m.(interpretation) f args').
      
  Definition assignment_satisfies m
    (assignment : named_list idx m.(domain)) : list atom -> Prop :=
    all (fun a => (eval_atom m assignment a.(atom_fn) a.(atom_args)) <$>
                    (fun r => (named_list_lookup_err assignment a.(atom_ret)) <$>
                    (m.(domain_eq) r))).

  Definition assignment_unifies m
    (assignment : named_list idx m.(domain)) : list (idx * idx) -> Prop :=
    all (fun '(x,y) => named_list_lookup_err assignment x <$>
                         (fun xv => named_list_lookup_err assignment y <$>
                                      (m.(domain_eq) xv))).
  
  (* TODO: rewrite properties to be easier to read
   *)
  Record model_of
    (m : model)
    (rw : list (log_rule idx symbol)) : Prop :=
    {
      (* TODO: does it need to be an equivalence? *)
      domain_eq_PER : PER m.(domain_eq);
      rules_sound : all (fun r =>
                           forall query_assignment,
                             map fst query_assignment = r.(query_vars _ _) ->
                             assignment_satisfies m query_assignment r.(query_clauses _ _) ->
                             exists out_assignment,
                               (* query assignment first eliminates the need for an all_fresh condition*)
                               assignment_satisfies m (query_assignment ++ out_assignment)
                                 r.(write_clauses _ _)
                               /\ assignment_unifies m (query_assignment ++ out_assignment)
                                 r.(write_unifications _ _))
                      rw
    }.

  
  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map)
    (symbol_map_ok : forall A, map.ok (symbol_map A)).

  Context 
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (* TODO: define and assume weak_map_ok*)
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_plus : map_plus idx_trie).

  Notation instance := (instance idx symbol symbol_map idx_map idx_trie).
  (*TODO: many of these relations can be functions. what's the best way to define them?*)
  Definition atom_in_egraph '(Build_atom f args out) (i : instance) :=
    (map.get i.(db _ _ _ _ _) f) <$>
      (fun tbl => (map.get tbl args) <$>
                    (fun r => snd r = out)).

  Definition SomeRel {A B} (R : A -> B -> Prop) ma mb :=
    match ma, mb with
    | Some a, Some b => R a b
    | _, _ => False
    end.

  (* TODO: this is parametric, use the initial model instead? No.
     TODO: this is proof relevant; keep it that way or no?
   *)
  Record egraph_sound_for_model e m :=
    {
      (*  TODO: Is this the best way? Could also identify idxs w/ terms/atom trees
         terms/atom trees from the initial model.

         TODO: how to ensure this covers the whole domain?
       *)
      idx_interpretation : idx -> option m.(domain);
      (* TODO: write in a more natural way*)
      atom_interpretation :
      forall a,
        atom_in_egraph a e ->
        (Mbind (m.(interpretation) a.(atom_fn))
           (list_Mmap idx_interpretation a.(atom_args))) <$>
          (fun d => (idx_interpretation a.(atom_ret)) <$> (m.(domain_eq) d));
    }.

  Definition egraph_sound e rs :=
    forall m : model,
      model_of m rs ->
      egraph_sound_for_model e m.

  Context (spaced_list_intersect
             (*TODO: nary merge?*)
            : forall {B} (merge : B -> B -> B),
              ne_list (idx_trie B * list bool) ->
              (* Doesn't return a flag list because we assume it will always be all true*)
              idx_trie B).

  Theorem empty_sound rs : egraph_sound (empty_egraph idx_zero) rs.
  Proof.
    unfold empty_egraph.
    unshelve econstructor.
    1: exact (fun _ => None).
    unfold atom_in_egraph;
      destruct a;
      basic_goal_prep.
    rewrite map.get_empty in *.
    basic_goal_prep.
    tauto.    
  Qed.

  
  Notation saturate_until := (saturate_until idx_succ idx_zero spaced_list_intersect).
  
  Theorem saturation_sound e rs rs' P fuel b e'
    : (*TODO: needed: predicate_sound P rs -> *)
      egraph_sound e rs ->
      (*TODO: relationship between compiled rs' and uncompiled rs? incl rs' rs ->*)
      saturate_until rs' P fuel e = (b, e') ->
      egraph_sound e' rs.
  Proof.
    revert e.
    induction fuel;
      basic_goal_prep;
      basic_utils_crush;[].
  Abort.

End WithMap.

Arguments atom_in_egraph {idx symbol}%type_scope {symbol_map idx_map idx_trie}%function_scope
  pat i.

Arguments model_of {idx}%type_scope {Eqb_idx} {symbol}%type_scope m rw%list_scope.

Arguments assignment_satisfies {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  m assignment%list_scope _%list_scope.
Arguments assignment_unifies {idx}%type_scope {Eqb_idx} {symbol}%type_scope 
  m assignment%list_scope _%list_scope.
