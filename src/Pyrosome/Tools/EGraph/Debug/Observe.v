(* Debug scaffolding: cheap, blowup-proof observation of e-graph states.

   The e-graph automation (Automation.egraph_sound -> egraph_reducing_equal')
   does not terminate when it fails: the saturation loop is meant to
   short-circuit once the two subject ids unify, so when they never unify it
   runs to fuel exhaustion while the graph explodes.  These functions let us
   look at a (bounded) e-graph state WITHOUT dumping the whole thing -- they
   read sizes and single e-classes, and render positives back to readable
   source names through the renaming.

   Everything here is specialized to the `positive` instantiation that the
   egraph engine actually runs on (the string-level inputs are renamed to
   positive by egraph_reducing_equal'); use `of_p`/`unrename_term` with the
   renaming returned by setup to get readable output. *)
Set Implicit Arguments.

From Stdlib Require Import Lists.List Strings.String BinNums.
Import ListNotations.
Open Scope string.
Open Scope list.

From coqutil Require Import Map.Interface Datatypes.Result.
From Utils Require Import Utils Monad UnionFind TrieMap NamedList Result.
From Utils.EGraph Require Import Defs.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools Require Import PosRenaming.
From Pyrosome.Tools.EGraph Require Defs.
Import PosListMap.

(* The concrete e-graph state type the engine runs on. *)
Notation instance :=
  (Defs.instance positive positive trie_map trie_map (@pos_trie_map) (option positive)).

Section Observe.
  (* renaming back to the source variable type V (e.g. string) *)
  Context {V : Type} {V_default : WithDefault V}.
  Context (r : renaming V).

  Definition unp (p : positive) : V := @of_p V _ r p.

  Record egraph_stats :=
    {
      num_eclasses : nat;
      worklist_len : nat;
      epoch_val : positive;
      total_rows : nat;
      (* symbol (un-renamed) |-> number of rows in that table *)
      rows_per_symbol : list (V * nat);
    }.

  (* db rendered one level down: symbol |-> list of (args, db_entry).
     Uses the point-free `named_map map.tuples` idiom (as in print_egraph) so
     the inner trie's map instance resolves. *)
  Definition db_readout (g : instance) :=
    NamedList.named_map map.tuples (map.tuples g.(db)).

  Definition stats (g : instance) : egraph_stats :=
    let per_sym := map (fun p => (unp (fst p), List.length (snd p))) (db_readout g) in
    {|
      num_eclasses := List.length (map.tuples g.(equiv).(parent _ _ _));
      worklist_len := List.length g.(worklist);
      epoch_val := g.(epoch);
      total_rows := fold_right Nat.add 0%nat (map snd per_sym);
      rows_per_symbol := per_sym;
    |}.

  (* All enodes (atoms) in the e-class of x, rendered as readable terms.
     One class only, so this stays small even when the graph explodes. *)
  Definition readable_eclass (g : instance) (x : positive) : list (term V) :=
    let xr := snd (UnionFind.find g.(equiv) x) in
    let canon p := snd (UnionFind.find g.(equiv) p) in
    flat_map
      (fun p =>
         map (fun row =>
                con (unp (fst p)) (map (fun a => con (unp (canon a)) []) (fst row)))
           (filter (fun row => eqb (canon (snd row).(entry_value _ _)) xr) (snd p)))
      (db_readout g).

  (* Extracted normal form of an e-class, rendered as a readable term. *)
  Definition readable_nf (g : instance) (efuel : nat) (x : positive) : term V :=
    match Defs.extract_weighted g efuel x with
    | Success t => unrename_term r t
    | Failure _ => var default
    end.

End Observe.
