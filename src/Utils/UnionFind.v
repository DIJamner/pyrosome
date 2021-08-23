(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.
*)
Require Import Equalities Orders ZArith.

From Utils Require Import Natlike ArrayList.


(* All definitions and proofs need to be generic over arraylist implementations.
   Use the following code to test functions with a specific implementation: *)
Module UnionFind.   
  From Utils Require PersistentArrayList.
  Import PersistentArrayList.Int63Natlike.
  Import PersistentArrayList.PArrayList.

(* Use this module declaration for proofs.
Module UnionFind
       (Import NL : Natlike)
       (Import AL : ArrayList NL)
       (Import ALS : ArrayListSpec NL AL).
*)

(* For functions with difficult termination conditions, use fuel.
   Note: eventually we will use an upper bound on rank
*)  
