(* Self-test for RigidityChecker on a tiny dependent language:
     N : Sort;  F : (n:N) -> Sort;
     z : N;  s : (n:N) -> N;  h : (n:N)(x : F n) -> F n
   Rules under test (contexts in snoc order: head = most recently bound):

   rule_rigid: ctx [x : F n; n : N],  LHS = h n x
     - x's expected sort at its occurrence = (F n)[/ [n |-> n] /] = F n = declared  -> rigid
     - n's expected = N = declared                                                  -> rigid
     EXPECT: nodes_ok = true; x rigid; n rigid.

   rule_nonrigid: ctx [x : F n; n : N],  LHS = h z x
     - x's expected = (F n)[/ [n |-> z] /] = F z <> F n declared  -> x NOT rigid
     - n not in fv(LHS): not a candidate
     - internal node z fits: output N = expected N                -> nodes_ok = true
     EXPECT: nodes_ok = true; x not rigid.

   rule_nested: ctx [x : F (s n); n : N],  LHS = h (s n) x
     - x's expected = (F n')[/ [n' |-> s n] /] = F (s n) = declared -> rigid
     - node (s n): output N = expected N                            -> ok
     EXPECT: all rigid. *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import RigidityChecker.
Import Core.Notations.


Definition N_ : sort := scon "N" [].
Definition F_ (e : term) : sort := scon "F" [e].
Definition z_ : term := con "z" [].
Definition s_ (e : term) : term := con "s" [e].
(* h's args in ctx order: most-dependent first: h x n ~ con "h" [x; n] *)
Definition h_ (x n : term) : term := con "h" [x; n].

Definition Ltest : lang :=
  [("rule_nested", term_eq_rule [("x", F_ (s_ (var "n"))); ("n", N_)]
                     (h_ (var "x") (s_ (var "n"))) z_ (F_ (s_ (var "n"))));
   ("rule_nonrigid", term_eq_rule [("x", F_ (var "n")); ("n", N_)]
                       (h_ (var "x") z_) z_ (F_ z_));
   ("rule_rigid", term_eq_rule [("x", F_ (var "n")); ("n", N_)]
                    (h_ (var "x") (var "n")) z_ (F_ (var "n")));
   ("h", term_rule [("x", F_ (var "n")); ("n", N_)] ["x"; "n"] (F_ (var "n")));
   ("s", term_rule [("n", N_)] ["n"] N_);
   ("z", term_rule [] [] N_);
   ("F", sort_rule [("n", N_)] ["n"]);
   ("N", sort_rule [] [])].

Eval vm_compute in (reports Ltest).
(* EXPECT:
   rule_nested:  nodes_ok=true,  x rigid, n rigid
   rule_nonrigid: nodes_ok=true, x NOT rigid
   rule_rigid:   nodes_ok=true,  x rigid, n rigid *)
