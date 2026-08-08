(* Adversarial probe of the Phase-2 transport conjecture: a language where an
   ungated equation has a ctx var in only ONE side, letting a trans-chain
   route through a middle whose image is unconstrained by the endpoints.
     L: sorts ty, S, val (A:ty); terms a b : ty, g : (x:S) -> ty;
        equations [x:S] |- g x = a : ty and [x:S] |- g x = b : ty.
   In c' = [x:S]: a ≡ g x ≡ b, hence eq_sort c' (val a) (val b).
   In []: if S has no closed inhabitant, a ≢ b (model argument), so
   transport FAILS even though both endpoint images are wf.
   Question: does L pass syntactic_sort_eq_langb'? *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.SyntacticSorts.
Import Core.Notations.

Notation lang := (@lang string).
Notation sort := (@sort string).
Notation term := (@term string).

Definition ty_ : sort := scon "ty" [].
Definition S_ : sort := scon "S" [].
Definition a_ : term := con "a" [].
Definition b_ : term := con "b" [].
Definition gx_ : term := con "g" [var "x"].

Definition L : lang :=
  [("rule2", term_eq_rule [("x", S_)] gx_ b_ ty_);
   ("rule1", term_eq_rule [("x", S_)] gx_ a_ ty_);
   ("val", sort_rule [("A", ty_)] ["A"]);
   ("g", term_rule [("x", S_)] ["x"] ty_);
   ("b", term_rule [] [] ty_);
   ("a", term_rule [] [] ty_);
   ("S", sort_rule [] []);
   ("ty", sort_rule [] [])].

Eval vm_compute in (index_heads_sat L).
Eval vm_compute in (syntactic_sort_eq_langb' L).
