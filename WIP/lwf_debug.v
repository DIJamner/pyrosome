Set Implicit Arguments.
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Import Core.Notations.

Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation lang := (@lang string).

Definition ty_ : sort := scon "ty" [].
Definition S_ : sort := scon "S" [].
Definition a_ : term := con "a" [].
Definition b_ : term := con "b" [].
Definition gx_ : term := con "g" [var "x"].

Definition L : lang :=
  [("rule2", term_eq_rule [("x", S_)] gx_ b_ ty_);
   ("rule1", term_eq_rule [("x", S_)] gx_ a_ ty_);
   ("val",   sort_rule   [("A", ty_)] ["A"]);
   ("g",     term_rule   [("x", S_)] ["x"] ty_);
   ("b",     term_rule   [] [] ty_);
   ("a",     term_rule   [] [] ty_);
   ("S",     sort_rule   [] []);
   ("ty",    sort_rule   [] [])].

Lemma L_wf : wf_lang L.
Proof.
  repeat constructor; basic_core_crush; try congruence.
Admitted.
