From Stdlib Require Import Classes.RelationClasses.
From coqutil Require Export Option.
From Utils Require Import Base Default.

Section __.
  Context {A : Type}.

  #[export] Instance option_default : WithDefault (option A) := None.

  
  Definition Is_Some (x : option A) := if x then True else False.
  
  #[export] Instance option_relation_trans {R : A -> A -> Prop} `{Transitive _ R}
    : Transitive (option_relation R).
  Proof.
    unfold option_relation.
    intros ? ? ? ? ?.
    repeat case_match; try tauto; eauto.
    congruence.
  Qed.

End __.
