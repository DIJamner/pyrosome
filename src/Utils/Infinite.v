Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String Ascii.
From Utils Require Import Utils.

(* A class for using the infiniteness of types,
   designed to be convenient to use constructively.
   Note: this class is still for proof purposes
   and instances may have poor performance
 *)
Class Infinite (V : Type) := {
    gensym : list V -> V
  }.

Class Infinite_ok (V : Type) `{Infinite V} := {
    gensym_ok : forall l, ~ In (gensym l) l
  }.

Arguments Infinite_ok V%type_scope {H}.
 
#[export] Instance string_infinite : Infinite string :=
  {
    gensym l :=
      let len := S (list_max (map length l)) in
      string_of_list_ascii (repeat "!"%char len)
  }.

(*TODO: move to Utils.v*)
Lemma string_of_list_ascii_length l
  : length (string_of_list_ascii l) = List.length l.
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
Qed.

#[export] Instance string_infinite_ok : Infinite_ok string.
Proof.
  constructor; unfold gensym, string_infinite.
  intro l.
  set (string_of_list_ascii _) as s.
  intro HIn.
  assert ((list_max (map length l))< length s).
  {
    subst s.
    rewrite string_of_list_ascii_length, repeat_length.
    auto.
  }
  assert (map length l <> nil) by (destruct l; simpl; basic_utils_crush).
  epose proof (list_max_lt _ H0).
  apply H1 in H.
  assert (In (length s) (map length l)) by eauto using in_map.
  eapply Forall_forall in H; eauto.
  eapply PeanoNat.Nat.lt_irrefl; eauto.
Qed.
