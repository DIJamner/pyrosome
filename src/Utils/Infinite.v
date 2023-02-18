Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String Ascii.
From Utils Require Import Utils.

(* A class for using the infiniteness of types,
   designed to be convenient to use constructively
   via an implementation of choice for the complement
   of finite subsets of V.
   Note: this class is still for proof purposes
   and instances may have poor performance
 *)
Class Infinite (V : Type) := {
    gensym : list V -> V
  }.

Section WithInstance.
  Context (V : Type)
    {Inf : Infinite V}.

  Existing Instance Inf.

  Class Infinite_ok := {
      gensym_ok : forall l, ~ In (gensym l) l
    }.

  Context {Inf_ok : Infinite_ok}.

  Existing Instance Inf_ok.

  (* Useful when a concrete name is expected to be free,
   but would require a nontrivial proof.
   *)
  Definition gensym' `{Eqb V} (v : V) l :=
    if inb v l then gensym l else v.

  Lemma gensym'_ok `{Eqb_ok V}
    : forall (v : V) l, ~ In (gensym' v l) l.
  Proof.
    unfold gensym'.
    intros.
    case_match; basic_utils_crush.
    eapply gensym_ok; eauto.
  Qed.

End WithInstance.


#[export] Hint Resolve gensym_ok : utils.

  
Arguments Infinite_ok V%type_scope {Inf}.
 
#[export] Instance string_infinite : Infinite string :=
  {
    gensym l :=
      let len := S (list_max (map length l)) in
      string_of_list_ascii (repeat "!"%char len)
  }.


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
