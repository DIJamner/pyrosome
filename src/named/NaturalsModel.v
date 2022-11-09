Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Substable Model GeneralModel Term.
Require Import Coq.Logic.FunctionalExtensionality.

(* Import CompilerDefs.Notations. *)

Require Coq.derive.Derive.


Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
    {|
      term_substable := _;
      sort_substable := _;
      Model.eq_sort := eq_sort;
      (*TODO: rename the conflict*)
      Model.eq_term := eq_term;
      Model.wf_sort := wf_sort;
      Model.wf_term := wf_term;
    |}.

Section WithV.
Context {V : Type}.

Notation named_list := (@named_list V).
Notation Substable0 := (Substable0 V).
Notation Substable := (@Substable V).

Definition sort := Type.

Definition exp := nat.
Definition eq_exp (m n : exp) := m = n.
Definition wf_exp (m : exp) (t : Type) := t = nat.

Lemma exp_symm : forall e1 e2, eq_exp e1 e2 -> eq_exp e2 e1.
Proof.
  unfold eq_exp in *; intros.
  auto.
Qed.

Lemma exp_refl : forall e, eq_exp e e.
Proof.
  unfold eq_exp in *; intros.
  auto.
Qed.

Lemma exp_trans : forall e1 e2 e3, eq_exp e1 e2 -> eq_exp e2 e3 -> eq_exp e1 e3.
Proof.
  unfold eq_exp in *; intros.
  rewrite H.
  auto.
Qed.

Section WithEqb.
  Context {V_Eqb : Eqb V}.

Instance model : Model := GeneralModel.model 0 eq_exp wf_exp.
Instance model_ok : Model_ok model := GeneralModel.model_ok 0 eq_exp exp_symm exp_trans exp_refl wf_exp.

(* Constant folding:
   Gallina Fixpoint function operating on Terms from nat_lang_def
 *)

Notation term := (term string).

Fixpoint is_constant (t : term) : bool :=
  match t with
  | con "+1" [a] => is_constant a
  | con "0" [] => true
  | _ => false
  end.

Fixpoint add_constants (a b : term) : term :=
  match a with
  | con "+1" [a'] => add_constants a' (con "+1" [b])
  | _ => b
  end.

Fixpoint constant_fold (t : term) : term :=
  match t with
  | con "plus" [a; b] =>
      let a := constant_fold a in
      let b := constant_fold b in
      if (andb (is_constant a) (is_constant b))
      then add_constants a b
      else con "plus" [a; b]
  | _ => t
  end.

Definition plus a b : term := con "plus" [a; b].

Definition var : term := var "test".

Fixpoint num n : term :=
  match n with
  | 0 => con "0" []
  | S n' => con "+1" [num n']
  end.

Definition example := (plus (plus (plus (num 1) (num 2)) var) (plus (plus (num 2) (plus (num 0) (num 1))) (num 2))).

Compute (constant_fold example).

Local Notation compiler V := (compiler V (tgt_term := term (V:=V)) (tgt_sort := sort)).

Print nat_lang.

  Definition nat_lang_model_def : compiler string :=
    [
      ("plus", term_case ["b"; "a"] (bin_op plus (inj_var "a") (inj_var "b")));
      ("1+", term_case ["n"] (bin_op plus (inj_var "n") (val 1)));
      ("0", term_case [] (val 0));
      ("natural", sort_case [] (nat : Type))
    ].

Ltac break_preserving_compiler :=
  repeat match goal with
  | [ |- preserving_compiler_ext _ ?H _] => unfold H
  | [ |- preserving_compiler_ext _ _ ?H] => unfold H
  | [ |- preserving_compiler_ext _ _ ((_, Rule.term_rule ?a _ _) :: _)] => apply (CompilerDefs.preserving_compiler_term _ a)
  | [ |- preserving_compiler_ext _ _ ((_, Rule.sort_rule ?a _) :: _)] => apply (CompilerDefs.preserving_compiler_sort _ a)
  | [ |- preserving_compiler_ext _ _ ((_, Rule.term_eq_rule _ _ _ _) :: _)] => apply CompilerDefs.preserving_compiler_term_eq
  | [ |- preserving_compiler_ext _ _ ((_, Rule.sort_eq_rule _ _) :: _)] => apply CompilerDefs.preserving_compiler_sort_eq
  | [ |- preserving_compiler_ext _ [] []] => apply CompilerDefs.preserving_compiler_nil
  | _ => idtac
  end.

Ltac auto_preserving :=
  break_preserving_compiler;
  simpl; unfold wf_sort, wf_term, ws_term, eq_term, apply_subst;
  simpl; unfold term_subst;
  repeat
    (simpl; trivial; intros;
     match goal with
     | [ |- _ /\ _] => constructor
     | [ |- id_substable (val _)] => apply val_id_substable
     | [ |- id_substable (inj_var _)] => apply inj_var_id_substable
     | [ |- id_substable (bin_op _ _ _)] => apply bin_op_id_substable
     | [ |- _ = _] => unfold bin_op, inj_var, var, val
     | _ => idtac
     end; auto).

  Lemma nat_lang_model_preserving :
    (preserving_compiler_ext (V:=string) (H := fun _ => 0) (H0 := nat) (tgt_Model := model) [] nat_lang_model_def nat_lang).
  Proof.
    auto_preserving.
    - rewrite PeanoNat.Nat.add_shuffle0; apply PeanoNat.Nat.add_assoc.
  Qed.
