Set Implicit Arguments.
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import WIP.DttSyntax WIP.DttNf.
Import Core.Notations.

Lemma t1 G1 i1 A1 G2 i2 A2 : oExt G1 i1 A1 = oExt G2 i2 A2 -> G1 = G2.
Proof. intro H. inversion H. reflexivity. Qed.

Lemma t2 G i A : oExt G i A = oEmp -> False.
Proof. intro H. discriminate H. Qed.

Lemma t3 G r l G' i A : oU G r l = oExt G' i A -> False.
Proof. intro H. discriminate H. Qed.

Lemma t4 l1 l2 : iCode l1 = iCode l2 -> l1 = l2.
Proof. intro H. inversion H. reflexivity. Qed.

Lemma t5 l r l2 : iCode l = iEl r l2 -> False.
Proof. intro H. discriminate H. Qed.

Lemma t6 G i A x : VarT G i A x -> True.
Proof. intro H. inversion H; subst; exact I. Qed.
