Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches.
From Named Require Import Compilers SimpleVSubst ElabCompilersWithPrefix.
Require SimpleSubst.
Module S := SimpleSubst.
Module VS := SimpleVSubst.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Definition ptcv : compiler :=
  match # from (S.subst_elab) with
  | {{s #"exp" "G" "A"}} => {{s #"val" "G" "A" }}
  | {{e #"subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"val_subst" "g" "e" }}
  end.

Eval compute in ptcv.

Derive ptcv_elab
       SuchThat (elab_preserving_compiler [] (VS.exp_subst++VS.value_subst) ptcv ptcv_elab S.subst_elab)
       As ptcv_elab_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve ptcv_elab_preserving : elab_pfs.
