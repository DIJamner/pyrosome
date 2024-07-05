Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches
  (*Import as a temporary fill until this file can be removed*)
  Lang.PolySubst.
From Pyrosome.Lang Require Export GenericSubst.
Import Core.Notations.


Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).

Export Pyrosome.Lang.PolySubst
  (value_subst, value_subst_def, value_subst_wf,
    block_subst, block_subst_def, block_subst_wf).
#[export] Hint Resolve value_subst_wf : elab_pfs.
#[export] Hint Resolve block_subst_wf : elab_pfs.


Definition exp_subst : lang := exp_ret ++ exp_subst_base.
Definition exp_subst_def := exp_ret_def ++ exp_subst_base_def.

(*TODO: duplicated*)
Lemma exp_subst_wf : elab_lang_ext value_subst exp_subst_def exp_subst.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_subst_wf : elab_pfs.
