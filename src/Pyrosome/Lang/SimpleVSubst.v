Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Resolution Tools.EGraph.ComputeWf
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

(* TODO: modernize the definitions in PolySubst *)
Export Pyrosome.Lang.PolySubst
  (value_subst, value_subst_def, value_subst_wf,
    block_subst, block_subst_def, block_subst_wf).

(*TODO: check that I don't need these hints
#[local] Definition value_subst_entry :=
  lang_entry (elab_lang_implies_wf value_subst_wf).
#[export] Hint Resolve value_subst_entry : wf_lang_db.
#[local] Definition block_subst_entry :=
  lang_entry (elab_lang_implies_wf block_subst_wf).
#[export] Hint Resolve block_subst_entry : wf_lang_db.
*)

Definition exp_subst : lang := exp_ret ++ exp_subst_base.
Definition exp_subst_def := exp_ret_def ++ exp_subst_base_def.

(*TODO: duplicated *)
#[deprecated(note="Re-proves facts from PolySubst. Just use those.")]
Lemma exp_subst_wf : wf_lang_ext value_subst exp_subst.
Proof. compute_wf_lang. Qed.

(*TODO: check that I don't need this hint
#[local] Definition exp_subst_entry :=
  lang_entry exp_subst_wf.
#[export] Hint Resolve exp_subst_entry : wf_lang_db.
*)

Definition value_subst_injectivity :=
  [("hd", ["A"; "G"]); ("wkn", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("ext", ["A"; "G"]);
   ("forget", ["G"]); ("emp", []); ("val_subst", ["A"; "G"]); ("val", ["A"; "G"]);
   ("cmp", ["G3"; "G1"]); ("id", ["G"]); ("sub", ["G'"; "G"]); ("env", []); ("ty", [])].

Definition exp_subst_injectivity :=
  [("ret", ["v";"A"; "G"]); ("exp_subst", ["A"; "G"]); ("exp", ["A"; "G"])].
