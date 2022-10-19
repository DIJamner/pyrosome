Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.

From bedrock2 Require Import Syntax.

From Utils Require Import Utils.
From Named Require Import Substable Model GeneralModel.
From Named Require Import Term Rule.



Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).

(* This the the `term` type that should get plugged into the general model.
   We'll be adding a few more sorts later, but this is good for now.
   If you see an `access_size` just assume it is `word` for the moment,
   and if you see a bopname, assume it is `add`.
   The general model that you've been developing is well-suited for simple sorts
   (i.e. sorts that don't contain terms) and my current thinking is that
   we might want to specialize it to this case since it's a common one and
   will make most of the proofs we do easier.
   We can leave that for later though.

   For now, it would be helpful to look at the syntax of bedrock programs
   and start thinking about how to most easily fit it to the general model.
   We'll also need a Pyrosome encoding of bedrock at some point,
   although I wouldn't worry about completeness there any time soon.
 *)

(* this *)
Variant bedrock_term :=
  | bedrock_expr (e : expr)
  | bedrock_cmd (c : cmd).

Variant bedrock_sort :=
  | br_expr
  | br_cmd.

Print Substable0.
Print Model.Model.

Print Model.Model_ok.
Print Substable.subst.
Set Printing Implicit.
Print GeneralModel.model.

Check (GeneralModel.model (V := string)).

(* Need to supply eq_sort, eq_term, wf_sort, wf_term on lcosed terms here *)
Definition bedrock_model := GeneralModel.model (V := string) bedrock_term.
Definition bedrock_model_ok : Model.Model_ok bedrock_model := GeneralModel.model_ok bedrock_term bedrock_sort.

Check GeneralModel.model.
Check Model.Model.
Check bedrock_model.
Definition get_substable (m : Model.Model) : Substable.Substable.

  (* Make a pyrosome language with a limited subset of the bedrock language *)
