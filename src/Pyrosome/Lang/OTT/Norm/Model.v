Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Gluing Require Import CutTModel.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel.
From Pyrosome.Lang.OTT Require Import Base Nat.
Import Core.Notations.

(* The normalization (gluing) model as a cut-free Type-valued model over the
   first-order cast-free OTT language, on the ENVIRONMENT-FREE evaluator.

   The model relation has TWO components (a product):
   - the Core judgmental equality [eq_term fo_lang [] t e1 e2] (resp. [eq_sort]).
     This is the *well-formedness* gate the user identified as the missing
     structure: the relation only accepts inputs that are well formed AT THE
     SORT [t] (eq_term .. t entails wf_term .. t), and it is what every law
     discharges via the corresponding Core lemma (this part is exactly the
     SyntacticModel CutTModel_ok).
   - the eval GLUE: the two terms evaluate to the SAME semantic value/type/
     substitution/environment.  Because evaluation is environment-free the glue
     does NOT depend on the sort's arguments (no ambient context to thread), so
     it dispatches purely on the sort head; the static info sorts
     (relevance/lvl/tlvl/tyinfo) are compared by [nf_info], and proof-irrelevant
     sorts (ltl) are [unit].

   The well-formedness component supplies, for the Tier-C eliminator/composition
   cases, the typing/scope facts the eval glue needs (canonical forms, lengths)
   which are FALSE for the ill-typed junk that an unguarded relation would admit. *)

Definition fo_lang : lang string := ott_nat ++ ott_base ++ subst_ott ++ ott_info.

Section Model.
  Notation term := (@term string).
  Notation sort := (@sort string).
  Notation ctx := (@ctx string).

  Definition sort_head (S : sort) : string := match S with scon n _ => n end.

  (* The eval glue: two terms glue iff they evaluate to the same semantic value. *)
  Definition glue_term (t : sort) (e1 e2 : term) : Type :=
    match t with
    | scon n args =>
        if eqb n "exp"
        then { v : sval & (eval_rel e1 v * eval_rel e2 v)%type }
        else if eqb n "ty"
        then { S : svalty & (eval_ty e1 S * eval_ty e2 S)%type }
        else if eqb n "sub"
        then { s : ssub & (eval_sub e1 s * eval_sub e2 s)%type }
        else if eqb n "env"
        then { Genv : senv & (eval_env e1 Genv * eval_env e2 Genv)%type }
        else match args with
             | [] => (nf_info e1 = nf_info e2)  (* relevance/lvl/tlvl/tyinfo *)
             | _ => unit                         (* ltl etc.: proof-irrelevant *)
             end
    end.

  (* norm_ceq_term relates only WELL-FORMED terms at the sort [t] (the eq_term
     component), additionally gluing them to a common semantic value. *)
  Definition norm_ceq_term (t : sort) (e1 e2 : term) : Type :=
    (eq_term fo_lang [] t e1 e2 * glue_term t e1 e2)%type.

  (* Glue for sorts: same head and arity. *)
  Definition glue_sort (S1 S2 : sort) : Type :=
    match S1, S2 with
    | scon n1 a1, scon n2 a2 => ((eqb n1 n2 = true) * (length a1 = length a2))%type
    end.

  Definition norm_ceq_sort (S1 S2 : sort) : Type :=
    (eq_sort fo_lang [] S1 S2 * glue_sort S1 S2)%type.

  Definition Norm : CutTModel :=
    {|
      ceq_sort := norm_ceq_sort;
      ceq_term := norm_ceq_term;
    |}.

End Model.
