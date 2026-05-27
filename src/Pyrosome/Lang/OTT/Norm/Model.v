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
Import Core.Notations.

(* The normalization (gluing) model as a cut-free Type-valued model over the
   first-order cast-free OTT language, on the ENVIRONMENT-FREE evaluator.

   Two terms are related at an exp/ty/sub/env sort iff they evaluate to the SAME
   semantic value/type/substitution/environment.  Because evaluation is environment-
   free the relation does NOT depend on the sort's arguments (no ambient context to
   thread), so it dispatches purely on the sort head; the static info sorts
   (relevance/lvl/tlvl/tyinfo) are compared by [nf_info], and proof-irrelevant sorts
   (ltl) are [unit].  Consequently SORT equality need only record matching head and
   arity — conversion ([cterm_conv]) is then the identity on the term relation. *)
Section Model.
  Notation term := (@term string).
  Notation sort := (@sort string).
  Notation ctx := (@ctx string).

  Definition sort_head (S : sort) : string := match S with scon n _ => n end.

  Definition norm_ceq_term (t : sort) (e1 e2 : term) : Type :=
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

  (* Sort equality: same head and arity.  (The term relation ignores sort arguments
     under env-free eval, so this suffices to make conversion sound.) *)
  Definition norm_ceq_sort (S1 S2 : sort) : Type :=
    match S1, S2 with
    | scon n1 a1, scon n2 a2 => ((eqb n1 n2 = true) * (length a1 = length a2))%type
    end.

  Definition Norm : CutTModel :=
    {|
      ceq_sort := norm_ceq_sort;
      ceq_term := norm_ceq_term;
    |}.

End Model.
