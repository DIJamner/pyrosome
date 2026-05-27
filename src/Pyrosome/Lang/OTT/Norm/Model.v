Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Gluing Require Import CutTModel.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Env.
Import Core.Notations.

(* The normalization (gluing) model as a cut-free Type-valued model over the
   first-order cast-free OTT language. Two terms are related when they evaluate to
   the same semantic value in the reflecting environment of their sort's context
   [G] (which [eval_env] builds by normalizing [G] to its ext-telescope). Two
   sorts are related when they share a head and a normalized context.

   This file gives the judgments [Norm : CutTModel]; the CutTModel_ok operations
   (the per-former congruence/computation coherence) come next. *)
Section Model.
  Notation term := (@term string).
  Notation sort := (@sort string).
  Notation ctx := (@ctx string).

  Definition sort_head (S : sort) : string := match S with scon n _ => n end.
  (* The ambient env is the LAST argument of a sort: Pyrosome stores con/scon
     arguments in the rule's context order (innermost binding first), so for
     [exp G i A] / [ty G i] / [sub G' G] the env [G] sits last, not first. *)
  Definition sort_env (S : sort) : term :=
    match S with scon _ args => List.last args (con "emp" []) end.

  (* Normal form of the *static* info fragment (relevance / lvl / tlvl / tyinfo).
     This data has no environment and is not subject to the substitution calculus;
     its only computation is the [tlvl] rewriting [next L0 = iota L1], [next L1 = inf]
     (rules next0/next1).  Everything else is in normal form, so [nf_info] recurses
     structurally and only fires on [next].  Using [nf_info]-equality (rather than the
     old trivial [eval_env = [] ] collapse, which identified *all* info data) is what
     makes the info-sorted [ceq_term] sound and validates next0/next1 in [cterm_by].
     Inner [let fix] over the argument list per the [term] recursion idiom (a top-level
     mutual fixpoint over [list term] would fail the guard checker). *)
  Fixpoint nf_info (e : term) : term :=
    match e with
    | var x => var x
    | con n args =>
        let args' :=
          (fix nf_list (l : list term) : list term :=
             match l with
             | [] => []
             | x :: xs => nf_info x :: nf_list xs
             end) args in
        if eqb n "next"
        then match args' with
             | [l'] =>
                 match l' with
                 | con m [] =>
                     if eqb m "L0" then con "iota" [con "L1" []]
                     else if eqb m "L1" then con "inf" []
                     else con "next" [l']
                 | _ => con "next" [l']
                 end
             | _ => con n args'
             end
        else con n args'
    end.

  Definition norm_ceq_term (t : sort) (e1 e2 : term) : Type :=
    match t with
    | scon n args =>
        match args with
        | [] =>
            (* argless sorts: [env] is compared by its reflecting environment;
               the static info sorts (tyinfo/tlvl/lvl/relevance) by [nf_info]. *)
            if eqb n "env"
            then (eval_env e1 = eval_env e2)
            else (nf_info e1 = nf_info e2)
        | _ =>
            let G := List.last args (con "emp" []) in
            if eqb n "exp"
            then { v : sval & (eval_rel (eval_env G) e1 v * eval_rel (eval_env G) e2 v)%type }
            else if eqb n "ty"
            then { S : svalty & (eval_ty (eval_env G) e1 S * eval_ty (eval_env G) e2 S)%type }
            else if eqb n "sub"
            then { rr : senv & (eval_sub (eval_env G) e1 rr * eval_sub (eval_env G) e2 rr)%type }
            else unit
        end
    end.

  (* The "environment-bearing" sorts: their last argument is an actual env, so the
     model compares it by [eval_env].  The static sorts (tyinfo/tlvl/lvl/relevance/
     ltl) have no env — comparing their [List.last] by [eval_env] would be the same
     collapse fixed on the term side — so they are compared argument-wise by
     [nf_info] instead.  ([env] itself is nullary, so either branch is trivial; it
     sits here only for uniformity with the env-bearing sorts.) *)
  Definition is_env_sort (n : string) : bool :=
    eqb n "exp" || eqb n "ty" || eqb n "sub" || eqb n "env".

  (* The dispatch is kept in [Prop] (via [return Prop]) so the [Prop] rule-name
     disjunction can be eliminated into it during [csort_cong]; left at [Type] (the
     second factor of the [Type]-level [*] below) that elimination is forbidden. *)
  Definition norm_ceq_sort (S1 S2 : sort) : Type :=
    ((eqb (sort_head S1) (sort_head S2) = true)
     * (match S1, S2 return Prop with
        | scon n1 args1, scon _ args2 =>
            if is_env_sort n1
            then eval_env (List.last args1 (con "emp" []))
                 = eval_env (List.last args2 (con "emp" []))
            else map nf_info args1 = map nf_info args2
        end))%type.

  Definition Norm : CutTModel :=
    {|
      ceq_sort := norm_ceq_sort;
      ceq_term := norm_ceq_term;
    |}.

End Model.
