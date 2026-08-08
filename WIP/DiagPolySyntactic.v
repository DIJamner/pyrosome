(* Diagnostic: which polymorphic languages fail syntactic_sort_eq_langb,
   and precisely why (index heads + offending term_eq rules). *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.SyntacticSorts.
From Pyrosome Require Import Lang.PolySubst.
Import Core.Notations.

(* The type-substitution calculus alone: predict PASS (ty is NOT an index
   head here -- nothing is indexed by a ty). *)
Definition L_tysub := ty_subst_lang ++ ty_env_lang.

(* Add parameterized values: now [val D G A] makes [ty] an index head,
   and ty_subst_lang's [ty_act_*] equations conclude at [ty]: predict FAIL. *)
Definition L_val := val_parameterized ++ ty_subst_lang ++ ty_env_lang.

Eval vm_compute in (syntactic_sort_eq_langb L_tysub).
Eval vm_compute in (syntactic_sort_eq_langb L_val).

(* Show the index heads of L_val. *)
Eval vm_compute in (index_heads_b L_val).

(* Show which term_eq rules conclude at an index head of L_val. *)
Eval vm_compute in
  (let R := index_heads_b L_val in
   map fst (filter (fun p => match snd p with
                    | term_eq_rule _ _ _ t => inb (sort_head t) R
                    | _ => false end) L_val)).

(* Are there any sort_eq_rules at all in L_val? *)
Eval vm_compute in
  (map fst (filter (fun p => is_sort_eq_ruleb (snd p)) L_val)).

(* For each offending rule: is any ctx var a pure "gate" (appears in NO
   equated term)?  Print [ctx names] and [fv e1 ++ fv e2] for each. *)
Definition offenders : list string := ["ty_act_id"; "ty_act_cmp"; "ty_snoc_hd"].

Eval vm_compute in
  (map (fun nm => match named_list_lookup_err L_val nm with
        | Some (term_eq_rule c e1 e2 t) =>
            (nm, (map fst c, (fv e1 ++ fv e2, fv_sort t)))
        | _ => (nm, ([], ([], []))) end) offenders).
