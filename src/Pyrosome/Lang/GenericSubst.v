Require Import Ascii Lists.List Datatypes.String.
Import ListNotations.
Require Import Utils.Utils.
Require Import Pyrosome.Theory.Core.
Import Core.Notations.

Local Open Scope string.  

Definition definitely_fresh (s : string) (l : list string) :=
  let len := List.fold_left Nat.max (map String.length l) 0 in
  String.append s (string_of_list_ascii (repeat ("'"%char : ascii) len)).

Definition choose_fresh (s : string) (c:list string) :=
  if negb (inb s c) then s else definitely_fresh s c.

Definition tysubst_prefix_map :=
  [("exp", "exp_ty_");
   ("val", "val_ty_");
   ("sub", "sub_ty_");
   ("env", "env_ty_");
   ("blk", "blk_ty_");
   ("ty", "ty_")
  ].

Definition expsubst_prefix_map :=
  [("exp", "exp_");
   ("val", "val_");
   ("blk", "blk_")   
  ].

Variant subst_mode := val_subst_mode | type_subst_mode.
Definition is_val_subst (m : subst_mode) := if m then true else false.

Section __.
  Context (mode : subst_mode).

  Let default_ctx_name := if is_val_subst mode then "G'" else "D'".
  Let default_subst_name := if is_val_subst mode then "g" else "d".

  Let prefix_map := if is_val_subst mode then expsubst_prefix_map else tysubst_prefix_map.

  Definition prefix := (if is_val_subst mode then "" else "ty_").

  (*Let subst := named_list_lookup "ERR" prefix_map sort ++ "subst".*)
  Let snoc := prefix ++ "snoc".
  Let cmp := prefix ++ "cmp".
  Let hd := prefix ++ "hd".
  Let wkn := prefix ++ "wkn".
  Let forget := prefix ++ "forget". (*
  Let emp := prefix ++ "emp".
  Let ext := prefix ++ "ext".*)

  Definition under s :=
    {{e #snoc (#cmp #wkn {s}) #hd}}.

  (* TODO: half-hardcoded. Less of an issue here because the multiplicity is by env, not subst target *)
  (* G: codom of g
     s: codom of resultant subst
     TODO: G' is arriving from out-of-context. WHy does it not equal G?
   *)
  Fixpoint gen_arg_subst G g s :=
    match s with
    | {{e#"ty_emp"}}
    | {{e#"emp"}} => {{e#forget}}
    | var G' => if G =? G' then var g else {{e#"ERR1" G G'}}
    | {{e#"ext" {s'} {_} }} => under (gen_arg_subst G g s')
    | {{e#"ty_ext" {s'} }} => under (gen_arg_subst G g s')
    | _ => {{e#"ERR2" {s} }}
    end.

    
Section WithRule.
  Context (l : lang string) (name : string) (r : rule string).
  Let c_args_and_t :=
        match r with
        | term_rule c args t => (c,args,t)
        | _ => default
        end.
  Let c : ctx _ := fst (fst c_args_and_t).
  Let args := snd (fst c_args_and_t).
  (* TODO: how to manage possible substs on elements of the type? *)
  Let t := snd c_args_and_t.
  (*INVARIANT: env is the last component of the sort and is a metavariable
    TODO: how to autogenerate G substs for All, Exists?
   *)
  Let G : string := let (_,s):= t in
           match last s default with
           | var G => G
           | con _ _ => "ERR"
           end.
  Let sort_name := let (n,_):= t in n.
  
  Let G' := choose_fresh default_ctx_name (map fst c).
  Let g := choose_fresh default_subst_name (map fst c).

  Let subst t := named_list_lookup "ERR" prefix_map t ++ "subst".
  Let sub := prefix ++ "sub".
  Let emp := prefix ++ "emp".
  Let ext := prefix ++ "ext".
  Let env := prefix ++ "env".

  Let lhs :=
        let blank_term := con name (map var args) in
        {{e #(subst sort_name) g {blank_term} }}.
  
  Fixpoint gen_rhs_subterms c args {struct c} :=
    match c, args with
    | (n1,t)::c', n2::args' =>
      if n1 =? n2
      then
        match t with
        | scon name [G']
        | scon name [_;G']
        | scon name [_;_;G'] =>
            (if named_list_lookup_err prefix_map name then
               let s := gen_arg_subst G g G' in
               {{e #(subst name) {s} n1 }}
             else var n2)
              ::(gen_rhs_subterms c' args')
        | _ => (var n2)::(gen_rhs_subterms c' args')
        end
      else gen_rhs_subterms c' args
    | _, _ => []
    end.

  Let rhs : term _ := con name (gen_rhs_subterms c args).

  (* TODO: parameterization for G : env D *)
  Let c' := (g,{{s #sub G' G }})::(G',{{s #env }})::c.

  (* c is the context from the sort's rule *)
  Fixpoint gen_sort_subterms c args s {struct c} :=
    match c, args, s with
    (* we should never apply a subst to the last argument
       (Note: small bug possible on future language extensions related to above principle)
       If the last arg is the env, replace it
     *)
    | [_], [_], [var G_var] =>
    (* assume n1 = n2*)
        if eqb G_var G then [var G'] else [var G_var]
    | (n1,t)::c', n2::args', e::s' =>
      if n1 =? n2
      then
        match t with
        | scon name [G']
        | scon name [_;G']
        | scon name [_;_;G'] =>
            (if named_list_lookup_err prefix_map name then
               let s := gen_arg_subst G g G'[/combine args' s'/] in
               {{e #(subst name) {s} {e} }} 
             else e)
              ::(gen_sort_subterms c' args' s')
        | _ => e::(gen_sort_subterms c' args' s')
        end
      else gen_sort_subterms c' args s
    | _, _,_ => []
    end.
  
  (* sort of the term w/ a subst applied to it.
     TODO: change last arg from G to G'
   *)
  Let t' : sort string :=
        match named_list_lookup_err l sort_name with
        | Some (sort_rule c_sort args) =>
            let (_,s):= t in
            let s' := gen_sort_subterms c_sort args s in
            scon sort_name s'
        | _ => t
        end.

  Definition eqn_rule : option _ :=
    if named_list_lookup_err prefix_map sort_name 
    then Some (term_eq_rule c' lhs rhs t')
    else None.

  Definition eqn_name := subst sort_name ++ " " ++ name.
    
  Definition with_sub_eqn : lang string :=
    match eqn_rule with
    | Some r' => [(eqn_name,r');(name,r)]
    | None => [(name,r)]
    end.

End WithRule.

Fixpoint sc (dep l : lang string) : lang string :=
  match l with
  | [] => []
  | (n,r)::l' => (with_sub_eqn (l++dep)%list n r ++ sc dep l')%list
  end.


Definition opt_to_list {A} (ma : option A) :=
  match ma with
  | Some a => [a]
  | None => []
  end.

(* Just the new equations *)
Fixpoint eqn_rules (dep l : lang string) : lang string :=
  match l with
  | [] => []
  | (n,r)::l' =>
      (map (pair (eqn_name n r)) (opt_to_list (eqn_rule (l++dep)%list n r)) ++ eqn_rules dep l')%list
  end.

End __.

Notation "'{[l/subst' [ dep ] r1 ; .. ; r2 ]}" :=
  (sc val_subst_mode dep (cons r2 .. (cons r1 nil) ..))%rule
  (format "'[' {[l/subst  '[' [ dep ] ']'  '[hv' r1 ; '/' .. ; '/' r2 ']' ]} ']'") : lang_scope.
