(* 
 Gallina functions for matching an expression against a pattern
*)
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Pf.
Require Import String.
Import OptionMonad.

Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".


(* constructs the union of the two lists viewed as maps,
   choosing the second list when they disagree*)
Fixpoint unordered_merge_unsafe {A : eqType} (l1 l2 : named_list A) :=
  match l1 with
  | [::] => l2
  | (n,e)::l1' =>
    (if fresh n l2 then [:: (n,e)] else [::])
      ++ (unordered_merge_unsafe l1' l2)
  end.

Section InnerLoop.
  Context (matches_unordered : forall (e pat : pf), option (named_list pf)).
  Fixpoint args_match_unordered (s pat : list pf) :=
       match pat, s with
       | [::],[::] => do ret [::]
       | pe::pat',e::s' =>
         do res_e <- matches_unordered e pe;
            res_s <- args_match_unordered s' pat';
            ret (unordered_merge_unsafe res_e res_s)                          
       | _,_ => None
       end.
End InnerLoop.

(* Finds the subst s such that s >= acc, e = pat[/s/]
   and (map fst s) = FV(e) U (map fst acc), if such a substitution exists.
   Behavior intentionally unspecified otherwise.
*)
Fixpoint matches_unordered (e pat : pf) : option (named_list pf) :=
  match pat, e with
  | pvar px, _ => Some ([:: (px,e)])
  | pcon pn ps, pcon n s =>
    if pn == n then args_match_unordered matches_unordered s ps else None
  (*TODO: handle other constructors? Definitely need to handle conv*)
  | _,_ => None
end.

(*attempts to look up a list of arguments from a named list*)
Fixpoint get_from_named_list {A} (s : named_list A) l : option (list A):=
  match l with
  | [::] => Some [::]
  | n::l'=>
    do e <- named_list_lookup_err s n;
       s' <- get_from_named_list s l';
       ret e::s'
end.

(*returns the list of arguments that satisfies
  e = pat[/zip args s/] and |s| = |args|, if any
*)
Definition matches e pat args :=
  do s <- matches_unordered e pat;
     s' <- get_from_named_list s args;
     ret s'.
