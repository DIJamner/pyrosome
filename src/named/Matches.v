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
From Named Require Import Exp Rule.
From Named Require Import Tactics.
Require Import String.
Import OptionMonad.

Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".


(* constructs the union of the two lists viewed as maps,
   arbitrarily choosing one list when they disagree*)
Fixpoint unordered_merge_unsafe {A : eqType} (l1 l2 : named_list A) :=
  match l1 with
  | [::] => l2
  | (n,e)::l1' =>
    (if fresh n l2 then [:: (n,e)] else [::])
      ++ (unordered_merge_unsafe l1' l2)
  end.

(* Finds the subst s such that s >= acc, e = pat[/s/]
   and (map fst s) = FV(e) U (map fst acc), if such a substitution exists
   and sufficient fuel is provided.
   Behavior intentionally unspecified otherwise.
*)
Fixpoint matches_unordered_fuel (fuel : nat) (e pat : exp) {struct fuel} : option subst :=
  match pat, e, fuel with
  | var px, _,_ => Some ([:: (px,e)])
  | con pn ps, con n s,fuel'.+1 =>
    if pn == n then args_match_unordered_fuel fuel' s ps else None
  | _,_,_ => None
end
with args_match_unordered_fuel (fuel : nat)
                               (s pat : list exp) {struct fuel} : option subst :=
       match pat, s, fuel with
       | [::],[::],_ => do ret [::]
       | pe::pat',e::s',fuel'.+1 =>
         do res_e <- matches_unordered_fuel fuel' e pe;
            res_s <- args_match_unordered_fuel fuel' s' pat';
            ret (unordered_merge_unsafe res_e res_s)                          
       | _,_,_ => None
       end.

(* The maximum depth of the expression is enough fuel for the matcher *)
Fixpoint exp_depth (e: exp) : nat :=
  match e with
  | var _ => 0
  | con _ s => (foldl (fun n e => max (exp_depth e) n) 0 s).+1
  end.

(*
Definition matches_unordered e pat :=
  do s <- matches_unordered_fuel (exp_depth pat) e pat;
     ! e == pat[/s/]; (* since we don't check merges, we check post-hoc *)
     ret s.
 *)

Fixpoint order_subst' s args : option subst :=
  match args with
  | [::] => do ret [::]
  | x::args' =>
    do e <- named_list_lookup_err s x;
       s' <- order_subst' s args';
       ret ((x,e)::s')
  end.

(*
Lemma order_subst'_vals s args s' p
  : all_fresh s ->
    order_subst' s args = Some s' ->
    p \in s ->
    p.1 \in args ->
    p \in s'.             
Proof.
  simpl in *.
  ltac1:(break); simpl.
  revert s'.
  induction args; intro s'; simpl.
  {    
    intros _ _ _ absurd; inversion absurd.
  }
  {
    intro.
    ltac1:(case_match;[|inversion]).
    ltac1:(case_match;[|inversion]).
    intro s'eq; inversion s'eq; clear s'eq; subst.
    rewrite !in_cons.
    intro.
    ltac1:(move /orP; case).
    {
      ltac1:(move /eqP); intro s0eq; subst.
      (*Lemma lookup_in
       *)
Admitted.
*)

Definition order_subst s args :=
  (*guarantees that args is a permutation of (map fst s)
    if this function returns a result.
   *)
  if size s == size args then order_subst' s args else None.

(*
Lemma order_subst_vals s args s' p
  : all_fresh s ->
    order_subst s args = Some s' ->
    p \in s ->
    p.1 \in args ->
    p \in s'.             
Proof.
  intro.
  unfold order_subst.
  ltac1:(case_match;[|inversion]).
  eauto using order_subst'_vals.
Qed.
*)

(*
Lemma matches_unordered_fuel_all_fresh e pat fuel s
  : matches_unordered_fuel fuel e pat = Some s ->
    all_fresh s.
Proof.
  unfold matches_unordered.
*)

(*
Lemma matches_unordered_all_fresh e pat s
  : matches_unordered e pat = Some s ->
    all_fresh s.
Proof.
  unfold matches_unordered.
  *)

(* Note that 'args' is critical to getting the order of the output subst correct.
   We assume of the input that FV(pat) is a permutation of args.
 *)
Definition matches (e pat : exp) (args : list string) : option subst :=
  do s <- matches_unordered_fuel (exp_depth pat) e pat;
     s' <- order_subst s args;
     (* this condition can fail because merge doesn't check for conflicts *)
     !e == pat[/s'/];
     ret s'.


(* This lemma is pretty much trivial, but it's the useful property.
   A 'completeness' lemma is much harder, but also not as useful
   for proofs of positive statements.
*)
Lemma matches_recognizes e pat args s
  : matches e pat args = Some s ->
    e = pat[/s/].
Proof.
  unfold matches.
  ltac1:(case_match;[|inversion]).
  ltac1:(case_match;[|inversion]).
  ltac1:(case_match;[|inversion]).
  symmetry in HeqH1.
  intro seq; inversion seq; subst.
  ltac1:(apply /eqP); assumption.
Qed.

Lemma order_subst_args s args s'
  : order_subst s args = Some s' ->
    args = map fst s'.
Proof.
  unfold order_subst.
  ltac1:(case_match;[|inversion]).
  clear HeqH.
  revert s'.
  induction args; intro s'; simpl.
  {
    ltac1:(inversion); subst; reflexivity.
  }
  {
    ltac1:(case_match;[|inversion]).
    ltac1:(case_match;[|inversion]).
    ltac1:(inversion).
    simpl in *.
    f_equal.
    eauto.
  }
Qed.

Lemma matches_args e pat args s
  : matches e pat args = Some s ->
    args = map fst s.
Proof.
  unfold matches.
  ltac1:(case_match;[|inversion]).
  ltac1:(case_match;[|inversion]).
  ltac1:(case_match;[|inversion]).
  ltac1:(inversion); subst.
  eapply order_subst_args.
  symmetry; eauto.
Qed.



Goal (matches (con "foo" [:: con "quox" [::]; con "bar" [:: con "baz"[::]]; var "b"])
              (con "foo" [:: con "quox" [::]; var "b"; var "a"])
              [:: "b"; "a"])%string.
  unfold matches.
  ltac1:(case_match).
  simpl in HeqH.
  vm_compute in HeqH.

Notation "'{{e' e }}" := (e) (at level 0,e custom expr at level 100).
Notation "'{{s' e }}" := (e) (at level 0,e custom srt at level 100).



Goal (matches {{e #"foo" %"b" (#"bar" #"baz") #"quox"}}
     {{e #"foo" %"a" %"b" #"quox"}} [:: "b"; "a"]).
