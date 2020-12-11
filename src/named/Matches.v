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
   choosing the second list when they disagree*)
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

Definition matches_unordered e pat :=
  (* multiply depth by 2 because each level consumes 1 fuel for exp
     and 1 for its args
   *)
  matches_unordered_fuel (exp_depth pat).*2 e pat.


Definition matches_unordered_sort (t pat : sort) :=
  match t, pat with
  | scon n s, scon n_pat s_pat =>
    if n == n_pat then
      (* multiply depth by 2 because each level consumes 1 fuel for exp
     and 1 for its args
       *)
      args_match_unordered_fuel (foldl (fun n e => max (exp_depth e) n) 0 s_pat).*2 s s_pat
    else None
  end.
          
(* Note that 'args' is critical to getting the order of the output subst correct.
   FV(pat) must be a permutation of args to get a result.
 *)
Definition matches (e pat : exp) (args : list string) : option subst :=
  do s <- matches_unordered e pat;
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


Goal
  (let e:= con "foo" [:: con "quox" [::]; con "bar" [:: con "baz"[::]]; var "b"]in
   matches e  (con "foo" [:: con "quox" [::]; var "b"; var "a"]) [::"b";"a"])%string.
  vm_compute.
  reflexivity.
Qed.

Variant matchable := match_exp (e:exp) | match_sort (s : sort).

Coercion match_exp : exp >-> matchable.
Coercion match_sort : sort >-> matchable.

(* matching checks only work when the pattern contains all 
   variables in args. This allows us to use multiple patterns
   to cover the variables, such as for an equivalence rule
 *)
Fixpoint match_all_unordered (l_exp l_pat : list matchable): option subst :=
  match l_exp, l_pat with
  | [::], [::] => do ret [::]
  | (match_exp e)::l'_exp, (match_exp pat)::l'_pat =>
    do s <- matches_unordered e pat;
       s' <- match_all_unordered l'_exp l'_pat;
       ret (unordered_merge_unsafe s s')
  | (match_sort e)::l'_exp, (match_sort pat)::l'_pat =>
    do s <- matches_unordered_sort e pat;
       s' <- match_all_unordered l'_exp l'_pat;
       ret (unordered_merge_unsafe s s')
  | _, _ => None
  end.

Fixpoint check_all (l_exp l_pat : list matchable) s :=
  match l_exp, l_pat with
  | [::],[::] => true
  | (match_exp e)::l'_exp, (match_exp pat)::l'_pat =>
    (e == pat[/s/]) && (check_all l'_exp l'_pat s)
  | (match_sort e)::l'_exp, (match_sort pat)::l'_pat =>
    (e == pat[/s/]) && (check_all l'_exp l'_pat s)
  | _, _ => false
end.

Definition match_all l_exp l_pat args :=
  do s <- match_all_unordered l_exp l_pat;
     s' <- order_subst s args;
     (* this condition can fail because merge doesn't check for conflicts *)
     !check_all l_exp l_pat s';
     ret s'.

Definition matchable_related s (e p : matchable) : Prop :=
  match e, p with
  | match_exp e', match_exp p' => e' = p'[/s/]
  | match_sort e', match_sort p' => e' = p'[/s/]
  | _,_ => False
  end.

Arguments matchable_related s !e !p/.

Lemma check_all_related l lp s
  : check_all l lp s -> List.Forall2 (matchable_related s) l lp.
Proof.
  revert lp; induction l; intro lp; destruct lp; intros; simpl in *;
    ltac1:(repeat match goal with
                  | h : matchable |- _=> destruct h
                  | [h : is_true false |- _] => inversion H
                  | [|- _ = _] => apply /eqP; assumption
                  | [|-_ ]=> break; try (constructor; simpl); auto
                  end).
Qed.

Lemma match_all_recognizes l lp args s
  : match_all l lp args = Some s -> List.Forall2 (matchable_related s) l lp.      
Proof.
  intro H.
  apply check_all_related.
  revert H.
  unfold match_all.
  repeat ltac1:(case_match;[|inversion]).
  intro seq; inversion seq; clear seq; subst.
  rewrite <-HeqH1.
  reflexivity.
Qed.


Lemma match_all_args e pat args s
  : match_all e pat args = Some s ->
    args = map fst s.
Proof.
  unfold match_all.
  repeat ltac1:(case_match;[|inversion]).
  ltac1:(inversion); subst.
  eapply order_subst_args.
  symmetry; eauto.
Qed.

(* Designed for the specific case of generating
   a pair of (potentially) related substitutions *)
Definition match_all_le l1 lp1 l2 lp2 args : option (subst* subst) :=
  do s1 <- match_all_unordered l1 lp1;
     s2 <- match_all_unordered l2 lp2;
     s1'' <- order_subst (unordered_merge_unsafe s2 s1) args;
     s2'' <- order_subst (unordered_merge_unsafe s1 s2) args;
     (* this condition can fail because merge doesn't check for conflicts *)
     !check_all l1 lp1 s1'';
     (* this condition can fail because merge doesn't check for conflicts *)
     !check_all l2 lp2 s2'';
     ret (s1'',s2'').

Lemma match_all_le_recognizes_l l1 lp1 l2 lp2 args s1 s2
  : match_all_le l1 lp1 l2 lp2 args = Some (s1,s2) ->
    List.Forall2 (matchable_related s1) l1 lp1.      
Proof.
  intro H.
  apply check_all_related.
  revert H.
  unfold match_all_le.
  repeat ltac1:(case_match;[|inversion]).
  intro seq; inversion seq; clear seq; subst.
  rewrite <-HeqH3.
  reflexivity.
Qed.


Lemma match_all_le_recognizes_r l1 lp1 l2 lp2 args s1 s2
  : match_all_le l1 lp1 l2 lp2 args = Some (s1,s2) ->
    List.Forall2 (matchable_related s2) l2 lp2.      
Proof.
  intro H.
  apply check_all_related.
  revert H.
  unfold match_all_le.
  repeat ltac1:(case_match;[|inversion]).
  intro seq; inversion seq; clear seq; subst.
  rewrite <-HeqH4.
  reflexivity.
Qed.


Lemma match_all_le_args_l l1 lp1 l2 lp2 args s1 s2
  : match_all_le l1 lp1 l2 lp2 args = Some (s1,s2) ->
    args = map fst s1.
Proof.
  unfold match_all_le.
  repeat ltac1:(case_match;[|inversion]).
  ltac1:(inversion); subst.
  eapply order_subst_args.
  symmetry; eauto.
Qed.


Lemma match_all_le_args_r l1 lp1 l2 lp2 args s1 s2
  : match_all_le l1 lp1 l2 lp2 args = Some (s1,s2) ->
    args = map fst s2.
Proof.
  unfold match_all_le.
  repeat ltac1:(case_match;[|inversion]).
  ltac1:(inversion); subst.
  eapply order_subst_args.
  symmetry; eauto.
Qed.

Require Import Rule Core.

Definition apply_le_term l n (e1 e2 : exp) (t : sort) : option (subst * subst*ctx) :=
  do (term_le c pat1 pat2 patt) <- named_list_lookup_err l n;
  (s1,s2) <- match_all_le [:: e1:matchable]
                          [:: pat1 : matchable]
                          [:: t:matchable; e2:matchable]
                          [:: patt:matchable; pat2:matchable]
                          (map fst c);
  ret (s1,s2,c).

Lemma apply_le_term_recognizes n l c e1 e2 t s1 s2 c'
  : apply_le_term l n e1 e2 t = Some (s1,s2,c') ->
    le_subst l c c' s1 s2 ->
    le_term l c t e1 e2.
(* e1 = e1'[/s1/]
   e2 = e2'[/s2/]
   e1' ~ e2' (by rule n)*)
Proof.
  unfold apply_le_term.
  repeat ltac1:(case_match;[|inversion]).
  destruct r; 
    repeat ltac1:(case_match;[|inversion]);
    try ltac1:(by inversion).
  ltac1:(break); simpl.
  intro seq; inversion seq; clear seq; subst.
  
  pose HeqH0.
  symmetry in e3.
  apply match_all_le_recognizes_l in e3.
  inversion e3; subst.
  clear e3 H4.
  
  pose HeqH0.
  symmetry in e3.
  apply match_all_le_recognizes_r in e3.
  inversion e3; inversion H5; subst.
  clear e3 H5 H11.

  simpl in *; subst.
  intro.
  symmetry in  HeqH.
  apply (@named_list_lookup_err_in rule_eqType) in HeqH.  
  eapply le_term_subst; eauto.
  eapply le_term_by; eauto.
Qed.

Arguments apply_le_term_recognizes n%string_scope [l c e1 e2 t s1 s2 c'].

(*
Goal match_all_unordered
            [:: Exp.con "ty_subst"
                  [:: Exp.var "A"; Exp.con "id" [:: Exp.var "G"]; Exp.var "G"; Exp.var "G"]:matchable]
            [:: Exp.con "ty_subst"
                [:: Exp.var "A"; Exp.con "id" [:: Exp.var "G"]; Exp.var "G"; Exp.var "G"]:matchable].
Proof.
  unfold match_all_unordered.
  ltac1:(case_match).
  unfold matches_unordered in HeqH.
  cbv [exp_depth foldl Nat.max] in HeqH.
  unfold matches_unordered_fuel in HeqH.
  
  vm_compute in HeqH.






e1 ~ e2
<= e1 = e1'[/s1/]
   e2 = e2'[/s2/]
   e1' ~ e2' (by rule n)

args : t...
--------- n
e1' ~ e2'

s1 = s2

beta: C |- (\x.e) e'~ e[e'/x]

           ....
---- refl  -------
4~4        4~2+2
----------------------cong
(4,4) ~ (2+2,4)
------------------ beta
(\x.(x,x)) 4 ~ (2+2,4)

*)
