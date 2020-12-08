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
From Named Require Import Exp.
From Named Require Import Tactics.
Require Import String.
Import OptionMonad.

Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

(* Finds the subst s such that s >= acc, e = pat[/s/]
   and (map fst s) = FV(e) U (map fst acc), if such a substitution exists*)
Fixpoint matches_unordered_fuel (fuel : nat) (e pat : exp) (acc : subst) {struct fuel} : option subst :=
  match pat, e, fuel with
  | var px, _,_ =>
    match named_list_lookup_err acc px with
    | Some e' =>
      do !e == e';
         ret acc
    | None =>
      do ret ((px,e)::acc)
    end
  | con pn ps, con n s,fuel'.+1 =>
    do !pn == n;
       res <- args_match_unordered_fuel fuel' s ps acc;
       ret res
  | _,_, _ => None
end
  with args_match_unordered_fuel (fuel : nat)
                            (s pat : list exp) acc {struct fuel} : option subst :=
       match pat, s, fuel with
       | [::],[::],_ => do ret acc
       | pe::pat',e::s',fuel'.+1 =>
         do acc' <- matches_unordered_fuel fuel' pe e acc;
            res <- args_match_unordered_fuel fuel' s' pat' acc';
            ret res                          
       | _,_,_ => None
       end.

Fixpoint exp_depth (e: exp) : nat :=
  match e with
  | var _ => 0
  | con _ s => (foldl (fun n e => max (exp_depth e) n) 0 s).+1
  end.
  
Definition matches_unordered e pat :=
  matches_unordered_fuel (exp_depth pat) e pat [::].

Fixpoint order_subst' s args : option subst :=
  match args with
  | [::] => do ret [::]
  | x::args' =>
    do e <- named_list_lookup_err s x;
       s' <- order_subst' s args';
       ret ((x,e)::s')
  end.

Definition order_subst s args :=
  do !size s == size args;
  res <- order_subst' s args;
  ret res.

(* Note that 'args' is critical to getting the order of the output subst correct.
   We assume of the input that FV(pat) is a permutation of args.
 *)
Definition matches (e pat : exp) (args : list string) : option subst :=
  do s <- matches_unordered e pat;
    s' <- order_subst s args;
ret s'.

(* TODO: move to utils*)
Lemma named_list_lookup_err_found {A:eqType} l n d (e : A)
  : Some e = named_list_lookup_err l n ->
    e = named_list_lookup d l n.
Proof.
  induction l> [ltac1:(inversion)|]; ltac1:(break); simpl.
  ltac1:(change (?a =? ?b)%string with (a == b)).
  ltac1:(case_match); auto.
  intro seq; inversion seq; reflexivity.
Qed.

Lemma matches_unordered_fuel_recognizes fuel e pat acc s
  : matches_unordered_fuel fuel e pat acc = Some s ->
    e = pat[/s/].
Proof.
  revert fuel e.
  induction pat; intros fuel e.
  {
    destruct fuel; simpl;
      ltac1:(case_match)>
            [
              ltac1:(case_match;[|inversion]);
              symmetry in HeqH0;
              revert HeqH0;
              ltac1:(move /eqP ->);
              intro seq; inversion seq; clear seq; subst;
              unfold subst_lookup;
              eapply (@named_list_lookup_err_found exp_eqType);
              assumption
            | intro seq; inversion seq; clear seq;
              simpl;
              rewrite eqb_refl;
              reflexivity].
  }
  {
    destruct e;destruct fuel; try (solve[ltac1:(inversion)]).
    simpl.
    ltac1:(case_match;[|inversion]).
    symmetry in HeqH0.
    revert HeqH0.
    ltac1:(move => /eqP HeqH0); subst.
    ltac1:(case_match;[|inversion]).
    intro seq; inversion seq; clear seq; subst.
    f_equal.
    revert fuel l H HeqH0.
    induction l0; intros fuel l H.
    {
      destruct l; auto.
      destruct fuel; try (solve[ltac1:(inversion)]).
    }
    {
      destruct l; destruct fuel; try (solve[ltac1:(inversion)]).
      simpl.
      ltac1:(case_match;[|inversion]).
      ltac1:(case_match;[|inversion]).
      intro seq; inversion seq; clear seq; subst.
      simpl in *; ltac1:(break).
      f_equal.
      ltac1:(change (exp_var_map (subst_lookup ?s) ?e) with e[/s/]).
      erewrite <-H; eauto.
      symmetry; eauto.
      ltac1:(fold_Substable).
      cbv.
      {
        
    }
    {
      
      in H.
    vm_compute in H.
    inversion H.
    simpl.
    rewrite eqb_refl.
    reflexivity.
  }
  destruct e.
  {
    unfold matches_unordered in H0.
    simpl in H0.
    inversion H0.
  }
  {
    revert H0.
    unfold matches_unordered in *.
    revert H.
    generalize (exp_depth (con n l)); intro fuel.
    intro H.
    simpl.

    
    (destruct fuel; simpl)>[ltac1:(inversion)|].
    
    ltac1:(case neq:(n==s0);[|inversion]).
    ltac1:(move: neq => /eqP neq); subst.
    ltac1:(case_match;[|inversion]).
    intro seq; inversion seq; subst.
    f_equal.
    revert l H HeqH0.
    clear seq s0.
    revert fuel.
    induction l0.
    {
      intros fuel l; destruct l; intros; simpl in *; ltac1:(break); simpl in *; auto.
      destruct fuel; simpl in HeqH0; inversion HeqH0.
    }
    {
      intros fuel l; destruct l; intros; simpl in *; ltac1:(break); simpl in *; auto.
      destruct fuel; simpl in HeqH0; inversion HeqH0.
      destruct fuel; simpl in HeqH0; try (solve[inversion HeqH0]).
      revert HeqH0.
      ltac1:(case_match;[|inversion]).
      ltac1:(case_match;[|inversion]).
      intro seq; inversion seq; subst; clear seq.
      f_equal.
      symmetry in HeqH1.
      unfold matches_unordered in H.
      apply H in HeqH1.
