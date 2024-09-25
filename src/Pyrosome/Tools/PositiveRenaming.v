Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import ZArith Lists.List.
Import ListNotations.
Open Scope list.
Open Scope positive.

From Tries Require Import Canonical.
Import PTree.


From Utils Require Import Utils Monad.
Import StateMonad.
From Pyrosome Require Import Theory.Core Proof.TreeProofs.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_default : WithDefault V}.
  
  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Record renaming :=
    MkRenaming {
        p_to_v : tree V
      ; v_to_p : named_list positive
      ; next_id : positive
      }.

  Local Notation ST := (state renaming).
  
  Definition alloc (n : V) : ST positive :=
    fun r =>
      (r.(next_id),
        MkRenaming (set r.(next_id) n r.(p_to_v))
          ((n,r.(next_id))::r.(v_to_p))
          (r.(next_id)+1)).

  Definition to_p (v : V) : ST positive :=
    fun r =>
      match named_list_lookup_err r.(v_to_p) v with
      | Some p => (p,r)
      | None => alloc v r
      end.

  Fixpoint rename_term (e : term) : ST (Term.term positive) :=
    match e with
    | var x =>
        @! let x' <- to_p x in
          ret var x'
    | con n s =>
        @! let s' <- list_Mmap rename_term s in
          let n' <- to_p n in
          ret con n' s'
    end.

  Definition rename_sort (t : sort) : ST _ :=
    let (n,s) := t in
    @! let s' <- list_Mmap rename_term s in
      let n' <- to_p n in
      ret scon n' s'.

  Definition rename_ctx (c : ctx) : ST _ :=
    list_Mmap (fun '(x,t) =>
                 @! let t' <- rename_sort t in
                   let x' <- to_p x in
                   ret (x',t')) c.
  
  Definition rename_rule r : ST _ :=
    match r with
    | sort_rule c args =>
        @! let c' <- rename_ctx c in
          let args' <- list_Mmap to_p args in
          ret sort_rule c' args'
    | term_rule c args t =>
        @! let c' <- rename_ctx c in
          let args' <- list_Mmap to_p args in
          let t' <- rename_sort t in
          ret term_rule c' args' t'
    | sort_eq_rule c t1 t2 =>
        @! let c' <- rename_ctx c in
          let t1' <- rename_sort t1 in
          let t2' <- rename_sort t2 in
          ret sort_eq_rule c' t1' t2'
    | term_eq_rule c e1 e2 t =>
        @! let c' <- rename_ctx c in
          let e1' <- rename_term e1 in
          let e2' <- rename_term e2 in
          let t' <- rename_sort t in
          ret term_eq_rule c' e1' e2' t'
    end.

  Definition rename_lang : lang -> ST _ :=
    list_Mmap (fun '(x,r) =>
                 @! let r' <- rename_rule r in
                   let x' <- to_p x in
                   ret (x',r')).

  Definition empty_rename : renaming :=
    MkRenaming (empty _) [] 1.

  Section Unrename.

    Context (r : renaming).

    Definition of_p (p : positive) : V :=
      unwrap_with_default (get p r.(p_to_v)). 

    
    Fixpoint unrename_term (e : Term.term positive) : Term.term V :=
      match e with
      | var x => var (of_p x)
      | con n s => con (of_p n) (map unrename_term s)
      end.
    
  End Unrename.
          
End WithVar.
