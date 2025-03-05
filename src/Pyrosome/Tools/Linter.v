Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad SumMonad.
From Pyrosome.Theory Require Import Term Rule.
From Pyrosome.Compilers Require Import CompilerDefs.
Import Term.Notations.
Import Rule.Notations.

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

  Notation compiler_case := (@compiler_case V term sort).
  
  (*TODO: use s-expr framing to show locations?
   *)
  Inductive lint_error : Type :=
  | var_not_fresh_in_context : list V -> V -> lint_error
  | constr_not_fresh_in_lang : list V -> V -> lint_error
  | var_unbound_in_context : list V -> V -> lint_error
  | arg_unbound_in_context : list V -> V -> lint_error
  | constr_unbound_in_lang : list V -> V -> lint_error
  | sort_used_as_term_constr : V -> term -> lint_error
  | term_used_as_sort_constr : V -> sort -> lint_error
  | eqn_used_as_constr : V -> lint_error
  | arity_mismatch : V -> nat -> list term -> lint_error
  (*compiler errors*)                                                
  | ccase_constr_unbound_in_lang : V -> compiler_case -> lint_error
  | ccase_sort_give_term_case : V -> term -> lint_error
  | ccase_term_give_sort_case : V -> sort -> lint_error
  | ccase_eqn_give_term_case : V -> term -> lint_error
  | ccase_eqn_give_sort_case : V -> sort -> lint_error
  | ccase_wrong_args_number : list V -> ctx -> lint_error.

  Record constr_info :=
    MkConstrInfo {
      constr_is_sort : bool;
      constr_arity : nat;
    }.

  Section LintRule.
    Context (l : lang).

    Let fstl := map fst l.

    (* returns the arity of the constructor *)
    Definition lookup_constr_in_lang n : lint_error + constr_info :=
      match named_list_lookup_err l n with
      | Some (term_rule _ args _) => inr (MkConstrInfo false (length args))
      | Some (sort_rule _ args) => inr (MkConstrInfo true (length args))
      | Some _ => inl (eqn_used_as_constr n)
      | None => inl (constr_unbound_in_lang fstl n)
      end.
    
    Definition check_fresh_in_lang n :=
      if inb n fstl then [constr_not_fresh_in_lang fstl n] else [].
    
    Section LintTerm.
      Context (args : list V).

      Definition check_var_in_ctx x :=
        if inb x args then [] else [var_unbound_in_context args x].
      
      Definition check_fresh_in_ctx x :=
        if inb x args then [var_not_fresh_in_context args x] else [].
      
      
      (* currently just roughly checks Well-scopedness properties 
     TODO: also check arity of constructors
     TODO: also check term vs sort constr
       *)
      Fixpoint lint_term  (e : term) : list lint_error :=
        match e with
        | var x => check_var_in_ctx x
        | con n s =>
            match lookup_constr_in_lang n with
            | inl e => [e]
            | inr info =>
                if info.(constr_is_sort)
                then [sort_used_as_term_constr n e]
                else if Nat.eqb info.(constr_arity) (length s)
                     then []
                     else [arity_mismatch n info.(constr_arity) s]
            end
              ++(flat_map lint_term s)
        end.

      Definition lint_args := flat_map lint_term.

      
      Definition lint_sort (e : sort) : list lint_error :=
        match e with
        | scon n s =>
            match lookup_constr_in_lang n with
            | inl e => [e]
            | inr info =>
                if info.(constr_is_sort)
                then if Nat.eqb info.(constr_arity) (length s)
                     then []
                     else [arity_mismatch n info.(constr_arity) s]
                else [term_used_as_sort_constr n e]
            end
              ++ (lint_args s)
        end.
      
    End LintTerm.

    Fixpoint lint_subst args s :=
      match s with
      | [] => []
      | (x,e)::s' =>
          (check_fresh_in_ctx (map fst s') x)
            ++ (lint_term args e)
            ++ (lint_subst args s')
      end.

    Fixpoint lint_ctx (c : ctx) :=
      match c with
      | [] => []
      | (x,t) :: c' =>
          (check_fresh_in_ctx (map fst c') x)
            ++ (lint_sort (map fst c') t)
            ++ (lint_ctx c')
      end.

    (* TODO: better info, e.g. if args are out of order*)
    Fixpoint lint_explicits fstc args :=
      match args, fstc with
      | [], _ => []
      | _, [] => map (arg_unbound_in_context fstc) args
      | x::args', x'::fstc' =>
          if eqb x x' then lint_explicits fstc' args'
          else lint_explicits fstc' args
      end.
    
    Definition lint_rule r :=
      match r with
      | sort_rule c args =>
          (lint_explicits (map fst c) args) ++ (lint_ctx c)
      | term_rule c args t =>
          (lint_sort (map fst c) t) ++ (lint_explicits (map fst c) args) ++ (lint_ctx c)
      | sort_eq_rule c t t'=>
          (lint_sort (map fst c) t')
            ++ (lint_sort (map fst c) t)
            ++ (lint_ctx c)
      | term_eq_rule c e e' t =>
          (lint_sort (map fst c) t)
            ++ (lint_term (map fst c) e')
            ++ (lint_term (map fst c) e)
            ++ (lint_ctx c)
      end.

  End LintRule.

  Fixpoint lint_lang_ext (l_base l : lang) :=
    match l with
    | [] => []
    | (n,r)::l' =>
        (check_fresh_in_lang (l' ++ l_base) n)
          ++ (lint_rule (l' ++ l_base) r)
          ++ (lint_lang_ext l_base l')
    end.

  Section LintCompiler.
    
    Definition lint_ccase_args (args : list V) c :=
      if eqb (length args) (length c) then []
      else [ccase_wrong_args_number args c].

    Context (src tgt : lang).
    
    Definition lint_ccase '(n,c) :=
      match named_list_lookup_err src n, c with
      (* rule disagreements *)
      | None, (term_case args e) =>
          [ccase_constr_unbound_in_lang n c] ++ (lint_term tgt args e)
      | None, (sort_case args t) =>
          [ccase_constr_unbound_in_lang n c] ++ (lint_sort tgt args t)
      | Some (sort_rule _ _), (term_case args e) =>
          [ccase_sort_give_term_case n e] ++ (lint_term tgt args e)
      | Some (term_rule _ _ _), (sort_case args t)=>
          [ccase_term_give_sort_case n t] ++ (lint_sort tgt args t)
      | Some (sort_eq_rule _ _ _), (sort_case args t) 
      | Some (term_eq_rule _ _ _ _), (sort_case args t) =>
          [ccase_eqn_give_sort_case n t] ++ (lint_sort tgt args t)
      | Some (sort_eq_rule _ _ _), (term_case args e)
      | Some (term_eq_rule _ _ _ _), (term_case args e) =>
          [ccase_eqn_give_term_case n e] ++ (lint_term tgt args e)
      (* rule-matching cases *)
      | Some (sort_rule c _), sort_case args t =>
          (lint_ccase_args args c) ++ (lint_sort tgt args t)
      | Some (term_rule c _ t), term_case args e =>
          (lint_ccase_args args c) ++ (lint_term tgt args e)
      end.

    (*TODO: make more precise wrt comparing to src *)
    Definition lint_cmp_ext cmp :=
      flat_map lint_ccase cmp.

  End LintCompiler.
      

End WithVar.

Ltac print_linting_err e :=
  lazymatch e with
  | var_not_fresh_in_context ?c ?x =>
      fail "Variable" x "not fresh in" c
  | constr_not_fresh_in_lang ?c ?x =>
      fail "Constructor name" x "not fresh in" c
  | var_unbound_in_context ?c ?x =>
      fail "Variable" x "unbound in" c
  | constr_unbound_in_lang ?c ?x =>
      fail "Constructor name" x "unbound in" c
  | sort_used_as_term_constr ?n ?e => 
      fail "Sort constructor name" n "used as term constructor in" e
  | term_used_as_sort_constr ?n ?t => 
      fail "Term constructor name" n "used as sort constructor in" t
  | eqn_used_as_constr ?n => 
      fail "Equation name" n "used as constructor"
  | arity_mismatch ?n ?a [] =>
      fail "Constructor" n "expects" a "explicit arguments, but has no arguments"
  | arity_mismatch ?n ?a ?s =>
      let s' := constr:(argument_seq_marker s) in
      fail "Constructor" n "expects" a "explicit arguments, but has arguments" s'
  | arg_unbound_in_context ?c ?x =>
      fail "Argument" x "unbound in" c    
  | ccase_constr_unbound_in_lang ?n ?cc =>
      fail "Constructor" n "with compiler case" cc "not found in language"
  | ccase_sort_give_term_case ?n ?e =>
      fail "Sort" n "given term compilation" e
  | ccase_term_give_sort_case ?n ?t =>
      fail "Term" n "given sort compilation" t
  | ccase_eqn_give_term_case ?n ?e =>
      fail "Equation" n "given term compilation" e
  | ccase_eqn_give_sort_case ?n ?t =>
      fail "Equation" n "given sort compilation" t
  | ccase_wrong_args_number ?args ?c =>
      fail "Arguments" args "do not match length of context" c
  end.

Ltac lint_lang_ext base l :=
  let lint_res := (eval vm_compute in (lint_lang_ext base l)) in
  lazymatch lint_res with
  | [] => idtac
  (* TODO: print all errors *)
  | ?e::_ => print_linting_err e
  end.

(*TODO: not conservative; has some bug. FInd and fix *)
Ltac lint_compiler l cmp :=
  let lint_res := (eval vm_compute in (lint_cmp_ext l cmp)) in
  lazymatch lint_res with
  | [] => idtac
  (* TODO: print all errors *)
  | ?e::_ => print_linting_err e
  end.



