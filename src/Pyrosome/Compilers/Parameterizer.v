Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core Compilers.CompilerDefs.
Import Core.Notations.


(*TOOD: duplicated; move to Utils.v*)
Definition inb {A} `{Eqb A} x := existsb (eqb x).

(*TODO: move to Monad.v *)
Definition named_list_Mmap {M V A B} `{Monad M} (f : A -> M B)
  : @named_list V A -> M (@named_list V B) :=
  list_Mmap (fun '(x,a) => @! let b <- f a in ret (x,b)).

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
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  Section WithParameter.

    (*TODO: how to handle p_name freshness*)
    Context (p_name : V)
      (p_sort : sort).
    
    Section WithRules.    

      Context (rules_to_parameterize : list V).

        Fixpoint parameterize_term (e : term) : term :=
          match e with
          | var x => var x
          | con n s =>
              let s' := map parameterize_term s in
              if inb n rules_to_parameterize
              (*TODO: p_name freshness as fn of c.
                  Question: should c already be parameterized?
               *)
              then con n (s'++[var p_name])
              else con n s'
          end.
        
        Definition parameterize_sort (e : sort) : sort :=
          match e with
          | scon n s =>
              let s' := map parameterize_term s in
              if inb n rules_to_parameterize
                (*TODO: p_name freshness as fn of c.
                  Question: should c already be parameterized?
                 *)
                then scon n (s'++[var p_name])
                else scon n s'
          end.

        (*TODO: double-check when delta should be added.
          E.G. sort w/ parametric arg must be parameterized
          simple sort should not
         *)
        Definition parameterize_ctx (c : ctx) : ctx :=
          (named_map parameterize_sort c)++[(p_name, p_sort)].

        Definition parameterize_rule (r : rule) : rule :=
          match r with
          | sort_rule c args =>
              sort_rule (parameterize_ctx c) args
          | term_rule c args t =>
              term_rule (parameterize_ctx c) args (parameterize_sort t)
          | sort_eq_rule c t1 t2 =>
              sort_eq_rule (parameterize_ctx c)
                (parameterize_sort t1)
                (parameterize_sort t2)
          | term_eq_rule c e1 e2 t =>
              term_eq_rule (parameterize_ctx c)
                (parameterize_term e1)
                (parameterize_term e2)
                (parameterize_sort t)
          end.

        
        Definition parameterize_ccase n c : compiler_case V :=
          let ext_args :=
            if inb n rules_to_parameterize
            then fun a => a++[p_name]
            else fun a => a
          in
          match c with
          | sort_case args t =>
              sort_case (ext_args args) (parameterize_sort t)
          | term_case args e =>
              term_case (ext_args args) (parameterize_term e)
          end.

        Fixpoint parameterize_compiler c : compiler V :=
          match c with
          | [] => []
          | (n,cc)::c' =>
              (n, parameterize_ccase n cc):: (parameterize_compiler c')
          end.

        Fixpoint should_parameterize_term (e : term) : bool :=
          match e with
          | var _ => false
          | con n s =>
              (inb n rules_to_parameterize)
              || (existsb should_parameterize_term s)
          end.

        
        Definition should_parameterize_sort t : bool :=
          match t with
          | scon n s =>
              (inb n rules_to_parameterize)
              || (existsb should_parameterize_term s)
          end.

        Definition should_parameterize_ctx : ctx -> _ :=
          existsb (fun '(_,t) => should_parameterize_sort t).

        Definition should_parameterize (r : rule) : bool :=
          match r with
          | sort_rule c args => (should_parameterize_ctx c)
          | term_rule c args t =>
              (should_parameterize_ctx c)
              || (should_parameterize_sort t)
          | sort_eq_rule c t1 t2 =>
              (should_parameterize_ctx c)
              || (should_parameterize_sort t1)
              || (should_parameterize_sort t2)
          | term_eq_rule c e1 e2 t =>
              (should_parameterize_ctx c)
              || (should_parameterize_term e1)
              || (should_parameterize_term e2)
              || (should_parameterize_sort t)
          end.    
        
    End WithRules.

    Fixpoint parameterize_lang' (l : lang) rules :=
      match l with
      | [] => ([], rules)
      | (x,r)::l' =>
          let (l'', rules') := parameterize_lang' l' rules in
          if inb x rules'
                 (*TODO: add to args in this case*)
          then ((x,parameterize_rule rules r)::l'', rules')
          else if should_parameterize rules' r
               then ((x,parameterize_rule rules r)::l'', x::rules')
               else ((x,r)::l'', rules')
      end.

    Definition parameterize_lang rules l : lang :=
      fst (parameterize_lang' l rules).

    End WithParameter.

End WithVar.

Require Import Pyrosome.Lang.SimpleVSubst.

Compute (parameterize_lang' "D" {{s #"ty_env"}}
           value_subst
           ["env"; "ty"; "sub"; "exp"; "val"]
        ).
(*
TODO: what's the benefit (ignoring inference) over just parameterizing everything?
*)
