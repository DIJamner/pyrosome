Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core.
Import Core.Notations.


(* each element is the image for that constructor or axiom*)
Variant compiler_case :=
 | term_case (args : list string) (e:term)
 | sort_case (args : list string) (t:sort).
Definition compiler := named_list compiler_case.

Lemma invert_eq_term_case_term_case args args' e e'
  : term_case args e = term_case args' e' <-> args = args' /\ e = e'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_case_term_case : lang_core.

Lemma invert_eq_term_case_sort_case args args' e e'
  : term_case args e = sort_case args' e' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_case_sort_case : lang_core.

Lemma invert_eq_sort_case_term_case args args' e e'
  : sort_case args e = term_case args' e' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_case_term_case : lang_core.

Lemma invert_eq_sort_case_sort_case args args' e e'
  : sort_case args e = sort_case args' e' <-> args = args' /\ e = e'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_case_sort_case : lang_core.

Section CompileFn.
  Context (tgt : lang)
          (cmp : compiler)
          (src : lang).

  (* does not use src or tgt, only cmp *)
  (*TODO: notations do a poor job of spacing this*)
  Fixpoint compile (e : term) : term :=
    match e with
    | var x => var x
    | con n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := con "ERR" [] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (term_case args e) => e[/combine args arg_terms/]
      | _ => default
      end
    end.
  
  (* does not use src or tgt, only cmp *)
  Definition compile_sort (t : sort) : sort :=
    match t with
    | scon n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := scon "ERR" [] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (sort_case args t) => t[/combine args arg_terms/]
      | _ => default
      end
    end.  
  
  Definition compile_args := map compile.

  Definition compile_subst (s : named_list term) := named_map compile s.

  Definition compile_ctx (c:named_list sort) := named_map compile_sort c.

   (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
   *)
  Definition sort_wf_preserving_sem :=
    forall c t,
      wf_sort src c t ->
      wf_ctx src c ->
      wf_sort tgt (compile_ctx c) (compile_sort t).

  Definition term_wf_preserving_sem :=
    forall c e t,
      wf_term src c e t ->
      wf_ctx src c ->
      wf_term tgt (compile_ctx c) (compile e) (compile_sort t).

  Definition sort_eq_preserving_sem :=
    forall c t1 t2,
      eq_sort src c t1 t2 ->
      wf_ctx src c ->
      eq_sort tgt (compile_ctx c) (compile_sort t1) (compile_sort t2).
  
  Definition term_eq_preserving_sem :=
    forall c t e1 e2,
      eq_term src c t e1 e2 ->
      wf_ctx src c ->
      eq_term tgt (compile_ctx c) (compile_sort t) (compile e1) (compile e2).

  Definition args_wf_preserving_sem :=
    forall c s c',
      wf_args src c s c' ->
      wf_ctx src c ->
      wf_ctx src c' ->
      wf_args tgt (compile_ctx c) (compile_args s) (compile_ctx c').

  Definition subst_eq_preserving_sem :=
    forall c c' s1 s2,
      eq_subst src c c' s1 s2 ->
      wf_ctx src c ->
      wf_ctx src c' ->
      eq_subst tgt (compile_ctx c) (compile_ctx c') (compile_subst s1) (compile_subst s2).
   
  Definition ctx_wf_preserving_sem :=
    forall c, wf_ctx src c -> wf_ctx tgt (compile_ctx c).

  (*Set up to match the combined scheme for the judgment inductives *)
  Definition semantics_preserving :=
    sort_eq_preserving_sem /\ term_eq_preserving_sem /\ subst_eq_preserving_sem
    /\ sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
    /\ ctx_wf_preserving_sem.

End CompileFn.

(*
First we define an inductively provable (and in fact decidable) property 
of elaborated compilers.
*)

Section Extension.
  Context (cmp_pre : compiler).
  (*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
  Inductive preserving_compiler_ext (target : lang) : compiler -> lang -> Prop :=
  | preserving_compiler_nil : preserving_compiler_ext target [] []
  | preserving_compiler_sort : forall cmp l n c args t,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      wf_sort target (compile_ctx (cmp ++ cmp_pre) c) t ->
      preserving_compiler_ext target
                              ((n,sort_case (map fst c) t)::cmp)
                              ((n,sort_rule c args) :: l)
  | preserving_compiler_term : forall cmp l n c args e t,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c, t *)
      wf_term target (compile_ctx (cmp ++ cmp_pre) c) e (compile_sort (cmp ++ cmp_pre) t) ->
      preserving_compiler_ext target
                              ((n, term_case (map fst c) e)::cmp)
                              ((n,term_rule c args t) :: l)
  | preserving_compiler_sort_eq : forall cmp l n c t1 t2,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      eq_sort target (compile_ctx (cmp ++ cmp_pre) c)
              (compile_sort (cmp ++ cmp_pre) t1)
              (compile_sort (cmp ++ cmp_pre) t2) ->
      preserving_compiler_ext target cmp ((n,sort_eq_rule c t1 t2) :: l)
  | preserving_compiler_term_eq : forall cmp l n c e1 e2 t,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      eq_term target (compile_ctx (cmp ++ cmp_pre) c)
              (compile_sort (cmp ++ cmp_pre) t)
              (compile (cmp ++ cmp_pre) e1)
              (compile (cmp ++ cmp_pre) e2) ->
      preserving_compiler_ext target cmp ((n,term_eq_rule c e1 e2 t) :: l).

End Extension.
#[export] Hint Constructors preserving_compiler_ext : lang_core.

(*TODO: add preserving_compiler notation once other files are updated *)

Declare Custom Entry comp_case.

Module Notations.

  Notation "| '{{s' # constr }} => t " :=
    (constr, sort_case nil t)
      (in custom comp_case at level 50,
          left associativity,
          constr constr at level 0,
          t constr,
          format "|  '{{s' # constr }}  =>  t").

  Notation "| '{{e' # constr }} => e " :=
    (constr, term_case nil e)
      (in custom comp_case at level 50,
          left associativity,
          constr constr at level 0,
          e constr,
          format "|  '{{e' # constr }}  =>  e").

  Notation "| '{{s' # constr x .. y }} => t" :=
    (constr, sort_case (cons y .. (cons x nil) ..) t)
      (in custom comp_case at level 50,
          left associativity,
          constr constr at level 0,
          x constr at level 0,
          y constr at level 0,
          t constr,
          format "|  '{{s' # constr  x  ..  y }}  =>  t").

  Notation "| '{{e' # constr x .. y }} => e " :=
    (constr, term_case (cons y .. (cons x nil) ..) e)
      (in custom comp_case at level 50,
          left associativity,
          constr constr at level 0,
          x constr at level 0,
          y constr at level 0,
          e constr,
          format "|  '{{e' # constr  x  ..  y }}  =>  e").

  (* Cases must be given in the order of the source language,
     and argument names must match the context of the related source rule.
     All cases must be defined.
   *)
  Notation "'match' # 'with' case_1 .. case_n 'end'" :=
    (cons case_n .. (cons case_1 nil) ..)
      (left associativity, at level 50,
       case_1 custom comp_case,
       case_n custom comp_case,
       format "'[' 'match'  #  'with' '//' '[v' case_1 '//' .. '//' case_n ']'  '//' 'end' ']'").

  Definition gen_rule (cmp : compiler) (p : string * rule) : named_list compiler_case :=
    let (n,r) := p in
    match r with
    | sort_rule c args =>
      match named_list_lookup (sort_case (map fst c) (scon n (map var args))) cmp n with
      | sort_case args' t =>
        [(n,sort_case (map fst c) t[/combine args' (map var (map fst c))/])]
      | _ => [(n,sort_case [] {{s#"ERR: expected sort case"}})]
      end
    | term_rule c args t => 
      match named_list_lookup (term_case (map fst c) (con n (map var args))) cmp n with
      | term_case args' e =>
        [(n,term_case (map fst c) e[/combine args' (map var (map fst c))/])]
      | _ => [(n,sort_case [] {{s#"ERR: expected term case"}})]
      end
    | sort_eq_rule _ _ _
    | term_eq_rule _ _ _ _ => []
    end.
  

  (* accepts rules unordered and handles renaming to match language.
     Defaults to an identity rule for anything unspecified.
   *)
  Notation "'match' # 'from' l 'with' case_1 .. case_n 'end'" :=
    (flat_map (gen_rule (cons case_n .. (cons case_1 nil) ..)) l)
      (left associativity, at level 50,
       case_1 custom comp_case,
       case_n custom comp_case,
       format "'[' 'match'  #  'from'  l  'with' '//' '[v' case_1 '//' .. '//' case_n ']' '//' 'end' ']'").
End Notations.
