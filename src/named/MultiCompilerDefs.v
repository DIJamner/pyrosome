Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core.
Import Core.Notations.



Lemma true_false_inv : true = false <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite true_false_inv : utils.
  
(* TODO: Extract proofs outside Defined?
   TODO: finish, move to Utils*)
#[export, refine] Instance list_Eqb {A} `{Eqb A} : Eqb (list A) :=
  {|
  eqb := all2 eqb;
  Eqb_dec := @list_eq_dec _ Eqb_dec;
  |}.
Proof.
  {
    induction n; destruct m; basic_goal_prep; basic_utils_firstorder_crush. 
  }
  {
    induction x; destruct y; basic_goal_prep; basic_utils_firstorder_crush.
    my_case Heq (eqb a a0); simpl; auto.
    basic_utils_firstorder_crush.
  }
  {
    induction x; basic_goal_prep; basic_utils_firstorder_crush.
  }
Defined.

(*TODO: move to Utils*)

Fixpoint all_unique {A} (l : list A) :=
  match l with
  | [] => True
  | n::l' => ~ In n l' /\ all_unique l'
  end.
Arguments all_unique {_} !_ /.

(*TODO: move to Utils*)
#[export] Instance list_default {A} : WithDefault (list A) := [].

Notation named_list := (@named_list (list string)).
Notation named_map := (@named_map (list string)).
Notation term := (@term (list string)). 
Notation ctx := (@ctx (list string)).
Notation sort := (@sort (list string)).
Notation subst := (@subst (list string)).
Notation rule := (@rule (list string)).
Notation lang := (@lang (list string)).

(* each element is the image for that constructor or axiom*)
Variant compiler_case :=
 | term_case (args : list (list string)) (el:list term)
 | sort_case (args : list (list string)) (tl:list sort).
Definition compiler : Type := (list string * named_list compiler_case).

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

  (*TODO: move to Term.v*)
  Existing Instance term_default.
  Existing Instance sort_default.

  Definition env_args args : list (list string) :=
    flat_map (fun x => map (fun c => c::x) (fst cmp)) args.
  
  (* does not use src or tgt, only cmp *)
  (*TODO: notations do a poor job of spacing this*)
  Fixpoint compile cname e : term :=
    match e with
    | var x => var (cname::x)
    | con n s =>
        let arg_terms :=
          flat_map (fun x => map (fun cname => compile cname x) (fst cmp)) s in
      match named_list_lookup_err (snd cmp) n with
      | Some (term_case args el) =>
        let e := named_list_lookup default (combine (fst cmp) el) cname in
        e[/combine (env_args args) arg_terms/]
      | _ => default : term
      end
    end.

  Definition compile_args s := flat_map (fun x => map (fun cname => compile cname x) (fst cmp)) s.
  
  (* does not use src or tgt, only cmp *)
  Definition compile_sort cname (t : sort) : sort :=
    match t with
    | scon n s =>
      let arg_terms := compile_args s in
      match named_list_lookup_err (snd cmp) n with
      | Some (sort_case args el) =>
        let e := named_list_lookup default (combine (fst cmp) el) cname in
        e[/combine (env_args args) arg_terms/]
      | _ => default
      end
    end. 

  (*TODO: needs renaming*)
  Definition compile_subst (s : named_list term) : named_list term :=
    flat_map (fun '(n, e) => map (fun cname => (cname::n,compile cname e)) (fst cmp)) s.

  Definition compile_ctx (c:named_list sort) := 
    flat_map (fun '(n, t) => map (fun cname => (cname::n,compile_sort cname t)) (fst cmp)) c.

  (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
   *)
  Definition sort_wf_preserving_sem :=
    forall c t,
      wf_sort src c t ->
      wf_ctx src c ->
      forall cname,
        In cname (fst cmp) ->
        wf_sort tgt (compile_ctx c) (compile_sort cname t).

  Definition term_wf_preserving_sem :=
    forall c e t,
      wf_term src c e t ->
      wf_ctx src c ->
      forall cname,
        In cname (fst cmp) ->
        wf_term tgt (compile_ctx c) (compile cname e) (compile_sort cname t).

  Definition sort_eq_preserving_sem :=
    forall c t1 t2,
      eq_sort src c t1 t2 ->
      wf_ctx src c ->
      forall cname,
        In cname (fst cmp) ->
        eq_sort tgt (compile_ctx c) (compile_sort cname t1) (compile_sort cname t2).
  
  Definition term_eq_preserving_sem :=
    forall c t e1 e2,
      eq_term src c t e1 e2 ->
      wf_ctx src c ->
      forall cname,
        In cname (fst cmp) ->
        eq_term tgt (compile_ctx c) (compile_sort cname t)
                (compile cname e1) (compile cname e2).

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

Definition extend_cmp cmp '((args, cmp_pre) : compiler) : compiler :=
  (args, cmp++cmp_pre).

(*
First we define an inductively provable (and in fact decidable) property 
of elaborated compilers.
*)

Section Extension.
  Context (cmp_pre : compiler).
  (*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
  Inductive preserving_compiler_ext (target : lang)
    : named_list compiler_case -> lang -> Prop :=
  | preserving_compiler_nil : all_unique (fst cmp_pre) -> preserving_compiler_ext target [] []
  | preserving_compiler_sort : forall cmp l n c args t,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      all (wf_sort target (compile_ctx (extend_cmp cmp cmp_pre) c)) t ->
      (* make sure combine doesn't truncate *)
      length t = length (fst cmp_pre) ->
      preserving_compiler_ext target
                              ((n,sort_case (map fst c) t)::cmp)
                              ((n,sort_rule c args) :: l)
  | preserving_compiler_term : forall cmp l n c args e t,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c, t *)
      all (fun '(cname,e) =>
             wf_term target (compile_ctx (extend_cmp cmp cmp_pre) c) e
                     (compile_sort (extend_cmp cmp cmp_pre) cname t))
          (combine (fst cmp_pre) e) ->
      (* make sure combine doesn't truncate *)
      length e = length (fst cmp_pre) ->
      preserving_compiler_ext target
                              ((n, term_case (map fst c) e)::cmp)
                              ((n,term_rule c args t) :: l)
  | preserving_compiler_sort_eq : forall cmp l n c t1 t2,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      all (fun cname => eq_sort target (compile_ctx (extend_cmp cmp cmp_pre) c)
                                (compile_sort (extend_cmp cmp cmp_pre) cname t1)
                                (compile_sort (extend_cmp cmp cmp_pre) cname t2))
      (fst cmp_pre) ->
      preserving_compiler_ext target cmp ((n,sort_eq_rule c t1 t2) :: l)
  | preserving_compiler_term_eq : forall cmp l n c e1 e2 t,
      preserving_compiler_ext target cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      all (fun cname => eq_term target (compile_ctx (extend_cmp cmp cmp_pre) c)
                                (compile_sort (extend_cmp cmp cmp_pre) cname t)
                                (compile (extend_cmp cmp cmp_pre) cname e1)
                                (compile (extend_cmp cmp cmp_pre) cname e2))
      (fst cmp_pre) ->
      preserving_compiler_ext target cmp ((n,term_eq_rule c e1 e2 t) :: l).

End Extension.

(*TODO: remove earlier ones?*)
#[export] Hint Rewrite invert_eq_term_case_term_case : lang_core.
#[export] Hint Rewrite invert_eq_term_case_sort_case : lang_core.
#[export] Hint Rewrite invert_eq_sort_case_term_case : lang_core.
#[export] Hint Rewrite invert_eq_sort_case_sort_case : lang_core.
#[export] Hint Constructors preserving_compiler_ext : lang_core.

(*TODO: add preserving_compiler notation once other files are updated *)

Declare Custom Entry comp_case.

(* TODO: notations
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

  (*TODO: specialized to strings. Generalize.*)
  Definition gen_rule (cmp : compiler) (p : string * rule) : named_list (compiler_case) :=
    let (n,r) := p in
    match r with
    | sort_rule c args =>
      match named_list_lookup (sort_case (map fst c) (scon n (map (@var string) args))) cmp n with
      | sort_case args' t =>
        [(n,sort_case (map fst c) t[/combine args' (map (@var string) (map fst c))/])]
      | _ => [(n,sort_case [] {{s#"ERR: expected sort case"}})]
      end
    | term_rule c args t => 
      match named_list_lookup (term_case (map fst c) (con n (map (@var string) args))) cmp n with
      | term_case args' e =>
        [(n,term_case (map fst c) e[/combine args' (map (@var string) (map fst c))/])]
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
*)
