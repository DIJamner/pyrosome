
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp Rule Core Compilers.
From Named Require Import IExp ICore.

Require Import String.

(* TODO: this does not admit for optimization *)
Variant compiler_case : Set :=
| sort_case : list string (* holes *) -> (* target *) sort -> compiler_case
| term_case :  list string (* holes *) -> (* target *) exp -> compiler_case.

(*
Definition eq_compiler_case c1 c2 : bool :=
  match c1,c2 with
  | sort_case args1 t1, sort_case args2 t2 =>
    (args1 == args2) && (t1 == t2)
  | term_case args1 e1, term_case args2 e2 =>
    (args1 == args2) && (e1 == e2)
  | _,_ => false
  end.

Lemma eq_compiler_caseP c1 c2 : reflect (c1 = c2) (eq_compiler_case c1 c2).
Proof using .
  case: c1; case: c2; simpl; eauto.
Admitted.

Definition compiler_case_eqMixin := Equality.Mixin eq_compiler_caseP.

Canonical compiler_case_eqType := @Equality.Pack compiler_case compiler_case_eqMixin.
*)
(* each element is the map for that constructor *)
Definition compiler := named_list compiler_case. 

(*TODO: this is an equal stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive elab_preserving_compiler (target : ARule.lang) : compiler -> Compilers.compiler -> ARule.lang -> Prop :=
| preserving_compiler_nil : elab_preserving_compiler target [::] [::] [::]
| preserving_compiler_sort : forall cmp ecmp l n c args t et,
    elab_preserving_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    elab_sort target (compile_ctx ecmp c) t et ->
    elab_preserving_compiler target
                             ((n, sort_case (map fst c) t)::cmp)
                             ((n, Compilers.sort_case (map fst c) et)::ecmp)
                             ((n,ARule.sort_rule c args) :: l)
| preserving_compiler_term : forall cmp ecmp l n c args e ee t,
    elab_preserving_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    elab_term target (compile_ctx ecmp c) e ee (compile_sort ecmp t) ->
    elab_preserving_compiler target
                             ((n, term_case (map fst c) e)::cmp)
                             ((n, Compilers.term_case (map fst c) ee)::ecmp)
                             ((n,ARule.term_rule c args t) :: l)
| preserving_compiler_sort_le : forall cmp ecmp l n c t1 t2,
    elab_preserving_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_sort (strip_args target) (compile_ctx ecmp c)
            (compile_sort ecmp t1)
            (compile_sort ecmp t2) ->
    elab_preserving_compiler target cmp ecmp ((n,ARule.sort_le c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp ecmp l n c e1 e2 t,
    elab_preserving_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_term (strip_args target) (compile_ctx ecmp c)
            (compile_sort ecmp t)
            (compile_term ecmp e1)
            (compile_term ecmp e2) ->
    elab_preserving_compiler target cmp ecmp ((n,ARule.term_le c e1 e2 t) :: l).
Hint Constructors elab_preserving_compiler : judgment.

Lemma elab_implies_preserving_compiler cmp ecmp target source
  : elab_preserving_compiler target cmp ecmp source ->
    preserving_compiler (strip_args target) ecmp (strip_args source).
Proof using .
  elim; intros; simpl; constructor; eauto using elab_sort_wf, elab_term_wf.
Qed.

Class ElabCompiler lt ls cmp :=
  {
  elab_compiler : Compilers.compiler;
  elab_compiler_pf : elab_preserving_compiler lt cmp elab_compiler ls
  }.

Fixpoint make_compiler
           (cmp_sort : string -> list string -> sort)
           (cmp_exp : string -> list string -> exp)
           (l : Rule.lang) : compiler :=
  match l with
  | (n,Rule.sort_rule c)::l' =>
    (n,sort_case (map fst c) (cmp_sort n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,Rule.term_rule c _)::l' => (n,term_case (map fst c) (cmp_exp n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,_)::l' => 
    (make_compiler cmp_sort cmp_exp l')
  | [::] => [::]
  end.

Lemma preserving_compiler_term' target
  : forall cmp ecmp l n c args e ee t case_args,
    case_args = map fst c ->
    elab_preserving_compiler target cmp ecmp l ->
    elab_term target (compile_ctx ecmp c) e ee (compile_sort ecmp t) ->
    elab_preserving_compiler target
                             ((n, term_case case_args e)::cmp)
                             ((n, Compilers.term_case case_args ee)::ecmp)
                             ((n,ARule.term_rule c args t) :: l).
Proof using .
  intros.
  rewrite H.
  constructor; eauto.
Qed.


Lemma preserving_compiler_sort' target
  : forall cmp ecmp l n c args t et case_args,
    case_args = map fst c ->
    elab_preserving_compiler target cmp ecmp l ->
    elab_sort target (compile_ctx ecmp c) t et ->
    elab_preserving_compiler target
                             ((n, sort_case case_args t)::cmp)
                             ((n, Compilers.sort_case case_args et)::ecmp)
                             ((n,ARule.sort_rule c args ) :: l).
Proof using .
  intros.
  rewrite H.
  constructor; eauto.
Qed.
