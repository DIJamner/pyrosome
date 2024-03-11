Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

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

  (* Compilers can target an arbitrary model.
     They do not have to target syntax.
   *)

  Section WithPreModel.
    Context {tgt_term tgt_sort : Type}
            {tgt_Model : @PreModel V tgt_term tgt_sort}
            (*TODO: should I make it so that these aren't necessary?*)
            `{WithDefault tgt_term}
            `{WithDefault tgt_sort}.

(* each element is the image for that constructor or axiom*)
Variant compiler_case :=
 | term_case (args : list V) (e:tgt_term)
 | sort_case (args : list V) (t:tgt_sort).
Definition compiler := named_list compiler_case.

Lemma invert_eq_term_case_term_case args args' e e'
  : term_case args e = term_case args' e' <-> args = args' /\ e = e'.
Proof using. prove_inversion_lemma. Qed.
Hint Rewrite invert_eq_term_case_term_case : lang_core.

Lemma invert_eq_term_case_sort_case args args' e e'
  : term_case args e = sort_case args' e' <-> False.
Proof using. prove_inversion_lemma. Qed.
Hint Rewrite invert_eq_term_case_sort_case : lang_core.

Lemma invert_eq_sort_case_term_case args args' e e'
  : sort_case args e = term_case args' e' <-> False.
Proof using. prove_inversion_lemma. Qed.
Hint Rewrite invert_eq_sort_case_term_case : lang_core.

Lemma invert_eq_sort_case_sort_case args args' e e'
  : sort_case args e = sort_case args' e' <-> args = args' /\ e = e'.
Proof using. prove_inversion_lemma. Qed.
Hint Rewrite invert_eq_sort_case_sort_case : lang_core.

Section CompileFn.
  Context (cmp : compiler).

  (*TODO: move to Term.v*)
  Existing Instance term_default.
  Existing Instance sort_default.

  (*TODO: is this the right choice? 
    It's the same as combine for wf terms,
    but it makes some theorems easier
    at the expense of requiring a default instance for V
   *)
  Fixpoint combine_r_padded {A B : Type} `{WithDefault B}
           (l : list A) (l' : list B) {struct l} : list (A * B) :=
  match l, l' with
  | [],_ => []
  | x :: tl, [] => (x, default) :: combine_r_padded tl []
  | x :: tl, y :: tl' => (x, y) :: combine_r_padded tl tl'
  end.

Arguments combine_r_padded [A B]%type_scope {_} (_ _)%list_scope.
  
  (*TODO: notations do a poor job of spacing this*)
  Fixpoint compile (e : term) : tgt_term :=
    match e with
    | var x => inj_var x
    | con n s =>
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (term_case args e) => e[/combine_r_padded args arg_terms/]
      | _ => default
      end
    end.

  Definition compile_sort (t : sort) : tgt_sort :=
    match t with
    | scon n s =>
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (sort_case args t) => t[/combine_r_padded args arg_terms/]
      | _ => default
      end
    end.  
  
  Definition compile_args := map compile.

  Definition compile_subst (s : named_list term) := named_map compile s.

  Definition compile_ctx (c:named_list sort) := named_map compile_sort c.

End CompileFn.
End WithPreModel.

  
  Section WithModel.
    Context {tgt_term tgt_sort : Type}
      {tgt_Model : @Model V tgt_term tgt_sort}
      (*TODO: should I make it so that these aren't necessary?*)
      `{WithDefault tgt_term}
      `{WithDefault tgt_sort}.

    Existing Instance tgt_Model.

    Notation compiler :=
      (compiler (tgt_term:=tgt_term)
         (tgt_sort:=tgt_sort)).

(*
First we define an inductively provable (and in fact decidable) property 
of elaborated compilers.
*)

Section Extension.
  Context (cmp_pre : compiler).
  (*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
  Inductive preserving_compiler_ext : compiler -> lang -> Prop :=
  | preserving_compiler_nil : preserving_compiler_ext [] []
  | preserving_compiler_sort : forall cmp l n c args t,
      preserving_compiler_ext cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      Model.wf_sort (compile_ctx (cmp ++ cmp_pre) c) t ->
      preserving_compiler_ext ((n,sort_case (map fst c) t)::cmp)
                              ((n,sort_rule c args) :: l)
  | preserving_compiler_term : forall cmp l n c args e t,
      preserving_compiler_ext cmp l ->
      (* Notable: only uses the previous parts of the compiler on c, t *)
      Model.wf_term (compile_ctx (cmp ++ cmp_pre) c) e (compile_sort (cmp ++ cmp_pre) t) ->
      preserving_compiler_ext ((n, term_case (map fst c) e)::cmp)
                              ((n,term_rule c args t) :: l)
  | preserving_compiler_sort_eq : forall cmp l n c t1 t2,
      preserving_compiler_ext cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      Model.eq_sort (compile_ctx (cmp ++ cmp_pre) c)
              (compile_sort (cmp ++ cmp_pre) t1)
              (compile_sort (cmp ++ cmp_pre) t2) ->
      preserving_compiler_ext cmp ((n,sort_eq_rule c t1 t2) :: l)
  | preserving_compiler_term_eq : forall cmp l n c e1 e2 t,
      preserving_compiler_ext cmp l ->
      (* Notable: only uses the previous parts of the compiler on c *)
      Model.eq_term (compile_ctx (cmp ++ cmp_pre) c)
              (compile_sort (cmp ++ cmp_pre) t)
              (compile (cmp ++ cmp_pre) e1)
              (compile (cmp ++ cmp_pre) e2) ->
      preserving_compiler_ext cmp ((n,term_eq_rule c e1 e2 t) :: l).

End Extension.

End WithModel.
    
End WithVar.
#[export] Hint Rewrite invert_eq_term_case_term_case : lang_core.
#[export] Hint Rewrite invert_eq_term_case_sort_case : lang_core.
#[export] Hint Rewrite invert_eq_sort_case_term_case : lang_core.
#[export] Hint Rewrite invert_eq_sort_case_sort_case : lang_core.
#[export] Hint Constructors preserving_compiler_ext : lang_core.

(*TODO: add preserving_compiler notation once other files are updated *)
(*TODO: shouth the RHS be in the constr entry?
  Probably not now that compilers are more general.
*)

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

  (*TODO: specialized to strings. Generalize.*)
  Definition gen_rule (cmp : compiler string) (p : string * rule string) : named_list string (compiler_case string) :=
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
