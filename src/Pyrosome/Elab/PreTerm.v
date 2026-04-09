Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Term.
(*From Pyrosome.Theory Require Import Substable.*)

Section WithVar.
  Context (V : Type).

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).

  Notation term := (term V).
  
Unset Elimination Schemes.
Inductive preterm : Type :=
(* variable name        ()*)
| pre_var : V -> preterm
(* Rule label, list of subpreterms*)
| pre_con : V -> list ((V*preterm) + preterm) -> preterm.
Set Elimination Schemes.

Coercion pre_var : V >-> preterm.

Fixpoint of_term t :=
  match t with
  | var x => pre_var x
  | con n s =>
      let s' := map (fun x => inr (of_term x)) s in
      pre_con n s'
  end.

Fixpoint to_term t :=
  match t with
  | pre_var x => var x
  | pre_con n s =>
      let arg_to_term x :=
        match x with
        | inr x => [to_term x]
        | inl _ => []
        end in
      let s' := flat_map arg_to_term s in
      con n s'
  end.



Variant presort : Type := pre_scon : V -> list ((V*preterm) + preterm) -> presort.

Definition of_sort t :=
  match t with
  | scon n s =>
      let s' := map (fun x => inr (of_term x)) s in
      pre_scon n s'
  end.

Definition to_sort t :=
  match t with
  | pre_scon n s =>
      let arg_to_term x :=
        match x with
        | inr x => [to_term x]
        | inl _ => []
        end in
      let s' := flat_map arg_to_term s in
      scon n s'
  end.

Definition of_ctx := named_map of_sort.
Definition to_ctx := named_map to_sort.

End WithVar.

Arguments pre_var {V}%type_scope _.
Arguments pre_con {V}%type_scope _ _.
Arguments pre_scon {V}%type_scope _ _.

Arguments of_term {V}%type_scope t.
Arguments of_sort {V}%type_scope t.
Arguments of_ctx {V}%type_scope _.

Arguments to_term {V}%type_scope t.
Arguments to_sort {V}%type_scope t.
Arguments to_ctx {V}%type_scope _.

Notation prectx V := (named_list V (presort V)).

(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry preterm.
Declare Custom Entry presort.

Declare Custom Entry pre_arg_list.
Declare Custom Entry pre_arg.


Declare Custom Entry pre_ctx.
Declare Custom Entry pre_ctx_binding.

Module Notations.

  (* Since contexts are regular lists, 
     we need a scope to determine when to print them *)
  Declare Scope pre_ctx_scope.
  Bind Scope pre_ctx_scope with prectx.
  
  Notation "'{{pe' e }}" :=
    (e) (at level 0,
         e custom preterm at level 100,
         format "'[' '{{pe'  e '}}' ']'").
  Notation "'{{ps' e }}" :=
    (e) (at level 0,
         e custom presort at level 100,
         format "'[' '{{ps'  e '}}' ']'").
  
  Notation "{ x }" :=
    x (in custom preterm at level 0, x constr).
  Notation "{ x }" :=
    x (in custom pre_arg at level 0, x constr).
  Notation "{ x }" :=
    x (in custom presort at level 0, x constr).

  (*TODO: still including string scope here for convenience.
    Is there a way to parameterize that?
   *)
  Notation "# c" :=
    (inr (pre_con c%string []))
      (right associativity,in custom pre_arg at level 0, c constr at level 0,
                              format "# c").
  Notation "( e )" := (inr e)
                        (in custom pre_arg at level 0, e custom preterm at level 100, 
                            format "'[' ( e ) ']'").

  Notation "[ X := e ]" :=
    (inl (X,e))
      (in custom pre_arg at level 0,
          e custom preterm at level 100,
          X constr at level 100,
          format "'[' [ X := e ] ']'").

  Notation "" := [] (in custom pre_arg_list at level 0).
  Notation "a1 .. an" :=
    (cons an .. (cons a1 nil) ..)
      (right associativity,
        in custom pre_arg_list at level 50,
           a1 custom pre_arg, an custom pre_arg,
           format " '[hv' a1  ..  an ']'"
      ).
  
  Notation "# c al" :=
    (pre_con c%string al)
      (right associativity,
        in custom preterm at level 60,
           c constr at level 0,
           al custom pre_arg_list,
           format "'[' # c al ']'").
  
  Notation "# c al" :=
    (pre_scon c%string al)
      (right associativity,
        in custom presort at level 60,
           c constr at level 0,
           al custom pre_arg_list,
           format "'[' # c al ']'").
  
  Notation "x" :=
    (pre_var x%string)
      (in custom preterm at level 0, x constr at level 0, format "x").
  
  Notation "x" :=
    (inr (pre_var x%string))
      (in custom pre_arg at level 0, x constr at level 0, format "x").


Goal False.
  pose {{pe #"foo" }}.
  pose {{pe #"foo" (#"bar" "x") #"baz" "y"}}.
  pose {{ps #"foo" }}.
  pose {{ps #"foo" (#"bar" "x") #"baz" "y"}}.
  pose {{ps #"id" ["A" := #"bool"]}}.
Abort.
                               
(*Bind Scope ctx_scope with ctx.*)
(*
  Notation "'{{c' }}" :=
    nil
      (at level 0, format "'[' '{{c'  '}}' ']'", only parsing)
    : pre_ctx_scope.
  Notation "'{{c' bd , .. , bd' '}}'" :=
    (cons bd' .. (cons bd nil)..)
      (at level 0, bd custom pre_ctx_binding at level 100,
        format "'[' {{c  '[hv' bd ,  '/' .. ,  '/' bd' ']' }} ']'", only parsing) : pre_ctx_scope.
  *)

  Notation "bd , .. , bd'" :=
    (cons bd' .. (cons bd nil)..)
      (in custom pre_ctx at level 100, bd custom pre_ctx_binding at level 100,
          format "'[hv' bd ,  '/' .. ,  '/' bd' ']'").

  (*
  (* TODO: find uses and update*)
  Notation "! c" :=
    (c)
      (in custom prectx at level 0,
          c constr at level 0) : ctx_scope.
   *)

  Notation "" := nil (*(@nil (string*sort))*) (in custom pre_ctx at level 0) : pre_ctx_scope.

  Notation "x : t" :=
    (x%string, t)
      (in custom pre_ctx_binding at level 100, x constr at level 0,
          t custom presort at level 100).

  Local Definition as_prectx {V} (c:prectx V) :=c.

  (*TODO: fix
  Goal False.
    epose (as_ctx {{c }}).
    epose (as_ctx {{c "x" : #"env"}}).
    epose (as_ctx {{c "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"}}).
  Abort.
   *)

End Notations.



