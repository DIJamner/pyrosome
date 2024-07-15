(*
  A version of Term.v without metavariables.
  Can't be used to create rules, but makes computations on meta-closed more straightforward.

  Note: since there are no variables, there's no point in a separate type for sorts.
 *)
Set Implicit Arguments.

Require Import Lists.List Datatypes.String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Term.
From Pyrosome Require Import Tools.AllConstructors.
Import SumboolNotations.

Section WithVar.
  Context (V : Type).

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  
Unset Elimination Schemes.
Inductive term : Type :=
(* Rule label, list of subterms*)
| con : V -> list term -> term.
Set Elimination Schemes.

(*Stronger induction principle w/ better subterm knowledge
 *)
Fixpoint term_ind
         (P : term -> Prop)
         (IHC : forall n l, all P l ->
             P (con n l))
         (e : term) { struct e} : P e :=
  match e with
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [] => I
        | e' :: l' => conj (term_ind _ IHC e') (loop l')
        end in
    IHC n l (loop l)
  end.

Fixpoint term_rect
         (P : term -> Type)
         (IHC : forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))
         (e : term) { struct e} : P e :=
  match e with
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [] => tt
        | e' :: l' => (term_rect _ IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition term_rec := 
  term_rect
     : forall P : term -> Set,
       (forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))-> forall e : term, P e.

Lemma invert_eq_con_con n1 n2 s1 s2
  : con n1 s1 = con n2 s2 <-> (n1 = n2 /\ s1 = s2).
Proof. prove_inversion_lemma. Qed.
#[local] Hint Rewrite invert_eq_con_con : term.


Notation subst := (named_list term).

Section WithEqb.  
  Context {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}.

  
#[export] Instance term_eqb : Eqb term :=
  fix term_eqb (e1 e2 : term) :=
    let (n1,s1) := e1 in
    let (n2,s2) := e2 in
    andb (eqb n1 n2) (forallb2 term_eqb s1 s2).

#[local] Lemma term_eqb_refl e : Bool.Is_true (term_eqb e e).
Proof.
  induction e;
    basic_goal_prep;
    Term.basic_term_crush.
  revert H;
    induction l;
    basic_goal_prep;
    Term.basic_term_crush.
Qed.

(*TODO: there is definitely an easier way to prove this
  using list_eqb_ok.
 *)
#[export] Instance term_eqb_ok : Eqb_ok term_eqb.
Proof.
  unfold Eqb_ok;
    unfold eqb.
  induction a;
    destruct b;
    basic_goal_prep;
    Term.basic_term_crush.
  my_case Hn (eqb n v);
    basic_goal_prep;
    Term.basic_term_crush.
  revert l0 H; induction l;
    destruct l0;
    basic_goal_prep;
    Term.basic_term_crush.
  my_case Ha (term_eqb a t);
    basic_goal_prep;
    Term.basic_term_crush.
  2: solve [eauto using term_eqb_refl].
  specialize (IHl l0).
  case_match;
    basic_goal_prep;
    Term.basic_term_crush.
  specialize (H0 t).
  revert H0; case_match;
    basic_goal_prep;
    Term.basic_term_crush.
Qed.


Fixpoint close_term (e : Term.term V) : term :=
  match e with
  | Term.var n => con n []
  | Term.con n l => con n (map close_term l)
  end.

Definition close_sort (t : Term.sort V) : term :=
  let (n, l) := t in
  con n (map close_term l).

Section WithArgs.
  Context (args : list V).

  Fixpoint open_term (e : term) : Term.term V :=
    let (n, l) := e in
    if inb n args then Term.var n
    else Term.con n (map open_term l).
  
  Definition open_sort (e : term) : Term.sort V :=
    let (n, l) := e in
    Term.scon n (map open_term l).

  Lemma open_close_inverse_term e
    : all_constructors (fun n => ~ In n args) e ->
      (*TODO: use well_scoped?*)
      incl (Term.fv e) args ->
      open_term (close_term e) = e.
  Proof.
    induction e;
      basic_goal_prep;
      Term.basic_term_crush.
    all: case_match;
      Term.basic_term_crush.
    f_equal.
    revert dependent l.
    induction l;
      basic_goal_prep;
      Term.basic_term_crush.
    {
      (*TODO: make incl_app_inv a rewrite rule*)
      apply incl_app_inv in H1.
      Term.basic_term_crush.
    }
    {
      (*TODO: make incl_app_inv a rewrite rule*)
      apply incl_app_inv in H1.
      Term.basic_term_crush.
    }
  Qed.

End WithArgs.

Section WithDefault.
  
  Context {V_default : WithDefault V}.
  
  Instance term_default : WithDefault term := con default [].
  
End WithDefault.

End WithEqb.



End WithVar.

Arguments con {V}%type_scope _ _%list_scope.

#[export] Hint Rewrite invert_eq_con_con : term.
  
#[export] Existing Instance term_default.

Notation subst V := (@named_list V (term V)).

(* Copied from Term.v *)
Declare Custom Entry closed_term.

Declare Custom Entry closed_arg_list.
Declare Custom Entry closed_arg.

Module Notations.
  
  Notation "'{{:' e }}" :=
    (e) (at level 0,
         e custom closed_term at level 100,
         format "'[' '{{:'  e '}}' ']'").
  
  Notation "{ x }" :=
    x (in custom closed_term at level 0, x constr).
  Notation "{ x }" :=
    x (in custom closed_arg at level 0, x constr).

  (*TODO: still including string scope here for convenience.
    Is there a way to parameterize that?
   *)
  (*
    TODO: do I want the # for closed terms? don't need to distinguish variables.
    Related: should I change Term.v to use a symbol on vars instead?
   *)
  Notation "# c" :=
    (con c%string [])
      (right associativity,in custom closed_arg at level 0, c constr at level 0,
                              format "# c").
  Notation "( e )" := e (in custom closed_arg at level 0, e custom closed_term at level 100, 
           format "'[' ( e ) ']'").

  Notation "" := [] (in custom closed_arg_list at level 0).
  Notation "a1 .. an" :=
    (cons an .. (cons a1 nil) ..)
      (right associativity,
        in custom closed_arg_list at level 50,
           a1 custom closed_arg, an custom closed_arg,
           format " '[hv' a1  ..  an ']'"
      ).
  
  Notation "# c al" :=
    (con c%string al)
      (right associativity,
        in custom closed_term at level 60,
           c constr at level 0,
           al custom closed_arg_list,
           format "'[' # c al ']'").

Goal False.
  pose ({{: #"foo" }}).
  pose {{: #"foo" (#"bar" #"x") #"baz" #"y"}}.
Abort.

End Notations.

