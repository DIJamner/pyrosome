Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable.
Import SumboolNotations.

(*TODO:  this is a hack, discharge it properly *)
  Lemma Eqb_eqb_extensionally_unique {A} (Heqb1 Heqb2 : Eqb A)
    : forall a b, eqb (Eqb:=Heqb1) a b = eqb (Eqb:=Heqb2) a b.
  Proof.
    intros.
    destruct (Eqb_dec a b); subst.
    {
      rewrite !eqb_refl.
      reflexivity.
    }
    {
      match goal with
        |- ?lhs = ?rhs =>
          remember lhs as lhsb;
          remember rhs as rhsb;
          destruct lhsb; destruct rhsb; try tauto
      end.
      {
        symmetry in Heqlhsb.
        rewrite eqb_eq in Heqlhsb.
        tauto.
      }
      {
        symmetry in Heqrhsb.
        rewrite eqb_eq in Heqrhsb.
        tauto.
      }
    }
  Qed.

  
  Lemma Eqb_unique_named_list_lookup {A B} (Heqb1 Heqb2 : Eqb A)
    : forall x y (s : @named_list A B), named_list_lookup (H := Heqb1) x s y
                  = named_list_lookup (H := Heqb2)x s y.
  Proof.
    induction s; basic_goal_prep; basic_utils_crush.
    rewrite Eqb_eqb_extensionally_unique with (Heqb1:= Heqb1) (Heqb2:= Heqb2).
    rewrite IHs.
    reflexivity.
  Qed.

Create HintDb term discriminated.
Ltac basic_term_crush := let x := autorewrite with utils term in * in
                                  let y := eauto with utils term in
                                          generic_crush x y.
Ltac basic_term_firstorder_crush :=
  let x := autorewrite with utils term in * in
          let y := eauto with utils term in
                  generic_firstorder_crush x y.

Section WithVar.
  Context (V : Type).

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  
  Notation Substable0 := (Substable0 V).
  Notation Substable := (@Substable V).
  
Unset Elimination Schemes.
Inductive term : Type :=
(* variable name *)
| var : V -> term
(* Rule label, list of subterms*)
| con : V -> list term -> term.
Set Elimination Schemes.

Coercion var : V >-> term.

(*Stronger induction principle w/ better subterm knowledge
 *)
Fixpoint term_ind
         (P : term -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n l, all P l ->
             P (con n l))
         (e : term) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [] => I
        | e' :: l' => conj (term_ind _ IHV IHC e') (loop l')
        end in
    IHC n l (loop l)
  end.

Fixpoint term_rect
         (P : term -> Type)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))
         (e : term) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [] => tt
        | e' :: l' => (term_rect _ IHV IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition term_rec := 
  term_rect
     : forall P : term -> Set,
       (forall n, P (var n)) ->
       (forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))-> forall e : term, P e.

Variant sort : Type := scon : V -> list term -> sort.

Lemma invert_eq_var_var x y
  : var x = var y <-> x = y.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_var_var : term.

Lemma invert_eq_var_con x n s
  : var x = con n s <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_var_con : term.

Lemma invert_eq_con_var n s y
  : con n s = var y <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_con_var : term.

Definition ctx : Type := named_list sort.

Definition subst : Type := named_list term.

Definition subst_lookup `{V_Eqb : Eqb V} (s : subst) (n : V) : term :=
  named_list_lookup (var n) s n.

Arguments subst_lookup {_} !s n/.

Section WithEqb.  
  Context {V_Eqb : Eqb V}.


Fixpoint term_var_map (f : V -> term) (e : term) : term :=
  match e with
  | var n => f n
  | con n l => con n (map (term_var_map f) l)
  end.

Arguments term_var_map f !e /.

Definition term_subst (s : subst) e : term :=
  term_var_map (subst_lookup s) e.

Arguments term_subst s !e /.

Arguments subst_cmp [V]%type_scope {A}%type_scope {Substable0} _ _ /.

(* Well-scoped languages
   Written as functions that decide the properties
   determines that variables (but not constructor symbols) are well-scoped

   Note: we could write this in bool using a decidable In (which is fine
   because Vs have decidable equality)
 *)
Fixpoint ws_term (args : list V) (e : term) : Prop :=
  match e with
  | var x => In x args
  | con _ s => all (ws_term args) s
  end.
Arguments ws_term args !e/.

  Local Hint Resolve args_well_scoped_subst : term.

  Instance substable_term : Substable0 term :=
    {
      inj_var := var;
      apply_subst0 := term_subst;
      well_scoped0 := ws_term;
    }.

  Notation ws_args := (ws_args (V:=V) (A:=term)).

  (*TODO: I have a false dependency on Eqb V here
    due to the structure of Substable0.
    Could eliminate it by parameterizing apply_subst0 by Eqb V.
*)
Definition ws_sort args (t : sort) : Prop :=
  match t with scon _ s => ws_args args s end.
Arguments ws_sort args !t/.

(* TODO: currently duplicated in Model.v
   What's the best way to organize the code to avoid?
   Maybe the following:
   Rule -> |- RuleDefs , CoreDefs |- Rule
   Core -> RuleDefs |- CoreDefs, RuleDefs,Rule, CoreDefs|- Core
 *)
Fixpoint ws_ctx (c : ctx) : Prop :=
  match c with
  | [] => True
  | (n,t) :: c' => fresh n c' /\ ws_sort (map fst c') t /\ ws_ctx c'
  end.
Arguments ws_ctx !c/.

Lemma ws_all_fresh_ctx c
  : ws_ctx c -> all_fresh c.
Proof using .
  induction c; basic_goal_prep; basic_utils_crush.
Qed.

Lemma id_args_cons A n (a :A) c
  : id_args ((n,a)::c) = (var n)::(id_args c).
Proof.
  reflexivity.
Qed.

  
  (*TODO: move to Substable.v*)
  Lemma id_args_nil {A} `{Substable0 A} B'
    : @id_args V A _ B' [] = [].
  Proof.
    reflexivity.
  Qed.
  
Hint Rewrite id_args_nil : term.  
Hint Rewrite id_args_cons : term.
Hint Rewrite @subst_assoc : term.
Hint Rewrite @subst_id : term.
Hint Rewrite @strengthen_subst : term.
Hint Resolve well_scoped_subst : term.

Lemma term_subst_nil e : term_subst [] e = e.
Proof.  
  induction e; basic_goal_prep; basic_utils_crush.
  f_equal.
  revert H.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite term_subst_nil : term.


Lemma named_map_subst_nil s : named_map (term_subst []) s = s.
Proof.
  induction s; basic_goal_prep;basic_term_crush.
Qed.
Hint Rewrite named_map_subst_nil : term.

Lemma subst_lookup_map s1 s2 n
  : In n (map fst s2) ->
          term_subst s1 (subst_lookup s2 n) = subst_lookup (named_map (term_subst s1) s2) n.
Proof.
  induction s2; basic_goal_prep;
  basic_term_crush.
  case_match; basic_term_crush.
Qed.
Hint Rewrite subst_lookup_map : term.
  
Lemma term_subst_assoc : forall s1 s2 a,
    ws_term (map fst s2) a ->
    term_subst s1 (term_subst s2 a)
    = term_subst (subst_cmp s1 s2) a.
Proof.
  induction a; basic_goal_prep;
    basic_term_crush.
  f_equal.
  revert dependent l;
    induction l;
    basic_goal_prep;
    basic_term_crush.
Qed.
Hint Rewrite term_subst_assoc : term.

Lemma subst_lookup_id A (c : named_list A) n
  : subst_lookup (id_subst c) n = var n.
Proof.
  induction c; basic_goal_prep;
    basic_term_crush.
  (*TODO: get rid of need for symmetry*)
  case_match; symmetry in HeqH;
    basic_goal_prep;
    basic_term_crush.
Qed.
Hint Rewrite subst_lookup_id : term.

Lemma term_subst_id
  : forall A (c : named_list A) a,
    term_subst (id_subst c) a = a.
Proof.
  induction a; basic_goal_prep;
    basic_term_crush.
  f_equal.
  revert dependent l;
    induction l;
    basic_goal_prep;
    basic_term_crush.
Qed.
Hint Rewrite term_subst_id : term.

Lemma term_strengthen_subst s a n e
  : ws_term (map fst s) a ->
    fresh n s ->
    term_subst ((n,e)::s) a = term_subst s a.
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_term_crush.
    
  f_equal.

  revert dependent l.
  induction l; basic_goal_prep;
    basic_term_crush.
Qed.


Lemma ws_term_subst_lookup args s n
  : ws_subst args s ->
    In n (map fst s) ->
    ws_term args (subst_lookup s n).
Proof.
  induction s; basic_goal_prep; try case_match;
    basic_term_crush.
Qed.
Hint Resolve ws_term_subst_lookup : term.
  
Lemma term_well_scoped_subst args s a
    : ws_subst args s ->
      ws_term (map fst s) a ->
      ws_term args (term_subst s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_term_crush.

  revert dependent l.
  induction l; basic_goal_prep;
    basic_term_crush.
Qed.
  Local Hint Resolve term_well_scoped_subst : term.

  
  
  (*TODO: Prove*)
  Lemma subst_var `{EqbV: Eqb V}
    : forall s x, apply_subst0 s (inj_var x) = subst_lookup (V_Eqb:=EqbV) s x.
  Proof.
    intros.
    simpl.
    unfold subst_lookup.
    eapply Eqb_unique_named_list_lookup.
  Qed.    
  
  Instance substable_term_ok : Substable0_ok term :=
    {
      subst_var := @subst_var;
      subst_assoc0 := term_subst_assoc;
      subst_id0 := term_subst_id;
      strengthen_subst0 := term_strengthen_subst;
      well_scoped_subst0 := term_well_scoped_subst;
    }.
 
Local Hint Resolve subst_well_scoped_subst : term.


Definition sort_subst (s : subst) (t : sort) : sort :=
  let (c, s') := t in scon c s'[/s/].
Arguments sort_subst s !t/.

Lemma sort_subst_assoc : forall s1 s2 a,
    ws_sort (map fst s2) a ->
    sort_subst s1 (sort_subst s2 a)
    = sort_subst (subst_cmp s1 s2) a.
Proof.
  destruct a; basic_goal_prep;
    basic_term_crush.
  (* TODO: the automation should get this *)
  erewrite subst_assoc; eauto.
  typeclasses eauto.
Qed.


Lemma sort_subst_id
  : forall A (c : named_list A) a,
    sort_subst (id_subst c) a = a.
Proof.
  destruct a; basic_goal_prep;
    basic_term_crush.
Qed.


Lemma sort_strengthen_subst s a n e
  : ws_sort (map fst s) a ->
    fresh n s ->
    sort_subst ((n,e)::s) a = sort_subst s a.
Proof.
  destruct a; basic_goal_prep;
    basic_term_crush.
  (* TODO: the automation should get this *)
  erewrite strengthen_subst; eauto.
  typeclasses eauto.
Qed.

Lemma sort_well_scoped_subst args s a
    : ws_subst args s ->
      ws_sort (map fst s) a ->
      ws_sort args (sort_subst s a).
Proof.
  destruct a; basic_goal_prep; try case_match;
    basic_term_crush.
  (* TODO: the automation should get this *)
  change (ws_args ?c ?a) with (well_scoped c a) in *.
  eapply well_scoped_subst; eauto.
  typeclasses eauto.
Qed.

  #[export] Instance substable_sort : Substable term sort :=
    {
      apply_subst := sort_subst;
      well_scoped := ws_sort;
    }.
  
  #[export] Instance substable_sort_ok : Substable_ok term sort :=
    {
      subst_assoc := sort_subst_assoc;
      subst_id := sort_subst_id;
      strengthen_subst := sort_strengthen_subst;
      well_scoped_subst := sort_well_scoped_subst;
    }.

Fixpoint eq_term e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => eqb x y
  | con n1 l1, con n2 l2 =>
    (eqb n1 n2) && (all2 eq_term l1 l2)
  | _,_ => false
  end.

Definition eq_sort (t1 t2 : sort) : bool :=
  let (n1, l1) := t1 in
  let (n2, l2) := t2 in
    (eqb n1 n2) && (all2 eq_term l1 l2).

Lemma with_names_from_args_subst (c':ctx) s' (s : list term)
  : with_names_from c' s[/s'/] = (with_names_from c' s)[/s'/].
Proof.
  revert s.
  induction c';
    destruct s;
    basic_goal_prep;
    basic_term_crush.
Qed.

Lemma well_scoped_change_args A `{Substable term A} (a:A) args args'
  : well_scoped args' a ->
    args = args' ->
    well_scoped args a.
Proof.  
  intros; subst; auto.
Qed.
Hint Resolve well_scoped_change_args : term.


Lemma invert_con n n' s s'
  : con n s = con n' s' <-> n = n' /\ s = s'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_con : term.

Lemma invert_var_con n s x
  : var x = con n s <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_var_con : term.

Lemma invert_con_var n s x
  : con n s = var x <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_var_con : term.


Lemma invert_scon n n' s s'
  : scon n s = scon n' s' <-> n = n' /\ s = s'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_scon : term.

(*TODO: put in substable?*)
(*TODO: guarentee all_fresh or no?*)
Fixpoint fv e : list V :=
  match e with
  | var x => [x]
  | con _ s => flat_map fv s
  end.

Definition fv_args := flat_map fv.

Definition fv_sort (t:sort) :=
  let (_,s) := t in
  fv_args s.


Fixpoint term_eq_dec (e1 e2 : term) {struct e1} : {e1 = e2} + {~ e1 = e2}.
  refine(match e1, e2 with
         | var x, var y => SB! Eqb_dec x y
         | con n s, con n' s' =>
           SB! (Eqb_dec n n') SB& (list_eq_dec term_eq_dec s s')
         | _, _ => right _
         end); basic_term_crush.
Defined.


Definition sort_eq_dec (e1 e2 : sort) : {e1 = e2} + {~ e1 = e2}.
  refine(match e1, e2 with
         | scon n s, scon n' s' =>
           SB! (Eqb_dec n n') SB& (list_eq_dec term_eq_dec s s')
         end); basic_term_crush.
Defined.

Definition ctx_eq_dec := list_eq_dec (pair_eq_dec Eqb_dec sort_eq_dec).

  Section WithDefault.
    
    Context {V_default : WithDefault V}.
    
    Instance term_default : WithDefault term := con default [].
    Instance sort_default : WithDefault sort := scon default [].


    Definition ctx_lookup (c: ctx) (n : V) : sort :=
      named_list_lookup default c n.

    Arguments ctx_lookup !c n/.

  End WithDefault.
    
  End WithEqb.
  
End WithVar.

Arguments var {V}%type_scope _.
Arguments con {V}%type_scope _ _%list_scope.

#[export] Hint Rewrite @subst_assoc : term.
#[export] Hint Rewrite @subst_id : term.
#[export] Hint Rewrite @strengthen_subst : term.
#[export] Hint Resolve well_scoped_subst : term.
#[export] Hint Rewrite id_args_nil : term.
#[export] Hint Rewrite id_args_cons : term.
#[export] Hint Rewrite invert_eq_con_var : term.
#[export] Hint Rewrite invert_eq_var_con : term.
#[export] Hint Rewrite invert_eq_var_var : term.
#[export] Hint Rewrite term_subst_nil : term.
#[export] Hint Rewrite named_map_subst_nil : term.
#[export] Hint Rewrite subst_lookup_map : term.
#[export] Hint Rewrite term_subst_assoc : term.
#[export] Hint Rewrite subst_lookup_id : term.
#[export] Hint Rewrite term_subst_id : term.
#[export] Hint Resolve ws_term_subst_lookup : term.
#[export] Hint Resolve well_scoped_change_args : term.
#[export] Hint Rewrite invert_con : term.
#[export] Hint Rewrite invert_var_con : term.
#[export] Hint Rewrite invert_scon : term.

#[export] Existing Instance substable_term.
#[export] Existing Instance substable_term_ok.                   
#[export] Existing Instance substable_sort.
#[export] Existing Instance substable_args.
#[export] Existing Instance substable_subst.
  
#[export] Existing Instance term_default.
#[export] Existing Instance sort_default.


Ltac fold_Substable :=
  try change (named_map (term_subst ?s') ?s) with s[/s'/];
  try change (term_subst ?s ?e) with e[/s/];
  try change (sort_subst ?s ?e) with e[/s/];
  try change (args_subst ?s ?e) with e[/s/];
  try change (subst_cmp ?s ?e) with e[/s/];
  try change (map (term_var_map (subst_lookup ?s')) ?s) with s[/s'/].

(*TODO: specialized to strings*)
Ltac cbn_substs :=
  cbn [apply_subst with_names_from term_subst subst_cmp args_subst sort_subst
                   substable_sort substable_args substable_term substable_subst map
      term_var_map subst_lookup named_list_lookup eqb String.eqb Ascii.eqb Bool.eqb].


Arguments subst_lookup [V]%type_scope {V_Eqb} !s n/.
Arguments ctx_lookup [V]%type_scope {V_Eqb V_default} !c n/.
Arguments term_var_map [V]%type_scope f !e /.
Arguments term_subst [V]%type_scope {V_Eqb} s !e /.
Arguments subst_cmp [V]%type_scope {A}%type_scope {Substable0} _ _ /.


Arguments ws_term [V]%type_scope args !e/.
Arguments ws_ctx [V]%type_scope {V_Eqb} !c/.
Arguments id_args : simpl never.
Arguments sort_subst [V]%type_scope {V_Eqb} s !t/.

(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry term.
Declare Custom Entry sort.

Declare Custom Entry arg_list.
Declare Custom Entry arg.


Declare Custom Entry ctx.
Declare Custom Entry ctx_binding.

Module Notations.

  (* Since contexts are regular lists, 
     we need a scope to determine when to print them *)
  Declare Scope ctx_scope.
  Bind Scope ctx_scope with ctx.
  
  Notation "'{{e' e }}" :=
    (e) (at level 0,
         e custom term at level 100,
         format "'[' '{{e'  e '}}' ']'").
  Notation "'{{s' e }}" :=
    (e) (at level 0,
         e custom sort at level 100,
         format "'[' '{{s'  e '}}' ']'").
  
  Notation "{ x }" :=
    x (in custom term at level 0, x constr).
  Notation "{ x }" :=
    x (in custom arg at level 0, x constr).
  Notation "{ x }" :=
    x (in custom sort at level 0, x constr).
  (* TODO: issues; fix *)
  (*
    Notation "{ x }" :=
    x (in custom ctx at level 0, x constr).
  *)

  (*TODO: still including string scope here for convenience.
    Is there a way to parameterize that?
   *)
  Notation "# c" :=
    (con c%string [])
      (right associativity,in custom arg at level 0, c constr at level 0,
                              format "# c").
  Notation "( e )" := e (in custom arg at level 0, e custom term at level 100).

  Notation "" := [] (in custom arg_list at level 0).
  Notation "a1 .. an" :=
    (cons an .. (cons a1 nil) ..)
      (right associativity,
        in custom arg_list at level 50,
           a1 custom arg, an custom arg,
           format " '[hv' a1  ..  an ']'"
      ).
  
  Notation "# c al" :=
    (con c%string al)
      (right associativity,
        in custom term at level 60,
           c constr at level 0,
           al custom arg_list,
           format "'[' # c al ']'").
  
  Notation "# c al" :=
    (scon c%string al)
      (right associativity,
        in custom sort at level 60,
           c constr at level 0,
           al custom arg_list,
           format "'[' # c al ']'").
  
  Notation "x" :=
    (var x%string)
      (in custom term at level 0, x constr at level 0, format "x").
  
  Notation "x" :=
    (var x%string)
      (in custom arg at level 0, x constr at level 0, format "x").

  
  (* TODO: allow redundant parens?
  Notation "( e )" := e (in custom term at level 0, e custom term at level 100).
  Notation "( e )" := e (in custom sort at level 0, e custom sort at level 100).
   *)


  Check {{e #"foo" }}.
  Check {{e #"foo" (#"bar" "x") #"baz" "y"}}.
  Check {{s #"foo" }}.
  Check {{s #"foo" (#"bar" "x") #"baz" "y"}}.
                               
  Bind Scope ctx_scope with ctx.

  Notation "'{{c' }}" :=
    nil
      (at level 0, format "'[' '{{c'  '}}' ']'")
    : ctx_scope.
  Notation "'{{c' bd , .. , bd' '}}'" :=
    (cons bd' .. (cons bd nil)..)
      (at level 0, bd custom ctx_binding at level 100,
          format "'[' {{c  '[hv' bd ,  '/' .. ,  '/' bd' ']' }} ']'") : ctx_scope.

  Notation "bd , .. , bd'" :=
    (cons bd' .. (cons bd nil)..)
      (in custom ctx at level 100, bd custom ctx_binding at level 100,
          format "'[hv' bd ,  '/' .. ,  '/' bd' ']'") : ctx_scope.

  (*
  (* TODO: find uses and update*)
  Notation "! c" :=
    (c)
      (in custom ctx at level 0,
          c constr at level 0) : ctx_scope.
   *)

  Notation "" := nil (*(@nil (string*sort))*) (in custom ctx at level 0) : ctx_scope.

  Notation "x : t" :=
    (x%string, t)
      (in custom ctx_binding at level 100, x constr at level 0,
          t custom sort at level 100).

  Local Definition as_ctx {V} (c:ctx V) :=c.
  Check (as_ctx {{c }}).
  Check (as_ctx {{c "x" : #"env"}}).
  Check (as_ctx {{c "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"}}).

  
  (* Used to print arguments in the order the appear in a term *)
  Definition argument_seq_marker {V} (s : list (term V)) := s.
  
  Notation "al" :=
    (argument_seq_marker al)
      (at level 0,
        al custom arg_list,
        only printing).

End Notations.

