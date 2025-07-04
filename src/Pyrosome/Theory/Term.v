Set Implicit Arguments.

Require Import Lists.List Datatypes.String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable.
Import SumboolNotations.

(*TODO: this is a hack, discharge it properly
  TODO: Check whether this is still used
 *)
Lemma Eqb_eqb_extensionally_unique {A} (Heqb1 Heqb2 : Eqb A)
  {_ : Eqb_ok Heqb1}
  {_ : Eqb_ok Heqb2}
  : forall a b, eqb (Impl:=Heqb1) a b = eqb (Impl:=Heqb2) a b.
  Proof.
    intros.
    specialize (H a b).
    specialize (H0 a b).
    revert H H0; repeat case_match; basic_goal_prep; basic_utils_crush.
  Qed.

  
  Lemma Eqb_unique_named_list_lookup {A B} (Heqb1 Heqb2 : Eqb A)
  {_ : Eqb_ok Heqb1}
  {_ : Eqb_ok Heqb2}
    : forall x y (s : @named_list A B), named_list_lookup (EqbS := Heqb1) x s y
                  = named_list_lookup (EqbS := Heqb2) x s y.
  Proof.
    induction s; basic_goal_prep; basic_utils_crush.
    rewrite Eqb_eqb_extensionally_unique with (Heqb1:= Heqb1) (Heqb2:= Heqb2); try assumption.
    rewrite IHs.
    reflexivity.
  Qed.

Create HintDb term discriminated.
Ltac basic_term_crush :=
  let x := autorewrite with bool rw_prop inversion utils term in * in
        let y := eauto with bool utils term in
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

Lemma invert_eq_con_con n1 n2 s1 s2
  : con n1 s1 = con n2 s2 <-> (n1 = n2 /\ s1 = s2).
Proof. prove_inversion_lemma. Qed.
#[local] Hint Rewrite invert_eq_con_con : term.

Lemma invert_eq_var_var x y
  : var x = var y <-> x = y.
Proof. prove_inversion_lemma. Qed.
#[local] Hint Rewrite invert_eq_var_var : term.

Lemma invert_eq_var_con x n s
  : var x = con n s <-> False.
Proof. prove_inversion_lemma. Qed.
#[local] Hint Rewrite invert_eq_var_con : term.

Lemma invert_eq_con_var n s y
  : con n s = var y <-> False.
Proof. prove_inversion_lemma. Qed.
#[local] Hint Rewrite invert_eq_con_var : term.


Lemma invert_eq_scon_scon n1 n2 s1 s2
  : scon n1 s1 = scon n2 s2 <-> (n1 = n2 /\ s1 = s2).
Proof. prove_inversion_lemma. Qed.
#[local] Hint Rewrite invert_eq_scon_scon : term.


#[local] Notation ctx := (named_list sort).

#[local] Notation subst := (named_list term).

Definition term_subst_lookup `{V_Eqb : Eqb V} (s : subst) (n : V) : term :=
  named_list_lookup (var n) s n.

Arguments term_subst_lookup {_} !s n/.

Section WithEqb.  
  Context {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}.
  
#[export] Instance term_eqb : Eqb term :=
  fix term_eqb (e1 e2 : term) :=
    match e1, e2 with
    | var n1, var n2 => eqb n1 n2
    | con n1 s1, con n2 s2 =>
        andb (eqb n1 n2) (forallb2 term_eqb s1 s2)
    | _, _ => false
    end.

#[export] Instance sort_eqb : Eqb sort :=
  fun e1 e2 =>
    let (n1,s1) := e1 in
    let (n2,s2) := e2 in
    andb (eqb n1 n2) (eqb s1 s2).

#[local] Lemma term_eqb_refl e : Bool.Is_true (term_eqb e e).
Proof.
  induction e;
    basic_goal_prep;
    basic_term_crush.
  revert H;
    induction l;
    basic_goal_prep;
    basic_term_crush.
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
    basic_term_crush.
  {
    case_match;
      basic_term_crush.
  }
  {
    my_case Hn (eqb n v);
      basic_goal_prep;
      basic_term_crush.
    revert l0 H; induction l;
      destruct l0;
      basic_goal_prep;
      basic_term_crush.
    my_case Ha (term_eqb a t);
      basic_goal_prep;
      basic_term_crush.
    2: solve [eauto using term_eqb_refl].
    specialize (IHl l0).
    case_match;
      basic_goal_prep;
      basic_term_crush.
    specialize (H0 t).
    revert H0; case_match;
      basic_goal_prep;
      basic_term_crush.
  }
Qed.


#[export] Instance sort_eqb_ok : Eqb_ok sort_eqb.
Proof.
  unfold Eqb_ok;
    unfold eqb.
  destruct a;
    destruct b;
    simpl.
  my_case Hv (eqb v v0);
    simpl;
    basic_term_crush.
  case_match; basic_goal_prep;
    basic_term_crush.
Qed.
  
Fixpoint term_var_map (f : V -> term) (e : term) : term :=
  match e with
  | var n => f n
  | con n l => con n (map (term_var_map f) l)
  end.

Arguments term_var_map f !e /.

Definition term_subst (s : subst) e : term :=
  term_var_map (term_subst_lookup s) e.

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

  #[export] Instance substable_term : Substable0 term :=
    {
      inj_var := var;
      apply_subst0 := term_subst;
      well_scoped0 := ws_term;
    }.

  Notation ws_args := (ws_args (V:=V) (A:=term)).

  (* TODO: make sure term_subst_lookup doesn't appear in goals *)
  Lemma term_subst_lookup_to_subst_lookup n s
    : term_subst_lookup s n = subst_lookup s n.
  Proof. reflexivity. Qed.
  
  Lemma subst_lookup_hd n e s : (subst_lookup ((n, e) :: s) n) = e.
  Proof.
    unfold subst_lookup; simpl.
    basic_utils_crush.
  Qed.

  Lemma subst_lookup_tl n m e s
    : m <> n -> subst_lookup ((n, e) :: s) m = subst_lookup s m.
  Proof.
    unfold subst_lookup; simpl.
    intros.
    basic_utils_crush.
  Qed.

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
  
#[local] Hint Rewrite id_args_nil : term.  
#[local] Hint Rewrite id_args_cons : term.

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
  case_match; symmetry in case_match_eqn;
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

  
  Lemma subst_var : forall s x, apply_subst0 s (inj_var x) = subst_lookup s x.
  Proof.
    intros.
    simpl.
    unfold subst_lookup.
    eapply Eqb_unique_named_list_lookup;
      typeclasses eauto.
  Qed.    

  Lemma subst_var_internal
     : forall (s : named_list term) (x : V),
         named_list_lookup_prop (inj_var x) s x (apply_subst0 s (inj_var x)).
  Proof.
    intros.
    rewrite named_list_lookup_prop_correct.
    rewrite subst_var.
    reflexivity.
  Qed.
      
  #[export] Instance substable_term_ok : Substable0_ok term :=
    {
      subst_var_internal := subst_var_internal;
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

  Lemma sort_subst_nil (t:sort) : t[/[]/] = t.
  Proof using .  
    induction t; basic_goal_prep; basic_utils_crush.
    f_equal.
    induction l; basic_goal_prep; basic_utils_crush.
    apply term_subst_nil.
  Qed.
  #[local] Hint Rewrite sort_subst_nil : term.

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

Context `{DecidableEq V}.
Fixpoint term_eq_dec (e1 e2 : term) {struct e1} : {e1 = e2} + {~ e1 = e2}.
  refine(match e1, e2 with
         | var x, var y => SB! dec x y
         | con n s, con n' s' =>
           SB! (dec n n') SB& (list_eq_dec term_eq_dec s s')
         | _, _ => right _
         end); basic_term_crush.
Defined.


Definition sort_eq_dec (e1 e2 : sort) : {e1 = e2} + {~ e1 = e2}.
  refine(match e1, e2 with
         | scon n s, scon n' s' =>
           SB! (dec n n') SB& (list_eq_dec term_eq_dec s s')
         end); basic_term_crush.
Defined.

Definition ctx_eq_dec := list_eq_dec (pair_eq_dec dec sort_eq_dec).

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

#[export] Hint Rewrite id_args_nil : term.
#[export] Hint Rewrite id_args_cons : term.
#[export] Hint Rewrite invert_eq_con_con : inversion.
#[export] Hint Rewrite invert_eq_con_var : inversion.
#[export] Hint Rewrite invert_eq_var_con : inversion.
#[export] Hint Rewrite invert_eq_var_var : inversion.
#[export] Hint Rewrite invert_eq_scon_scon : inversion.
#[export] Hint Rewrite term_subst_nil : term.
#[export] Hint Rewrite named_map_subst_nil : term.
#[export] Hint Rewrite subst_lookup_map : term.
#[export] Hint Rewrite subst_lookup_hd : term.
#[export] Hint Rewrite term_subst_lookup_to_subst_lookup : term.
#[export] Hint Rewrite term_subst_assoc : term.
#[export] Hint Rewrite subst_lookup_id : term.
#[export] Hint Rewrite term_subst_id : term.
#[export] Hint Resolve ws_term_subst_lookup : term.
#[export] Hint Resolve well_scoped_change_args : term.

#[export] Hint Rewrite sort_subst_nil : term.

#[export] Existing Instance substable_term.
#[export] Existing Instance substable_term_ok.                   
#[export] Existing Instance substable_sort.
#[export] Existing Instance substable_args.
#[export] Existing Instance substable_subst.
  
#[export] Existing Instance term_default.
#[export] Existing Instance sort_default.


Notation ctx V := (@named_list V (sort V)).

Notation subst V := (@named_list V (term V)).


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

  (*TODO: still including string scope here for convenience.
    Is there a way to parameterize that?
   *)
  Notation "# c" :=
    (con c%string [])
      (right associativity,in custom arg at level 0, c constr at level 0,
                              format "# c").
  Notation "( e )" := e (in custom arg at level 0, e custom term at level 100, 
           format "'[' ( e ) ']'").

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


Goal False.
  pose {{e #"foo" }}.
  pose {{e #"foo" (#"bar" "x") #"baz" "y"}}.
  pose {{s #"foo" }}.
  pose {{s #"foo" (#"bar" "x") #"baz" "y"}}.
Abort.
                               
  Bind Scope ctx_scope with ctx.

  Notation "'{{c' }}" :=
    nil
      (at level 0, format "'[' '{{c'  '}}' ']'", only parsing)
    : ctx_scope.
  Notation "'{{c' bd , .. , bd' '}}'" :=
    (cons bd' .. (cons bd nil)..)
      (at level 0, bd custom ctx_binding at level 100,
          format "'[' {{c  '[hv' bd ,  '/' .. ,  '/' bd' ']' }} ']'", only parsing) : ctx_scope.

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

  Goal False.
    epose (as_ctx {{c }}).
    epose (as_ctx {{c "x" : #"env"}}).
    epose (as_ctx {{c "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"}}).
  Abort.
  
  (* Used to print arguments in the order they appear in a term *)
  Definition argument_seq_marker {V} (s : list (term V)) := s.
  
  Notation "al" :=
    (argument_seq_marker al)
      (at level 0,
        al custom arg_list,
        only printing).

End Notations.

