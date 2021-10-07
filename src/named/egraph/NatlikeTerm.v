Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Natlike PersistentArrayList.
From Named Require Term Rule.
Import SumboolNotations.


Module NatlikeTerm (Import NL : Natlike).

  Unset Elimination Schemes.
  Inductive term : Type :=
  (* variable name *)
  | var : t -> term
  (* Rule label, list of subterms*)
  | con : t -> list term -> term.
  Set Elimination Schemes.

  Coercion var : t >-> term.

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

  Variant sort : Type := scon : t -> list term -> sort.

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

  
  (*TODO: generalize named_list to assoc_list*)
  Definition named_list A := list (t * A).

  Fixpoint named_list_lookup {A} default (l : named_list A) (s : t) : A :=
    match l with
    | [] => default
    | (s', v)::l' =>
      if eqb s s' then v else named_list_lookup default l' s
    end.
  
  Fixpoint named_list_lookup_err {A} (l : named_list A) s : option A :=
    match l with
    | [] => None
    | (s', v) :: l' => if eqb s s' then Some v else named_list_lookup_err l' s
    end.

  
  Definition named_map {A B} (f : A -> B) : named_list A -> named_list B
    := map (pair_map_snd f).
  Arguments named_map {A B} f !l/.

  
  Definition ctx : Type := named_list sort.

  Definition subst : Type := named_list term.  

  Definition subst_lookup (s : subst) (n : t) : term :=
    named_list_lookup (var n) s n.

  Arguments subst_lookup !s n/.

  Definition ctx_lookup (c: ctx) (n : t) : sort :=
    named_list_lookup (scon zero []) c n.

  Arguments ctx_lookup !c n/.


  Fixpoint term_var_map (f : t -> term) (e : term) : term :=
    match e with
    | var n => f n
    | con n l => con n (map (term_var_map f) l)
    end.

  Arguments term_var_map f !e /.

  Definition term_subst (s : subst) e : term :=
    term_var_map (subst_lookup s) e.

  Arguments term_subst s !e /.

  Definition subst_cmp s1 s2 : subst := named_map (term_subst s1) s2.
  Arguments subst_cmp s1 s2 /.

  
  Inductive rule : Type :=
  | sort_rule :  ctx -> rule
  | term_rule :  ctx -> sort -> rule
  | sort_eq_rule : ctx -> sort -> sort -> rule
  | term_eq_rule : ctx -> term -> term -> sort -> rule.

  Definition lang := named_list rule.

  Record name_mapping :=
    {
    constr_names : Utils.named_list t;
    var_names : Utils.named_list t;
    }.

  Section Conversions.
    Context (m : name_mapping).

  Fixpoint from_term (e : Term.term) : term :=
    match e with
    | Term.var x => var (Utils.named_list_lookup zero m.(var_names) x)
    | Term.con n s =>
      con (Utils.named_list_lookup zero m.(constr_names) n)
          (map from_term s)
    end.

  (*TODO: to_term needs a right-to-left lookup*)

  End Conversions.

End NatlikeTerm.

Module Int63Term.

  Module M := NatlikeTerm Int63Natlike.

  Export M.
  Import Int63Natlike.

  
  (*TODO make exhaustive*)
  Ltac avoid_int63_bug c :=
    let x := eval cbv delta
                  [Int63Natlike.eqb
                     Int63Natlike.leb
                     Int63Natlike.ltb
                     M.named_list_lookup
                     M.subst_lookup
                     M.term_subst
                     M.subst_cmp
                  ] in c in
        exact x.

  Definition named_list_lookup := ltac:(avoid_int63_bug @named_list_lookup).

  Definition subst_lookup := ltac:(avoid_int63_bug @subst_lookup).
  Arguments subst_lookup !s n/.

  Definition ctx_lookup := ltac:(avoid_int63_bug @ctx_lookup).
  Arguments ctx_lookup !c n/.

  
  Definition term_subst := ltac:(avoid_int63_bug @term_subst).
  Arguments term_subst s !e /.
  
  Definition subst_cmp := ltac:(avoid_int63_bug @subst_cmp).
  Arguments subst_cmp s1 s2 /.

End Int63Term.
