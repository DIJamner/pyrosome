Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool List.
Import ListNotations.
Import BoolNotations.
Open Scope list.

From Utils Require Import Base Booleans Eqb.

Section __.
  Context (A : Type).

  (* nil_nil not necessary because of reflexivity
  Lemma invert_eq_nil_nil : @nil A = @nil A <-> True.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite invert_eq_nil_nil : utils. *)
  
  Lemma invert_eq_cons_nil (e:A) es : e::es = [] <-> False.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite invert_eq_cons_nil : utils.
  Lemma invert_eq_nil_cons (e:A) es : [] =e::es <-> False.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite invert_eq_nil_cons : utils.
  Lemma invert_eq_cons_cons (e e':A) es es' : e::es = e'::es' <-> e = e' /\ es = es'.
  Proof.
    solve_invert_constr_eq_lemma.
  Qed.
  Hint Rewrite invert_eq_cons_cons : utils.

  
  Fixpoint sublist (s l : list A) : Prop :=
    match s,l with
    | [],_ => True
    | sa::s', [] => False
    | sa::s', la::l' =>
        ((sa = la) /\ (sublist s' l')) \/ (sublist s l')
    end.

  Lemma sublist_cons_rest (a:A) l1 l2
    : sublist (a::l1) l2 -> sublist l1 l2.
  Proof using.
    induction l2; destruct l1; basic_goal_prep; basic_utils_crush.
  Qed.
  Hint Resolve sublist_cons_rest : utils.

  Lemma sublist_cons_first (a:A) l1 l2
    : sublist (a::l1) l2 -> In a l2.
  Proof using.
    induction l2; basic_goal_prep; basic_utils_crush.
  Qed.
  Hint Resolve sublist_cons_first : utils.

  Lemma rewrite_sublist_refl l : sublist l l <-> True.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
  Qed.
  Hint Rewrite rewrite_sublist_refl : utils.
  
  Lemma sublist_refl l : sublist l l.
  Proof.
    basic_utils_crush.
  Qed.
  Hint Resolve sublist_refl : utils.
  
  Lemma sublist_l_cons_l (a:A) l
    : sublist l (a::l).
  Proof.
    simpl.
    destruct l;
      basic_utils_crush.
  Qed.
  Hint Resolve sublist_l_cons_l : utils.

  Lemma rewrite_sublist_nil (l : list A) : sublist [] l <-> True.
  Proof.
    destruct l; simpl; easy.
  Qed.
  Hint Rewrite rewrite_sublist_nil : utils.
  
  Lemma sublist_nil (l : list A) : sublist [] l.
  Proof.
    destruct l; simpl; easy.
  Qed.
  Hint Resolve sublist_nil : utils.

  (*TODO: check if still needed.
    Original note: redefined to use the right concatenation
  Definition flat_map {B} (f : A -> list B) :=
    fix flat_map l :=
      match l with
      | [] => []
      | x :: t => (f x ++ flat_map t)
      end.
   *)

  Section All.
    Context (P : A -> Prop).
    
    (* A Fixpoint version of List.Forall *)
    Fixpoint all l : Prop :=
      match l with
      | [] => True
      | e::l' => P e /\ all l'
      end.
    
    Lemma in_all l a
      : all l -> In a l -> P a.
    Proof.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

  End All.

  
  Definition set_eq (l1 l2 : list A) :=
    incl l1 l2 /\ incl l2 l1.


  Lemma incl_nil (l : list A)
    : incl l [] <-> l = [].
  Proof.
    split; intros; subst;
      eauto using incl_l_nil,
      incl_nil_l.
  Qed.  
  Hint Rewrite incl_nil : utils.

  Lemma incl_cons (a:A) l1 l2
    : incl (a::l1) l2 <-> In a l2 /\ incl l1 l2.
  Proof.
    split; intros; break; eauto using incl_cons, incl_cons_inv.
  Qed.
  Hint Rewrite incl_cons : utils.


  Section Eqb.

    Context `{Eqb_ok A}.
    
    #[export] Instance list_eqb : Eqb (list A) := all2 (eqb (A:=A)).

    #[export] Instance list_eqb_ok : Eqb_ok (list_eqb).
    Proof.
      unfold Eqb_ok;
        unfold eqb.
      induction a;
        destruct b;
        basic_goal_prep;
        basic_utils_crush.
      my_case Ha (eqb a a1);
        basic_goal_prep;
        basic_utils_crush.
      specialize (IHa b).
      case_match;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Definition inb (x : A) := existsb (eqb x).

    Lemma inb_is_In a l
      : Is_true (inb a l) <-> In a l.
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Fixpoint sublistb (s l : list A) : bool :=
      match s,l with
      | [],_ => true
      | sa::s', [] => false
      | sa::s', la::l' =>
          if eqb sa la then sublistb s' l' else sublistb s l'
      end.

    Lemma use_sublistb (s l : list A)
      : Is_true (sublistb s l) -> sublist s l.
    Proof.
      revert s; induction l; destruct s; basic_goal_prep; try easy.
      revert H1. case_match; basic_utils_crush.
    Qed.
    
  End Eqb.

  (*
  (*TODO: remove, replace with the Eqb version *)
  Fixpoint compute_sublist (dec : forall x y : A, {x = y} + {x <> y})
    (s l : list A) {struct l} :=
    match s,l with
    | [],_ => true
    | sa::s', [] => false
    | sa::s', la::l' => if dec sa la
                        then compute_sublist dec s' l'
                        else compute_sublist dec s l'
    end.

  Lemma use_compute_sublist
    (dec : forall x y : A, {x = y} + {x <> y})
    (s l : list A)
    : compute_sublist dec s l = true -> sublist s l.
  Proof.
    revert s; induction l; destruct s; basic_goal_prep; try easy.
    revert H. case_match; basic_utils_crush.
  Qed.
  *)

End __.


Arguments sublist {A}%type_scope (s l)%list_scope.
Arguments all {A}%type_scope P%function_scope l%list_scope.
Arguments set_eq {A}%type_scope (l1 l2)%list_scope.

Arguments sublistb {A}%type_scope {Eqb_A} (s l)%list_scope : rename.

#[export] Hint Rewrite invert_eq_cons_nil : utils.
#[export] Hint Rewrite invert_eq_nil_cons : utils.
#[export] Hint Rewrite invert_eq_cons_cons : utils.


#[export] Hint Resolve in_nil : utils.
#[export] Hint Resolve in_eq : utils.
#[export] Hint Resolve in_cons : utils.

#[export] Hint Rewrite map_length : utils.
#[export] Hint Rewrite in_app_iff : utils.
#[export] Hint Rewrite app_nil_r : utils.

#[export] Hint Resolve sublist_cons_rest : utils.
#[export] Hint Resolve sublist_cons_first : utils.

#[export] Hint Rewrite rewrite_sublist_refl : utils.
#[export] Hint Resolve sublist_refl : utils.

#[export] Hint Resolve sublist_l_cons_l : utils.

#[export] Hint Rewrite rewrite_sublist_nil : utils.
#[export] Hint Resolve sublist_nil : utils.

#[export] Hint Rewrite incl_nil : utils.
#[export] Hint Rewrite incl_cons : utils.

#[export] Hint Resolve incl_appr : utils.
#[export] Hint Resolve incl_refl : utils.
#[export] Hint Resolve incl_app : utils.
#[export] Hint Resolve incl_appl : utils.
#[export] Hint Resolve incl_tl : utils.


#[export] Hint Rewrite inb_is_In using solve[typeclasses eauto] : utils.
