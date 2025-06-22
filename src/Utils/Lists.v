Set Implicit Arguments.

Require Import Coq.Lists.List. Import ListNotations.
Require Import Bool.
Require Import Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import Coq.Sorting.Permutation.
Require Export Datatypes.List.
Import BoolNotations.
Open Scope list.

From Utils Require Import Base Booleans Eqb Default.

Section __.
  Context (A : Type).
  
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

    
    Lemma all_app l1 l2 : all (l1++l2) <-> all l1 /\ all l2.
    Proof.
      induction l1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

  End All.
  
  Lemma all_wkn l (P Q : A -> Prop)
    : (forall x, In x l -> P x -> Q x) -> all P l -> all Q l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Section All2.
    Context (B : Type) (R : A -> B -> Prop).

    (* A Fixpoint version of List.Forall2 *)
    Fixpoint all2 l1 l2 : Prop :=
      match l1, l2 with
      | [], [] => True
      | [] , _::_ => False
      | _::_, [] => False
      | a::l1', b::l2' => R a b /\ all2 l1' l2'
      end.
    
    Lemma all2_len_False l1 l2
      : List.length l1 <> List.length l2 -> ~ all2 l1 l2.
    Proof using.
      clear.
      revert l2;
        induction l1;
        destruct l2;
        basic_goal_prep; basic_utils_crush.
    Qed.
    
    Lemma all2_app l1 l1' l2 l2'
      : all2 l1 l1' -> all2 l2 l2' -> all2 (l1++l2) (l1'++l2').
    Proof using.
      clear.
      revert l1'.
      induction l1; destruct l1'; basic_goal_prep; basic_utils_crush.
    Qed.
    
  End All2.

  Section All2_AA.
    Context (R : A -> A -> Prop) {R_refl : Reflexive R}.
    
    Lemma all2_refl l : all2 R l l.
    Proof using R_refl.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

    Hint Resolve all2_refl : utils.
    
    Lemma all2_app_shared_tail l1 l1' l
      : all2 R (l1++l) (l1'++l) <-> all2 R l1 l1'.
    Proof using R_refl.
      revert l1'.
      induction l1; destruct l1'; basic_goal_prep; basic_utils_crush.
      {
        eapply all2_len_False; eauto.
        cbn.
        rewrite app_length.
        Lia.lia.
      }
      {
        destruct l; basic_goal_prep; try tauto.
        eapply all2_len_False; eauto.
        cbn.
        rewrite app_length.
        cbn.
        Lia.lia.
      }
      all:apply IHl1 in H1; eauto.
    Qed.
    
    Lemma all2_app_shared_head l1 l1' l
      : all2 R (l++l1) (l++l1') <-> all2 R l1 l1'.
    Proof using R_refl.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Context {R_sym : Symmetric R}.
    
    Lemma all2_Symmetric : Symmetric (all2 R).
    Proof using R_sym.
      intros l1 l2;
        revert l2;
        induction l1; destruct l2;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    

    Context {R_trans : Transitive R}.
    
    Lemma all2_Transitive : Transitive (all2 R).
    Proof using R_trans.
      clear R_sym.
      intros l1 l2 l3;
        revert l2 l3;
        induction l1; destruct l2, l3;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

  End All2_AA.
  
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

  
  #[export] Instance list_default : WithDefault (list A) := [].

  Section Eqb.

    Context `{Eqb_ok A}.
    
    (*TODO: rename Booleans.all2 to allb2*)
    #[export] Instance list_eqb : Eqb (list A) := forallb2 (eqb (A:=A)).

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

    
    Fixpoint inclb (l1 l2 : list A) {struct l1} : bool :=
      match l1 with
      | [] => true
      | a::l1' =>
          (inb a l2) && (inclb l1' l2)
      end.

    
    #[local] Hint Resolve incl_nil_l : utils.
    #[local] Hint Rewrite incl_cons : utils.
    #[local] Hint Rewrite inb_is_In : utils.

    Lemma use_inclb (l1 l2 : list A)
      : Is_true (inclb l1 l2) -> incl l1 l2.
    Proof.
      induction l1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Lemma inclb_spec (l1 l2 : list A)
      : Is_true (inclb l1 l2) <-> incl l1 l2.
    Proof.
      induction l1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Fixpoint no_dupb (l : list A) : bool :=
      match l with
      | [] => true
      | a::l' => (negb (inb a l')) && (no_dupb l')
      end.

    #[local] Hint Constructors NoDup : utils.
    (* TODO: should we use a propositional fixpoint instead of NoDup? *)
    Lemma use_no_dupb l
      : Is_true (no_dupb l) -> NoDup l.
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    (*TODO: should be option? currently returns length if a is not in l*)
    Fixpoint idx_of (a:A) l : nat :=
      match l with
      | [] => 0
      | a'::l =>
          if eqb a a' then 0 else S (idx_of a l)
      end.
    
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

  Lemma Is_true_forallb (f : A -> _) l
    : Is_true (forallb f l) <-> all (fun x => Is_true (f x)) l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (*TODO: move to Permutation.v?*)
  Lemma removeb_perm `{Eqb_ok A} x l
    : In x l -> NoDup l -> Permutation (x :: List.removeb (eqb (A:=A)) x l) l.
  Proof.
    induction l; basic_goal_prep;
      basic_utils_crush.
    {
      apply perm_skip.
      safe_invert H2.
      rewrite removeb_not_In; eauto.
    }
    {
      safe_invert H2.
      eqb_case x a; cbn.
      {
        apply perm_skip.
        rewrite removeb_not_In; eauto.
      }
      {
        etransitivity.
        { apply perm_swap. }
        apply perm_skip.
        eauto.
      }        
    }
  Qed.

  
    #[export] Instance filter_Permutation_Proper (f : A -> bool)
      : Proper (Permutation (A:=A) ==> Permutation (A:=A)) (List.filter f).
    Proof.
      intros l l' Hl.
      induction Hl;
        basic_goal_prep;
        basic_utils_crush.

      { destruct (f x) eqn:Hf; eauto. }
      { destruct (f x) eqn:Hx; destruct (f y) eqn:Hy; eauto using perm_skip, perm_swap. }
      { etransitivity; eauto. }
    Qed.
    
    #[export] Instance removeb_Permutation_Proper (eqb : A -> A -> bool)
      : Proper (eq ==> Permutation (A:=A) ==> Permutation (A:=A)) (List.removeb eqb).
    Proof.
      intros a a' Ha; subst.
      apply filter_Permutation_Proper.
    Qed.

    
    #[export] Instance map_Permutation_Proper B (f : A -> B)
      : Proper (Permutation (A:=A) ==> Permutation (A:=B)) (List.map f).
    Proof.
      intros l l' Hl.
      induction Hl;
        basic_goal_prep;
        basic_utils_crush;
        eauto using perm_skip, perm_swap, perm_trans. 
    Qed.

End __.



Arguments sublist {A}%type_scope (s l)%list_scope.
Arguments all {A}%type_scope P%function_scope l%list_scope.
Arguments set_eq {A}%type_scope (l1 l2)%list_scope.

Arguments sublistb {A}%type_scope {Eqb_A} (s l)%list_scope : rename.

Arguments use_sublistb {A}%type_scope {H H0} (s l)%list_scope _.
Ltac compute_sublist := apply use_sublistb; vm_compute; exact I.


Arguments use_inclb {A}%type_scope {H H0} (l1 l2)%list_scope _ a _.
Ltac compute_incl := apply use_inclb; vm_compute; exact I.

#[export] Hint Rewrite inclb_spec : utils.

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

#[export] Hint Rewrite all_app : utils.


#[export] Hint Rewrite inb_is_In using solve[typeclasses eauto] : utils.

#[export] Hint Rewrite Is_true_forallb : utils.

#[export] Hint Resolve all2_refl : utils.

#[export] Hint Constructors NoDup : utils.
