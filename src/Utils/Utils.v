Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List Bool String.
Import ListNotations.
Import BoolNotations.
Open Scope string.
Open Scope list.

(***************
 Tactics 
****************)

Tactic Notation "intro_to" constr(ty) :=
  repeat match goal with
         | |- ty -> _ => idtac
         | |- ty _ -> _ => idtac
         | |- ty _ _-> _ => idtac
         | |- ty _ _ _ -> _ => idtac
         | |- ty _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ _ -> _ => idtac
         | |- _ -> _ => intro
         | |- _ => fail 2 "could not find argument with head" ty
         end.


(* Performs inversion on H exactly when 
    either: 
    - no constructors can produce H and the goal is solved
    - exactly one constructor can produce H and inversion
      makes progress
 *)
Ltac safe_invert H :=
  let t := type of H in
  inversion H; clear H;
  let n := numgoals in
  guard n <= 1;
  lazymatch goal with
  | [ H' : t|-_]=>
    fail "safe_invert did not make progress"
  | _ => subst
  end.

Ltac solve_invert_constr_eq_lemma :=
   match goal with
    [|- ?lhs <-> _] =>
    firstorder (match goal with
                    | [H : lhs |-_] => inversion H; subst; easy
                    | _ => solve[ subst;constructor; assumption | f_equal; assumption]
                    end)
   end.


Ltac generic_crush rewrite_tac hint_auto :=
  subst; rewrite_tac;
  firstorder (subst; rewrite_tac;hint_auto;
              try (solve [ exfalso; hint_auto
                         | repeat (f_equal; hint_auto)])).

(*TODO: generalize this to something that works nicely for generic_crush
Tactic Notation "text" ident(u) := eauto with u.
 *)

(****************
Definitions
*****************)

(* grouped right with the fixpoint for better decreasing argument analysis*)
Definition all2 := 
fun (S T : Type) (r : S -> T -> bool) =>
fix all2 (s : list S) (t : list T) {struct s} : bool :=
  match s, t with
  | [], [] => true
  | x :: s0, y::t0 => r x y && all2 s0 t0
  | _,_ => false
  end.



Definition named_list_set (A : Set) :=list (string * A).
Definition named_list (A : Type) :=list (string * A).

Fixpoint named_list_lookup {A} default (l : named_list A) (s : string) : A :=
  match l with
  | [] => default
  | (s', v)::l' =>
    if eqb s s' then v else named_list_lookup default l' s
  end.

Lemma eqb_eq' n m : true = (n =? m) <-> n = m.
Proof.
  rewrite <- eqb_eq; intuition.
Qed.
Hint Rewrite eqb_eq' : utils.

Hint Resolve in_nil : utils.
Hint Resolve in_eq : utils.
Hint Resolve in_cons : utils.

Inductive len_eq {A} {B} : list A -> list B -> Type :=
| len_eq_nil : len_eq [] []
| len_eq_cons : forall a a' l l',
    len_eq l l' -> len_eq (a::l) (a'::l').

Definition pair_map_snd {A B C} (f : B -> C) (p : A * B) :=
  let (a,b) := p in (a, f b).
Arguments pair_map_snd {A B C} f !p/.

Definition named_map {A B} (f : A -> B) : named_list A -> named_list B
  := map (pair_map_snd f).
Arguments named_map {A B} f !l/.

Definition fresh {A} n (nl : named_list A) : Prop :=
  ~ List.In n (map fst nl).
Arguments fresh : simpl never.

(* These two lemmas should totally define fresh *)
Lemma fresh_cons A n m (e:A) es : fresh n ((m,e)::es) <-> ~ n = m /\ fresh n es.
Proof.
  unfold fresh.
  firstorder eauto.
Qed.
Hint Rewrite fresh_cons : utils.

Lemma fresh_nil A n : fresh n (@nil (_*A)%type) <-> True.
Proof.
  unfold fresh; firstorder eauto.
Qed.

(*
Lemma fresh_tail {A} n (l1 l2 : named_list A)
  : fresh n (l1 ++ l2) -> fresh n l2.
Proof using .
  elim: l1; simpl; auto.
  intros a l.
  unfold fresh; simpl; intro IH.
  rewrite !in_cons.
  move /norP => [_] //.
Qed.

Lemma fresh_neq_in {A : eqType} n l n' (t : A)
  : fresh n l -> (n',t) \in l -> ~~ (n'==n).
Proof using .
  elim: l; unfold fresh; simpl.
  by cbv.
  move => [n1 t1] l IH.
  rewrite !in_cons.
  move /norP => //= [nn1 nnl].
  move /orP; case; eauto.
  {
    move /eqP.
    case.
    move -> => _.
    
    apply /negP.
    move /eqP.
    move: nn1=> /eqP.
    intros nnneq nneq.
    apply nnneq.
    by symmetry.
  }
Qed.

Lemma fresh_neq_in_fst {A : eqType} n (l : named_list A) n'
  : fresh n l -> n' \in (map fst l) -> ~~ (n'==n).
Proof using .
  elim: l; unfold fresh; simpl.
  by cbv.
  move => [n1 t1] l IH.
  rewrite !in_cons.
  move /norP => //= [nn1 nnl].
  move /orP; case; eauto.
  {
    move /eqP.
    case.
    move ->.
    
    apply /negP.
    move /eqP.
    move: nn1=> /eqP.
    intros nnneq nneq.
    apply nnneq.
    by symmetry.
  }
Qed.
 *)

(*
Fixpoint all_notin (l : list string) : Prop :=
  match l with
  | [] => True
  | n::l' => (~ List.In n l') /\ all_notin l'
  end.
*)

Fixpoint all_fresh {A} (l : named_list A) :=
  match l with
  | [] => True
  | (n,_)::l' => fresh n l' /\ all_fresh l'
  end.
Arguments all_fresh {_} !_ /.

Ltac break :=
  repeat match goal with
         | [H: unit|-_]=> destruct H
         | [H: _*_|-_]=> destruct H
         | [H: _/\_|-_]=> destruct H
         end.


Hint Rewrite pair_equal_spec : utils.

Lemma pair_fst_in {N A} l (n: N) (a : A)
  : In (n,a) l -> In n (map fst l).
Proof using.
  induction l; break; simpl; autorewrite with utils; firstorder eauto.
Qed.
Hint Resolve pair_fst_in : utils.

Lemma named_map_fst_eq {A B} (f : A -> B) l
  : map fst (named_map f l) = map fst l.
Proof using .
  induction l; intros; break; simpl in *; f_equal; eauto.
Qed.

(*
Lemma in_map_snd {A B : eqType} e (l : list (A*B))
  : e \in (map snd l) -> exists n, (n,e) \in l.
Proof using .
  elim: l; simpl; [ by inversion|];
    intros; break; simpl in *.
  move: H0; rewrite in_cons; move /orP; case.
  {
    move => /eqP ->.
    exists s.
    rewrite in_cons.
    apply /orP; left; apply eq_refl.
  }
  {
    move /H.
    case.
    intros.
    exists x.
    rewrite in_cons; apply /orP; right; done.
  }
Qed.
*)

(*
Module OptionMonad.
  (* TODO: use general monad instead of duplicating*)
  Declare Custom Entry monadic_do.
  
  Notation "'do' e" := (e) (at level 92, e custom monadic_do).

  Notation "p <- e ; b" :=
    (match e with
     | Some (p) => b
     | _ => None
     end)
      (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).

  Notation "'ret' e" := (Some e) (in custom monadic_do at level 90, e constr).
  
  Notation "'let' p := e ; b" :=
    (let p := e in b)
      (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).

  Notation "! e ; b" :=
    (if e then b else None)
      (in custom monadic_do at level 90, left associativity, e constr, b custom monadic_do).
End OptionMonad.
*)

Fixpoint named_list_lookup_err {A} (l : named_list A) s : option A :=
  match l with
  | [] => None
  | (s', v) :: l' => if (s =? s')%string then Some v else named_list_lookup_err l' s
  end.

Ltac case_match :=match goal with
  | [|- context[match ?e with _ => _ end]]
    => let e':= fresh in remember e as e'; destruct e'
  end.

Lemma invert_none_some A (x:A)
  : None = Some x <-> False.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_none_some : utils.

Lemma invert_some_none A (x:A)
  : Some x = None <-> False.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_some_none : utils.
Lemma invert_some_some A (x y:A)
  : Some x = Some y <-> x = y.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_some_some : utils.

Ltac my_case eqnname exp :=
  let casevar := fresh "casevar" in
  remember exp as casevar eqn:eqnname;
  destruct casevar; symmetry in eqnname.

Hint Rewrite eqb_eq : utils.
Hint Rewrite eqb_neq : utils.
Hint Rewrite eqb_refl : utils.

Ltac basic_utils_crush := let x := autorewrite with utils in * in
                                  let y := eauto with utils in
                                          generic_crush x y.

Ltac basic_goal_prep := intros; break; simpl in *.

Lemma named_list_lookup_err_in {A} c n (t : A)
  : Some t = named_list_lookup_err c n -> In (n,t) c.
Proof using .
  induction c; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (n =? s); basic_utils_crush.
Qed.

Lemma all_fresh_named_list_lookup_err_in A c n (t : A)
  : all_fresh c -> Some t = named_list_lookup_err c n <-> In (n,t) c.
Proof using .
  induction c; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (n =? s); basic_utils_crush.  
Qed.
(*Note: this is a bit dangerous since the list might not be all-fresh,
  but in this project all lists should be
*)
Hint Rewrite all_fresh_named_list_lookup_err_in : utils.

Fixpoint with_names_from {A B} (c : named_list A) (l : list B) : named_list B :=
  match c, l with
  | [],_ => []
  | _,[] => []
  | (n,_)::c',e::l' =>
    (n,e)::(with_names_from c' l')
  end.

Fixpoint sublist {A} (s l : list A) : Prop :=
  match s,l with
  | [],_ => True
  | sa::s', [] => False
  | sa::s', la::l' =>
    ((sa = la) /\ (sublist s' l')) \/ (sublist s l')
  end.

Lemma sublist_cons_rest {A} (a:A) l1 l2
  : sublist (a::l1) l2 -> sublist l1 l2.
Proof using.
  induction l2; destruct l1; basic_goal_prep; basic_utils_crush.
Qed.
Hint Resolve sublist_cons_rest : utils.

Lemma sublist_cons_first {A} (a:A) l1 l2
  : sublist (a::l1) l2 -> In a l2.
Proof using.
  induction l2; basic_goal_prep; basic_utils_crush.
Qed.
Hint Resolve sublist_cons_first : utils.

(*TODO: better as a rewrite?*)
Lemma sublist_refl {A} l : @sublist A l l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Resolve sublist_refl : utils.
  
Lemma sublist_l_cons_l {A} (a:A) l
  : sublist l (a::l).
Proof.
  simpl.
  destruct l;
  basic_utils_crush.
Qed.
Hint Resolve sublist_l_cons_l : utils.

(* Reduce size of language terms for smaller goals *)
Fixpoint nth_tail {A} (n: nat) (l : list A) : list A :=
  match n,l with
  | 0,_ => l
  | S_,[]=> []
  | S n', _::l'=> nth_tail n' l'
  end.

Arguments nth_tail : simpl never.

Lemma nth_tail_nil A n : @nth_tail A n [] = [].
Proof.
  destruct n; simpl; reflexivity.
Qed.
Hint Rewrite nth_tail_nil : utils.

Lemma nth_tail_S_cons A n (e:A) l : nth_tail (S n) (e::l) = nth_tail n l.
Proof.
  reflexivity.
Qed.
Hint Rewrite nth_tail_S_cons : utils.

(*
Lemma nth_tail_cons_eq {A} (a:A) l n l'
  : a::l = nth_tail n l' -> l = nth_tail n.+1 l'.
Proof.
  revert a l l'.
  induction n.
  {
    intros; destruct l';
      cbv[nth_tail] in*;
      inversion H; auto.
  }
  {
    intros; destruct l'.
    {
      cbv[nth_tail] in*;
        inversion H; auto.
    }
    {
      rewrite nth_tail_S_cons.
      rewrite nth_tail_S_cons in H.
      eauto.
    }
  }
Qed.
*)

(*
Lemma nth_tail_0 {A} (l : list A) : nth_tail 0 l = l.
Proof. reflexivity. Qed.

      
Lemma nth_tail_show_hd {A} (default:A) n l
  : size l > n ->
    nth_tail n l = (nth default l n) ::(nth_tail (S n) l).
Proof.
  elim: n l; intros.
  {
    destruct l; simpl in *; inversion H.
    rewrite nth_tail_S_cons.
    rewrite !nth_tail_0.
    reflexivity.
  }   
  {
    destruct l; simpl in *; inversion H0.
    clear H2.
    rewrite !nth_tail_S_cons.
    apply H; exact H0.
  }
Qed.    
*)

(*redefined to use the right concatenation*)
Definition flat_map {A B} (f : A -> list B) :=
  fix flat_map l :=
  match l with
  | [] => []
  | x :: t => (f x ++ flat_map t)
  end.

(*
Lemma included_flatmap {A B:eqType} l1 l2 (f : A -> list B)
    : (forall x, x \in l1 -> included (f x) l2)->
      included (flat_map f l1) l2.
Proof.  
  induction l1; simpl; auto.
  intro fall.
  rewrite included_app; eauto.
  apply /andP; split.
  apply fall; apply mem_head.
  apply IHl1; intros.
  apply fall.
  rewrite in_cons.
  apply /orP; right; auto.
Qed.
*)


Lemma in_all_fresh_same {A} (a b : A) l s
  : all_fresh l -> In (s,a) l -> In (s,b) l -> a = b.
Proof.  
  induction l; basic_goal_prep; basic_utils_crush.
Qed.

(*
Lemma named_list_lookup_err_none {A} (l : named_list A) n
  : n \notin (map fst l) ->
    named_list_lookup_err l n = None.
Proof.
  elim: l; simpl; auto.
  intros; break; simpl.
  rewrite in_cons in H0.
  move: H0 => /norP []; simpl; intros.
  apply negbTE in a0;
    change (n =? s = false)%string in a0;
    rewrite a0.
  auto.
Qed.


  
Lemma named_list_lookup_err_inb {A : eqType} l x (v:A)
  : all_fresh l ->
    named_list_lookup_err l x == Some v = ((x,v) \in l).
Proof.
  induction l; break; [by compute | simpl]; intros; break.
  case_match.
  {
    match goal with
      [H : true = (?a =? ?b)%string |-_]=>
      symmetry in H; change (is_true (a == b)) in H;
        move: H => /eqP H; subst
    end.
    case veqs0: (s0 == v).
    {
      move:veqs0 => /eqP veqs0; subst.
      rewrite in_cons.
      rewrite !eq_refl.
      by compute.
    }
    {
      rewrite in_cons.
      cbn.
      rewrite veqs0 eqb_refl.
      rewrite eq_sym in veqs0.
      rewrite veqs0.
      simpl.
      simpl in IHl.
      rewrite <- IHl; auto.
      rewrite named_list_lookup_err_none; auto.
    }
  }
  {
      rewrite in_cons.
      cbn.
      rewrite <- HeqH1.
      cbn.
      auto.
  }
Qed.
*)

Lemma named_list_lookup_none {A} l s (a:A)
  : None = named_list_lookup_err l s ->
    ~ In (s, a) l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
  my_case Hs (s=? s0); basic_goal_prep; basic_utils_crush.
Qed.
Hint Resolve named_list_lookup_none : utils.

(* decomposes the way you want \in to on all_fresh lists*)
Fixpoint in_once {A} n e (l : named_list A) : Prop :=
  match l with
  | [] => False
  | (n',e')::l' =>
    ((n = n') /\ (e = e')) \/ ((~n = n') /\ (in_once n e l'))
  end.

Arguments in_once {A} n e !l/.

Lemma in_once_notin {A} n (e : A) l
  : ~ In n (map fst l) -> ~(in_once n e l).
Proof using .
  induction l; basic_goal_prep; basic_utils_crush.
Qed.


Lemma all_fresh_in_once {A} n (e : A) l
  : all_fresh l -> (In (n,e) l) <-> in_once n e l.
Proof using .
  induction l; basic_goal_prep; basic_utils_crush.
Qed.  

Section All.
  Context {A} (P : A -> Prop).
  
  (* A Fixpoint version of List.Forall *)
  Fixpoint all l : Prop :=
    match l with
    | [] => True
    | e::l' => P e /\ all l'
    end.
End All.

Hint Rewrite pair_equal_spec : utils.
