Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool String List.
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


Ltac break :=
  repeat match goal with
         | [H: unit|-_]=> destruct H
         | [H: _*_|-_]=> destruct H
         | [H: _/\_|-_]=> destruct H
         | [H: exists x, _|-_]=> destruct H
         end.


Ltac my_case eqnname exp :=
  let casevar := fresh "casevar" in
  remember exp as casevar eqn:eqnname;
  destruct casevar; symmetry in eqnname.


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
  repeat (intuition break; subst; rewrite_tac;
          (*TODO: is this the best place for this?*)
          try typeclasses eauto;
          intuition unshelve hint_auto).
(* Uses firstorder, which can have strange edge cases
   and interacts poorly with terms
 *)
Ltac generic_firstorder_crush rewrite_tac hint_auto :=
  repeat (intuition break; subst; rewrite_tac;
          (*TODO: is this the best place for this?*)
          try typeclasses eauto;
          firstorder unshelve hint_auto).
(*try (solve [ repeat (unshelve f_equal; hint_auto)])). *)

#[export] Hint Extern 100 => exfalso : utils.
#[export] Hint Extern 100 (_ _ = _ _) => f_equal : utils.

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


Ltac basic_utils_crush := let x := autorewrite with utils in * in
                                  let y := eauto with utils in
                                          generic_crush x y.
Ltac basic_utils_firstorder_crush :=
  let x := autorewrite with utils in * in
          let y := eauto with utils in
                  generic_firstorder_crush x y.

Ltac basic_goal_prep := intros; break; simpl in *.


#[export] Hint Resolve in_nil : utils.
#[export] Hint Resolve in_eq : utils.
#[export] Hint Resolve in_cons : utils.

Inductive len_eq {A} {B} : list A -> list B -> Type :=
| len_eq_nil : len_eq [] []
| len_eq_cons : forall a a' l l',
    len_eq l l' -> len_eq (a::l) (a'::l').

Hint Rewrite pair_equal_spec : utils.

Lemma pair_fst_in {N A} l (n: N) (a : A)
  : In (n,a) l -> In n (map fst l).
Proof using.
  induction l; break; simpl; autorewrite with utils; firstorder eauto.
Qed.
#[export] Hint Resolve pair_fst_in : utils.


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

Lemma invert_false_true : false = true <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_false_true : utils.

Lemma invert_eq_0_S x : 0 = S x <-> False.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_eq_0_S : utils.
Lemma invert_eq_S_0 x : S x = 0 <-> False.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_eq_S_0 : utils.

Lemma invert_eq_S_S x y : S x = S y <-> x = y.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_eq_S_S : utils.


Lemma invert_eq_cons_nil A (e:A) es : e::es = [] <-> False.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_eq_cons_nil : utils.
Lemma invert_eq_nil_cons A (e:A) es : [] =e::es <-> False.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_eq_nil_cons : utils.
Lemma invert_eq_cons_cons A (e e':A) es es' : e::es = e'::es' <-> e = e' /\ es = es'.
Proof.
  solve_invert_constr_eq_lemma.
Qed.
Hint Rewrite invert_eq_cons_cons : utils.

(*TODO: does this exist somewhere I can use?
  TODO: include minimum necessary to prove the given properties
*) 
Class Eqb (A : Type) :=
  {
  eqb : A -> A -> bool;
  eqb_eq : forall n m : A, eqb n m = true <-> n = m;
  eqb_neq : forall x y : A, (eqb x y) = false <-> x <> y;
  eqb_refl : forall x : A, (eqb x x) = true;
  Eqb_dec : forall (s1 s2 : A), {s1 = s2} + {s1 <> s2}
  }.
#[export] Hint Rewrite @eqb_eq : utils.
#[export] Hint Rewrite @eqb_neq : utils.
#[export] Hint Rewrite @eqb_refl : utils.

#[export] Instance string_Eqb : Eqb string :=
  {|
  eqb := String.eqb;
  eqb_eq := String.eqb_eq;
  eqb_neq := String.eqb_neq;
  eqb_refl := String.eqb_refl;
  Eqb_dec := string_dec
  |}.

(* Not defined as a record so that firstorder doesn't mess with it*)
Definition WithDefault (A : Type) := A.
Definition default {A} {d : WithDefault A} : A := d.
Existing Class WithDefault.


#[export] Instance option_default {A} : WithDefault (option A) := None.
#[export] Instance string_default : WithDefault string := "".
(* TODO: is this bad practice? *)
Hint Extern 10 (WithDefault _) => solve [typeclasses eauto].

                   
Definition unwrap_with_default {A} (default : A) ma :=
  match ma with None => default | Some a => a end.
                   
(* TODO: separate file? *)
Section NamedList.
  Context {S : Type}
          `{Eqb S}.

Polymorphic Definition named_list (A : Type) :=list (S * A).

Fixpoint named_list_lookup {A} default (l : named_list A) (s : S) : A :=
  match l with
  | [] => default
  | (s', v)::l' =>
    if eqb s s' then v else named_list_lookup default l' s
  end.



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

Lemma fresh_nil A n : fresh n (@nil (_*A)%type) <-> True.
Proof.
  unfold fresh; firstorder eauto.
Qed.

Fixpoint all_fresh {A} (l : named_list A) :=
  match l with
  | [] => True
  | (n,_)::l' => fresh n l' /\ all_fresh l'
  end.
Arguments all_fresh {_} !_ /.


Lemma named_map_fst_eq {A B} (f : A -> B) l
  : map fst (named_map f l) = map fst l.
Proof using .
  induction l; intros; break; simpl in *; f_equal; eauto.
Qed.


Fixpoint named_list_lookup_err {A} (l : named_list A) s : option A :=
  match l with
  | [] => None
  | (s', v) :: l' => if eqb s s' then Some v else named_list_lookup_err l' s
  end.


Lemma named_list_lookup_err_in {A} c n (t : A)
  : Some t = named_list_lookup_err c n -> In (n,t) c.
Proof using .
  induction c; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (eqb n s); basic_utils_crush.
Qed.

Lemma all_fresh_named_list_lookup_err_in A c n (t : A)
  : all_fresh c -> Some t = named_list_lookup_err c n <-> In (n,t) c.
Proof using .
  induction c; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (eqb n s); basic_utils_crush.  
Qed.

Lemma fresh_named_map A B l (f : A -> B) n
  : fresh n (named_map f l) <-> fresh n l.
Proof using .
  clear H.
  induction l; basic_goal_prep;
    basic_utils_firstorder_crush.
Qed.

Fixpoint with_names_from {A B} (c : named_list A) (l : list B) : named_list B :=
  match c, l with
  | [],_ => []
  | _,[] => []
  | (n,_)::c',e::l' =>
    (n,e)::(with_names_from c' l')
  end.


Lemma map_fst_with_names_from A B (c : named_list A) (l : list B)
  : length c = length l -> map fst (with_names_from c l) = map fst c.
Proof.
  revert l; induction c; destruct l; basic_goal_prep; basic_utils_crush.
Qed.


Lemma named_list_lookup_none {A} l s (a:A)
  : None = named_list_lookup_err l s ->
    ~ In (s, a) l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
  my_case Hs (eqb s s0); basic_goal_prep; basic_utils_crush.
Qed.


Lemma in_named_map A B (f : A -> B) l n x
  : In (n,x) l -> In (n, f x) (named_map f l).
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.


Lemma in_all_fresh_same {A} (a b : A) l s
  : all_fresh l -> In (s,a) l -> In (s,b) l -> a = b.
Proof.  
  induction l; basic_goal_prep; basic_utils_crush.
Qed.

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
  induction l; basic_goal_prep;
  basic_utils_crush.
Qed.

Lemma all_fresh_in_once {A} n (e : A) l
  : all_fresh l -> (In (n,e) l) <-> in_once n e l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.  



Lemma with_names_from_map_is_named_map A B C (f : A -> B) (l1 : named_list C) l2
  : with_names_from l1 (map f l2) = named_map f (with_names_from l1 l2).
Proof.
  revert l2; induction l1;
    destruct l2; break; subst; simpl; f_equal; eauto.
Qed.
(* TODO: do I want to rewrite like this?
  Hint Rewrite with_names_from_map_is_named_map : utils.*)

Lemma combine_map_fst_is_with_names_from A B (c : named_list A) (s : list B)
  : combine (map fst c) s = with_names_from c s.
Proof.
  revert s; induction c; destruct s;
    basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma named_map_length A B (f : A -> B) l
  : length (named_map f l) = length l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.


Lemma fresh_notin A n (a:A) l
  : fresh n l -> ~In (n,a) l.
Proof.
  unfold fresh.
  intuition eauto using pair_fst_in.
Qed.


Definition fresh_dec {A} x (l : named_list A) : {fresh x l} + {~ fresh x l}.
  refine(if in_dec Eqb_dec x (map fst l) then right _ else left _);
    basic_utils_crush.
Defined.

Definition compute_fresh {A} x (l : named_list A)  :=
  if fresh_dec x l then true else false.

Lemma use_compute_fresh {A} x (l : named_list A) 
  : compute_fresh x l = true -> fresh x l.
Proof.
  unfold compute_fresh.
  destruct (fresh_dec x l); easy.
Qed.


Lemma fresh_app A s (l1 l2 : named_list A)
  : fresh s (l1 ++ l2) <-> fresh s l1 /\ fresh s l2.
Proof.
  induction l1; basic_goal_prep; basic_utils_firstorder_crush.
Qed.


#[local] Hint Resolve fresh_notin : utils.
#[local] Hint Rewrite fresh_app : utils.
#[local] Hint Rewrite in_app_iff : utils.
Lemma all_fresh_insert_is_fresh A (a:A) l1 l2 s
  : all_fresh (l1++(s,a)::l2) ->
    fresh s l1.
Proof.
  induction l1; basic_goal_prep;
  basic_utils_firstorder_crush.  
Qed.
Local Hint Resolve all_fresh_insert_is_fresh : utils.

Lemma all_fresh_insert_rest_is_fresh A (a:A) l1 l2 s
  : all_fresh (l1++(s,a)::l2) ->
    all_fresh (l1++l2).
Proof.
  induction l1; basic_goal_prep; basic_utils_firstorder_crush.
Qed.


Fixpoint compute_all_fresh {A} (l : named_list A) : bool :=
  match l with
  | [] => true
  | (x,_)::l' => (compute_fresh x l') && (compute_all_fresh l')
  end.
#[local] Hint Rewrite Bool.andb_true_iff : utils.

Lemma use_compute_all_fresh A (l : named_list A)
  : compute_all_fresh l = true -> all_fresh l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
  apply use_compute_fresh; eauto.
Qed.


(* TODO: shouldn't be needed if I flip order equations reliably
   TODO: should be in a different location
*)
Lemma eqb_eq' n m : true = (eqb n m) <-> n = m.
Proof.
  rewrite <- eqb_eq; intuition.
Qed.

End NamedList.

#[export] Hint Rewrite @fresh_cons : utils.
#[export] Hint Rewrite @fresh_named_map : utils.
#[export] Hint Rewrite @map_fst_with_names_from : utils.
(*Note: this is a bit dangerous since the list might not be all-fresh,
  but in this project all lists should be
*)
#[export] Hint Rewrite @all_fresh_named_list_lookup_err_in : utils.
#[export] Hint Resolve @named_list_lookup_none : utils.
#[export] Hint Resolve @in_named_map : utils.
#[export] Hint Rewrite @combine_map_fst_is_with_names_from : utils.
#[export] Hint Rewrite @named_map_length : utils.
#[export] Hint Rewrite map_length : utils.
#[export] Hint Resolve @fresh_notin : utils.
#[export] Hint Rewrite @fresh_app : utils.
#[export] Hint Rewrite in_app_iff : utils.
#[export] Hint Resolve @all_fresh_insert_rest_is_fresh : utils.
#[export] Hint Rewrite Bool.andb_true_iff : utils.
#[export] Hint Rewrite @eqb_eq' : utils.

(*
TODO: remove once the project builds without it

(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry monadic_do.

Module OptionMonad.
  (* TODO: use general monad instead of duplicating*)
  
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

  Section Mmap.
    Context  {A B} (f : A -> option B).
    Fixpoint Mmap (l_a : list A) : option (list B) :=
      match l_a with
      | [] => do ret []
               | a::l_a' =>
                 do l_b' <- Mmap l_a';
                 b <- f a;
              ret (b::l_b')
      end.
  End Mmap.
End OptionMonad.
*)




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
#[export] Hint Resolve sublist_cons_rest : utils.

Lemma sublist_cons_first {A} (a:A) l1 l2
  : sublist (a::l1) l2 -> In a l2.
Proof using.
  induction l2; basic_goal_prep; basic_utils_crush.
Qed.
#[export] Hint Resolve sublist_cons_first : utils.

(*TODO: better as a rewrite?*)
Lemma sublist_refl {A} l : @sublist A l l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
#[export] Hint Resolve sublist_refl : utils.
  
Lemma sublist_l_cons_l {A} (a:A) l
  : sublist l (a::l).
Proof.
  simpl.
  destruct l;
  basic_utils_crush.
Qed.
#[export] Hint Resolve sublist_l_cons_l : utils.

(*TODO: redefine as skipn?*)
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


(*redefined to use the right concatenation*)
Definition flat_map {A B} (f : A -> list B) :=
  fix flat_map l :=
  match l with
  | [] => []
  | x :: t => (f x ++ flat_map t)
  end.

Section All.
  Context {A} (P : A -> Prop).
  
  (* A Fixpoint version of List.Forall *)
  Fixpoint all l : Prop :=
    match l with
    | [] => True
    | e::l' => P e /\ all l'
    end.
End All.

Lemma in_all {A} {P : A -> Prop} l a
  : all P l -> In a l -> P a.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.

Hint Rewrite pair_equal_spec : utils.



Lemma sublist_nil A (l : list A) : sublist [] l.
Proof.
  destruct l; simpl; easy.
Qed.
#[export] Hint Resolve sublist_nil : utils.

Fixpoint compute_sublist {A} (dec : forall x y : A, {x = y} + {x <> y}) (s l : list A) {struct l} :=
  match s,l with
  | [],_ => true
  | sa::s', [] => false
  | sa::s', la::l' => if dec sa la then compute_sublist dec s' l' else compute_sublist dec s l'
  end.

Lemma use_compute_sublist {A} (dec : forall x y : A, {x = y} + {x <> y}) (s l : list A)
  : compute_sublist dec s l = true -> sublist s l.
Proof.
  revert s; induction l; destruct s; basic_goal_prep; try easy.
  revert H. case_match; basic_utils_crush.
Qed.

Lemma as_nth_tail: forall (A : Type) (l : list A), l = nth_tail 0 l.
Proof.
  intros; unfold nth_tail; reflexivity.
Qed.

Definition set_eq {A} (l1 l2 : list A) :=
  incl l1 l2 /\ incl l2 l1.


Lemma incl_nil A  (l : list A)
  : incl l [] <-> l = [].
Proof.
  split; intros; subst;
    eauto using incl_l_nil,
    incl_nil_l.
Qed.  
Hint Rewrite incl_nil : utils.

Lemma incl_cons A (a:A) l1 l2
  : incl (a::l1) l2 <-> In a l2 /\ incl l1 l2.
Proof.
  split; intros; break; eauto using incl_cons, incl_cons_inv.
Qed.
Hint Rewrite incl_cons : utils.

Lemma nth_tail_to_cons A l n (x:A)
  : nth_error l n = Some x ->
    nth_tail n l = x::(nth_tail (S n) l).
Proof.
  revert l; induction n; destruct l;
    basic_goal_prep; basic_utils_crush.
Qed.

Lemma nth_tail_equals_cons_res A n l l' (x:A)
  : nth_tail n l = x :: l' -> l' = nth_tail (S n) l.
Proof.
  revert l l'; induction n; destruct l;
    basic_goal_prep; basic_utils_crush.
  cbv in H; inversion H; subst.
  reflexivity.
Qed.
  

Lemma nth_error_nil A n : @nth_error A [] n = None.
Proof.
  destruct n; simpl; auto.
Qed.
Hint Rewrite nth_error_nil : utils.


#[export] Hint Resolve incl_appr : utils.
#[export] Hint Resolve incl_refl : utils.
#[export] Hint Resolve incl_app : utils.
#[export] Hint Resolve incl_appl : utils.
#[export] Hint Resolve incl_tl : utils.


Module SumboolNotations.
  Notation "SB! e" :=
    (if e then left _ else right _)
      (at level 90).
  Notation "e1 'SB&' e2" :=
    (Sumbool.sumbool_and _ _ _ _ e1 e2)
      (at level 58, left associativity).
End SumboolNotations.
Import SumboolNotations.

Definition pair_eq_dec {A B}
           (A_eq_dec : forall s1 s2 : A, {s1 = s2} + {s1 <> s2})
           (B_eq_dec : forall s1 s2 : B, {s1 = s2} + {s1 <> s2})
           (p1 p2 : A*B)
  : {p1 = p2} + {~p1 = p2}.
  refine (match p1, p2 with
          | (a1,b1),(a2,b2) =>
            SB! (A_eq_dec a1 a2) SB& (B_eq_dec b1 b2)
          end); basic_utils_crush.
Defined.

Fixpoint incl_dec {A} (eq_dec : forall s1 s2 : A, {s1 = s2} + {s1 <> s2})
         (l1 l2 : list A) {struct l1} : {incl l1 l2} + {~ incl l1 l2}.
  refine(match l1 with
         | [] => left _
         | a::l1' =>
           SB! (in_dec eq_dec a l2) SB& (incl_dec _ _ l1' l2)
         end); basic_utils_firstorder_crush.
Defined.


#[export] Hint Rewrite app_nil_r : utils.
