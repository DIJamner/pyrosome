Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool String List.
Import ListNotations.
Import BoolNotations.
Open Scope string.
Open Scope list.

From Utils Require Export Base Booleans Props Eqb Lists Default.

(****************
Definitions
*****************)



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



(*TODO: move to standard library? *)
Lemma string_of_list_ascii_length l
  : String.length (string_of_list_ascii l) = List.length l.
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
Qed.


(* TODO: separate file? *)
Section NamedList.
  Context {S : Type}
    {EqbS : Eqb S}
    {EqbS_ok : Eqb_ok EqbS}.

  Definition named_list (A : Type) :=list (S * A).

  (* A helper for stating theorems about named lists without depending on Eqb *)
Fixpoint named_list_lookup_prop {A} default (l : named_list A) (s : S) (a : A) : Prop :=
  match l with
  | [] => default = a
  | (s', v)::l' =>
      (s = s'/\ v = a) \/ (s <> s' /\ named_list_lookup_prop default l' s a)
  end.

Fixpoint named_list_lookup {A} default (l : named_list A) (s : S) : A :=
  match l with
  | [] => default
  | (s', v)::l' =>
    if eqb s s' then v else named_list_lookup default l' s
  end.

(*TODO: add hints for this?*)
Lemma named_list_lookup_prop_correct {A} (d : A) l s a
  :  named_list_lookup_prop d l s a <-> named_list_lookup d l s = a.
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
  my_case Heqb (eqb s s0);
    basic_goal_prep;
    basic_utils_crush.
Qed.


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
Proof using EqbS_ok.
  induction c; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (eqb n s);
    basic_utils_crush.
Qed.

Lemma all_fresh_named_list_lookup_err_in A c n (t : A)
  : all_fresh c -> Some t = named_list_lookup_err c n <-> In (n,t) c.
Proof using EqbS_ok.
  induction c; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (eqb n s); basic_utils_crush.  
Qed.

Lemma fresh_named_map A B l (f : A -> B) n
  : fresh n (named_map f l) <-> fresh n l.
Proof using .
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


Lemma fresh_app A s (l1 l2 : named_list A)
  : fresh s (l1 ++ l2) <-> fresh s l1 /\ fresh s l2.
Proof.
  induction l1; basic_goal_prep; basic_utils_firstorder_crush.
Qed.


#[local] Hint Resolve fresh_notin : utils.
#[local] Hint Rewrite fresh_app : utils.
#[local] Hint Rewrite in_app_iff : utils.
#[local] Hint Rewrite fresh_cons : utils.
Lemma all_fresh_insert_is_fresh A (a:A) l1 l2 s
  : all_fresh (l1++(s,a)::l2) ->
    fresh s l1.
Proof.
  induction l1; basic_goal_prep;
    basic_utils_crush.
Qed.
Local Hint Resolve all_fresh_insert_is_fresh : utils.

Lemma all_fresh_insert_rest_is_fresh A (a:A) l1 l2 s
  : all_fresh (l1++(s,a)::l2) ->
    all_fresh (l1++l2).
Proof.
  induction l1; basic_goal_prep; basic_utils_crush.
Qed.


Definition freshb {A} x (l : named_list A) : bool :=
  negb (inb x (map fst l)).

Lemma use_compute_fresh {A} x (l : named_list A) 
  : Is_true (freshb x l) -> fresh x l.
Proof.
  unfold freshb.
  unfold fresh.
  basic_utils_crush.
Qed.


Fixpoint all_freshb {A} (l : named_list A) : bool :=
  match l with
  | [] => true
  | (x,_)::l' => (freshb x l') && (all_freshb l')
  end.


#[local] Hint Resolve use_compute_fresh : utils.

Lemma use_compute_all_fresh A (l : named_list A)
  : Is_true (all_freshb l) -> all_fresh l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.


End NamedList.

#[export] Hint Rewrite @fresh_cons : utils.
#[export] Hint Rewrite @fresh_named_map : utils.
#[export] Hint Rewrite @map_fst_with_names_from : utils.
(*Note: this is a bit dangerous since the list might not be all-fresh,
  but in this project all lists should be

TODO: reassess whether it's necessary

#[export] Hint Rewrite @all_fresh_named_list_lookup_err_in : utils.
*)
#[export] Hint Resolve @named_list_lookup_none : utils.
#[export] Hint Resolve @in_named_map : utils.
#[export] Hint Rewrite @combine_map_fst_is_with_names_from : utils.
#[export] Hint Rewrite @named_map_length : utils.
#[export] Hint Resolve @fresh_notin : utils.
#[export] Hint Rewrite @fresh_app : utils.
#[export] Hint Resolve @all_fresh_insert_rest_is_fresh : utils.
#[export] Hint Resolve @named_list_lookup_err_in : utils.


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


Hint Rewrite pair_equal_spec : utils.


Lemma as_nth_tail: forall (A : Type) (l : list A), l = nth_tail 0 l.
Proof.
  intros; unfold nth_tail; reflexivity.
Qed.


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

