Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool String List.
Import ListNotations.
Import BoolNotations.
Open Scope string.
Open Scope list.

From Utils Require Import Base Booleans Nats Props Eqb Default Lists Pairs Options.


Section __.
  Context (S : Type)
    {EqbS : Eqb S}
    {EqbS_ok : Eqb_ok EqbS}.

  Section WithA.
    Context (A : Type).

    Definition named_list := list (S * A).
    Bind Scope list_scope with named_list.

    (* A helper for stating theorems about named lists without depending on Eqb *)
    Fixpoint named_list_lookup_prop default (l : named_list) (s : S) (a : A) : Prop :=
      match l with
      | [] => default = a
      | (s', v)::l' =>
          (s = s'/\ v = a) \/ (s <> s' /\ named_list_lookup_prop default l' s a)
      end.

    Fixpoint named_list_lookup default (l : named_list) (s : S) : A :=
      match l with
      | [] => default
      | (s', v)::l' =>
          if eqb s s' then v else named_list_lookup default l' s
      end.

    (*TODO: add hints for this?*)
    Lemma named_list_lookup_prop_correct (d : A) l s a
      :  named_list_lookup_prop d l s a <-> named_list_lookup d l s = a.
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      my_case Heqb (eqb s s0);
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    Definition fresh n (nl : named_list) : Prop :=
      ~ List.In n (map fst nl).

    
    (* These two lemmas should totally define fresh *)
    Lemma fresh_cons n m (e:A) es : fresh n ((m,e)::es) <-> ~ n = m /\ fresh n es.
    Proof.
      unfold fresh.
      firstorder eauto.
    Qed.

    Lemma fresh_nil n : fresh n [] <-> True.
    Proof.
      unfold fresh; firstorder eauto.
    Qed.

    Fixpoint all_fresh (l : named_list) :=
      match l with
      | [] => True
      | (n,_)::l' => fresh n l' /\ all_fresh l'
      end.

    Fixpoint named_list_lookup_err (l : named_list) s : option A :=
      match l with
      | [] => None
      | (s', v) :: l' => if eqb s s' then Some v else named_list_lookup_err l' s
      end.

    Lemma named_list_lookup_err_in c n t
      : Some t = named_list_lookup_err c n -> In (n,t) c.
    Proof using EqbS_ok.
      induction c; basic_goal_prep.
      basic_utils_crush.
      my_case Heq (eqb n s);
        basic_utils_crush.
    Qed.

    
    Lemma pair_fst_in (l : named_list) n a
      : In (n,a) l -> In n (map fst l).
    Proof using.
      induction l; break; simpl; autorewrite with utils; firstorder eauto.
    Qed.
    Hint Resolve pair_fst_in : utils.

    Lemma all_fresh_named_list_lookup_err_in c n (t : A)
      : all_fresh c -> Some t = named_list_lookup_err c n <-> In (n,t) c.
    Proof using EqbS_ok.
      induction c; basic_goal_prep.
      basic_utils_crush.  
      my_case Heq (eqb n s); basic_utils_crush.
    Qed.

    
    Lemma named_list_lookup_none l s (a:A)
      : None = named_list_lookup_err l s ->
        ~ In (s, a) l.
    Proof using EqbS_ok.
      induction l; basic_goal_prep; basic_utils_crush.
      my_case Hs (eqb s s0); basic_goal_prep; basic_utils_crush.
    Qed.

    
    Lemma in_all_fresh_same (a b : A) l s
      : all_fresh l -> In (s,a) l -> In (s,b) l -> a = b.
    Proof.  
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

    
    (* decomposes the way you want \in to on all_fresh lists*)
    Fixpoint in_once n e (l : named_list) : Prop :=
      match l with
      | [] => False
      | (n',e')::l' =>
          ((n = n') /\ (e = e')) \/ ((~n = n') /\ (in_once n e l'))
      end.

    Arguments in_once n e !l/.

    Lemma in_once_notin n (e : A) l
      : ~ In n (map fst l) -> ~(in_once n e l).
    Proof using .
      induction l; basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma all_fresh_in_once n (e : A) l
      : all_fresh l -> (In (n,e) l) <-> in_once n e l.
    Proof.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

    
    Lemma fresh_notin n (a:A) l
      : fresh n l -> ~In (n,a) l.
    Proof.
      unfold fresh.
      intuition eauto using pair_fst_in.
    Qed.


    Lemma fresh_app s (l1 l2 : named_list)
      : fresh s (l1 ++ l2) <-> fresh s l1 /\ fresh s l2.
    Proof.
      induction l1; basic_goal_prep; basic_utils_firstorder_crush.
    Qed.

    #[local] Hint Resolve fresh_notin : utils.
    #[local] Hint Rewrite fresh_app : utils.
    #[local] Hint Rewrite in_app_iff : utils.
    #[local] Hint Rewrite fresh_cons : utils.
    
    Lemma all_fresh_insert_is_fresh (a:A) l1 l2 s
      : all_fresh (l1++(s,a)::l2) ->
        fresh s l1.
    Proof.
      induction l1; basic_goal_prep;
        basic_utils_crush.
    Qed.
    Local Hint Resolve all_fresh_insert_is_fresh : utils.

    Lemma all_fresh_insert_rest_is_fresh (a:A) l1 l2 s
      : all_fresh (l1++(s,a)::l2) ->
        all_fresh (l1++l2).
    Proof.
      induction l1; basic_goal_prep; basic_utils_crush.
    Qed.


    Definition freshb x (l : named_list) : bool :=
      negb (inb x (map fst l)).

    Lemma use_compute_fresh x (l : named_list) 
      : Is_true (freshb x l) -> fresh x l.
    Proof.
      unfold freshb.
      unfold fresh.
      basic_utils_crush.
    Qed.


    Fixpoint all_freshb (l : named_list) : bool :=
      match l with
      | [] => true
      | (x,_)::l' => (freshb x l') && (all_freshb l')
      end.


    #[local] Hint Resolve use_compute_fresh : utils.

    Lemma use_compute_all_fresh (l : named_list)
      : Is_true (all_freshb l) -> all_fresh l.
    Proof.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

    
    Lemma in_all_named_list  P (l : named_list) n a
      : all P (map snd l) -> In (n,a) l -> P a.
    Proof.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

    
  End WithA.

  Section WithAB.
    Context {A B : Type}.

    Definition named_map (f : A -> B) : named_list A -> named_list B
      := map (pair_map_snd f).


    Lemma named_map_fst_eq (f : A -> B) l
      : map fst (named_map f l) = map fst l.
    Proof using .
      induction l; intros; break; simpl in *; f_equal; eauto.
    Qed.

    Lemma fresh_named_map l (f : A -> B) n
      : fresh n (named_map f l) <-> fresh n l.
    Proof using .
      induction l; basic_goal_prep;
        basic_utils_firstorder_crush.
    Qed.

    Fixpoint with_names_from (c : named_list A) (l : list B) : named_list B :=
      match c, l with
      | [],_ => []
      | _,[] => []
      | (n,_)::c',e::l' =>
          (n,e)::(with_names_from c' l')
      end.

    Lemma map_fst_with_names_from (c : named_list A) (l : list B)
      : length c = length l -> map fst (with_names_from c l) = map fst c.
    Proof.
      revert l; induction c; destruct l; basic_goal_prep; basic_utils_crush.
    Qed.

    Lemma in_named_map (f : A -> B) l n x
      : In (n,x) l -> In (n, f x) (named_map f l).
    Proof.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

    Lemma combine_map_fst_is_with_names_from (c : named_list A) (s : list B)
      : combine (map fst c) s = with_names_from c s.
    Proof.
      revert s; induction c; destruct s;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma named_map_length (f : A -> B) l
      : length (named_map f l) = length l.
    Proof.
      induction l; basic_goal_prep; basic_utils_crush.
    Qed.

  End WithAB.

  
  Lemma with_names_from_map_is_named_map A B C (f : A -> B) (l1 : named_list C) l2
    : with_names_from l1 (map f l2) = named_map f (with_names_from l1 l2).
  Proof.
    revert l2; induction l1;
      destruct l2; break; subst; simpl; f_equal; eauto.
  Qed.
(* TODO: do I want to rewrite like this?
  Hint Rewrite with_names_from_map_is_named_map : utils.*)

End __.


Arguments fresh {S A}%type_scope n nl%list_scope : simpl never.
Arguments all_fresh {S A}%type_scope !_%list_scope /.

Arguments in_once {S A}%type_scope n e !l%list_scope /.

Arguments in_all_named_list {S A}%type_scope [_]%function_scope {_} {_} {_}.

Arguments named_map {S A B}%type_scope f !l%list_scope/.
Arguments with_names_from {S A B}%type_scope c l%list_scope.

Arguments named_list_lookup_err_in {S}%type_scope {EqbS EqbS_ok} 
  [A]%type_scope c%list_scope n [t] _.

Arguments named_list_lookup_prop_correct {S}%type_scope 
  {EqbS EqbS_ok} [A]%type_scope d l s a.

#[export] Hint Resolve pair_fst_in : utils.

#[export] Hint Rewrite fresh_cons : utils.
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
#[export] Hint Resolve named_list_lookup_err_in : utils.
