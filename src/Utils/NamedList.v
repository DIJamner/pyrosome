Set Implicit Arguments.

From Stdlib Require Import Bool.
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Import BoolNotations.
Open Scope string.
Open Scope list.

From Utils Require Import Base Booleans Eqb Lists Pairs.


(* Single-round variant of [basic_utils_crush] (which is a [repeat] of
   intuition/autorewrite/eauto).  Most call sites below converge in one
   round, and the repeated [autorewrite ... in *] / [intuition] dominate
   this file's compile time. *)
Ltac utils_crush1 :=
  intuition break; subst;
  autorewrite with bool rw_prop inversion utils in *;
  intuition (unshelve eauto with utils).
(* Leaner still: only the [utils] rewrite db.  The [bool]/[rw_prop]/[inversion]
   dbs are what make [autorewrite ... in *] expensive here, and most sites do
   not need them. *)
Ltac utils_crush1u :=
  intuition break; subst;
  autorewrite with utils in *;
  intuition (unshelve eauto with utils).

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
      induction l; basic_goal_prep; [ reflexivity | ].
      eqb_case s s0; cbn.
      - split;
          [ intros [[_ ?]|[? _]]; [ assumption | congruence ]
          | intros ?; left; split; [ reflexivity | assumption ] ].
      - rewrite IHl; split;
          [ intros [[? _]|[_ ?]]; [ congruence | assumption ]
          | intros ?; right; split; assumption ].
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
      { utils_crush1. }
      {
        destruct (eqb n s) eqn:Heq;
          utils_crush1.
      }
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
      induction c as [| [s v] c IHc]; basic_goal_prep.
      - split; [ intros H'; discriminate | intros [] ].
      - destruct H as [Hfr Hall]; specialize (IHc Hall).
        eqb_case n s; cbn.
        + split.
          * intros Heq; injection Heq as ?; subst; left; reflexivity.
          * intros [Heq|Hin];
              [ injection Heq; intros; subst; reflexivity
              | exfalso; apply Hfr; eapply pair_fst_in; eassumption ].
        + rewrite IHc; split.
          * intros Hin; right; exact Hin.
          * intros [Heq|Hin]; [ injection Heq; intros; subst; congruence | exact Hin ].
    Qed.

    
    Lemma named_list_lookup_none l s (a:A)
      : None = named_list_lookup_err l s ->
        ~ In (s, a) l.
    Proof using EqbS_ok.
      induction l; basic_goal_prep; basic_utils_crush.
      destruct (eqb s s0) eqn:Hs; basic_goal_prep; basic_utils_crush.
    Qed.

    
    Lemma in_all_fresh_same (a b : A) l s
      : all_fresh l -> In (s,a) l -> In (s,b) l -> a = b.
    Proof.  
      induction l as [| [s0 a0] l IHl]; basic_goal_prep; [ contradiction | ].
      destruct H as [Hfr Hall].
      destruct H0 as [Heq1|Hin1]; destruct H1 as [Heq2|Hin2].
      - injection Heq1 as ? ?; injection Heq2 as ? ?; subst; reflexivity.
      - injection Heq1 as ? ?; subst; exfalso;
          apply Hfr; eapply pair_fst_in; eassumption.
      - injection Heq2 as ? ?; subst; exfalso;
          apply Hfr; eapply pair_fst_in; eassumption.
      - eauto.
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
        utils_crush1u.
    Qed.

    Lemma all_fresh_in_once n (e : A) l
      : all_fresh l -> (In (n,e) l) <-> in_once n e l.
    Proof.
      induction l; basic_goal_prep; utils_crush1u.
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
      induction l1; basic_goal_prep; utils_crush1u.
    Qed.


    Definition freshb x (l : named_list) : bool :=
      negb (inb x (map fst l)).

    Lemma use_compute_fresh x (l : named_list) 
      : Is_true (freshb x l) -> fresh x l.
    Proof.
      unfold freshb.
      unfold fresh.
      utils_crush1.
    Qed.
    
    Lemma freshb_spec x (l : named_list) 
      : Is_true (freshb x l) <-> fresh x l.
    Proof.
      unfold freshb.
      unfold fresh.
      utils_crush1.
    Qed.


    Fixpoint all_freshb (l : named_list) : bool :=
      match l with
      | [] => true
      | (x,_)::l' => (freshb x l') && (all_freshb l')
      end.


    #[local] Hint Resolve use_compute_fresh : utils.

    (*TODO: remove uses*)
    Lemma use_compute_all_fresh (l : named_list)
      : Is_true (all_freshb l) -> all_fresh l.
    Proof.
      induction l; basic_goal_prep; utils_crush1.
    Qed.

    
    Lemma all_freshb_spec (l : named_list)
      : Is_true (all_freshb l) <-> all_fresh l.
    Proof.
      induction l; basic_goal_prep; utils_crush1.
      apply freshb_spec; eauto.
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
      revert l; induction c; destruct l; basic_goal_prep; utils_crush1.
    Qed.

    Lemma in_named_map (f : A -> B) l n x
      : In (n,x) l -> In (n, f x) (named_map f l).
    Proof.
      induction l; basic_goal_prep; utils_crush1u.
    Qed.

    Lemma combine_map_fst_is_with_names_from (c : named_list A) (s : list B)
      : combine (map fst c) s = with_names_from c s.
    Proof.
      revert s; induction c; destruct s;
        basic_goal_prep;
        utils_crush1u.
    Qed.

    Lemma named_map_length (f : A -> B) l
      : length (named_map f l) = length l.
    Proof.
      induction l; basic_goal_prep; utils_crush1u.
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

  
  Lemma all_fresh_tail {A} (l1 l2: named_list A)
    : all_fresh (l1++l2) -> all_fresh l2.
  Proof.
    induction l1; basic_goal_prep; utils_crush1u.
  Qed.

  
  #[local] Hint Resolve fresh_notin : utils.
  #[local] Hint Rewrite fresh_app : utils.
  Lemma all_fresh_conflict_impossible {A} (l1 l2: named_list A) n a1 a2
    : all_fresh (l1++l2) -> In (n,a1) l1 -> In (n,a2) l2 -> False.
  Proof.
    induction l1; basic_goal_prep; utils_crush1u.
    (*TODO: what later-proven lemma is missing here? (should be automatic)*)
    eapply fresh_notin in H5.
    basic_utils_crush.
  Qed.
  (* TODO: a bit problematic as a hint. See where (in Compilers.v)
     leaving this hint out fails.
   *)
  #[local] Hint Resolve all_fresh_conflict_impossible : utils.

  Lemma in_twice_appended_all_fresh {A} (l1 l2: named_list A) n a
    : all_fresh (l1++l2) ->
      In (n,a) l1 ->
      ~In n (map fst l2).
  Proof.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Hint Rewrite fresh_cons : utils.
  (*TODO: this is better than the non-iff version. Entirely replace? *)
  Lemma named_list_lookup_none_iff {A} (l : named_list A) s
    : None = named_list_lookup_err l s <-> fresh s l.
  Proof.
    induction l.
    1: basic_goal_prep; utils_crush1.
    break; simpl.
    case_match; basic_goal_prep; utils_crush1.
  Qed.

  (* Note: does not error out on bad inputs *)
  Fixpoint select_sublist {A} (s : named_list A) (filter : list S) :=
    match s, filter with
    | [], _ | _, [] => []
    | (n,a)::s', n'::filter' =>
        if eqb n n' then a::(select_sublist s' filter')
        else (select_sublist s' filter)
    end.

End __.


Arguments fresh {S A}%_type_scope n nl%_list_scope : simpl never.
Arguments all_fresh {S A}%_type_scope !_%_list_scope /.


Arguments use_compute_fresh {S}%_type_scope {EqbS EqbS_ok} 
  [A]%_type_scope x l%_list_scope _ _.
Ltac compute_fresh := eapply use_compute_fresh; vm_compute; exact I.

Arguments use_compute_all_fresh {S}%_type_scope {EqbS EqbS_ok} 
  [A]%_type_scope l _.
Ltac compute_all_fresh := eapply use_compute_all_fresh; vm_compute; exact I.


#[export] Hint Rewrite freshb_spec : utils.
#[export] Hint Rewrite all_freshb_spec : utils.

Arguments in_once {S A}%_type_scope n e !l%_list_scope /.

Arguments in_all_named_list {S A}%_type_scope [_]%_function_scope {_} {_} {_}.

Arguments named_map {S A B}%_type_scope f !l%_list_scope/.
Arguments with_names_from {S A B}%_type_scope c l%_list_scope.

Arguments named_list_lookup_err_in {S}%_type_scope {EqbS EqbS_ok} 
  [A]%_type_scope c%_list_scope n [t] _.

Arguments named_list_lookup_prop_correct {S}%_type_scope 
  {EqbS EqbS_ok} [A]%_type_scope d l s a.

Arguments named_list_lookup_none_iff {S}%_type_scope {EqbS EqbS_ok} {A}%_type_scope l%_list_scope s.

#[export] Hint Resolve pair_fst_in : utils.

#[export] Hint Rewrite fresh_cons : utils.

#[export] Hint Rewrite fresh_named_map : utils.
#[export] Hint Rewrite @map_fst_with_names_from : utils.
(*Note: this is a bit dangerous since the list might not be all-fresh,
  but in this project all lists should be

TODO: reassess whether it's necessary

#[export] Hint Rewrite @all_fresh_named_list_lookup_err_in : utils.
 *)
Arguments named_list_lookup_none {S}%_type_scope {EqbS EqbS_ok} [A]%_type_scope l s a _ _.
#[export] Hint Resolve named_list_lookup_none : utils.
#[export] Hint Resolve in_named_map : utils.
#[export] Hint Rewrite @combine_map_fst_is_with_names_from : utils.
#[export] Hint Rewrite @named_map_length : utils.
#[export] Hint Resolve fresh_notin : utils.
#[export] Hint Rewrite @fresh_app : utils.
#[export] Hint Resolve all_fresh_insert_rest_is_fresh : utils.
#[export] Hint Resolve named_list_lookup_err_in : utils.



Lemma pair_fst_in_exists:
  forall [S A : Type] (l : named_list S A) (n : S),
    In n (map fst l) -> exists a, In (n, a) l.
Proof.
  induction l;
    basic_goal_prep;
    utils_crush1u.
  apply IHl in H0; break.
  exists x; eauto.
Qed.
