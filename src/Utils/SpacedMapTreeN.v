Require Import NArith Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface.

From Utils Require Import Booleans Default Base Eqb Options ExtraMaps Monad MapTreeN.
From Utils Require TrieMap.

(*TODO: move to Booleans or a new file *)
Definition compute_checked {b A} : (Is_true b -> A) -> option A :=
  if b as b return (Is_true b -> _) -> _
  then fun f => Some (f I)
  else fun _ => None.

(*TODO: move to Booleans or a new file *)
Definition compute_unchecked {b A} `{WithDefault A} : (Is_true b -> A) -> A :=
  if b as b return (Is_true b -> _) -> _
  then fun f => f I
  else fun _ => default.

Lemma compute_unchecked_eq {b A}  `{WithDefault A} (f : Is_true b -> A) Hb
  : compute_unchecked f = f Hb.
Proof.
  revert f Hb;
    destruct b; cbn;
    try tauto.
  destruct Hb; tauto.
Qed.
  
Section __.
  Context {key} {m : forall A, map.map key A}.

  Section __.
    
    Context (A : Type).

    Notation ntree' n := (@ntree key m A n).

    Record ntree : Type :=
      {
        constrained_indices : list bool;
        inner_tree : ntree' (length (filter id constrained_indices));
      }.

    Instance ntree_default `{WithDefault A} : WithDefault ntree :=
      Build_ntree [] default.

    
    Section __.
      Context {B} (f : B -> list key -> A -> B).

      Notation ntree_fold' := (@ntree_fold key m A B f).

      (*Note: only works if constrained indices = [true...]*)
      Definition ntree_fold (t : ntree) : B -> B :=
        ntree_fold' _ t.(inner_tree).
      
    End __.

    (* assumes the inputs have the same length *)
    Fixpoint filter_key (k : list key) (ci : list bool) :=
      match k, ci with
      | [], _
      | _, [] => []
      | k1::k, b::ci =>
          if b then k1::(filter_key k ci) else filter_key k ci
      end.
    (*
    Assumes k has length exactly equal to the length of constrained indices
     *)
    Definition ntree_get (t : ntree) (k : list key) : option A :=
      let k' := filter_key k t.(constrained_indices) in
      MapTreeN.ntree_get t.(inner_tree) k'.


  End __.
  Arguments constrained_indices {A}%type_scope n.
  Arguments inner_tree {A}%type_scope n.
  Existing Instance ntree_default.

  Section __.
    
    Notation ntree' A n := (@MapTreeN.ntree key m A n).
    
    (* Question: Should I handle empty ntree 0s?
     *)
    Context {A B C : Type}
      (merge : A -> B -> C)
      `{map_plus_ok key (m := m)}.

    (* TODO: define w/out refine. *)
    Fixpoint ntree_intersect' ci1 ci2
      : (*TODO: check whether this affects performance*)
      Is_true (eqb (length ci1) (length ci2)) -> 
      ntree' A (length (filter id ci1)) ->
      ntree' B (length (filter id ci2)) ->
      ntree' C (length (filter id (List.zip orb ci1 ci2))).
      refine (match ci1 as ci1, ci2 as ci2 with
              | [], [] => fun _ t1 t2 => merge t1 t2
              | b1::ci1', b2::ci2' =>
                  if b1 as b1 return _ then
                    if b2 as b2 return _ then fun eqlen t1 t2 => _
                    else fun eqlen t1 t2 => _
                  else
                    if b2 as b2 return _ then fun eqlen t1 t2 => _
                    else _
              | _,_ => fun fls => match fls with end
              end).
      1:refine (map_intersect (ntree_intersect' ci1' ci2' eqlen) t1 t2).
      1:refine (map_map (fun t => ntree_intersect' ci1' ci2' eqlen t t2) t1).
      1:refine (map_map (fun t => ntree_intersect' ci1' ci2' eqlen t1 t) t2).
      1:refine (ntree_intersect' ci1' ci2').
    Defined.

    Section __.
      Context `{WithDefault C}.
      Context (t1 : ntree A) (t2 : ntree B).
      Definition ntree_len_eq :=
        Is_true (eqb (length t1.(constrained_indices))
                   (length t2.(constrained_indices))).

      Definition ntree_intersect (Heq : ntree_len_eq) : ntree C :=
        Build_ntree _ (List.zip orb t1.(constrained_indices)
                                         t2.(constrained_indices))
          (ntree_intersect' _ _ Heq t1.(inner_tree) t2.(inner_tree)).

      
      Definition ntree_intersect_unchecked : ntree C :=
        compute_unchecked ntree_intersect.
      
    End __.

    
    Arguments ntree_get {A}%type_scope t k%list_scope.
    
    Lemma ntree_intersect_spec (t1 : ntree A) (t2 : ntree B) k Hlen
      : ntree_get (ntree_intersect t1 t2 Hlen) k
        = match ntree_get t1 k, ntree_get t2 k with
          | Some a, Some b => Some (merge a b)
          | _, _ => None
          end.
    Proof.
      destruct t1, t2.
      unfold ntree_intersect, ntree_get, ntree_len_eq in *.
      cbn [inner_tree constrained_indices] in *.
      revert k.
      revert dependent constrained_indices1.
      revert inner_tree0.
      induction constrained_indices0;
        destruct constrained_indices1;
        basic_goal_prep;
        basic_utils_crush.
      destruct a,b, k;
        basic_goal_prep;
        basic_utils_crush.
      all: rewrite ?intersect_spec; eauto.
      all: cbn in *;
        unfold MapTreeN.ntree in *;
        repeat case_match; try tauto.
      all: unfold List.zip in *; cbn in *.
      all: rewrite ?IHconstrained_indices0; eauto.
      all: repeat lazymatch goal with
             | H : None = ?A |- context[?A] =>
                 rewrite <- H; cbn; eauto
             | H : Some _ = ?A |- context[?A] =>
                 rewrite <- H; cbn; eauto
             end.       
      all: rewrite ?map_map_spec in *; eauto.
      all: repeat lazymatch goal with
             | H1 : context[?A], H2 : None = ?A |- _ =>
                 rewrite <- H2 in H1;
                 try safe_invert H1
             | H1 : context[?A], H2 : Some _ = ?A |- _ =>
                 rewrite <- H2 in H1;
                 try safe_invert H1
             end.
      all: rewrite ?IHconstrained_indices0; eauto.
      all: repeat lazymatch goal with
             | H : None = ?A |- context[?A] =>
                 rewrite <- H; cbn; eauto
             | H : Some _ = ?A |- context[?A] =>
                 rewrite <- H; cbn; eauto
             end.
      {
        (*contradiction? watch HeqH0*)
        my_case Hit1 (map.get inner_tree1 k).
        all: cbn in *; try congruence.
        safe_invert HeqH1.
        rewrite ?IHconstrained_indices0; eauto.
        rewrite <- HeqH0.
        eauto.
      }
      all: change []
        with (filter_key []
                (map (fun '(x, y) => x || y)
                   (combine constrained_indices0  constrained_indices1)));
        rewrite IHconstrained_indices0; eauto; cbn;
        repeat lazymatch goal with
          | H : None = ?A |- context[?A] =>
              rewrite <- H; cbn; eauto
          | H : Some _ = ?A |- context[?A] =>
              rewrite <- H; cbn; eauto
          end.
    Qed.
        
    Lemma ntree_intersect_unchecked_spec (t1 : ntree A) (t2 : ntree B) k `{WithDefault C}
      : ntree_len_eq t1 t2 ->
        ntree_get (ntree_intersect_unchecked t1 t2) k
        = match ntree_get t1 k, ntree_get t2 k with
          | Some a, Some b => Some (merge a b)
          | _, _ => None
          end.
    Proof.
      intro Hb.
      unfold ntree_intersect_unchecked.
      unshelve erewrite compute_unchecked_eq; eauto.
      eapply ntree_intersect_spec;eauto.
    Qed.
    
  End __.

End __.

#[export] Existing Instance ntree_default.

Arguments constrained_indices
  {key}%type_scope {m}%function_scope {A}%type_scope n.
Arguments inner_tree {key}%type_scope {m}%function_scope {A}%type_scope n.

Arguments ntree_get {key}%type_scope {m}%function_scope {A}%type_scope t k%list_scope.
