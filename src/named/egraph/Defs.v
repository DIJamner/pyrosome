Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool String List Orders.
Import ListNotations.
Open Scope string.
Open Scope list.
From coqutil Require Import Map.Interface.
From coqutil Require Map.SortedList.
From Utils Require Import Utils PersistentArrayList UnionFind.
From Named Require Import Term.
(*Import Core.Notations.*)

Require MSets.


(*TODO: parameterize by ArrayList impl;
  depends on UnionFind coq bug
 *)
Import Int63.
Import OrdersEx.

(*TODO: move anything not touching terms or nodes to utils, nodes to sep. file*)

(*TODO: is this defined anywhere?*)
Module ListDecidableType(D :DecidableType) <: DecidableType.

  Definition t := list D.t.

  Definition eq := Forall2 D.eq.

  #[global]
   Instance eq_equiv : Equivalence eq.
  Proof.
    unfold eq.
    repeat constructor.
    {
      intro l; induction l;
        constructor; eauto.
      apply D.eq_equiv.
    }
    {
      intro l; induction l;
      inversion 1;
      constructor; eauto;
      subst.
      apply D.eq_equiv; auto.
    }
    {
      intro l; induction l;
      inversion 1;
      inversion 1;
      subst;
      constructor; eauto.
      destruct D.eq_equiv as [_ _ Dtrans];
        eapply Dtrans; eauto.
    }
  Qed.  

 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
   unfold eq.
   induction x; destruct y; eauto.
   1,2: right; inversion 1.
   destruct (D.eq_dec a t0);
     destruct (IHx y).
   {
     intuition.
   }
   all: right; inversion 1; subst; auto.
 Defined.
 
End ListDecidableType.

Module ListOrderedType(O:OrderedType) <: OrderedType.
  Include ListDecidableType O.

  Definition lt : t -> t -> Prop. Admitted.

  #[global]
   Instance lt_strorder : StrictOrder lt.
  Proof.
  Admitted.

  #[global]
   Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  Admitted.

  Fixpoint compare x y :=
    match x, y with
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | (a::x), (b::y) =>
      match O.compare a b with
      | Eq => compare x y
      | Lt => Lt
      | Gt => Gt
      end
    end.

 Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
 Proof.
 Admitted.

End ListOrderedType.

Module IntListOT := ListOrderedType Int63Natlike.
Module ENode : OrderedType :=
  PairOrderedType String_as_OT IntListOT.

Module EClass := MSets.MSetAVL.Make ENode.


Module Int63Map.
  (* Make this an instance so we can use single-curly-braces so we don't need to qualify field-names with [SortedList.parameters.] *)
  Import Int63Natlike.
  Local Instance int63_strict_order: @SortedList.parameters.strict_order _ ltb.
  {
    constructor.
    {
      intros.
      rewrite <- not_true_iff_false.
      rewrite ltb_lt.
      int_lia.
    }
    {
      intros.
      rewrite ltb_lt in *.
      int_lia.
    }
    {
      intros.
      rewrite <- not_true_iff_false in *.
      rewrite ltb_lt in *.
      int_lia.
    }
  }
  Qed.
  
  Definition Build_parameters T :=
    SortedList.parameters.Build_parameters _ T ltb.
  
  Definition map T := SortedList.map (Build_parameters T) int63_strict_order.

  Definition ok T : @Interface.map.ok _ T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.
  
End Int63Map.



Module ENodeMap.
  (* Make this an instance so we can use single-curly-braces so we don't need to qualify field-names with [SortedList.parameters.] *)
  Import ENode.
  Local Instance enode_strict_order: @SortedList.parameters.strict_order _ ltb.
  Admitted (*TODO: use existing strorder?*).
  
  Definition Build_parameters T :=
    SortedList.parameters.Build_parameters _ T ltb.
  
  Definition map T := SortedList.map (Build_parameters T) enode_strict_order.

  Definition ok T : @Interface.map.ok _ T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.
  
End ENodeMap.

Instance eclass_map_ty : Interface.map.map Int63Natlike.t EClass.t := Int63Map.map _.

Record egraph :=
  MkEGraph {
      id_equiv : UnionFind.union_find;
      eclass_map : Int63Map.map EClass.t;
      hashcons : ENodeMap.map Int63Natlike.t
  }.



