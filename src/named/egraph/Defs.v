(*
  Implementation based on Egg: https://dl.acm.org/doi/pdf/10.1145/3434304
*)
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

Fixpoint list_ltb {A} (ltb : A -> A -> bool) (a b : list A) : bool :=
    match a,b with
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | (a::x), (b::y) =>
      (ltb a b) && (list_ltb ltb x y)
    end.

Module IntListOT := ListOrderedType Int63Natlike.
Module ENode.
  Include (PairOrderedType String_as_OT IntListOT).

  Definition ltb '(n1, args1) '(n2,args2) :=
    (String.ltb n1 n2) && (list_ltb Int63.ltb args1 args2).
    
End ENode.

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
  Local Instance enode_strict_order: @SortedList.parameters.strict_order _ ENode.ltb.
  Admitted (*TODO: use existing strorder?*).
  
  Definition Build_parameters T :=
    SortedList.parameters.Build_parameters _ T ltb.
  
  Definition map T := SortedList.map (Build_parameters T) enode_strict_order.

  Definition ok T : @Interface.map.ok _ T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.
  
End ENodeMap.


Instance eclass_map_ty : Interface.map.map Int63Natlike.t EClass.t := Int63Map.map _.
Instance hashcons_ty : Interface.map.map ENode.t Int63Natlike.t := ENodeMap.map _.

Record egraph :=
  MkEGraph {
      id_equiv : UnionFind.union_find;
      eclass_map : Int63Map.map EClass.t;
      hashcons : ENodeMap.map Int63Natlike.t
  }.

Require Import Utils.Monad.

Definition ST S A := S -> (S * A).

Instance state_monad {S} : Monad (ST S) :=
  {
  Mret _ a := fun s => (s,a);
  Mbind _ _ f ma :=
    fun s =>
      let (s,a) := ma s in
      f a s
  }.

Fixpoint list_Mmap {M A B} `{Monad M} (f : A -> M B) (l : list A) : M (list B) :=
  match l with
  | [] => do ret []
  | a::al' =>
    do let b <- f a in
       let bl' <- list_Mmap f al' in
       ret (b::bl')
       end.

Definition unwrap_with_default {A} (default : A) ma :=
  match ma with None => default | Some a => a end.
  
Section EGraphOps.

  Local Notation "'ST'" := (ST egraph).


  Definition find a : ST int :=
    fun g =>
    let (uf, fa) := UnionFind.find g.(id_equiv) a in
    (MkEGraph uf g.(eclass_map) g.(hashcons), fa).

  (*TODO: check this*)
  Definition alloc : ST int :=
    fun g =>
    let (uf, a) := UnionFind.alloc g.(id_equiv) in
    (MkEGraph uf g.(eclass_map) g.(hashcons), a).

  Definition hashcons_lookup (n : ENode.t) : ST (option int) :=
    fun g =>
      let mi := map.get g.(hashcons) n in
      (g, mi).

  Definition set_eclass i (c : EClass.t) : ST unit :=
    fun '(MkEGraph U M H) =>
      let M := map.put M i c in
      (MkEGraph U M H,tt).

  Definition union_ids a b : ST unit :=
    fun '(MkEGraph U M H) =>
      let U := UnionFind.union U a b in
      (MkEGraph U M H,tt).

  (* return a default value rather than none
     for ease-of-use
   *)
  Definition get_eclass i : ST EClass.t :=
    fun g => (g, unwrap_with_default EClass.empty (map.get g.(eclass_map) i)).    

  Definition canonicalize '(n,args) : ST ENode.t :=
    do let args' <- list_Mmap find args in
       ret (n,args').
      
  Definition eqb_ids a b : ST bool :=
    do let fa <- (find a) in
       let fb <- (find b) in
       ret eqb fa fb.

       
  Definition lookup n : ST (option int) :=
    do let n <- canonicalize n in
       (hashcons_lookup n).
       
  Definition add (n : ENode.t) : ST int :=
    do let mn <- lookup n in
       match mn with
       | Some i => do ret i
       | None => 
         do let i <- alloc in
            let tt <- set_eclass i (EClass.singleton n) in
            ret i
            end.

  Definition merge (a b : int) : ST unit :=
    do let tt <- union_ids a b in
       let ca <- get_eclass a in
       let cb <- get_eclass b in
       let c := EClass.union ca cb in
       let tt <- set_eclass a c in
       (set_eclass b c).

  Definition match_result := list (named_list int * EClass.t).
       
  (*Definition ematch (e : term) : ST match_result *)
    

    
