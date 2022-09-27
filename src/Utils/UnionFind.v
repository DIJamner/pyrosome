(* A union-find data structure that can be instantiated 
   with either persistent arrays or a functional implementation of the same spec.
   The instantiation with persistent arrays should be performant,
   while the instantiation with a function implementation should be closed
   under the global context.

   based on this paper:
   Sylvain Conchon and Jean-Christophe Filliâtre. A persistent union-find data structure.
   In ACM SIGPLAN Workshop on ML, 37–45. Freiburg, Germany, October 2007. ACM Press.
   URL: https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf.
*)

Require ZArith.

From Tries Require Import Canonical.

From Utils Require Import Utils Natlike ArrayList.
From Utils Require TrieMap NatlikePos.




(* Use typeclasses since passing some instances to functors breaks the VM
   (issue #12519)
 *)
Section UnionFind.
  
  Context {idx : Type}
    `{Natlike_ok idx}
    {array : Type -> Type}
    `{ArrayList idx array}.

  Notation zero := (zero : idx).

  (*TODO: make notations use ops*)
  (*Module Ntns := (ArrayNotations NL AL).
  Import NL AL Ntns.
   *)

  Record union_find :=
    MkUF {
        rank : array idx;
        parent : array idx;
        (* we include an upper bound on the rank for purposes of termination *)
        max_rank : idx
      }.

  Definition length uf := length uf.(parent).
  
  Definition empty : union_find :=
    MkUF (make zero) (make zero) zero.

  (*TODO: write w/ state monad for clarity?*)
  
  Definition alloc '(MkUF ra pa mr) :=
    let (i,pa) := alloc pa zero in
    (*We don't need to initialize rank since default of 0 is correct*)
    (MkUF ra (set pa i i) mr, i).

  Definition find_aux
    : idx -> array idx -> idx -> array idx * idx :=
    iter
      (fun f i => (f,i))
      (fun find_aux f i =>         
      let fi := get f i in
      if eqb fi i then
        (f,i)
      else
        let (f, r) := find_aux f fi in
        let f := set f i r in
        (f,r)
      ).

  
  Definition find '(MkUF ra pa mr) x :=
    let (f,cx) := find_aux mr pa x in
    (MkUF ra f mr, cx).

  
  (*TODO: move to the right place*)
  Definition max (x y : idx) :=
    if leb x y then y else x.

  (*TODO: needs to return the root id*)
  Definition union h x y :=
    let (h, cx) := find h x in
    let (h, cy) := find h y in
    if eqb cx cy then (h, cx) else
      let (ra, pa, mr) := h in
      let rx := get ra cx in
      let ry := get ra cy in
      if ltb ry rx then
        (MkUF ra (set pa cy cx) mr, cx)
      else if ltb rx ry then
             (MkUF ra (set pa cx cy) mr, cy)
           else
             (MkUF (set ra cx (succ rx))
                  (set pa cy cx)
                  (max mr (succ rx)), cx).
    
End UnionFind.


(* All definitions and proofs need to be generic over arraylist implementations.
   Use the following code to test functions with a specific implementation: *)

(*Testing *)
(*
#[local] Existing Instance PArrayList.arraylist_ops.
#[local] Existing Instance Int63Natlike.natlike_ops.
*)

Module Int63UnionFind.

  Require Import Int63 ZArith.
  From Utils Require Import PersistentArrayList.

  Axiom TODO : forall A, A.
  
  #[refine] Instance int63eqb : Eqb int := { eqb := Int63Natlike.eqb}.
  - exact Int63Natlike.eqb_eq.
  - apply TODO.
  - apply TODO.
  - exact Int63Natlike.eq_dec.
  Defined.

  Instance natlike_int63 : Natlike int :=
    {
      natlike_eqb := int63eqb;
      ltb := Int63Natlike.ltb;
      leb := Int63Natlike.leb;
      zero := Int63Natlike.zero;
      succ := Int63Natlike.succ;
      is_top := Int63Natlike.is_top;
      iter := @Int63Natlike.iter;
    }.

  Instance arraylist_parraylist : ArrayList int PArrayList.array :=
    {
    make := @PArrayList.make;
    get := @PArrayList.get;
    set := @PArrayList.set;
    length := @PArrayList.length;
    alloc := @PArrayList.alloc;
    }.

  (* takes around 7s
  Time Eval vm_compute in
    let uf :=N.recursion empty
                         (fun _  uf =>
                            let (uf, i) := alloc uf in
                            if ltb i 10 then uf else
                              let (uf,_) := union uf i (sub i 10) in
                              uf)
                         1000000 in
    snd (find uf 604828%int63).
   *)

End Int63UnionFind.
  
Module PositiveUnionFind.
  Import ZArith.
  Import TrieMap.TrieArrayList.
  Open Scope positive.

  Notation union_find := (@UnionFind.union_find positive trie_array).

  
  Definition is_parent '(MkUF ra pa mr : union_find) x y : Prop :=
    get pa y = x.

  (* TODO: will there be issues w/ positive overflowing here?
     TODO: if we assume is_top = false, do the issues go away?
   *)
  Inductive parent_degree (pa : trie_array positive) : positive -> positive -> Prop :=
  | pdegree_0 i : get pa i = i -> parent_degree pa i 1
  | pdegree_S i j n : get pa i = j -> parent_degree pa j n -> parent_degree pa i (succ n).
  
  Inductive parent_degree_bound (pa : trie_array positive) : positive -> positive -> Prop :=
  | pdegree_b0_bound i n : get pa i = i -> parent_degree_bound pa i n
  | pdegree_S_bound i j n m
    : get pa i = j ->
      parent_degree_bound pa j n ->
      n < m ->
      parent_degree_bound pa i m.
  
  Record trie_array_ok {A} (a : trie_array A) :=
    {
      len_gt_max_key : forall i e,
        PTree.get i (snd (fst a)) = Some e ->
        fst (fst a) > i
    }.

  Definition dense {A} (a : trie_array A) :=
    forall i, i < fst (fst a) ->
              if PTree.get i (snd (fst a)) then True else False.
  
  Record union_find_ok (u : union_find) :=
    {
      max_rank_ok : forall i, (get u.(rank) i) <= u.(max_rank);
      ranks_ok : forall i, parent_degree_bound u.(parent) i (get u.(rank) i);
      len_same : ArrayList.length u.(parent) = ArrayList.length u.(rank);
      parents_ok : trie_array_ok u.(parent);
      parents_dense : dense u.(parent);
      rank_ok : trie_array_ok u.(rank);
      rank_dense : dense u.(rank);
    }.

  (*TODO: move to Utils.v*)
  Inductive equivalence_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | eq_clo_base a b : R a b -> equivalence_closure R a b
  | eq_clo_refl a : equivalence_closure R a a
  | eq_clo_trans a b c : equivalence_closure R a b -> equivalence_closure R b c -> equivalence_closure R a c
  | eq_clo_sym a b : equivalence_closure R a b -> equivalence_closure R b a.

  Hint Constructors equivalence_closure : utils.

  Inductive parent_path (pa : trie_array positive) : positive -> positive -> Prop :=
  | ppath_0 i : parent_path pa i i
  | ppath_S i j k : get pa i = j -> parent_path pa j k -> parent_path pa i k.
  Hint Constructors parent_path : utils.

  Let uf_clo uf := equivalence_closure (is_parent uf).
  
  Lemma find_preserves_len_parents (uf : union_find) i uf' i'
    : find uf i = (uf', i') ->
      i < ArrayList.length uf.(parent) ->
      ArrayList.length uf.(parent) =  ArrayList.length uf'.(parent).
  Proof.    
    destruct uf as [ra pa mr].
    revert ra pa i uf' i'.
    eapply Pos.peano_ind with (p:=mr);
      intros;
      destruct uf' as [ra' pa' mr'];
      unfold trie_array in *; break; simpl in *.
    {
      revert H; case_match.
      repeat (revert HeqH;case_match); simpl in *;
        basic_goal_prep;
          basic_utils_crush;
        try congruence;
        safe_invert H3;
        rewrite Pos.max_l; Lia.lia.
    }
  Abort.

  (*
    
  Lemma find_preserves_ok uf i uf' i'
    : union_find_ok uf ->
      find uf i = (uf', i') ->
      (*TODO: do I want this condition?*)
      i < ArrayList.length uf.(parent) ->
      union_find_ok uf'.
  Proof.
    
    destruct uf as [ra pa mr].
    revert ra pa i uf' i'.
    eapply Pos.peano_ind with (p:=mr);
      intros; unfold trie_array in *; break.
    {
      destruct H;
        revert H0; simpl in *.
      case_match;
      revert HeqH.
      case_match;
        revert HeqH.
      {
        case_match;
          intro H'; symmetry in H'; apply Pos.eqb_eq in H'; subst;
          intro H'; safe_invert H';
          intro H'; safe_invert H';
          constructor; eauto.
      }
      {
        case_match.
        {
          intros _.
          intro H'; safe_invert H';
            intro H'; safe_invert H'.
          assert (Pos.max p1 (i + 1) = p1).
          {
            eapply Pos.max_l.
            destruct parents_ok0.
            simpl in *.
            symmetry in HeqH.
            apply len_gt_max_key0 in HeqH.
            Lia.lia.
          }
          {
            constructor; simpl; eauto.
            
            simpl.
      }
        }
        {
          
        }
          
    
  Lemma find_preserves_relation uf i uf' i'
    : union_find_ok uf ->
      find uf i = (uf', i') ->
      (forall x y, uf_clo uf x y <-> uf_clo uf' x y)
      /\ (uf_clo uf i i').
  Proof.
    destruct uf as [ra pa mr].
    revert ra pa i uf' i'.
    eapply Pos.peano_ind with (p:=mr);
      intros; unfold trie_array in *; break.
    {
      simpl in *.
      revert H.
      my_case Hir (PTree.get i r).
      2:{
      case_match.
      revert HeqH.
      case_match.
    }
  
  (*TODO: not true because arrays are non-canonical due to default elt*)
  Lemma get_set_same_existing (pa : trie_array positive) i
    :  trie_array_ok pa ->
       i < ArrayList.length pa -> set pa i (get pa i) = pa.
  Proof.
    destruct pa as [[? ?] ?]; simpl.
    intros [?] iltp; simpl in *.
    f_equal; f_equal.
    {
      unfold Pos.max.
      destruct (Pos.compare_spec p (i+1)); try Lia.lia.
    }
    case_match.
    2:{
    [|f_equal].
    cbn 
    unfold get, set.
    

  Lemma find_aux_path pa mr
    : forall i i' pa',
      i < ArrayList.length pa ->
        find_aux mr pa i = (pa', i') ->
        parent_path pa i i'.
  Proof.
    cbn [find_aux Natlike.iter NatlikePos.natlike_positive].
    revert pa.
    
    eapply Pos.peano_ind with (p:=mr);
      intros; break.
    {
      cbn -[get set] in H0.
      revert H0; case_match.
      {        
        basic_goal_prep;
          basic_utils_crush.
      }
      {
        destruct 
      }
    rewrite iter_succ in *; eauto.
    2:{
      apply is_top_spec; eauto.
    }
    revert H4; case_match.
    { 
      basic_goal_prep;
        basic_utils_crush.
    }
    remember (iter _ _ _ _ _) as loop.
    destruct loop.
    basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma max_rank_upper_bound u
    : union_find_ok u ->
      forall i, parent_degree_bound u.(parent) i u.(max_rank).
  Proof.
    intro H'; destruct H'.
    intro i.
    specialize (ranks_ok0 i).
    specialize (max_rank_ok0 i).
    clear len_same0.
    revert ranks_ok0 max_rank_ok0.
    generalize (get (rank u) i).
    induction 1.
    {
      constructor; eauto.
    }
    {
      econstructor 2; eauto.
      
    }

  Lemma find_aux_degree pa mr
    : forall i i' pa',
      find_aux mr pa i = (pa', i') ->
      (get pa' i = i' /\
      forall n j,
      parent_degree_bound pa j n ->
      parent_degree_bound pa' j n).
  Proof.
    revert pa.
    unfold find_aux.
    eapply natlike_ind with (n:=mr); auto;
      [ rewrite iter_zero in * |];
      basic_goal_prep;
      basic_utils_crush.
    rewrite iter_succ in *; eauto.
    2:{
      apply is_top_spec; eauto.
    }
    revert H4; case_match.
    { 
      basic_goal_prep;
        basic_utils_crush.
    }
    remember (iter _ _ _ _ _) as loop.
    destruct loop.
    basic_goal_prep;
      basic_utils_crush.
    symmetry in Heqloop.
    eapply H3 in Heqloop; eauto.
    TODO: need to know about i, i'

    Lemma decreasing_parent_degree_bound
      : parent_degree_bound pa j n ->
        parent_degree_bound (set pa i i') j n.
                             

    
  Lemma find_aux_sound pa mr
    : (forall i j, parent_degree pa i j -> leb j mr = true) ->
      forall i i' pa',
        find_aux mr pa i = (pa', i') ->
        equivalence_closure (fun a b => get pa a = b) i i'.
  Proof.
    unfold find_aux.
    revert pa.
    eapply natlike_ind with (n:=mr); auto;
      [ rewrite iter_zero in * |];
      basic_goal_prep;
      basic_utils_crush.
    rewrite iter_succ in *; eauto.
    2:{
      apply is_top_spec; eauto.
    }
    {
      revert H5; case_match.
      { 
        basic_goal_prep;
          basic_utils_crush.
      }
      remember (iter _ _ _ _ _) as loop.
      destruct loop.
      basic_goal_prep;
        basic_utils_crush.
      eapply H3; eauto.
      case_match'.
      eapply eq_clo_trans.
      rewrite iter_zero in H3.
      
      simpl in *.
    }
    auto.
    
    induction mr.
 
  Lemma find_sound u i u' i'
    : union_find_ok u -> find u i = (u', i') -> EqClo u i i'.
  Proof.
    destruct u.
    unfold find.
    unfold find_aux, union_find_ok.
    simpl.
    revert max_rank0 rank0 parent0.
    eapply natlike_ind; eauto.
    intros.
      with (n:=max_rank0).

    induction max_rank0.


  TODO: generalize proofs to any unionfind
*)

End PositiveUnionFind.
