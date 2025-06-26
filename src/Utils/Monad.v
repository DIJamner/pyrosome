Set Implicit Arguments.

Require Lists.List.
From Utils Require Import Utils.

Class Monad (M : Type -> Type) : Type :=
  {
  Mret : forall {A}, A -> M A;
  Mbind : forall {A B}, (A -> M B) -> M A -> M B
  }.

Definition Mseq {M} `{Monad M} {A B} (mu : M A) (ma : M B) : M B :=
  Mbind (fun _ => ma) mu.

Declare Custom Entry monadic_do.

(* I would use 'do', but it interferes with proof general indentation *)
Notation "@! e" := (e) (at level 200, e custom monadic_do).


Notation "'let' p <- e 'in' b" :=
  (Mbind (fun p => b) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

(*TODO: add fail
(* Uses the partiality of fail to perform additional matching where desired *)
Notation "p <?- e ; b" :=
  (Mbind (fun x => match x with p => b | _ => Mfail end) e)
    (in custom monadic_do at level 90, left associativity, p pattern at level 0, e constr, b custom monadic_do).
*)

(*TODO: this notation prints too readily*)
Notation "'let' p := e 'in' b" :=
  (let p := e in b)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do, only parsing).


Notation "'let' p <?- e 'in' b" :=
  (Mbind (fun x => match x with p => b | _ => default end) e)
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).

Notation "'let' ! e 'in' b" :=
  (if e then b else default)
    (in custom monadic_do at level 200, left associativity, e constr, b custom monadic_do).

Notation "'if' c 'then' b1 'else' b2" :=
  (if c then b1 else b2)
    (in custom monadic_do at level 200, left associativity,
        c constr, b1 custom monadic_do, b2 custom monadic_do, only parsing).

Notation "e1 ; e2" :=
  (Mseq e1 e2)
    (in custom monadic_do at level 100, left associativity,
        e1 custom monadic_do,
        e2 custom monadic_do).

Notation "'ret' e" := (Mret e) (in custom monadic_do at level 90, e constr).

Notation "e" := e (in custom monadic_do at level 90, e constr at level 0).

(* For disambiguation (usually debugging) *)
Notation "'ret' { M } e" :=
  (Mret (M:=M) e)
    (in custom monadic_do at level 90, e constr, only parsing).

Notation "'let' { M } p <- e 'in' b" :=
  (Mbind (M:=M) (fun p => b) e)
    (in custom monadic_do at level 200, left associativity,
        p pattern at level 0, e constr, b custom monadic_do,
        only parsing).

Notation "'let' { M } p <?- e 'in' b" :=
  (Mbind (M:=M) (fun x => match x with p => b | _ => default end) e)
    (in custom monadic_do at level 200, left associativity,
        p pattern at level 0, e constr, b custom monadic_do,
        only parsing).

(*
Notation "! e ; b" :=
  (if e then b else Mfail)
    (in custom monadic_do at level 90, left associativity, e constr, b custom monadic_do).
TODO: add fail
*)

Generalizable Variable M.
Definition Mfmap `{mmon:Monad M} {A B} (f : A -> B) (ma: M A) : M B :=
  @! let a <- ma in ret f a.

(*TODO: move these into separate files? *)

Section MonadListOps.
  Import List List.ListNotations.
  Context {M} {A B : Type} `{Monad M}.

  Fixpoint list_Mfoldl (f : B -> A -> M B) (l : list A) (acc : B) : M B :=
    match l with
    | [] => @! ret acc
    | a::al' =>
        @! let fab <- f acc a in
          (list_Mfoldl f al' fab)
    end.

  
  Fixpoint list_Mfoldr (f : A -> B -> M B) (l : list A) (base : B) : M B :=
    match l with
    | [] => @! ret base
    | a::al' =>
        @! let base' <- list_Mfoldr f al' base in
          (f a base')
    end.

  Section __.
    Context (f : A -> M B).
    Fixpoint list_Mmap (l : list A) : M (list B) :=
      match l with
      | [] => @! ret []
      | a::al' =>
          @! let b <- f a in
            let bl' <- list_Mmap al' in
            ret (b::bl')
      end.
    
  Fixpoint list_Miter (l : list A) : M unit :=
    match l with
    | [] => @! ret tt
    | a::al' => Mseq (f a) (list_Miter al')
    end.
  End __.
  
  Fixpoint list_Miter_idx' (f : nat -> A -> M unit) (l : list A) n : M unit :=
    match l with
    | [] => @! ret tt
    | a::al' =>
        @! let b <- f n a in
           let tt <- list_Miter_idx' f al' (S n) in
           ret tt
    end.

  Definition list_Miter_idx  (f : nat -> A -> M unit) (l : list A) := list_Miter_idx' f l 0.
  
End MonadListOps.



Class MonadTrans (T : (Type -> Type) -> Type -> Type) : Type :=
  {
    transformer_monad :: forall `{Monad M}, Monad (T M);
    lift : forall `{Monad M} {A}, M A -> T M A
  }.

#[export] Instance id_monad : Monad id :=
  {
    Mret _ a := a;
    Mbind _ _ f := f;
  }.


Notation "'let' p <^- e 'in' b" :=
  (Mbind (fun p => b) (lift e))
    (in custom monadic_do at level 200, left associativity, p pattern at level 0, e constr, b custom monadic_do).


Definition optionT (M : Type -> Type) A := M (option A).

#[export] Instance optionT_trans : MonadTrans optionT :=
  {|
    transformer_monad M _ :=
      {|
        Mret _ a := (Mret (Some a));
        Mbind _ _ f :=
          Mbind (M:=M) (fun ma => match ma with
                                      | Some a => f a
                                      | None => Mret None
                                      end)
      |};
  lift M _ A ma := @! let a <- ma in ret Some a
  |}.


Definition option_monad : Monad option :=
  Eval cbv in (optionT_trans.(transformer_monad) : Monad (optionT id)).
#[export] Existing Instance option_monad.

From coqutil Require Map.Interface.

Module StateMonad.

  Section WithS.

  Context {S : Type}.

  Definition stateT M A := S -> M (A * S)%type.

  #[export] Instance stateT_trans : MonadTrans stateT :=
    {|
      transformer_monad M _ :=
        {|      
          Mret _ a := fun s => Mret (a,s);
          Mbind _ _ f :=
            Basics.compose (Mbind (uncurry f))
        |};
      lift M _ A ma s := Mbind  (fun x => Mret (x,s)) ma
    |}.

  Definition state := Eval cbv in stateT id.
  
  Definition state_monad : Monad state :=
    Eval cbv in (stateT_trans.(transformer_monad) : Monad (stateT id)).
  #[export] Existing Instance state_monad.

  
  (*TODO: double check this is the right name*)
  (* backtracks the state if ma returns None *)       
  Definition try_with_backtrack {A}
             (ma : optionT (stateT id) A) :  optionT (stateT id) A :=
    fun g =>
      match ma g with
      | (Some a, g') => (Some a, g')
      | (None,_) => (None, g)
      end.
  
  Section MapOps.
    
    Import Map.Interface.
    
    Definition map_Mfold {K V A}
               {MP : map.map K V}
               (f : K -> V -> A -> state A)
               (p : @map.rep _ _ MP) a : state A :=
      fun g =>
        map.fold
          (fun '(a, g) k v => f k v a g)
          (a, g) p.

    Definition map_Miter {K V}
               {MP : map.map K V}
               (f : K -> V -> state unit)
               (p : @map.rep _ _ MP) : state unit :=
      map_Mfold (fun k v _ => f k v) p tt.

  End MapOps.

  
  (* Hoare logic reasoning about the state monad *)
  Definition state_triple {A} (P : S -> Prop) (c : state A) (Q : A * S -> Prop) :=
    forall e, P e -> Q (c e).

  
  Lemma state_triple_bind A B P Q H (f : A -> state B) c
    : state_triple P c Q ->
      (forall a, state_triple (curry Q a) (f a) H) ->
      state_triple P (Mbind f c) H.
  Proof.
    unfold curry, state_triple, Mbind in *.
    cbn.
    intuition eauto.
    specialize (H0 e).
    specialize (H1 (fst (c e)) (snd (c e))).
    destruct (c e); cbn in *.
    apply H1.
    eauto.
  Qed.

  
  Lemma state_triple_ret A (a:A) P
    : state_triple P (@! ret a) (fun p => (fst p = a) /\ P (snd p)).
  Proof.
    unfold state_triple.
    cbn; eauto.
  Qed.

  Lemma state_triple_wkn_post A P e (Q1 Q2 : A * S -> Prop)
    : (forall p, Q1 p -> Q2 p) ->
      state_triple P e Q1 ->
      state_triple P e Q2.
  Proof.
    unfold state_triple; firstorder.
  Qed.

  Lemma state_triple_wkn_ret A (a:A) P (Q : _ -> Prop)
    : (forall p, fst p = a /\ P (snd p) -> Q p) ->
        state_triple P (@! ret a) Q.
  Proof.
    intros.
    eapply state_triple_wkn_post.
    2: apply state_triple_ret.
    firstorder.
  Qed.
  

  Lemma state_triple_strengthen_pre A (P1 P2 : _ -> Prop) e (Q: A * S -> Prop)
    : (forall i, P1 i -> P2 i) ->
      state_triple P2 e Q ->
      state_triple P1 e Q.
  Proof.
    unfold state_triple; firstorder.
  Qed.

  Lemma state_triple_loosen A (P1 P2 : _ -> Prop) e (Q1 Q2 : A * S -> Prop)
    : (forall p, Q1 p -> Q2 p) ->
      (forall i, P1 i -> P2 i) ->
      state_triple P2 e Q1 ->
      state_triple P1 e Q2.
  Proof.
    intros; eapply state_triple_strengthen_pre; eauto.
    eapply state_triple_wkn_post; eauto.
  Qed.

  Lemma state_triple_lift_pre A (H : Prop) P e (Q: A * S -> Prop)
    : (H -> state_triple P e Q) ->
      state_triple (fun i => H /\ P i) e Q.
  Proof.
    unfold state_triple; firstorder.
  Qed.

  
  Lemma state_triple_lift_post A (H : Prop) P e (Q: A * S -> Prop)
    : H ->
      state_triple P e Q ->      
      state_triple P e (fun p => H /\ Q p).
  Proof.
    unfold state_triple; firstorder.
  Qed.

  
  Lemma state_triple_frame_const A H P e (Q: A * S -> Prop)
    : state_triple P e Q -> 
      state_triple (fun i => H /\ P i) e (fun p => H /\ Q p).
  Proof.
    intros. apply state_triple_lift_pre.
    intros. apply state_triple_lift_post; eauto.
  Qed.

  
  Lemma state_triple_list_Mmap1 A B (f : A -> state B) l P
    : (forall l1 a l2, l = l1 ++ a::l2 -> state_triple (P (a::l2)) (f a) (fun p => P l2 (snd p))) ->
      state_triple (P l) (list_Mmap f l) (fun p => P nil (snd p)).
  Proof.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_goal_prep; subst.
      eauto.
    }
    {
      cbn [all list_Mmap]; intros; break.
      eapply state_triple_bind; eauto.
      {
        apply H with (l1:=nil).
        reflexivity.
      }
      {
        unfold curry.
        intro a0.
        eapply state_triple_bind; eauto.
        {
          apply IHl.
          intros.
          eapply H with (l1:=a::l1).
          cbn; congruence.
        }
        intro l'.
        eapply state_triple_wkn_ret.
        basic_goal_prep; eauto.
      }
    }
  Qed.

  (* TODO: loses some info about the provenance of fl1; ok? *)
  Lemma state_triple_list_Mmap2 A B (f : A -> state B) l Q fl
    : (forall fl1 a, List.In a l ->
                     state_triple (Q fl1) (f a) (fun p => Q (fl1++(cons (fst p) nil)) (snd p))) ->
      state_triple (Q fl) (list_Mmap f l) (fun p => Q (fl++fst p) (snd p)).
  Proof.
    revert fl.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_utils_crush.
    }
    {
      cbn [all list_Mmap]; intros; break.
      eapply state_triple_bind; [basic_utils_crush |].
      unfold curry.
      intro b.
      eapply state_triple_bind; unfold curry.     
      { intros; cbn in *; eauto. }
      {
        intros.
        eapply state_triple_wkn_ret.
        basic_goal_prep; subst.
        rewrite <- List.app_assoc in H1.
        eauto.
      }
    }
  Qed.

  Lemma state_triple_conjunction A (c : state A) P1 P2 Q1 Q2
    : state_triple P1 c Q1 ->
      state_triple P2 c Q2 ->
      state_triple (fun e => P1 e /\ P2 e) c (fun e => Q1 e /\ Q2 e).
  Proof.
    unfold state_triple.
    intuition eauto.
  Qed.

  Lemma state_triple_list_Mmap' A B (f : A -> state B) l P fl
    : (forall fl1 l1 a l2, l = l1 ++ a::l2 ->
                           state_triple (fun e => P (a::l2) fl1 e)
                             (f a)
                             (fun p => P l2 (fl1++(cons (fst p) nil)) (snd p))) ->
      state_triple (fun e => P l fl e) (list_Mmap f l) (fun p => P nil (fl++fst p) (snd p)).
  Proof.
    revert fl.
    induction l.
    {
      cbn; intros.
      eapply state_triple_wkn_ret.
      basic_goal_prep; subst.
      basic_utils_crush.
    }
    {
      cbn [all list_Mmap]; intros; break.
      eapply state_triple_bind.
      { eapply H with (l1:=nil); eauto. }
      unfold curry.
      intro b.
      eapply state_triple_bind; unfold curry.     
      {
        intros; cbn in *.
        eapply IHl; intros.
        eapply H with (l1:=a::l1).
        cbn.
        congruence.
      }
      {
        intros.
        eapply state_triple_wkn_ret.
        basic_goal_prep; subst.
        rewrite <- List.app_assoc in *.
        eauto.
      }
    }
  Qed.

  
  Lemma state_triple_list_Mmap A B (f : A -> state B) l P
    : (forall fl1 l1 a l2, l = l1 ++ a::l2 ->
                           state_triple (fun e => P (a::l2) fl1 e)
                             (f a)
                             (fun p => P l2 (fl1++(cons (fst p) nil)) (snd p))) ->
      state_triple (fun e => P l nil e) (list_Mmap f l) (fun p => P nil (fst p) (snd p)).
  Proof. apply state_triple_list_Mmap'. Qed.

  End WithS.

  Notation "'for' kp vp 'from' m 'in' b" :=
    (map_Miter (fun kp vp => b) m)                       
      (in custom monadic_do at level 200, left associativity,
          kp pattern at level 0,
          vp pattern at level 0,
          m constr, b custom monadic_do).
  
  Notation "'for/fold' kp vp 'from' m [[ acc := a ]] 'in' b" :=
    (map_Mfold (fun kp vp acc => b) m a)                    
      (in custom monadic_do at level 200, left associativity,
          kp pattern at level 0,
          vp pattern at level 0,
          acc pattern at level 0,
          m constr, b custom monadic_do).
  
  Arguments stateT S%type_scope M%function_scope A%type_scope : clear implicits.
  Arguments state S%type_scope A%type_scope : clear implicits.

  
End StateMonad.

