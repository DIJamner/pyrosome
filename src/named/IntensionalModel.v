Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.


(* What I want:
Inductive ctx : Type :=
| ctx_nil : ctx
| ctx_cons : forall c : ctx, (subst c -> Type) -> ctx
with subst : ctx -> Type :=
| subst_nil : subst ctx_nil
| subst_cons c (s : subst c) (A : subst c -> Type) : A s -> subst (ctx_cons c A).

But: can't have ctx in type of subst
 *)

Require Import JMeq.

(*
Definition eq_conv : forall A, A -> forall B, B -> Prop.
  intros A a B b.
  refine {Heq : A = B | _}.
  rewrite Heq in a; (exact (a = b)).
Defined. *)

Section Inner.
  
  Context (subst_n : nat -> (forall A : Type, A -> Prop) -> Type).
  Fixpoint ctx_n (n : nat) : Type :=
    match n with
    | 0 => unit
    | S n0 => {c : ctx_n n0 & subst_n n0 (JMeq c) -> Type}
    end.

End Inner.

Fixpoint subst_n (n : nat) (P : forall A : Type, A -> Prop) : Type :=
  let ctx_n := ctx_n subst_n in
  match n with
  | 0 => unit
  | S n' => {c : ctx_n (S n') & {_ : P (ctx_n (S n')) c & {s : subst_n n' (JMeq (projT1 c)) & projT2 c s}}}
  end.

Definition ctx := { n & ctx_n subst_n n}.
Definition subst (c : ctx) := subst_n (projT1 c) (JMeq (projT2 c)).

    

Definition ctx_nil : ctx := existT _ 0 tt.
Definition ctx_cons : forall (c : ctx), (subst c -> Type) -> ctx :=
  fun c => let (n, cn) as c return ((subst c -> Type) -> ctx) := c in
           (fun A => existT _ (S n) (existT _ cn A)).
(* Note: this fails: *)
Fail Definition ctx_cons' (c : ctx) : (subst c -> Type) -> ctx :=
  let (n, cn) as c return ((subst c -> Type) -> ctx) := c in
  (fun A => existT _ (S n) (existT _ cn A)).

Lemma ctx_ind {P : _ -> Prop}
  (P_nil : P ctx_nil)
  (P_cons : forall c A, P c -> P (@ctx_cons c A))
  : forall c : ctx, P c.
Proof.
  destruct c as [n c].
  revert c.
  induction n; simpl; intros.
  {
    destruct c.
    eapply P_nil.
  }
  {
    destruct c.
    specialize (P_cons (existT _ n x)).
    eapply P_cons.
    eauto.
  }
Qed.

(*
Lemma eq_conv_refl {A} {a : A} : eq_conv a a.
Proof.
  unshelve esplit; reflexivity.
(* TODO: It might be important to use defined here for dependently-typed computation. Check*)
Qed.*)

Notation "{# x1 #}" := x1.
                               
Notation "{# x1 ; .. ; xn ; xr #}" :=
  (existT _ x1 .. (existT _ xn xr) ..)
    (format "'{#'  '[hv' x1 ;  .. ;  xn ;  xr ']'  '#}'").

Definition subst_nil : subst ctx_nil := tt.
Definition subst_cons : forall (c : ctx) (s : subst c) (A : subst c -> Type) (e : A s), subst (@ctx_cons c A) :=
  fun c : ctx =>
    let (n, c) as s return (forall (s0 : subst s) (A : subst s -> Type),
                        A s0 -> subst (ctx_cons s A)) :=
      c
    in (fun s A e => existT _ (existT _ c A) (existT _ JMeq_refl (existT _ s e))).

(*TODO: either go back to eq_conv, prove this from UIP,
  or find a way to discharge it
 *)
Axiom JMeq_UIP_refl
  : forall (U : Type) (x : U) (p : JMeq x x), p = JMeq_refl.

Lemma subst_ind {P : forall {c : ctx}, subst c -> Prop}
  (P_nil : P subst_nil)
  (P_cons : forall c (s : subst c) A e, P s -> P (subst_cons c s A e))
  : forall c (s : subst c), P s.
Proof.
  destruct c as [n c].
  revert c.
  induction n; simpl; intros.
  {
    destruct c.
    destruct s.
    eapply P_nil.
  }
  {
    destruct c as [c A].
    destruct s as [c' [Heq [s e]]].
    destruct c'.
    simpl in *.
    pose proof (Heq' := Heq).
    apply JMeq_eq in Heq'.
    inversion Heq'.
    subst.
    clear H1.
    assert (A = T) by (apply Eqdep.EqdepTheory.inj_pair2 in Heq'; auto).
    subst.
    clear Heq'.
    rewrite (JMeq_UIP_refl Heq).
    clear Heq.
    
    specialize (P_cons (existT _ n x) s).
    eapply P_cons.
    eapply IHn.
  }
Qed.


(* TODO: make a version with a good definition for computing*)
Lemma subst_rect {P : forall {c : ctx}, subst c -> Type}
  (P_nil : P subst_nil)
  (P_cons : forall c (s : subst c) A e, P s -> P (subst_cons c s A e))
  : forall c (s : subst c), P s.
Proof.
  destruct c as [n c].
  revert c.
  induction n; simpl; intros.
  {
    destruct c.
    destruct s.
    eapply P_nil.
  }
  {
    destruct c as [c A].
    destruct s as [c' [Heq [s e]]].
    destruct c'.
    simpl in *.
    pose proof (Heq' := Heq).
    apply JMeq_eq in Heq'.
    inversion Heq'.
    subst.
    clear H1.
    assert (A = T) by (apply Eqdep.EqdepTheory.inj_pair2 in Heq'; auto).
    subst.
    clear Heq'.
    rewrite (JMeq_UIP_refl Heq).
    clear Heq.
    
    specialize (P_cons (existT _ n x) s).
    eapply P_cons.
    eapply IHn.
  }
Defined.

(*TODO: naming on closed vs open subst*)


Notation sort c := (subst c -> Type).

Notation term c t := (forall s : subst c, t s).

Notation msubst c c' := (subst c -> subst c').


Notation "|# #|" := ctx_nil.
                               
Notation "|# x1 ; .. ; xn #|" :=
  (ctx_cons .. (ctx_cons ctx_nil x1) .. xn)
    (format "'|#'  '[hv' x1 ;  .. ;  xn ']'  '#|'").


Require Import Program.Basics.

Local Open Scope program_scope.

(*TODO: return an option?*)
Definition ctx_tl' n : ctx_n subst_n n -> ctx_n subst_n (pred n) :=
  match n as n' return ctx_n subst_n n' -> ctx_n subst_n (pred n') with
  | 0 => fun c => tt
  | S _ => @projT1 _ _
  end.

Definition ctx_tl (c : ctx) : ctx :=
  let (n, c') := c in
  {# pred n; ctx_tl' n c' #}.


Definition ctx_hd' n
  : forall (c : ctx_n subst_n n),
    sort {# pred n; ctx_tl' n c #} :=
    match n as n
          return forall (c : ctx_n subst_n n),
        sort {# pred n; ctx_tl' n c #}
    with
    | 0 => fun c s => False
    | S _ => @projT2 _ _
    end.

Definition ctx_hd : forall (c : ctx), sort (ctx_tl c) :=
  fun c =>
  let (n, c') as c' return sort (ctx_tl c') := c in ctx_hd' _ _.

Definition subst_tl' n
  : forall (c : ctx_n subst_n n),
    msubst {# n; c #} (ctx_tl {# n; c #}).
  refine (
    match n as n
          return forall (c : ctx_n subst_n n),
        msubst {# n; c #} (ctx_tl {# n; c #})
    with
    | 0 => fun c => id
    | S _ => fun c => _
    end).
  simpl in c.
  refine
    (let (c, A) as c return msubst {# S n0; c #} (ctx_tl {# S n0; c #})
       := c in  _).
  simpl in *.
  intro s.
  unfold subst in *.
  clear c0.
  simpl in *.
  destruct s.
  destruct x.
  destruct s.
  assert (c = x).
  {
    refine (match x0 in JMeq {# c; A #} {# x; T #}
                  return c = x with
            | _ => _
            end).
    destruct x0.
    inversion x0.
  in
  refine (let (n,c') as c return msubst c (ctx_tl c) := c in _)
  
  refine (projT2 _).
  {
    simpl.
    e
  refine (fun c => _).
  refine (let (n,c') as c return msubst c (ctx_tl c) := c in _).
  
Definition subst_tl : forall (c : ctx), msubst c (ctx_tl c).
  refine (fun c => _).
  refine (let (n,c') as c return msubst c (ctx_tl c) := c in _).
  refine (fun s => _).
  simpl.


(* TODO: make a version with a good definition for computing*)
Definition mwkn : forall (c : ctx) A, subst (ctx_cons c A) -> subst c.
  intro c.
  refine (let (n, c') as c return forall A : subst c -> Type, subst (ctx_cons c A) -> subst c := c in _).
  intros A s.
  unfold subst in *.
  simpl in *.
  refine (let (c, s0) := s in _).
  destruct c.
  destruct s0.
  (*TODO: lemma for inverting JMeq*)
  simpl in *.
  
    pose proof (Heq' := x0).
    apply JMeq_eq in Heq'.
    inversion Heq'.
    subst.
    destruct s0; auto.
    (*TODO: Universes
Defined.*)
Admitted.
Arguments mwkn {_} {_}.
  

(*TODO: difference between meta- and object-level substs. Need to make env sim. to ctx, but w/ open metavars.
Trying to reuse meta defns here.
 *)
Definition env : sort |##| := fun s => ctx.
(*TODO: need explicit weakening at the meta-level*)
Definition sub : sort |# env; env ∘ mwkn #|.
refine (fun s => _).
unfold subst in *.
simpl in *.
                                          


Definition hd : forall (c: ctx) A, term (ctx_cons c A) (ty_subst wkn A)
  
  refine (let '{# c; Heq; s; _ #} := s in _).
  

Definition wkn c A : subst (ctx_cons c A) -> subst c.
  refine 
  intro s.
  
  refine (let '{# c; Heq; s; _ #} := s in _).
  refine (subst_rect (P:=fun _ _ => subst c) _ _ _ s).
  {
    admit.
  }
  {
    auto.
  }
  Show Proof.
  unfold subst in *.
  simpl in *.
  intro s.
  refine (let '{# c'; Heq; s'; _ #} := s in _).
  destruct c'; simpl in *.
  inversion Heq.
  inversion H0.
  exact s'.
  refine (
  Show Proof.
  constructor.

Definition wkn c A : subst (ctx_cons c A) -> subst c.
  refine (let (n, c) as s return  subst (ctx_cons s A) -> subst s := c in _).
  destruct c.
  simpl.
  Show Proof.
  intro s.
  unfold ctx_cons in *.
  simpl.
  destruct s.
    as [s _].
