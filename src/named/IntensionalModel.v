Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Substable Model Compilers.
From Named Require Term.


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
