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

(*
Definition eq_conv : forall A, A -> forall B, B -> Prop.
  intros A a B b.
  refine {Heq : A = B | _}.
  rewrite Heq in a; (exact (a = b)).
Defined. *)

Section Inner.
  
  Context (subst_n : nat -> forall A : Type, A -> Type).
  Fixpoint ctx_n (n : nat) : Type :=
    match n with
    | 0 => unit
    | S n0 => {c : ctx_n n0 & subst_n n0 c -> Type}
    end.

End Inner.

Set Definitional UIP.

Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.

Arguments srefl {_ _}.


Definition conv {A B} (Heq : seq A B) : A -> B :=
  match Heq in seq _ B return A -> B with srefl => @id _ end.

Inductive sigST (A : SProp) (P : A -> Type) : Type :=  existST : forall x : A, P x -> @sigST A P.

Arguments sigST [A]%type_scope P%type_scope.
Arguments existST [A]%type_scope P%function_scope x _.

Fixpoint subst_n (n : nat) A (a : A) {struct n} : Type :=
  let ctx_n := ctx_n subst_n in
  match n with
  | 0 => unit
  | S n' =>
      @sigST (seq A (ctx_n (S n')))
            (fun Heq =>
               let c := conv Heq a in
               {s : subst_n n' (projT1 c) & projT2 c s})
  end.


Definition ctx := { n & ctx_n subst_n n}.
Definition subst (c : ctx) := subst_n (projT1 c) (projT2 c).

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

(*TODO: make a better defn for computation*)
Definition ctx_rect {P : _ -> Type}
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
Defined.

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
    let (n, c) as c return (forall (s : subst c) (A : subst c -> Type),
                        A s -> subst (ctx_cons c A)) := c
    in fun s _ e => existST _ srefl {#s; e #}.

(*
Require Import Eqdep.
Import EqdepTheory.*)
(*
Lemma conv_id {A} (p : A = A) x : conv p x = x.
Proof.
  unfold conv.
  replace p with (eq_refl A); auto.
  apply UIP.
Qed.
*)

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
    destruct s as [Heq [s e]].

    simpl in Heq.
    match goal with
      [Heq : seq ?A ?A |- _] =>
        change Heq with (@srefl _ A) in *
    end.
    simpl in *.
    specialize (P_cons {#n;c#} s A e).
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
    destruct s as [Heq [s e]].

    simpl in Heq.
    match goal with
      [Heq : seq ?A ?A |- _] =>
        change Heq with (@srefl _ A) in *
    end.
    simpl in *.
    specialize (P_cons {#n;c#} s A e).
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

(*
Require Import Program.Basics.

Local Open Scope program_scope.*)

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

(*
(*TODO: check that this computes*)
Definition subst_tl' n
  : forall (c : ctx_n subst_n n),
    msubst {# n; c #} (ctx_tl {# n; c #}).
  refine (
      match n as n
            return forall (c : ctx_n subst_n n),
          msubst {# n; c #} (ctx_tl {# n; c #})
      with
      | 0 => fun _ _ => tt
      | S n0 =>
          fun c =>
            let (c, A) as c return msubst {# S n0; c #} (ctx_tl {# S n0; c #})
              := c in  _
      end).
  simpl in c.
  intro s.
  simpl.
  destruct s.
  revert x s.
  simpl.
  eapply projT1.
Defined.

Definition subst_tl : forall (c : ctx), msubst c (ctx_tl c).
  refine (fun c => _).
  destruct c.
  (*TODO: universe issues with this:
  refine (let (n,c') as c return msubst c (ctx_tl c) := c in _).*)
  refine (fun s => _).
  eapply subst_tl'; eauto.
Defined.
*)


(* for convenience so that code can use names, not projections
open [nat;fun s => Vec (proj2 s)] (fun s => len (proj2 s) = proj2 (proj1 s))
=>
forall (x : nat) (v : Vec x), len v = x

 *)
Definition open : forall (c : ctx) (A : sort c), Type :=
  (ctx_rect (fun A => A subst_nil)
   (fun c (B : sort c) open (A : sort (ctx_cons c B)) =>
      open (fun s : subst c => forall x : B s, A (subst_cons c s B x)))).

Definition apply_subst : forall (c : ctx) (s : subst c) (A : sort c), open _ A -> A s.
  refine (subst_rect (fun A oa => oa) (fun c =>_)).
  destruct c.
(*  refine (let (n,c) as c return forall (s : subst c) (A : sort c) (e : A s),
                           (forall A0 : sort c, open c A0 -> A0 s) ->
                           forall A0 : sort (ctx_cons c A), open (ctx_cons c A) A0 -> A0 (subst_cons c s A e) := c in _).*)
  intros s A e apply_subst B OB.
  refine (apply_subst _ OB _).
Defined.

Lemma open_ctx_cons c B A
  : open (ctx_cons c B) A = open _ (fun s : subst c => forall x : B s, A (subst_cons c s B x)).
Proof.
  destruct c.
  simpl.
  reflexivity.
Qed.

Definition term_to_open : forall (c : ctx) (A : sort c), term c A -> open _ A.
  refine (ctx_rect (fun _ b => b _) _).
  destruct c.
  intros A term_to_open B e.
  eapply term_to_open.
  intros s a.
  eapply e.
Defined.


Definition open_to_term : forall (c : ctx) (A : sort c), open _ A -> term c A.
  intros; eapply apply_subst; eassumption.
Defined.

Notation "## |- A" := A (at level 80).

Check (open |##| (open_to_term |##| _ nat)).
(*TODO: does not compute away as I'd want; blocked on UIP_refl*)
Require Fin.
Compute (open |# (fun _ => nat) #| (open_to_term |# fun _ => nat #| _ (fun n => Fin.t n))).

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
