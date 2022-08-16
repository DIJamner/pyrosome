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

Definition conv {A B} (Heq : A = B) : A -> B :=
  match Heq in _ = B return A -> B with eq_refl => @id _ end.

Fixpoint subst_n (n : nat) A (a : A) {struct n} : Type :=
  let ctx_n := ctx_n subst_n in
  match n with
  | 0 => unit
  | S n' =>
      {Heq : A = ctx_n (S n') &
               let c := conv Heq a in
               {s : subst_n n' (projT1 c) & projT2 c s}}
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
    in fun s _ e => {#eq_refl; s; e #}.

Require Import Eqdep.
Import EqdepTheory.
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

    simpl in *.
    revert Heq s e.
    refine (Streicher_K _ _ _ _).
    simpl.
    intros.
    change {# eq_refl; s; e #} with (subst_cons {# n; c #} s A e).
    change {# S n; c; A #} with (ctx_cons {# n; c #} A).
    eapply P_cons.
    eapply IHn.
  }
Qed.

Definition eq_rect_r
  : forall (A : Type) (x : A) (P : A -> Type), P x -> forall y : A, y = x -> P y :=
  fun (A : Type) (x : A) P (H : P x) (y : A) (H0 : y = x) =>
    eq_rect x (fun y0 : A => P y0) H y (eq_sym H0).

Definition Type_Streicher_K_on_ := 
fun (U : Type) (x : U) (P : x = x -> Type) => P eq_refl -> forall p : x = x, P p.

Definition Type_UIP_refl_on__Streicher_K_on
  : forall (U : Type) (x : U) (P : x = x -> Type), UIP_refl_on_ U x -> Type_Streicher_K_on_ P
  := 
  fun (U : Type) (x : U) P (UIP_refl : UIP_refl_on_ U x) (H : P eq_refl) (p : x = x) =>
    eq_rect_r P H (UIP_refl p).

Definition Type_Streicher_K_ := fun U : Type => forall (x : U) (P : x = x -> Type), Type_Streicher_K_on_ P.

Definition Type_UIP_refl__Streicher_K
  : forall U : Type, UIP_refl_ U -> Type_Streicher_K_ U
  := 
  fun (U : Type) (UIP_refl : UIP_refl_ U) (x : U) (P : x = x -> Type) =>
    Type_UIP_refl_on__Streicher_K_on P (UIP_refl x).

Definition Type_Streicher_K : forall (U : Type) (x : U) (P : x = x -> Type), P eq_refl -> forall p : x = x, P p :=
  fun U : Type => Type_UIP_refl__Streicher_K (UIP_refl U).

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

    simpl in *.
    revert Heq s e.
    refine (Type_Streicher_K _ _).
    simpl.
    intros.
    change {# eq_refl; s; e #} with (subst_cons {# n; c #} s A e).
    change {# S n; c; A #} with (ctx_cons {# n; c #} A).
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
  refine (Type_Streicher_K _ _).
  simpl.
  eapply projT1.
Defined.
  
Definition subst_tl : forall (c : ctx), msubst c (ctx_tl c).
  refine (fun c => _).
  refine (let (n,c') as c return msubst c (ctx_tl c) := c in _).
  refine (fun s => _).
  eapply subst_tl'; eauto.
  TODO: universe issues
Defined.


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
