(* ===================================================================== *)
(* PHASE-0 PROTOTYPE (throwaway, NOT in the build).                        *)
(*                                                                        *)
(* Self-contained mini-domain that prototypes the Phase-0 design:          *)
(* ANNOTATED neutral applications [nApp f F B a] (F = domain code, B =      *)
(* codomain code under one binder), with the Pi type components (F,B)       *)
(* THREADED as indices through [Vapp]/[Apply_ne].  The two questions this   *)
(* answers before touching the real Domain.v:                              *)
(*   (1) does threading (F,B) through [Vapp] keep [Apply] DETERMINISTIC?    *)
(*   (2) does the annotated [refl_Pi] keep [Reflect] DETERMINISTIC?         *)
(* (The third risk -- the refl_Pi codomain reconciliation -- is ALREADY     *)
(* solved in the real ApplySubst.v as [Apply_reflect_cod], so it is out of  *)
(* scope here.)                                                             *)
(* ===================================================================== *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

(* --- minimal value domain (relevant fragment only; the I-variants are
       structurally identical and add nothing to the threading question) --- *)
Unset Elimination Schemes.
Inductive svalty : Type :=
| dU
| dEl (e : sval)
with sval : Type :=
| vNe   (n : neutral)
| vNat
| vEmpty
| vPi   (F B : sval)
| vLam  (b : sval)
with neutral : Type :=
| nVar  (k : nat)
| nApp  (f : neutral) (F B : sval) (a : sval).   (* <-- ANNOTATED with (F,B) *)
Set Elimination Schemes.

Scheme svalty_rect := Induction for svalty Sort Type
  with sval_rect   := Induction for sval   Sort Type
  with neutral_rect := Induction for neutral Sort Type.

(* cutoff-indexed shift; the codomain annotation [B] sits under one binder,
   so it shifts at [S c] exactly like a [vPi] codomain. *)
Fixpoint shift_val (c d : nat) (v : sval) : sval :=
  match v with
  | vNe n => vNe (shift_ne c d n)
  | vNat => vNat
  | vEmpty => vEmpty
  | vPi F B => vPi (shift_val c d F) (shift_val (S c) d B)
  | vLam b => vLam (shift_val (S c) d b)
  end
with shift_ne (c d : nat) (n : neutral) : neutral :=
  match n with
  | nVar k => nVar (if Nat.ltb k c then k else k + d)
  | nApp f F B a =>
      nApp (shift_ne c d f) (shift_val c d F) (shift_val (S c) d B) (shift_val c d a)
  end.

Definition ssub := list sval.
Definition id_list  (n : nat) : ssub := map (fun k => vNe (nVar k)) (seq 0 n).
Definition wkn_list (n : nat) : ssub := map (fun k => vNe (nVar (S k))) (seq 0 n).
Definition up (s : ssub) : ssub := vNe (nVar 0) :: map (shift_val 0 1) s.

(* --- relational hereditary substitution + application, (F,B)-THREADED --- *)
Inductive Apply_val : nat -> ssub -> sval -> sval -> Type :=
| ap_ne    : forall m s n v, Apply_ne m s n v -> Apply_val m s (vNe n) v
| ap_nat   : forall m s, Apply_val m s vNat vNat
| ap_empty : forall m s, Apply_val m s vEmpty vEmpty
| ap_pi    : forall m s F F' B B',
    Apply_val m s F F' -> Apply_val (S m) (up s) B B' ->
    Apply_val m s (vPi F B) (vPi F' B')
| ap_lam   : forall m s b b',
    Apply_val (S m) (up s) b b' -> Apply_val m s (vLam b) (vLam b')

with Apply_ne : nat -> ssub -> neutral -> sval -> Type :=
| ap_var : forall m s k, Apply_ne m s (nVar k) (nth_default (vNe (nVar k)) s k)
| ap_app : forall m s f vf F F' B B' a a' v,
    Apply_ne m s f vf ->
    Apply_val m s F F' ->            (* substitute the domain annotation       *)
    Apply_val (S m) (up s) B B' ->   (* ... and the codomain (under a binder)  *)
    Apply_val m s a a' ->
    Vapp m F' B' vf a' v ->          (* feed the substituted (F',B') to Vapp   *)
    Apply_ne m s (nApp f F B a) v

(* Vapp now carries the Pi type components (F,B): the neutral case stamps them
   onto the rebuilt [nApp]; the lambda (beta) case ignores them. *)
with Vapp : nat -> sval -> sval -> sval -> sval -> sval -> Type :=
| vapp_lam : forall m F B b a v, Apply_val m (a :: id_list m) b v -> Vapp m F B (vLam b) a v
| vapp_ne  : forall m F B n a, Vapp m F B (vNe n) a (vNe (nApp n F B a)).

Scheme Apply_val_mind := Induction for Apply_val Sort Type
  with Apply_ne_mind  := Induction for Apply_ne  Sort Type
  with Vapp_mind      := Induction for Vapp      Sort Type.

Definition Apply_mutind
  (P1 : forall m s v v', Apply_val m s v v' -> Type)
  (P2 : forall m s n v,  Apply_ne  m s n v  -> Type)
  (P3 : forall m F B vf a v, Vapp m F B vf a v -> Type)
  := fun f0 f1 f2 f3 f4 f5 f6 f7 f8 =>
  ( @Apply_val_mind P1 P2 P3 f0 f1 f2 f3 f4 f5 f6 f7 f8
  , @Apply_ne_mind  P1 P2 P3 f0 f1 f2 f3 f4 f5 f6 f7 f8
  , @Vapp_mind      P1 P2 P3 f0 f1 f2 f3 f4 f5 f6 f7 f8 ).

(* === QUESTION (1): determinism survives the (F,B) threading === *)
Lemma Apply_deterministic :
  (forall m s v v', Apply_val m s v v' -> forall v'', Apply_val m s v v'' -> v' = v'')
  * (forall m s n v, Apply_ne m s n v -> forall v'', Apply_ne m s n v'' -> v = v'')
  * (forall m F B vf a v, Vapp m F B vf a v -> forall v'', Vapp m F B vf a v'' -> v = v'').
Proof.
  refine (Apply_mutind
    (fun m s v v' _ => forall v'', Apply_val m s v v'' -> v' = v'')
    (fun m s n v _  => forall v'', Apply_ne m s n v'' -> v = v'')
    (fun m F B vf a v _ => forall v'', Vapp m F B vf a v'' -> v = v'')
    _ _ _ _ _ _ _ _ _);
    intros;
    match goal with
    | |- _ = ?rhs =>
        match goal with
        | H : Apply_val _ _ _ rhs |- _ => inversion H; subst; clear H
        | H : Apply_ne  _ _ _ rhs |- _ => inversion H; subst; clear H
        | H : Vapp  _ _ _ _ _ rhs |- _ => inversion H; subst; clear H
        end
    end;
    repeat match goal with
    | IH : forall v'', Apply_val ?m ?s ?v v'' -> _ = v'',
      H : Apply_val ?m ?s ?v _ |- _ => specialize (IH _ H); subst
    | IH : forall v'', Apply_ne ?m ?s ?n v'' -> _ = v'',
      H : Apply_ne ?m ?s ?n _ |- _ => specialize (IH _ H); subst
    | IH : forall v'', Vapp ?m ?F ?B ?vf ?a v'' -> _ = v'',
      H : Vapp ?m ?F ?B ?vf ?a _ |- _ => specialize (IH _ H); subst
    end;
    try reflexivity; try congruence.
Qed.

Definition Apply_val_det {m s v v' v''}
  (H : Apply_val m s v v') (H' : Apply_val m s v v'') : v' = v'' :=
  fst (fst Apply_deterministic) m s v v' H v'' H'.

(* === QUESTION (2): Reflect determinism survives the annotated refl_Pi ===
   refl_Pi stamps the eta-body neutral with the head's (weakened) domain
   [shift_val 0 1 F] and codomain [shift_val 1 1 B] -- the same annotations a
   later reify would read back. *)
Inductive Reflect : nat -> svalty -> neutral -> sval -> Type :=
| refl_U     : forall m n, Reflect m dU n (vNe n)
| refl_Nat   : forall m n, Reflect m (dEl vNat) n (vNe n)
| refl_Empty : forall m n, Reflect m (dEl vEmpty) n (vNe n)
| refl_neEl  : forall m c n, Reflect m (dEl (vNe c)) n (vNe n)
| refl_Pi    : forall m F B n ARG B' body,
    Reflect (S m) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
    Apply_val (S m) (ARG :: wkn_list m) B B' ->
    Reflect (S m) (dEl B')
            (nApp (shift_ne 0 1 n) (shift_val 0 1 F) (shift_val 1 1 B) ARG) body ->
    Reflect m (dEl (vPi F B)) n (vLam body).

Lemma Reflect_det : forall m T n v,
    Reflect m T n v -> forall v', Reflect m T n v' -> v = v'.
Proof.
  induction 1 as
    [ m n | m n | m n | m c n | m F B n ARG B' body Harg IHarg Hb Hbody IHbody ];
    intros v' Hr; inversion Hr; subst; try reflexivity.
  (* refl_Pi *)
  specialize (IHarg _ ltac:(eassumption)); subst ARG.
  (* the inverted second derivation supplies another [Apply_val] on the same
     (m, sub, codomain); identify it (it is not [Hb]) and apply determinism *)
  match goal with H : Apply_val _ _ _ _ |- _ =>
    lazymatch H with
    | Hb => fail
    | _ => pose proof (Apply_val_det Hb H); subst
    end
  end.
  specialize (IHbody _ ltac:(eassumption)); subst body.
  reflexivity.
Qed.

(* Both determinism results go through unchanged in shape from the real files:
   the (F,B) threading is index-determined, so it never obstructs inversion or
   the IH plumbing.  Phase 0 is therefore a mechanical arity ripple + reuse of
   the already-proven [Apply_reflect_cod]. *)
