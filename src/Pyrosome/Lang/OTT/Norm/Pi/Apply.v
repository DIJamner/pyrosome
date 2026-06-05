Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain.
Import Core.Notations.

(* ===================================================================== *)
(* Relational hereditary substitution and semantic application for the    *)
(* Pi-extended value domain.                                              *)
(*                                                                        *)
(* In the first-order fragment [apply] was a structural [Fixpoint].  With *)
(* binders, substituting a [vLam] for an applied variable creates a beta  *)
(* redex, so substitution is HEREDITARY (reduce on the fly) and no longer *)
(* structurally recursive.  We therefore present it as a RELATION:        *)
(*                                                                        *)
(*   Apply_val m s v v'   :  substituting [s] into value  [v] yields [v'] *)
(*   Apply_ty  m s T T'   :  ... into type   [T] yields [T']             *)
(*   Apply_ne  m s n v    :  ... into neutral [n] yields VALUE [v]        *)
(*                            (a neutral may become non-neutral via beta) *)
(*   Vapp  m vf a v       :  semantic application [vf a = v] (relevant)   *)
(*   VappI m vf a v       :  ... (proof-irrelevant)                       *)
(*                                                                        *)
(* The index [m] is the length of the CODOMAIN context (where the result  *)
(* lives); it is needed only to phrase beta as a substitution             *)
(* [a :: id_list m] that decrements the body's remaining indices.  Going  *)
(* under a binder bumps [m] to [S m] and lifts the substitution by [up].  *)
(*                                                                        *)
(* Type-directed eta-long reflection (the [Reflect] relation, for the eta *)
(* law) is added separately on top of this layer. *)

Section Apply.

  (* Identity / weakening substitutions over an [n]-variable context. *)
  Definition id_list  (n : nat) : ssub := map (fun k => vNe (nVar k)) (seq 0 n).
  Definition wkn_list (n : nat) : ssub := map (fun k => vNe (nVar (S k))) (seq 0 n).

  (* Lift a semantic substitution under one binder: the fresh variable maps to
     itself, the rest are weakened (shifted by 1 at cutoff 0). *)
  Definition up (s : ssub) : ssub := vNe (nVar 0) :: map (shift_val 0 1) s.

  Inductive Apply_ty : nat -> ssub -> svalty -> svalty -> Type :=
  | ap_dU  : forall m s r l, Apply_ty m s (dU r l) (dU r l)
  | ap_dEl : forall m s e e', Apply_val m s e e' -> Apply_ty m s (dEl e) (dEl e')

  with Apply_val : nat -> ssub -> sval -> sval -> Type :=
  | ap_ne    : forall m s n v, Apply_ne m s n v -> Apply_val m s (vNe n) v
  | ap_zero  : forall m s, Apply_val m s vZero vZero
  | ap_suc   : forall m s v v', Apply_val m s v v' -> Apply_val m s (vSuc v) (vSuc v')
  | ap_nat   : forall m s, Apply_val m s vNat vNat
  | ap_empty : forall m s, Apply_val m s vEmpty vEmpty
  | ap_pi    : forall m s F F' B B',
      Apply_val m s F F' -> Apply_val (S m) (up s) B B' ->
      Apply_val m s (vPi F B) (vPi F' B')
  | ap_piI   : forall m s F F' B B',
      Apply_val m s F F' -> Apply_val (S m) (up s) B B' ->
      Apply_val m s (vPiI F B) (vPiI F' B')
  | ap_lam   : forall m s b b',
      Apply_val (S m) (up s) b b' -> Apply_val m s (vLam b) (vLam b')
  | ap_lamI  : forall m s b b',
      Apply_val (S m) (up s) b b' -> Apply_val m s (vLamI b) (vLamI b')

  with Apply_ne : nat -> ssub -> neutral -> sval -> Type :=
  | ap_var      : forall m s k, Apply_ne m s (nVar k) (nth_default (vNe (nVar k)) s k)
  | ap_emptyrec : forall m s rA lA A A' scrut scrut',
      Apply_val m s A A' -> Apply_ne m s scrut (vNe scrut') ->
      Apply_ne m s (nEmptyrec rA lA A scrut) (vNe (nEmptyrec rA lA A' scrut'))
  | ap_app      : forall m s f vf F F' B B' a a' v,
      Apply_ne m s f vf ->
      Apply_val m s F F' ->            (* substitute the domain annotation       *)
      Apply_val (S m) (up s) B B' ->   (* ... and the codomain (under a binder)  *)
      Apply_val m s a a' -> Vapp m F' B' vf a' v ->
      Apply_ne m s (nApp f F B a) v
  | ap_appI     : forall m s f vf F F' B B' a a' v,
      Apply_ne m s f vf ->
      Apply_val m s F F' ->
      Apply_val (S m) (up s) B B' ->
      Apply_val m s a a' -> VappI m F' B' vf a' v ->
      Apply_ne m s (nAppI f F B a) v

  with Vapp : nat -> sval -> sval -> sval -> sval -> sval -> Type :=
  | vapp_lam : forall m F B b a v, Apply_val m (a :: id_list m) b v -> Vapp m F B (vLam b) a v
  | vapp_ne  : forall m F B n a, Vapp m F B (vNe n) a (vNe (nApp n F B a))

  with VappI : nat -> sval -> sval -> sval -> sval -> sval -> Type :=
  | vappI_lam : forall m F B b a v, Apply_val m (a :: id_list m) b v -> VappI m F B (vLamI b) a v
  | vappI_ne  : forall m F B n a, VappI m F B (vNe n) a (vNe (nAppI n F B a)).

End Apply.

(* Mutual induction principle for the five relations (paired by hand, as
   [Combined Scheme] supports only [Prop]). *)
Scheme Apply_ty_mind  := Induction for Apply_ty  Sort Type
  with Apply_val_mind := Induction for Apply_val Sort Type
  with Apply_ne_mind  := Induction for Apply_ne  Sort Type
  with Vapp_mind      := Induction for Vapp      Sort Type
  with VappI_mind     := Induction for VappI     Sort Type.

Definition Apply_mutind
  (P0 : forall m s T T', Apply_ty  m s T T' -> Type)
  (P1 : forall m s v v', Apply_val m s v v' -> Type)
  (P2 : forall m s n v,  Apply_ne  m s n v  -> Type)
  (P3 : forall m F B vf a v, Vapp  m F B vf a v -> Type)
  (P4 : forall m F B vf a v, VappI m F B vf a v -> Type)
  := fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 =>
  ( @Apply_ty_mind  P0 P1 P2 P3 P4 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18
  , @Apply_val_mind P0 P1 P2 P3 P4 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18
  , @Apply_ne_mind  P0 P1 P2 P3 P4 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18
  , @Vapp_mind      P0 P1 P2 P3 P4 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18
  , @VappI_mind     P0 P1 P2 P3 P4 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 ).

(* ===================================================================== *)
(* Determinism: the (m, s, input) triple determines the output value.     *)
(* ===================================================================== *)
Lemma Apply_deterministic :
  (forall m s T T', Apply_ty m s T T' -> forall T'', Apply_ty m s T T'' -> T' = T'')
  * (forall m s v v', Apply_val m s v v' -> forall v'', Apply_val m s v v'' -> v' = v'')
  * (forall m s n v, Apply_ne m s n v -> forall v'', Apply_ne m s n v'' -> v = v'')
  * (forall m F B vf a v, Vapp m F B vf a v -> forall v'', Vapp m F B vf a v'' -> v = v'')
  * (forall m F B vf a v, VappI m F B vf a v -> forall v'', VappI m F B vf a v'' -> v = v'').
Proof.
  refine (Apply_mutind
    (fun m s T T' _ => forall T'', Apply_ty m s T T'' -> T' = T'')
    (fun m s v v' _ => forall v'', Apply_val m s v v'' -> v' = v'')
    (fun m s n v _  => forall v'', Apply_ne m s n v'' -> v = v'')
    (fun m F B vf a v _ => forall v'', Vapp m F B vf a v'' -> v = v'')
    (fun m F B vf a v _ => forall v'', VappI m F B vf a v'' -> v = v'')
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    intros;
    (* invert the SECOND derivation, identified as the hyp whose output is the
       goal's RHS (the sub-derivations output the LHS components instead) *)
    match goal with
    | |- _ = ?rhs =>
        match goal with
        | H : Apply_ty  _ _ _ rhs |- _ => inversion H; subst; clear H
        | H : Apply_val _ _ _ rhs |- _ => inversion H; subst; clear H
        | H : Apply_ne  _ _ _ rhs |- _ => inversion H; subst; clear H
        | H : Vapp  _ _ _ _ _ rhs |- _ => inversion H; subst; clear H
        | H : VappI _ _ _ _ _ rhs |- _ => inversion H; subst; clear H
        end
    end;
    repeat match goal with
    | IH : forall T'', Apply_ty ?m ?s ?T T'' -> _ = T'',
      H : Apply_ty ?m ?s ?T _ |- _ => specialize (IH _ H); subst
    | IH : forall v'', Apply_val ?m ?s ?v v'' -> _ = v'',
      H : Apply_val ?m ?s ?v _ |- _ => specialize (IH _ H); subst
    | IH : forall v'', Apply_ne ?m ?s ?n v'' -> _ = v'',
      H : Apply_ne ?m ?s ?n _ |- _ => specialize (IH _ H); subst
    | IH : forall v'', Vapp ?m ?F ?B ?vf ?a v'' -> _ = v'',
      H : Vapp ?m ?F ?B ?vf ?a _ |- _ => specialize (IH _ H); subst
    | IH : forall v'', VappI ?m ?F ?B ?vf ?a v'' -> _ = v'',
      H : VappI ?m ?F ?B ?vf ?a _ |- _ => specialize (IH _ H); subst
    end;
    try reflexivity; try congruence.
Qed.

Definition Apply_ty_det  m s T T' T'' (H : Apply_ty m s T T') := fst (fst (fst (fst Apply_deterministic))) m s T T' H T''.
Definition Apply_val_det m s v v' v'' (H : Apply_val m s v v') := snd (fst (fst (fst Apply_deterministic))) m s v v' H v''.
Definition Apply_ne_det  m s n v v'' (H : Apply_ne m s n v) := snd (fst (fst Apply_deterministic)) m s n v H v''.
Definition Vapp_det  m F B vf a v v'' (H : Vapp m F B vf a v) := snd (fst Apply_deterministic) m F B vf a v H v''.
Definition VappI_det m F B vf a v v'' (H : VappI m F B vf a v) := snd Apply_deterministic m F B vf a v H v''.
