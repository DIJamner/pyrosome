Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply.
Import Core.Notations.

(* ===================================================================== *)
(* Semantic typing of the Pi-extended value domain.                       *)
(*                                                                        *)
(* Values are environment-free / absolute: a value over a context of      *)
(* length [m] has its free neutral de Bruijn indices in [0, m).  A senv   *)
(* records the TYPES of those variables (index 0 = innermost).  The       *)
(* binder formers ([vPi]/[vLam]/[nApp] ...) type their bodies/codomains   *)
(* in the EXTENDED environment [dEl F :: map (shift_ty 0 1) Ge]; an        *)
(* application's result type [B[a]] is the codomain code with the         *)
(* argument substituted (the relational [Apply_val]). *)

Section Typing.
  Notation term := (@term string).

  (* ===== Scopedness: every neutral index is below [m] ===== *)
  Fixpoint ne_below_val (m : nat) (v : sval) : Prop :=
    match v with
    | vNe n => ne_below_ne m n
    | vZero => True
    | vSuc v' => ne_below_val m v'
    | vNat => True
    | vEmpty => True
    | vPi F B => ne_below_val m F /\ ne_below_val (S m) B
    | vPiI F B => ne_below_val m F /\ ne_below_val (S m) B
    | vLam b => ne_below_val (S m) b
    | vLamI b => ne_below_val (S m) b
    end
  with ne_below_ne (m : nat) (n : neutral) : Prop :=
    match n with
    | nVar k => k < m
    | nEmptyrec _ _ A scrut => ne_below_val m A /\ ne_below_ne m scrut
    | nApp f a => ne_below_ne m f /\ ne_below_val m a
    | nAppI f a => ne_below_ne m f /\ ne_below_val m a
    end.

  Definition ne_below_ty (m : nat) (T : svalty) : Prop :=
    match T with
    | dU _ _ => True
    | dEl e => ne_below_val m e
    end.

  (* ===== Typing judgments ===== *)
  Unset Elimination Schemes.
  Inductive wf_svalty : senv -> svalty -> Prop :=
  | wf_dU  : forall Ge r l, wf_svalty Ge (dU r l)
  | wf_dEl : forall Ge e r l, has_svalty Ge e (dU r l) -> wf_svalty Ge (dEl e)
  with has_svalty : senv -> sval -> svalty -> Prop :=
  | t_ne    : forall Ge n T, wf_neutral Ge n T -> has_svalty Ge (vNe n) T
  | t_zero  : forall Ge, has_svalty Ge vZero (dEl vNat)
  | t_suc   : forall Ge v, has_svalty Ge v (dEl vNat) -> has_svalty Ge (vSuc v) (dEl vNat)
  | t_Nat   : forall Ge r l, has_svalty Ge vNat   (dU r l)
  | t_Empty : forall Ge r l, has_svalty Ge vEmpty (dU r l)
  | t_Pi    : forall Ge F B rF lF rB lB r l,
      has_svalty Ge F (dU rF lF) ->
      has_svalty (dEl F :: map (shift_ty 0 1) Ge) B (dU rB lB) ->
      has_svalty Ge (vPi F B) (dU r l)
  | t_PiI   : forall Ge F B rF lF rB lB r l,
      has_svalty Ge F (dU rF lF) ->
      has_svalty (dEl F :: map (shift_ty 0 1) Ge) B (dU rB lB) ->
      has_svalty Ge (vPiI F B) (dU r l)
  | t_lam   : forall Ge F B b,
      has_svalty (dEl F :: map (shift_ty 0 1) Ge) b (dEl B) ->
      has_svalty Ge (vLam b) (dEl (vPi F B))
  | t_lamI  : forall Ge F B b,
      has_svalty (dEl F :: map (shift_ty 0 1) Ge) b (dEl B) ->
      has_svalty Ge (vLamI b) (dEl (vPiI F B))
  with wf_neutral : senv -> neutral -> svalty -> Prop :=
  | n_var   : forall Ge k T, nth_error Ge k = Some T -> wf_neutral Ge (nVar k) T
  | n_emptyrec : forall Ge rA lA A scrut r l,
        has_svalty Ge A (dU r l) ->
        wf_neutral Ge scrut (dEl vEmpty) ->
        wf_neutral Ge (nEmptyrec rA lA A scrut) (dEl A)
  | n_app   : forall Ge f F B a B',
        wf_neutral Ge f (dEl (vPi F B)) ->
        has_svalty Ge a (dEl F) ->
        Apply_val (length Ge) (a :: id_list (length Ge)) B B' ->
        wf_neutral Ge (nApp f a) (dEl B')
  | n_appI  : forall Ge f F B a B',
        wf_neutral Ge f (dEl (vPiI F B)) ->
        has_svalty Ge a (dEl F) ->
        Apply_val (length Ge) (a :: id_list (length Ge)) B B' ->
        wf_neutral Ge (nAppI f a) (dEl B').
  Set Elimination Schemes.

End Typing.

(* The value-typing mutual pair. *)
Scheme has_svalty_rect := Induction for has_svalty Sort Prop
  with wf_neutral_rect := Induction for wf_neutral Sort Prop.

Definition has_neutral_mutind
  (P0 : forall Ge v T, has_svalty Ge v T -> Prop)
  (P1 : forall Ge n T, wf_neutral Ge n T -> Prop) := fun
  fne fzero fsuc fNat fEmpty fPi fPiI flam flamI fvar femptyrec fapp fappI =>
  ( @has_svalty_rect P0 P1 fne fzero fsuc fNat fEmpty fPi fPiI flam flamI fvar femptyrec fapp fappI
  , @wf_neutral_rect P0 P1 fne fzero fsuc fNat fEmpty fPi fPiI flam flamI fvar femptyrec fapp fappI ).

(* Canonical forms at El Empty: only a neutral inhabits it (used by Emptyrec). *)
Lemma canonical_empty : forall Ge v, has_svalty Ge v (dEl vEmpty) -> exists n, v = vNe n.
Proof.
  intros Ge v H.
  inversion H; subst; try (eexists; reflexivity); try discriminate; try congruence.
Qed.

(* A [Type]-valued version for use in [Type]-valued glue goals. *)
Lemma canonical_empty_sig : forall Ge v,
    has_svalty Ge v (dEl vEmpty) -> { n | v = vNe n }.
Proof.
  intros Ge v H; destruct v;
    solve [ eexists; reflexivity | exfalso; inversion H ].
Qed.

(* A neutral value's typing is a neutral typing. *)
Lemma has_svalty_neutral : forall Ge n T, has_svalty Ge (vNe n) T -> wf_neutral Ge n T.
Proof. intros Ge n T H. inversion H; subst. assumption. Qed.
