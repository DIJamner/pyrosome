Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply Reflect LogRel2Conv.
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
    | nApp f F B a =>
        ne_below_ne m f /\ ne_below_val m F /\ ne_below_val (S m) B /\ ne_below_val m a
    | nAppI f F B a =>
        ne_below_ne m f /\ ne_below_val m F /\ ne_below_val (S m) B /\ ne_below_val m a
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
      has_svalty (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge) B (dU rB lB) ->
      has_svalty Ge (vPi F B) (dU r l)
  | t_PiI   : forall Ge F B rF lF rB lB r l,
      has_svalty Ge F (dU rF lF) ->
      has_svalty (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge) B (dU rB lB) ->
      has_svalty Ge (vPiI F B) (dU r l)
  | t_lam   : forall Ge F B b rF lF,
      has_svalty Ge F (dU rF lF) ->
      has_svalty (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge) b (dEl B) ->
      has_svalty Ge (vLam b) (dEl (vPi F B))
  | t_lamI  : forall Ge F B b rF lF,
      has_svalty Ge F (dU rF lF) ->
      has_svalty (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge) b (dEl B) ->
      has_svalty Ge (vLamI b) (dEl (vPiI F B))
  (* ETA-typing of a relevant lambda (the rule that lets the eta-expanded
     reflection of a neutral type-check, cf. [reflect_red]'s [LRpi] case).
     The body [b] need only be well-typed at the codomain INSTANTIATED at the
     eta-long reflection [ARG] of the bound variable: [B'] is [B] (once-shifted)
     applied to [ARG :: id_list], matching how [n_app] types the eta-body
     [nApp (shift n) ARG].  When the domain [F] is a base type, [ARG = vNe
     (nVar 0)] and [B' = B], recovering [t_lam]; at a relevant-Pi domain [ARG]
     is itself a lambda and [B' = B[ARG/0] <> B], which rigid [t_lam] cannot
     type.  The [Reflect] premise pins [ARG] to the canonical eta-expansion of
     the variable, so the rule is no more permissive than eta on normal forms. *)
  | t_lam_eta : forall Ge F B b ARG B' rF lF,
      has_svalty Ge F (dU rF lF) ->
      Reflect (S (length Ge)) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
      Apply_val (S (length Ge)) (ARG :: id_list (S (length Ge)))
                (shift_val 1 1 B) B' ->
      has_svalty (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge) b (dEl B') ->
      has_svalty Ge (vLam b) (dEl (vPi F B))
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
        wf_neutral Ge (nApp f F B a) (dEl B')
  | n_appI  : forall Ge f F B a B',
        wf_neutral Ge f (dEl (vPiI F B)) ->
        has_svalty Ge a (dEl F) ->
        Apply_val (length Ge) (a :: id_list (length Ge)) B B' ->
        wf_neutral Ge (nAppI f F B a) (dEl B')
  (* TYPING-CONVERSION for neutrals (paper's [WfTmConv] / [ConvNeChChk], in the
     value world): a neutral typed at [dEl A] is typed at any [dEl B] whose code
     is convertible to [A] ([conv_nf], the structural [∼annot]).  This is the
     mechanism that dissolves the typing-conversion wall: the eta bound variable
     [nVar 0], typed at the LEFT domain [dEl FA'] by [n_var], transports to the
     RIGHT domain [dEl FB'] via [conv_nf FA' FB'] (the domain reify-ty).  Sound:
     in the gluing model [dEl A] and [dEl B] with [conv_nf A B] denote the same
     type, so membership transports. *)
  | n_conv  : forall Ge n A B,
        wf_neutral Ge n (dEl A) -> conv_nf A B -> wf_neutral Ge n (dEl B).
  Set Elimination Schemes.

End Typing.

(* The value-typing mutual pair. *)
Scheme has_svalty_rect := Induction for has_svalty Sort Prop
  with wf_neutral_rect := Induction for wf_neutral Sort Prop.

Definition has_neutral_mutind
  (P0 : forall Ge v T, has_svalty Ge v T -> Prop)
  (P1 : forall Ge n T, wf_neutral Ge n T -> Prop) := fun
  fne fzero fsuc fNat fEmpty fPi fPiI flam flamI flameta fvar femptyrec fapp fappI fnconv =>
  ( @has_svalty_rect P0 P1 fne fzero fsuc fNat fEmpty fPi fPiI flam flamI flameta fvar femptyrec fapp fappI fnconv
  , @wf_neutral_rect P0 P1 fne fzero fsuc fNat fEmpty fPi fPiI flam flamI flameta fvar femptyrec fapp fappI fnconv ).

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

(* Structural conversion preserves scopedness ([ne_below]): convertible normal
   forms share variable structure (the variable case [cne_var] relates [nVar k]
   to itself), so a bound on one bounds the other.  Needed by the [n_conv] case
   of [typing_ne_below] / [ren_typing] (RenTyping.v). *)
Lemma conv_ne_below :
  (forall a b, conv_nf a b -> forall m, ne_below_val m a -> ne_below_val m b)
  * (forall n p, conv_ne n p -> forall m, ne_below_ne m n -> ne_below_ne m p).
Proof.
  apply (conv_mutind
    (fun a b (_ : conv_nf a b) => forall m, ne_below_val m a -> ne_below_val m b)
    (fun n p (_ : conv_ne n p) => forall m, ne_below_ne m n -> ne_below_ne m p)).
  - intros n p _ IH m H. cbn [ne_below_val] in *. apply IH; exact H.
  - intros m H. exact H.
  - intros v w _ IH m H. cbn [ne_below_val] in *. apply IH; exact H.
  - intros m H. exact H.
  - intros m H. exact H.
  - intros F B F' B' _ IHF _ IHB m H. cbn [ne_below_val] in *.
    destruct H as [HF HB]. split; [ apply IHF; exact HF | apply IHB; exact HB ].
  - intros F B F' B' _ IHF _ IHB m H. cbn [ne_below_val] in *.
    destruct H as [HF HB]. split; [ apply IHF; exact HF | apply IHB; exact HB ].
  - intros b b' _ IH m H. cbn [ne_below_val] in *. apply IH; exact H.
  - intros b b' _ IH m H. cbn [ne_below_val] in *. apply IH; exact H.
  - intros k m H. exact H.
  - intros rA lA A scrut A' scrut' _ IHA _ IHs m H. cbn [ne_below_ne] in *.
    destruct H as [HA Hs]. split; [ apply IHA; exact HA | apply IHs; exact Hs ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa m H. cbn [ne_below_ne] in *.
    destruct H as [Hf [HF [HB Ha]]].
    split; [ apply IHf; exact Hf | split; [ apply IHF; exact HF
           | split; [ apply IHB; exact HB | apply IHa; exact Ha ] ] ].
  - intros f F B a f' F' B' a' _ IHf _ IHF _ IHB _ IHa m H. cbn [ne_below_ne] in *.
    destruct H as [Hf [HF [HB Ha]]].
    split; [ apply IHf; exact Hf | split; [ apply IHF; exact HF
           | split; [ apply IHB; exact HB | apply IHa; exact Ha ] ] ].
Qed.

Definition conv_nf_ne_below : forall a b, conv_nf a b ->
    forall m, ne_below_val m a -> ne_below_val m b := fst conv_ne_below.
Definition conv_ne_ne_below : forall n p, conv_ne n p ->
    forall m, ne_below_ne m n -> ne_below_ne m p := snd conv_ne_below.
