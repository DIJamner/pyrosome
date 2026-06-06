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

  (* ===== Eta-closed DECLARATIVE conversion (paper's [ConvTy]/[ConvTm]/    *)
  (* [ConvNe]) consumed by [n_conv].  This is a STANDALONE mutual inductive  *)
  (* (NO fusion with [has_svalty]/[wf_neutral]); [n_conv] references it      *)
  (* one-directionally.  The eta rule [ctm_eta] + the neutral-app rules      *)
  (* carry [Reflect]/[Apply_val]/[Vapp] premises; [ctm_eta] additionally     *)
  (* carries [ne_below_val] well-scopedness side-conditions, which make the  *)
  (* ne_below/shift/ren metatheory provable structurally (the result        *)
  (* member's scopedness is read off the side-condition since [Vapp] cannot  *)
  (* be inverted backward).  See WIP/ConvEtaProto.v for the design notes.    *)
  Notation ext F Ge := (dEl (shift_val 0 1 F) :: map (shift_ty 0 1) Ge).
  Unset Elimination Schemes.
  (* type-code conversion (paper ConvTy): structural congruence; eta lives at
     the term level inside neutral arguments. *)
  Inductive conv_ty_eta : senv -> sval -> sval -> Prop :=
  | cte_nat   : forall Ge, conv_ty_eta Ge vNat vNat
  | cte_empty : forall Ge, conv_ty_eta Ge vEmpty vEmpty
  | cte_pi    : forall Ge F F' B B',
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_ty_eta Ge (vPi F B) (vPi F' B')
  | cte_piI   : forall Ge F F' B B',
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_ty_eta Ge (vPiI F B) (vPiI F' B')
  | cte_ne    : forall Ge n n' r l,
      conv_ne_eta Ge (dU r l) n n' ->
      conv_ty_eta Ge (vNe n) (vNe n')
  (* type-DIRECTED value conversion (paper ConvTm): structural at base/code,
     ETA-expanding at relevant Pi (the rule that makes it eta-closed). *)
  with conv_tm_eta : senv -> svalty -> sval -> sval -> Prop :=
  | ctm_ne_nat   : forall Ge n n', conv_ne_eta Ge (dEl vNat) n n' ->
      conv_tm_eta Ge (dEl vNat) (vNe n) (vNe n')
  | ctm_ne_empty : forall Ge n n', conv_ne_eta Ge (dEl vEmpty) n n' ->
      conv_tm_eta Ge (dEl vEmpty) (vNe n) (vNe n')
  | ctm_ne_el    : forall Ge c n n', conv_ne_eta Ge (dEl (vNe c)) n n' ->
      conv_tm_eta Ge (dEl (vNe c)) (vNe n) (vNe n')
  | ctm_zero  : forall Ge, conv_tm_eta Ge (dEl vNat) vZero vZero
  | ctm_suc   : forall Ge v v', conv_tm_eta Ge (dEl vNat) v v' ->
      conv_tm_eta Ge (dEl vNat) (vSuc v) (vSuc v')
  | ctm_code  : forall Ge r l c c', conv_ty_eta Ge c c' ->
      conv_tm_eta Ge (dU r l) c c'
  (* ETA at relevant Pi.  [f],[g] are arbitrary values of [vPi F B]; relate
     their eta-expansions ([fa],[ga] = [f]/[g] applied to the reflected bound
     var [ARG]) at the instantiated codomain [B'].  SIDE-CONDITIONS carry
     scopedness (so the result member's ne_below is recoverable). *)
  | ctm_eta   : forall Ge F B f g ARG B' fa ga,
      ne_below_val (length Ge) F ->
      ne_below_val (length Ge) f ->
      ne_below_val (length Ge) g ->
      Reflect (S (length Ge)) (dEl (shift_val 0 1 F)) (nVar 0) ARG ->
      Apply_val (S (length Ge)) (ARG :: id_list (S (length Ge)))
                (shift_val 1 1 B) B' ->
      Vapp (S (length Ge)) (shift_val 0 1 F) (shift_val 1 1 B)
           (shift_val 0 1 f) ARG fa ->
      Vapp (S (length Ge)) (shift_val 0 1 F) (shift_val 1 1 B)
           (shift_val 0 1 g) ARG ga ->
      conv_tm_eta (ext F Ge) (dEl B') fa ga ->
      conv_tm_eta Ge (dEl (vPi F B)) f g
  (* proof-irrelevant Pi: deferred.  Neutral/LamI structural for now. *)
  | ctm_piI_ne : forall Ge F B n n', conv_ne_eta Ge (dEl (vPiI F B)) n n' ->
      conv_tm_eta Ge (dEl (vPiI F B)) (vNe n) (vNe n')
  | ctm_lamI   : forall Ge F B b b',
      conv_tm_eta (ext F Ge) (dEl B) b b' ->
      conv_tm_eta Ge (dEl (vPiI F B)) (vLamI b) (vLamI b')
  (* neutral conversion (paper ConvNe): args related by conv_tm_eta at the
     annotation type (this is where eta enters type codes). *)
  with conv_ne_eta : senv -> svalty -> neutral -> neutral -> Prop :=
  | cne_eta_var : forall Ge k T, nth_error Ge k = Some T ->
      conv_ne_eta Ge T (nVar k) (nVar k)
  | cne_eta_emptyrec : forall Ge rA lA A A' s s',
      conv_ty_eta Ge A A' ->
      conv_ne_eta Ge (dEl vEmpty) s s' ->
      conv_ne_eta Ge (dEl A) (nEmptyrec rA lA A s) (nEmptyrec rA lA A' s')
  | cne_eta_app : forall Ge f f' F F' B B' a a' Bres,
      conv_ne_eta Ge (dEl (vPi F B)) f f' ->
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_tm_eta Ge (dEl F) a a' ->
      Apply_val (length Ge) (a :: id_list (length Ge)) B Bres ->
      conv_ne_eta Ge (dEl Bres) (nApp f F B a) (nApp f' F' B' a')
  | cne_eta_appI : forall Ge f f' F F' B B' a a' Bres,
      conv_ne_eta Ge (dEl (vPiI F B)) f f' ->
      conv_ty_eta Ge F F' ->
      conv_ty_eta (ext F Ge) B B' ->
      conv_tm_eta Ge (dEl F) a a' ->
      Apply_val (length Ge) (a :: id_list (length Ge)) B Bres ->
      conv_ne_eta Ge (dEl Bres) (nAppI f F B a) (nAppI f' F' B' a').
  Set Elimination Schemes.

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
        wf_neutral Ge n (dEl A) -> conv_ty_eta Ge A B -> wf_neutral Ge n (dEl B).
  Set Elimination Schemes.

End Typing.

(* The eta-closed conversion mutual triple. *)
Scheme conv_ty_eta_ind := Induction for conv_ty_eta Sort Prop
  with conv_tm_eta_ind := Induction for conv_tm_eta Sort Prop
  with conv_ne_eta_ind := Induction for conv_ne_eta Sort Prop.
Combined Scheme conv_eta_mutind from
  conv_ty_eta_ind, conv_tm_eta_ind, conv_ne_eta_ind.

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

(* ===================================================================== *)
(* Eta-closed conversion preserves scopedness ([ne_below]) -- forward and  *)
(* backward.  Consumed by the [n_conv] cases of [typing_ne_below] and       *)
(* [ren_typing] (RenTyping.v).  Every constructor recurses structurally     *)
(* off the corresponding member except [ctm_eta], whose result scopedness   *)
(* is its own side-condition.  (Migrated from WIP/ConvEtaProto.v.)          *)
(* ===================================================================== *)
Lemma conv_eta_ne_below :
  (forall Ge A B, conv_ty_eta Ge A B ->
     ne_below_val (length Ge) A -> ne_below_val (length Ge) B)
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     ne_below_ty (length Ge) T -> ne_below_val (length Ge) a ->
     ne_below_val (length Ge) b)
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     ne_below_ty (length Ge) T -> ne_below_ne (length Ge) n ->
     ne_below_ne (length Ge) m).
Proof.
  apply conv_eta_mutind.
  - (* cte_nat *) intros Ge HA. exact HA.
  - (* cte_empty *) intros Ge HA. exact HA.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB HA.
    cbn [ne_below_val] in HA |- *. destruct HA as [HF HB].
    split.
    + apply IHF; exact HF.
    + pose proof (IHB) as IHB'.
      cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HB.
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB HA.
    cbn [ne_below_val] in HA |- *. destruct HA as [HF HB].
    split.
    + apply IHF; exact HF.
    + pose proof (IHB) as IHB'.
      cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HB.
  - (* cte_ne *) intros Ge n n' r l _ IH HA.
    cbn [ne_below_val] in HA |- *.
    apply (IH I HA).
  - (* ctm_ne_nat *) intros Ge n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH I Ha).
  - (* ctm_ne_empty *) intros Ge n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH I Ha).
  - (* ctm_ne_el *) intros Ge c n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH HT Ha).
  - (* ctm_zero *) intros Ge HT Ha. exact Ha.
  - (* ctm_suc *) intros Ge v v' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH I Ha).
  - (* ctm_code *) intros Ge r l c c' _ IH HT Ha.
    cbn [ne_below_ty] in *. apply IH; exact Ha.
  - (* ctm_eta -- result scopedness is the side-condition [nbg]. *)
    intros Ge F B f g ARG B' fa ga _nbF _nbf nbg _ _ _ _ _ _ HT Hf.
    exact nbg.
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *. apply (IH HT Ha).
  - (* ctm_lamI *) intros Ge F B b b' _ IH HT Ha.
    cbn [ne_below_val ne_below_ty] in *.
    pose proof (IH) as IH'. cbn [length] in IH'; rewrite length_map in IH'.
    apply IH'; [ exact (proj2 HT) | exact Ha ].
  - (* cne_eta_var *) intros Ge k T He HT Hn. exact Hn.
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT Hn.
    cbn [ne_below_ne ne_below_ty] in *. destruct Hn as [HA Hs].
    split; [ apply (IHA HA) | apply (IHs I Hs) ].
  - (* cne_eta_app *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn.
    cbn [ne_below_ne] in Hn |- *. destruct Hn as (Hnf & HnF & HnB & Hna).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf ].
    + apply (IHF HnF).
    + pose proof (IHB) as IHB'. cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HnB.
    + apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna ].
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hn.
    cbn [ne_below_ne] in Hn |- *. destruct Hn as (Hnf & HnF & HnB & Hna).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf ].
    + apply (IHF HnF).
    + pose proof (IHB) as IHB'. cbn [length] in IHB'; rewrite length_map in IHB'.
      apply IHB'. exact HnB.
    + apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna ].
Qed.

Definition conv_ty_eta_ne_below : forall Ge A B, conv_ty_eta Ge A B ->
    ne_below_val (length Ge) A -> ne_below_val (length Ge) B :=
  proj1 conv_eta_ne_below.

Lemma conv_eta_ne_below_rev :
  (forall Ge A B, conv_ty_eta Ge A B ->
     ne_below_val (length Ge) B -> ne_below_val (length Ge) A)
  /\ (forall Ge T a b, conv_tm_eta Ge T a b ->
     ne_below_ty (length Ge) T -> ne_below_val (length Ge) b ->
     ne_below_val (length Ge) a)
  /\ (forall Ge T n m, conv_ne_eta Ge T n m ->
     ne_below_ty (length Ge) T -> ne_below_ne (length Ge) m ->
     ne_below_ne (length Ge) n).
Proof.
  apply conv_eta_mutind.
  - (* cte_nat *) intros Ge HB. exact HB.
  - (* cte_empty *) intros Ge HB. exact HB.
  - (* cte_pi *) intros Ge F F' B B' _ IHF _ IHB HB0.
    cbn [ne_below_val] in HB0 |- *. destruct HB0 as [HF HB].
    split.
    + apply IHF; exact HF.
    + cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HB.
  - (* cte_piI *) intros Ge F F' B B' _ IHF _ IHB HB0.
    cbn [ne_below_val] in HB0 |- *. destruct HB0 as [HF HB].
    split.
    + apply IHF; exact HF.
    + cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HB.
  - (* cte_ne *) intros Ge n n' r l _ IH HB0.
    cbn [ne_below_val] in HB0 |- *. apply (IH I HB0).
  - (* ctm_ne_nat *) intros Ge n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH I Hb).
  - (* ctm_ne_empty *) intros Ge n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH I Hb).
  - (* ctm_ne_el *) intros Ge cc n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH HT Hb).
  - (* ctm_zero *) intros Ge HT Hb. exact Hb.
  - (* ctm_suc *) intros Ge v v' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH I Hb).
  - (* ctm_code *) intros Ge r l cc cc' _ IH HT Hb. cbn [ne_below_ty] in *. apply IH; exact Hb.
  - (* ctm_eta -- left scopedness is the side-condition [nbf]. *)
    intros Ge F B f g ARG B' fa ga nbF nbf _nbg _ _ _ _ _ _ HT Hg. exact nbf.
  - (* ctm_piI_ne *) intros Ge F B n n' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *. apply (IH HT Hb).
  - (* ctm_lamI *) intros Ge F B b b' _ IH HT Hb. cbn [ne_below_val ne_below_ty] in *.
    cbn [length] in IH; rewrite length_map in IH. apply IH; [ exact (proj2 HT) | exact Hb ].
  - (* cne_eta_var *) intros Ge k T He HT Hm. exact Hm.
  - (* cne_eta_emptyrec *) intros Ge rA lA A A' s s' _ IHA _ IHs HT Hm.
    cbn [ne_below_ne ne_below_ty] in *. destruct Hm as [HA Hs].
    split; [ apply (IHA HA) | apply (IHs I Hs) ].
  - (* cne_eta_app *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hm.
    cbn [ne_below_ne] in Hm |- *. destruct Hm as (Hnf' & HnF' & HnB' & Hna').
    assert (HnF : ne_below_val (length Ge) F) by (apply (IHF HnF')).
    assert (HnB : ne_below_val (S (length Ge)) B).
    { cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HnB'. }
    assert (Hna : ne_below_val (length Ge) a)
      by (apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna' ]).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf' ].
    + exact HnF.
    + exact HnB.
    + exact Hna.
  - (* cne_eta_appI *)
    intros Ge f f' F F' B B' a a' Bres _ IHf _ IHF _ IHB _ IHa Hap HT Hm.
    cbn [ne_below_ne] in Hm |- *. destruct Hm as (Hnf' & HnF' & HnB' & Hna').
    assert (HnF : ne_below_val (length Ge) F) by (apply (IHF HnF')).
    assert (HnB : ne_below_val (S (length Ge)) B).
    { cbn [length] in IHB; rewrite length_map in IHB. apply IHB. exact HnB'. }
    assert (Hna : ne_below_val (length Ge) a)
      by (apply IHa; [ cbn [ne_below_ty]; exact HnF | exact Hna' ]).
    repeat split.
    + apply IHf; [ cbn [ne_below_ty ne_below_val]; split; [ exact HnF | exact HnB ] | exact Hnf' ].
    + exact HnF.
    + exact HnB.
    + exact Hna.
Qed.

Definition conv_ty_eta_ne_below_rev : forall Ge A B, conv_ty_eta Ge A B ->
    ne_below_val (length Ge) B -> ne_below_val (length Ge) A :=
  proj1 conv_eta_ne_below_rev.
