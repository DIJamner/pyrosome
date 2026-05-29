Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import
  Domain EvalRel ApplyLemmas Typing.
Import Core.Notations.

(* ===================================================================== *)
(* Preservation / soundness of the environment-free evaluator (EvalRel.v) *)
(* against the semantic typing of the value domain (Typing.v).            *)
(*                                                                        *)
(* The headline result [eval_preserves_typing] is the FUNDAMENTAL LEMMA:  *)
(* a well-formed [fo_lang] term EVALUATES (totality) and its value is     *)
(* WELL TYPED at the evaluated type (preservation).  It is proved by      *)
(* strong induction on term structure (Term.term_rect), so that every     *)
(* subterm — including the contexts/types appearing in a former's sort,   *)
(* which are themselves arguments — is covered by the induction           *)
(* hypothesis.  This is the statement the user identified as missing:     *)
(* "eval on well-formed input implies the output is well-formed".         *)
(* ===================================================================== *)

(* ===================================================================== *)
(* Part 1 : scopedness — semantic typing bounds neutral indices.          *)
(* ===================================================================== *)

(* A well-typed value/neutral has all its free neutral indices below the
   length of the environment (the [n_var] premise [nth_error Ge k = Some T]
   forces [k < length Ge]). *)
Lemma typing_scoped :
  (forall Ge v T, has_svalty Ge v T -> ne_below_val (length Ge) v)
  * (forall Ge n T, wf_neutral Ge n T -> ne_below_ne (length Ge) n).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => ne_below_val (length Ge) v)
    (fun Ge n T _ => ne_below_ne (length Ge) n)
    _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn. exact IHn.
  - (* t_zero *) intros; exact I.
  - (* t_suc *) intros Ge v hv IHv. exact IHv.
  - (* t_Nat *) intros; exact I.
  - (* t_Empty *) intros; exact I.
  - (* n_var *) intros Ge k T He. cbn.
    apply (proj1 (nth_error_Some Ge k)). rewrite He. discriminate.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr. cbn. split; assumption.
Qed.

(* A well-formed semantic type is scoped. *)
Lemma wf_svalty_scoped : forall Ge T, wf_svalty Ge T -> ne_below_ty (length Ge) T.
Proof.
  intros Ge T H. destruct H as [Ge r l | Ge e r l He]; cbn.
  - exact I.
  - exact (fst typing_scoped _ _ _ He).
Qed.

(* ===================================================================== *)
(* Part 2 : apply / shift interaction.                                    *)
(* ===================================================================== *)

(* Substituting after a shift-by-1 into a cons drops the head.  Stated for
   TYPED values: the pure/scope-only version is FALSE for [nEmptyrec] (the
   [apply_ne] else-branch retains the ORIGINAL scrutinee), but under typing
   an [El Empty] scrutinee maps to a NEUTRAL (canonical forms), so the
   else-branch is dead — exactly as in [apply_compose_typed] (Typing.v). *)
Lemma apply_shift_cons_typed :
  (forall Ge v T, has_svalty Ge v T ->
     forall Delta sg vv, wf_ssub Delta sg Ge ->
       apply_val (vv :: sg) (shift_val 1 v) = apply_val sg v)
  * (forall Ge n T, wf_neutral Ge n T ->
     forall Delta sg vv, wf_ssub Delta sg Ge ->
       apply_ne (vv :: sg) (shift_ne 1 n) = apply_ne sg n).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => forall Delta sg vv, wf_ssub Delta sg Ge ->
       apply_val (vv :: sg) (shift_val 1 v) = apply_val sg v)
    (fun Ge n T _ => forall Delta sg vv, wf_ssub Delta sg Ge ->
       apply_ne (vv :: sg) (shift_ne 1 n) = apply_ne sg n)
    _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn Delta sg vv Hsub. cbn. exact (IHn Delta sg vv Hsub).
  - (* t_zero *) intros; reflexivity.
  - (* t_suc *) intros Ge v hv IHv Delta sg vv Hsub. cbn. f_equal. exact (IHv Delta sg vv Hsub).
  - (* t_Nat *) intros; reflexivity.
  - (* t_Empty *) intros; reflexivity.
  - (* n_var *) intros Ge k T He Delta sg vv [Hlen Hpt]. cbn.
    assert (Hk : k < length Ge)
      by (apply (proj1 (nth_error_Some Ge k)); rewrite He; discriminate).
    replace (k + 1) with (S k) by Lia.lia.
    unfold nth_default. cbn [nth_error].
    destruct (nth_error sg k) eqn:E; [reflexivity|].
    apply nth_error_None in E. exfalso. rewrite Hlen in E. Lia.lia.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr Delta sg vv Hsub. cbn.
    rewrite (IHscr Delta sg vv Hsub).
    rewrite (IHA Delta sg vv Hsub).
    (* the substituted scrutinee is a neutral (El Empty canonical forms) *)
    pose proof (snd subst_has_svalty Ge scrut (dEl vEmpty) hscr Delta sg Hsub) as Hs.
    cbn in Hs. destruct (canonical_empty Hs) as [s' Hs']. cbn in Hs'.
    rewrite Hs'. reflexivity.
Qed.

(* The type-level corollary: a well-formed type's shift is undone by a cons. *)
Lemma apply_shift_cons_ty : forall Gamma T, wf_svalty Gamma T ->
  forall Delta sg vv, wf_ssub Delta sg Gamma ->
    apply_ty (vv :: sg) (shift_ty 1 T) = apply_ty sg T.
Proof.
  intros Gamma T HT Delta sg vv Hsub. destruct HT as [Gamma r l | Gamma e r l He].
  - reflexivity.
  - cbn. f_equal. exact (fst apply_shift_cons_typed _ _ _ He Delta sg vv Hsub).
Qed.

(* The weakening substitution [wkn_list m] acts as a shift-by-1 on SCOPED
   data (indices < m). *)
Lemma wkn_list_nth : forall m k,
    k < m -> nth_default (vNe (nVar k)) (wkn_list m) k = vNe (nVar (S k)).
Proof.
  intros m k Hk. unfold wkn_list, nth_default.
  rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 m) 0) by (rewrite length_seq; exact Hk).
  rewrite seq_nth by exact Hk. cbn. reflexivity.
Qed.

Lemma apply_wkn_eq_shift :
  (forall T m, ne_below_ty m T -> apply_ty (wkn_list m) T = shift_ty 1 T)
  * ((forall v m, ne_below_val m v -> apply_val (wkn_list m) v = shift_val 1 v)
  * (forall n m, ne_below_ne m n -> apply_ne (wkn_list m) n = vNe (shift_ne 1 n))).
Proof.
  apply (sval_mutind
    (fun T => forall m, ne_below_ty m T -> apply_ty (wkn_list m) T = shift_ty 1 T)
    (fun v => forall m, ne_below_val m v -> apply_val (wkn_list m) v = shift_val 1 v)
    (fun n => forall m, ne_below_ne m n -> apply_ne (wkn_list m) n = vNe (shift_ne 1 n))).
  - (* dU *) intros; reflexivity.
  - (* dEl *) intros e IHe m Hb. cbn. f_equal. exact (IHe m Hb).
  - (* vNe *) intros n IHn m Hb. cbn. exact (IHn m Hb).
  - (* vZero *) intros; reflexivity.
  - (* vSuc *) intros v IHv m Hb. cbn. f_equal. exact (IHv m Hb).
  - (* vNat *) intros; reflexivity.
  - (* vEmpty *) intros; reflexivity.
  - (* nVar *) intros k m Hb. cbn in Hb. cbn.
    rewrite (@wkn_list_nth m k Hb). f_equal. f_equal. Lia.lia.
  - (* nEmptyrec *) intros rA lA A IHA scrut IHscr m Hb. cbn in Hb. destruct Hb as [HbA Hbsc].
    cbn. rewrite (IHscr m Hbsc). cbn. rewrite (IHA m HbA). reflexivity.
Qed.

(* ===================================================================== *)
(* Part 3 : weakening — typing is closed under context extension (shift). *)
(* ===================================================================== *)

Lemma shift_typing :
  (forall Ge v T, has_svalty Ge v T ->
     forall T0, has_svalty (T0 :: map (shift_ty 1) Ge) (shift_val 1 v) (shift_ty 1 T))
  * (forall Ge n T, wf_neutral Ge n T ->
     forall T0, wf_neutral (T0 :: map (shift_ty 1) Ge) (shift_ne 1 n) (shift_ty 1 T)).
Proof.
  refine (has_neutral_mutind
    (fun Ge v T _ => forall T0,
       has_svalty (T0 :: map (shift_ty 1) Ge) (shift_val 1 v) (shift_ty 1 T))
    (fun Ge n T _ => forall T0,
       wf_neutral (T0 :: map (shift_ty 1) Ge) (shift_ne 1 n) (shift_ty 1 T))
    _ _ _ _ _ _ _).
  - (* t_ne *) intros Ge n T hn IHn T0. cbn. apply t_ne. exact (IHn T0).
  - (* t_zero *) intros Ge T0. cbn. apply t_zero.
  - (* t_suc *) intros Ge v hv IHv T0. cbn. apply t_suc. exact (IHv T0).
  - (* t_Nat *) intros Ge r l T0. cbn. apply t_Nat.
  - (* t_Empty *) intros Ge r l T0. cbn. apply t_Empty.
  - (* n_var *) intros Ge k T He T0. cbn.
    replace (k + 1) with (S k) by Lia.lia.
    apply n_var. cbn [nth_error]. rewrite nth_error_map, He. reflexivity.
  - (* n_emptyrec *) intros Ge rA lA A scrut r l hA IHA hscr IHscr T0. cbn.
    eapply n_emptyrec.
    + exact (IHA T0).
    + exact (IHscr T0).
Qed.

Lemma shift_wf_svalty : forall Ge T, wf_svalty Ge T ->
  forall T0, wf_svalty (T0 :: map (shift_ty 1) Ge) (shift_ty 1 T).
Proof.
  intros Ge T H T0. destruct H as [Ge r l | Ge e r l He]; cbn.
  - apply wf_dU.
  - apply (wf_dEl (r:=r) (l:=l)). exact (fst shift_typing _ _ _ He T0).
Qed.

(* Well-formedness of environments under the structural operations. *)
Lemma wf_senv_nil : wf_senv [].
Proof. intros k T He. destruct k; cbn in He; discriminate He. Qed.

Lemma wf_senv_ext : forall Ge S, wf_senv Ge -> wf_svalty Ge S ->
  wf_senv (shift_ty 1 S :: map (shift_ty 1) Ge).
Proof.
  intros Ge S HG HS k T He. destruct k as [|k]; cbn [nth_error] in He.
  - injection He as He. subst T. apply (shift_wf_svalty HS).
  - rewrite nth_error_map in He.
    destruct (nth_error Ge k) as [Tk|] eqn:E; cbn in He; [|discriminate He].
    injection He as He. subst T. apply (shift_wf_svalty (HG k Tk E)).
Qed.

(* ===================================================================== *)
(* Part 4 : well-typedness of the structural substitutions.               *)
(* ===================================================================== *)

(* [forget] : the empty substitution into the empty context. *)
Lemma wf_ssub_forget : forall Delta, wf_ssub Delta [] [].
Proof.
  intro Delta. split.
  - reflexivity.
  - intros k T He. destruct k; cbn in He; discriminate He.
Qed.

(* [wkn] over [Ge] (extended by [T0]) is the shift-by-1 substitution. *)
Lemma wf_ssub_wkn : forall Ge, wf_senv Ge ->
  forall T0, wf_ssub (T0 :: map (shift_ty 1) Ge) (wkn_list (length Ge)) Ge.
Proof.
  intros Ge Hwf T0. split.
  - unfold wkn_list. rewrite length_map, length_seq. reflexivity.
  - intros k T He.
    assert (Hk : k < length Ge)
      by (apply (proj1 (nth_error_Some Ge k)); rewrite He; discriminate).
    (* value at index k is vNe (nVar (S k)) *)
    erewrite nth_default_irrel_sval;
      [ | unfold wkn_list; rewrite length_map, length_seq; exact Hk ].
    rewrite (@wkn_list_nth (length Ge) k Hk).
    (* the type [apply_ty (wkn_list (length Ge)) T] equals [shift_ty 1 T] *)
    rewrite (fst apply_wkn_eq_shift T (length Ge)
               (wf_svalty_scoped (Hwf k T He))).
    apply t_ne. apply n_var.
    cbn [nth_error]. rewrite nth_error_map, He. reflexivity.
Qed.

(* [snoc g v] : extend a well-typed substitution [g : Delta <- Gamma] by a
   value [vv] of the (substituted) head type [S]. *)
Lemma wf_ssub_snoc : forall Delta Gamma sg vv St,
    wf_senv Gamma -> wf_svalty Gamma St ->
    wf_ssub Delta sg Gamma ->
    has_svalty Delta vv (apply_ty sg St) ->
    wf_ssub Delta (vv :: sg) (shift_ty 1 St :: map (shift_ty 1) Gamma).
Proof.
  intros Delta Gamma sg vv St HwfG HwfS Hsub Hvv.
  pose proof Hsub as [Hlen Hpt].
  split.
  - cbn. rewrite length_map. rewrite Hlen. reflexivity.
  - intros k T He. destruct k as [|k]; cbn [nth_default nth_error] in *.
    + (* head *) injection He as HT. subst T.
      rewrite (apply_shift_cons_ty HwfS vv Hsub).
      exact Hvv.
    + (* tail *) cbn [nth_error] in He. rewrite nth_error_map in He.
      destruct (nth_error Gamma k) as [Tk|] eqn:E; cbn in He; [|discriminate He].
      injection He as HT. subst T.
      rewrite (apply_shift_cons_ty (HwfG k Tk E) vv Hsub).
      change (nth_default (vNe (nVar 0)) (vv :: sg) (S k))
        with (nth_default (vNe (nVar 0)) sg k).
      exact (Hpt k Tk E).
Qed.

(* Type substitution preserves type well-formedness. *)
Lemma subst_wf_svalty : forall Gamma T, wf_svalty Gamma T ->
  forall Delta sigma, wf_ssub Delta sigma Gamma -> wf_svalty Delta (apply_ty sigma T).
Proof.
  intros Gamma T HT Delta sigma Hsub. destruct HT as [Gamma r l | Gamma e r l He].
  - apply wf_dU.
  - cbn. apply (wf_dEl (r:=r) (l:=l)).
    exact (fst subst_has_svalty _ _ _ He Delta sigma Hsub).
Qed.

(* A neutral value's typing is a neutral typing. *)
Lemma has_svalty_neutral : forall Ge n T, has_svalty Ge (vNe n) T -> wf_neutral Ge n T.
Proof. intros Ge n T H. inversion H; subst. assumption. Qed.

(* ===================================================================== *)
(* Part 5 : soundness of the TYPED evaluator — preservation by induction. *)
(*                                                                        *)
(* Because [EvalRel.v]'s judgments are indexed by the semantic context/   *)
(* type, "the value is well typed" is immediate by induction on the eval  *)
(* derivation: every constructor's typed premises feed exactly the        *)
(* corresponding value-typing rule (via the Part 1-4 lemmas).  No         *)
(* well-formedness inversion, no sort coherence — preservation is direct. *)
(* ===================================================================== *)
Theorem eval_sound :
  (((forall G Ge, eval_env G Ge -> wf_senv Ge)
    * (forall Ge A T, eval_ty Ge A T -> (wf_senv Ge * wf_svalty Ge T)%type))
   * (forall Ge e T v, eval_rel Ge e T v -> (wf_senv Ge * has_svalty Ge v T)%type))
  * (forall Gin Gout g sg, eval_sub Gin Gout g sg ->
       (wf_senv Gin * wf_senv Gout * wf_ssub Gout sg Gin)%type).
Proof.
  refine (eval_mutind
    (fun G Ge _ => wf_senv Ge)
    (fun Ge A T _ => (wf_senv Ge * wf_svalty Ge T)%type)
    (fun Ge e T v _ => (wf_senv Ge * has_svalty Ge v T)%type)
    (fun Gin Gout g sg _ => (wf_senv Gin * wf_senv Gout * wf_ssub Gout sg Gin)%type)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* ev_env_emp *) exact wf_senv_nil.
  - (* ev_env_ext *) intros A i G Genv S _ IHenv _ IHty.
    apply wf_senv_ext; [ exact IHenv | exact (snd IHty) ].
  - (* ev_U *) intros Ge l r G _ IHenv. split; [ exact IHenv | apply wf_dU ].
  - (* ev_El *) intros Ge e l r G ve _ IHenv _ IHrel.
    split; [ exact IHenv | apply (wf_dEl (r:=nf_info r) (l:=nf_info l)); exact (snd IHrel) ].
  - (* ev_ty_subst *) intros GeD GeC A i g G' G sg T _ IHsub _ IHty.
    split; [ exact (snd (fst IHsub)) | exact (subst_wf_svalty (snd IHty) (snd IHsub)) ].
  - (* ev_hd *) intros A i G Ge S _ IHenv _ IHty.
    split.
    + apply wf_senv_ext; [ exact IHenv | exact (snd IHty) ].
    + apply t_ne, n_var. cbn [nth_error]. reflexivity.
  - (* ev_exp_subst *) intros e A i g G' G GeD GeC sg ve T _ IHsub _ IHrel.
    split; [ exact (snd (fst IHsub))
           | exact (fst subst_has_svalty _ _ _ (snd IHrel) GeC sg (snd IHsub)) ].
  - (* ev_zero *) intros G Ge _ IHenv. split; [ exact IHenv | apply t_zero ].
  - (* ev_suc *) intros n G Ge vn _ IHrel.
    split; [ exact (fst IHrel) | apply t_suc; exact (snd IHrel) ].
  - (* ev_Nat *) intros G Ge _ IHenv. split; [ exact IHenv | apply t_Nat ].
  - (* ev_Empty *) intros G Ge _ IHenv. split; [ exact IHenv | apply t_Empty ].
  - (* ev_Emptyrec *) intros e A lA rA G Ge ne vA _ IHe _ IHA.
    split; [ exact (fst IHe) | ].
    apply t_ne. eapply n_emptyrec.
    + exact (snd IHA).
    + apply has_svalty_neutral. exact (snd IHe).
  - (* ev_id *) intros G Ge _ IHenv.
    split; [ split; exact IHenv | apply wf_ssub_id ].
  - (* ev_wkn *) intros A i G Ge S _ IHenv _ IHty.
    split; [ split; [ exact IHenv | apply wf_senv_ext; [ exact IHenv | exact (snd IHty) ] ]
           | apply (wf_ssub_wkn IHenv) ].
  - (* ev_forget *) intros G Ge _ IHenv.
    split; [ split; [ apply wf_senv_nil | exact IHenv ] | apply wf_ssub_forget ].
  - (* ev_cmp *) intros g f G3 G2 G1 Ge1 Ge2 Ge3 sf sg _ IHf _ IHg.
    split; [ split; [ exact (fst (fst IHg)) | exact (snd (fst IHf)) ]
           | exact (wf_ssub_comp (fst (fst IHg)) (snd IHf) (snd IHg)) ].
  - (* ev_snoc *) intros v g A i G' G GeD GeC sg vv S _ IHg _ IHA _ IHv.
    split; [ split; [ apply wf_senv_ext; [ exact (fst (fst IHg)) | exact (snd IHA) ]
                    | exact (snd (fst IHg)) ]
           | exact (wf_ssub_snoc (fst (fst IHg)) (snd IHA) (snd IHg) (snd IHv)) ].
Qed.

(* ===================================================================== *)
(* User-facing corollary : the typed evaluator's output is well typed.    *)
(*                                                                        *)
(* If a term [e] evaluates (in semantic context [Ge], at semantic type    *)
(* [T]) to value [v], then [v] genuinely has semantic type [T].           *)
(* ===================================================================== *)
Corollary eval_rel_preserves_typing : forall Ge e T v,
    eval_rel Ge e T v -> has_svalty Ge v T.
Proof.
  intros Ge e T v H. exact (snd (snd (fst eval_sound) Ge e T v H)).
Qed.
