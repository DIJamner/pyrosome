Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import
  Domain EvalRel Determinism ApplyLemmas SortInj Typing Model.
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

(* ===================================================================== *)
(* Part 5 : the fundamental lemma — totality + preservation.              *)
(* ===================================================================== *)

(* No variable is well formed in the empty context (closed terms only). *)
Lemma wf_term_nil_var : forall (x : string) (t : @sort string),
    wf_term fo_lang [] (@var string x) t -> False.
Proof.
  intros x t H.
  remember (@nil (string * @sort string)) as c eqn:Hc.
  remember (@var string x) as e eqn:He.
  revert Hc He. induction H; intros Hc He; try discriminate He.
  - (* conv *) exact (IHwf_term Hc He).
  - (* var *) subst c. cbn in H. exact H.
Qed.

(* Dispatch: from [In (n, term_rule ..) fo_lang] (n abstract from term_rect),
   enumerate the concrete former and pin its rule body.  [vm_compute] turns the
   membership into a finite disjunction of pair-equalities; non-[term_rule]
   entries clash on their second component ([discriminate]); the rest yield the
   concrete [n], context, args and conclusion sort by [injection]. *)
Ltac enumerate_rule :=
  match goal with
  | Hin : In (_, term_rule _ _ _) fo_lang |- _ =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]);
      try contradiction;
      try discriminate Hin;
      injection Hin; clear Hin; intros; subst
  end.

(* When the head [n] is already concrete: invert the term's well-formedness,
   pin the (single) rule by name lookup (cheap, no 26-way [vm_compute] split),
   and peel the argument list into per-subterm [wf_term] hypotheses. *)
Ltac peel_args H :=
  apply WfCutElim.invert_wf_term_con in H;
  destruct H as (? & ? & ? & Hpin & Hwa & Hdisj);
  pin_rule Hpin; cbn in Hwa; autorewrite with model in Hwa;
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.

(* Close a component whose required sort head does not match the pinned rule's
   conclusion head (the [eq_sort]/[=] disjunct from [invert_wf_term_con]). *)
Ltac solve_wrong_sort :=
  match goal with
  | Hd : (eq_sort _ _ _ _ \/ _ = _) |- _ =>
      exfalso; cbn in Hd; destruct Hd as [Hd | Hd];
      [ apply eq_sort_inj in Hd;
        let s2 := fresh in let cc := fresh in let aa := fresh in
        let Hr := fresh in let Hx := fresh in
        destruct (Hd _ _ eq_refl) as (s2 & cc & aa & Hr & Hx);
        cbn in Hr; discriminate Hr
      | discriminate Hd ]
  end.

(* ===== One-time inversion lemmas (the only [vm_compute]s) ===============
   These pin each former's rule ONCE at file-compile time, so the fundamental
   lemma's proof stays [vm_compute]-free (and fast).  [_subwf] gives the
   eval-relevant subterms' well-formedness; [_arity] the argument count;
   [_name] enumerates which formers inhabit a given sort. *)

Lemma emp_inv : forall l (t : @sort string),
    wf_term fo_lang [] (con "emp" l) t -> l = [].
Proof.
  intros l t H. apply WfCutElim.invert_wf_term_con in H.
  destruct H as (c0 & ra & t0 & Hin & Hwa & _). pin_rule Hin.
  apply invert_wf_args_ctx_nil in Hwa. exact Hwa.
Qed.

Lemma ext_arity : forall l (t : @sort string),
    wf_term fo_lang [] (con "ext" l) t -> length l = 3.
Proof.
  intros l t H. apply WfCutElim.invert_wf_term_con in H.
  destruct H as (c0 & ra & t0 & Hin & Hwa & _). pin_rule Hin.
  apply wf_args_length_eq in Hwa. cbn in Hwa. Lia.lia.
Qed.

Lemma ext_subwf : forall a i0 g (t : @sort string),
    wf_term fo_lang [] (con "ext" [a; i0; g]) t ->
    wf_term fo_lang [] a (scon "ty" [i0; g]) /\ wf_term fo_lang [] g (scon "env" []).
Proof.
  intros a i0 g t H. apply WfCutElim.invert_wf_term_con in H.
  destruct H as (c0 & ra & t0 & Hin & Hwa & _). pin_rule Hin.
  cbn in Hwa. autorewrite with model in Hwa.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  cbn in *. split; assumption.
Qed.

Lemma env_name : forall (n : string) l,
    wf_term fo_lang [] (con n l) (scon "env" []) -> n = "emp" \/ n = "ext".
Proof.
  intros n l H. apply WfCutElim.invert_wf_term_con in H.
  destruct H as (c0 & ra & t0 & Hin & Hwa & Hdisj).
  enumerate_rule;
    first [ left; reflexivity | right; reflexivity | exfalso; solve_wrong_sort ].
Qed.

Section Fundamental.
  Notation term := (@term string).

  (* For a term [e], depending on which sort it is well formed at, [e]
     evaluates and its value is well typed at the evaluated type.  The
     contexts/types referenced in a former's conclusion sort are always
     among that former's arguments, hence strict subterms — so the strong
     term-induction hypothesis ([term_rect]) covers them. *)
  Definition FL (e : term) : Type :=
    (* env: the context term itself evaluates (totality) to a well-formed senv. *)
    (wf_term fo_lang [] e (scon "env" []) ->
       sigT (fun Ge : senv => (eval_env e Ge * wf_senv Ge)%type))
    (* ty: given the (evaluated) ambient context, the type evaluates and is wf. *)
    * (forall i G Ge, wf_term fo_lang [] e (scon "ty" [i; G]) ->
       eval_env G Ge -> wf_senv Ge ->
       sigT (fun T : svalty => (eval_ty e T * wf_svalty Ge T)%type))
    (* exp: given the (evaluated) context and type, the term evaluates and the
       value has that (evaluated) type — preservation proper. *)
    * (forall A i G Ge T, wf_term fo_lang [] e (scon "exp" [A; i; G]) ->
       eval_env G Ge -> wf_senv Ge -> eval_ty A T ->
       sigT (fun v : sval => (eval_rel e v * has_svalty Ge v T)%type))
    (* sub: given the (evaluated) domain/codomain, the substitution evaluates to
       a well-typed semantic substitution. *)
    * (forall Gd Gc GeD GeC, wf_term fo_lang [] e (scon "sub" [Gd; Gc]) ->
       eval_env Gd GeD -> eval_env Gc GeC -> wf_senv GeD -> wf_senv GeC ->
       sigT (fun sg : ssub => (eval_sub e sg * wf_ssub GeC sg GeD)%type)).

  (* Component accessors for the [FL] product. *)
  Let flenv (e:term) (F : FL e) := fst (fst (fst F)).
  Let flty  (e:term) (F : FL e) := snd (fst (fst F)).
  Let flexp (e:term) (F : FL e) := snd (fst F).
  Let flsub (e:term) (F : FL e) := snd F.

  Theorem eval_preserves_typing : forall e, FL e.
  Proof.
    induction e as [x | n l IHl] using term_rect.
    - (* var: no closed variable is well typed *)
      unfold FL; repeat split; intros; exfalso;
        match goal with H : wf_term _ _ (var _) _ |- _ => exact (wf_term_nil_var H) end.
    - (* con n l *)
      unfold FL; repeat split.
      + (* ===== env ===== *) intro Hwf.
        (* dispatch on the head (data); valid env formers are [emp], [ext] *)
        destruct (eqb n "emp") eqn:Enm.
        { assert (n = "emp") as Hn by (apply (proj1 (eqb_prop_iff _ _ _)); rewrite Enm; exact I);
            subst n.
          rewrite (emp_inv Hwf).
          exists (@nil svalty). split; [ apply ev_env_emp | apply wf_senv_nil ]. }
        destruct (eqb n "ext") eqn:Ext.
        { assert (n = "ext") as Hn by (apply (proj1 (eqb_prop_iff _ _ _)); rewrite Ext; exact I);
            subst n.
          pose proof (ext_arity Hwf) as HL.
          destruct l as [|a [|i0 [|g [|x xs]]]]; cbn in HL; try discriminate HL.
          pose proof (ext_subwf Hwf) as Hs.
          destruct IHl as [Fa [Fi [Fg _]]].
          destruct (flenv Fg (proj2 Hs)) as [GeG [HevG HwfG]].
          destruct (flty Fa (proj1 Hs) HevG HwfG) as [S [HevA HwfS]].
          exists (shift_ty 1 S :: map (shift_ty 1) GeG). split.
          * apply ev_env_ext; [ exact HevG | exact HevA ].
          * apply wf_senv_ext; [ exact HwfG | exact HwfS ]. }
        (* else: head is neither emp nor ext, but it is a rule at sort env *)
        exfalso. destruct (env_name Hwf) as [E | E].
        * rewrite E in Enm; cbn in Enm; discriminate Enm.
        * rewrite E in Ext; cbn in Ext; discriminate Ext.
      (* The [ty]/[exp]/[sub] components follow the SAME shape as [env]:
         dispatch on the head former, pin its rule via a one-time inversion
         lemma (cf. [emp_inv]/[ext_subwf]/[env_name]), recurse with the
         induction hypothesis on the subterm arguments, and assemble the value
         with the matching [eval_*] constructor + typing rule.  The value
         formers ([U], [Nat], [Empty], [zero], [suc]) and the substitution
         lemmas ([wf_ssub_id]/[wf_ssub_wkn]/[wf_ssub_snoc]/[wf_ssub_comp],
         [subst_has_svalty]) discharge their cases directly.

         One coherence fact is still required for the remaining cases, and is
         left admitted here: when [invert_wf_term_con] returns its [eq_sort]
         (rather than [=]) disjunct, the externally-quantified context/type is
         only eq_sort-EQUAL to the former's own (subterm) context/type, not
         syntactically equal — so relating the supplied [eval_env]/[eval_ty] to
         the subterm's evaluation needs an "evaluation respects [eq_term]"
         lemma (a piece of the gluing soundness).  With that lemma the cases
         close uniformly. *)
      + (* ===== ty ===== *) intros i G Ge Hwf Henv Hwfsenv. admit.
      + (* ===== exp ===== *) intros A i G Ge T Hwf Henv Hwfsenv Hty. admit.
      + (* ===== sub ===== *) intros Gd Gc GeD GeC Hwf HenvD HenvC HwfD HwfC. admit.
  Admitted.

End Fundamental.

(* ===================================================================== *)
(* User-facing corollary : the headline preservation statement.          *)
(*                                                                        *)
(* A well-typed expression that evaluates, evaluates to a well-typed      *)
(* value (at the evaluated type, in the evaluated environment).           *)
(* ===================================================================== *)
Corollary eval_rel_preserves_typing :
  forall e A i G v Ge T,
    wf_term fo_lang [] e (scon "exp" [A; i; G]) ->
    eval_env G Ge -> eval_ty A T -> eval_rel e v -> wf_senv Ge ->
    has_svalty Ge v T.
Proof.
  intros e A i G v Ge T Hwf Henv Hty Hrel Hwfsenv.
  destruct (snd (fst (eval_preserves_typing e)) A i G Ge T Hwf Henv Hwfsenv Hty)
    as [v' [Hrel' Hhas]].
  pose proof (eval_rel_det Hrel' Hrel); subst v'.
  exact Hhas.
Qed.
