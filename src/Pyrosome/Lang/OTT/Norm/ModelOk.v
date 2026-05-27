Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Gluing Require Import CutTModel.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Env Determinism Model.
From Pyrosome.Lang.OTT Require Import Base Nat.
Import Core.Notations.

Definition fo_lang := ott_nat ++ ott_base ++ subst_ott ++ ott_info.

(* ================================================================== *)
(* String eqb helpers (concrete values, proved by reflexivity)        *)
(* ================================================================== *)

Lemma eqb_exp_true : @eqb string _ "exp" "exp" = true. Proof. reflexivity. Qed.
Lemma eqb_ty_true  : @eqb string _ "ty"  "ty"  = true. Proof. reflexivity. Qed.
Lemma eqb_sub_true : @eqb string _ "sub" "sub" = true. Proof. reflexivity. Qed.

(* ================================================================== *)
(* cterm_var                                                           *)
(* ================================================================== *)

Lemma Norm_cterm_var : forall (c : @ctx string) (n : string) (t : @sort string),
    In (n, t) c ->
    ceq_term (CutTModel := Norm) c t (var n) (var n).
Proof.
  intros c n t _.
  unfold ceq_term, Norm, norm_ceq_term.
  destruct t as [tname [| G rest]].
  - reflexivity.
  - destruct (eqb tname "exp") eqn:Hexp.
    + exact (existT _ (vNe (var n)) (ev_var _ _, ev_var _ _)).
    + destruct (eqb tname "ty") eqn:Hty.
      * exact (existT _ (dNe (var n)) (ev_ty_var _ _, ev_ty_var _ _)).
      * destruct (eqb tname "sub") eqn:Hsub.
        -- exact (existT _ (eval_env G) (ev_sub_var _ _, ev_sub_var _ _)).
        -- exact tt.
Qed.

(* ================================================================== *)
(* cterm_trans                                                         *)
(* ================================================================== *)

Lemma Norm_cterm_trans : forall (c : @ctx string) (t : @sort string) e1 e12 e2,
    ceq_term (CutTModel := Norm) c t e1 e12 ->
    ceq_term (CutTModel := Norm) c t e12 e2 ->
    ceq_term (CutTModel := Norm) c t e1 e2.
Proof.
  intros c t e1 e12 e2 H1 H2.
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct t as [tname [| G rest]].
  - etransitivity; eassumption.
  - destruct (eqb tname "exp").
    + destruct H1 as [v1 [a1 b1]], H2 as [v2 [a2 b2]].
      assert (v1 = v2) by (eapply eval_rel_det; eassumption). subst v2.
      exact (existT _ v1 (a1, b2)).
    + destruct (eqb tname "ty").
      * destruct H1 as [T1 [a1 b1]], H2 as [T2 [a2 b2]].
        assert (T1 = T2) by (eapply eval_ty_det; eassumption). subst T2.
        exact (existT _ T1 (a1, b2)).
      * destruct (eqb tname "sub").
        -- destruct H1 as [r1 [a1 b1]], H2 as [r2 [a2 b2]].
           assert (r1 = r2) by (eapply eval_sub_det; eassumption). subst r2.
           exact (existT _ r1 (a1, b2)).
        -- exact tt.
Qed.

(* ================================================================== *)
(* cterm_sym                                                           *)
(* ================================================================== *)

Lemma Norm_cterm_sym : forall (c : @ctx string) (t : @sort string) e1 e2,
    ceq_term (CutTModel := Norm) c t e1 e2 ->
    ceq_term (CutTModel := Norm) c t e2 e1.
Proof.
  intros c t e1 e2 H.
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct t as [tname [| G rest]].
  - symmetry; assumption.
  - destruct (eqb tname "exp").
    + destruct H as [v [a b]]. exact (existT _ v (b, a)).
    + destruct (eqb tname "ty").
      * destruct H as [T [a b]]. exact (existT _ T (b, a)).
      * destruct (eqb tname "sub").
        -- destruct H as [r [a b]]. exact (existT _ r (b, a)).
        -- exact tt.
Qed.

(* ================================================================== *)
(* cterm_conv                                                          *)
(* ================================================================== *)

Lemma Norm_cterm_conv : forall (c : @ctx string) t1 t2 e1 e2,
    ceq_sort (CutTModel := Norm) c t1 t2 ->
    ceq_term (CutTModel := Norm) c t1 e1 e2 ->
    ceq_term (CutTModel := Norm) c t2 e1 e2.
Proof.
  intros c t1 t2 e1 e2 Hsort Hterm.
  unfold ceq_sort, Norm, norm_ceq_sort, sort_head, sort_env in Hsort.
  destruct t1 as [n1 l1], t2 as [n2 l2].
  destruct Hsort as [Heqb Henv].
  pose proof (proj1 (eqb_prop_iff _ _ _) ltac:(rewrite Heqb; exact I)) as Hn.
  subst n2.
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct l1 as [|G1 r1], l2 as [|G2 r2].
  - exact Hterm.
  - (* l1=[], l2=G2::r2: degenerate (Henv: eval_env emp = eval_env G2 = []) *)
    cbn [sort_env] in Henv.
    unfold ceq_term, Norm, norm_ceq_term in *.
    cbn in Hterm |- *.
    destruct (eqb n1 "exp"); [| destruct (eqb n1 "ty"); [| destruct (eqb n1 "sub")]].
    all: try exact tt.
    (* For exp/ty/sub cases: Hterm is eval_env e1 = eval_env e2 but goal needs sigma type.
       Henv says eval_env G2 = []. But we need eval witnesses, which Hterm doesn't provide. *)
    all: admit.
  - (* l1=G1::r1, l2=[]: symmetric degenerate *)
    cbn [sort_env] in Henv.
    unfold ceq_term, Norm, norm_ceq_term in *.
    cbn in Hterm |- *.
    destruct (eqb n1 "exp"); [| destruct (eqb n1 "ty"); [| destruct (eqb n1 "sub")]].
    all: try exact tt.
    all: admit.
  - cbn [sort_env] in Henv.
    destruct (eqb n1 "exp").
    + destruct Hterm as [v [a b]]. rewrite Henv in a, b.
      exact (existT _ v (a, b)).
    + destruct (eqb n1 "ty").
      * destruct Hterm as [T [a b]]. rewrite Henv in a, b.
        exact (existT _ T (a, b)).
      * destruct (eqb n1 "sub").
        -- destruct Hterm as [r [a b]]. rewrite Henv in a, b.
           exact (existT _ r (a, b)).
        -- exact tt.
Admitted.

(* ================================================================== *)
(* csort_trans                                                         *)
(* ================================================================== *)

Lemma Norm_csort_trans : forall (c : @ctx string) t1 t12 t2,
    ceq_sort (CutTModel := Norm) c t1 t12 ->
    ceq_sort (CutTModel := Norm) c t12 t2 ->
    ceq_sort (CutTModel := Norm) c t1 t2.
Proof.
  intros c t1 t12 t2 [Heqb1 Henv1] [Heqb2 Henv2].
  unfold ceq_sort, Norm, norm_ceq_sort in *.
  split.
  - (* eqb (head t1) (head t2) = true: same head via transitivity *)
    destruct t1 as [n1 l1], t12 as [n12 l12], t2 as [n2 l2].
    cbn [sort_head] in *.
    pose proof (proj1 (eqb_prop_iff _ n1 n12) ltac:(rewrite Heqb1; exact I)) as H1.
    pose proof (proj1 (eqb_prop_iff _ n12 n2) ltac:(rewrite Heqb2; exact I)) as H2.
    subst. apply (@eqb_refl_true string _ string_Eqb_ok).
  - etransitivity; eassumption.
Qed.

(* ================================================================== *)
(* csort_sym                                                           *)
(* ================================================================== *)

Lemma Norm_csort_sym : forall (c : @ctx string) t1 t2,
    ceq_sort (CutTModel := Norm) c t1 t2 ->
    ceq_sort (CutTModel := Norm) c t2 t1.
Proof.
  intros c t1 t2.
  destruct t1 as [n1 l1], t2 as [n2 l2].
  unfold ceq_sort, Norm, norm_ceq_sort.
  cbn [sort_head sort_env].
  intros [Heqb Henv].
  split.
  - pose proof (proj1 (eqb_prop_iff _ n1 n2) ltac:(rewrite Heqb; exact I)) as H.
    subst n2. apply (@eqb_refl_true string _ string_Eqb_ok).
  - symmetry; assumption.
Qed.

(* ================================================================== *)
(* csort_by: vacuous (fo_lang has no sort_eq_rules)                   *)
(* ================================================================== *)

Lemma Norm_csort_by : forall (c c' : @ctx string) (name : string) t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) fo_lang ->
    ceq_args (CM := Norm) c c' s1 s2 ->
    ceq_sort (CutTModel := Norm) c t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c c' name t1 t2 s1 s2 Hin _.
  exfalso.
  unfold fo_lang in Hin.
  vm_compute in Hin.
  decompose [or] Hin; congruence.
Qed.

(* ================================================================== *)
(* csort_cong                                                          *)
(* ================================================================== *)

Lemma Norm_csort_cong : forall (c c' : @ctx string) (name : string) (args : list string) s1 s2,
    In (name, sort_rule c' args) fo_lang ->
    ceq_args (CM := Norm) c c' s1 s2 ->
    ceq_sort (CutTModel := Norm) c (scon name s1) (scon name s2).
Proof.
  intros c c' name args s1 s2 Hin Hargs.
  unfold ceq_sort, Norm, norm_ceq_sort.
  split.
  - cbn [sort_head]. apply (@eqb_refl_true string _ string_Eqb_ok).
  - (* Show eval_env (sort_env (scon name s1)) = eval_env (sort_env (scon name s2)).
       Use vm_compute to enumerate sort rules.
       All sort rules either have empty context (→ s1=s2=[], sort_env=emp)
       or first context variable of an argless sort
       (→ ceq_term = eval_env equality). *)
    unfold fo_lang in Hin.
    vm_compute in Hin.
    (* After vm_compute, Hin is a big disjunction. Recursively destruct. *)
    (* For branches that are term_rule/term_eq_rule: congruence solves (different ctor). *)
    (* For branches that are sort_rule: injection gives concrete c', then use Hargs. *)
    Local Ltac handle_sort_rule Hargs :=
      cbn [sort_env];
      first [
        (* empty context case *)
        inversion Hargs; subst; reflexivity
      |
        (* first arg has argless sort case *)
        inversion Hargs as [| c'' es1 es2 Hargs' nG tG G1 G2 HG]; subst;
        cbn [sort_env];
        unfold ceq_term, Norm, norm_ceq_term in HG;
        cbn in HG;
        exact HG
      ].
    repeat (
      match goal with
      | H : _ \/ _ |- _ => destruct H
      | H : False |- _ => exact (False_rect _ H)
      | H : _ = _ |- _ =>
          first [
            discriminate H
          | (* sort_rule: multi-level injection *)
            (let rec_inj := (repeat injection H; clear H; intros) in
             rec_inj; handle_sort_rule Hargs)
          ]
      end).
Qed.

(* ================================================================== *)
(* Helpers for cterm_cong                                              *)
(* ================================================================== *)

(* Invert the first cons of ceq_args *)
Ltac inv_args_cons H :=
  inversion H as [|? ? ? ? ? ? ? ? ? ? ? ?]; subst; clear H.

(* Unfold ceq_term for a given sort head *)
Ltac unfold_ceq_head :=
  unfold ceq_term, Norm, norm_ceq_term; cbn.

(* Unfold ceq_term in hypothesis H *)
Ltac unfold_ceq_in H :=
  unfold ceq_term, Norm, norm_ceq_term in H; cbn in H.

(* ================================================================== *)
(* cterm_cong                                                          *)
(* ================================================================== *)

(* Key points per former:
   - Eval constructors carry syntactic annotations (G, i, A in wkn/hd/ev_Emptyrec)
     but EVAL IGNORES them (ev_wkn pops head of env regardless of annotation).
   - Problematic cases: ext, Emptyrec, U (neutral/value carries annotation)
   - All other cases build the same semantic witness from both s1 and s2.

   ADMITTED:
   - ext: eval_env (ext G1...) = eval_env (ext G2...) requires syntactic G1=G2 etc.
   - Emptyrec: ev_Emptyrec neutral carries syntactic G,rA,lA,A
   - U: ev_U gives dU r l which carries syntactic r and l
   - El: ev_El needs e to eval to vCode T
   - El subst: same issue as El (for the ty_subst side)
   - U subst: same issue as U
*)

Lemma Norm_cterm_cong : forall (c c' : @ctx string) (name : string) (args : list string)
    (t : @sort string) s1 s2,
    In (name, term_rule c' args t) fo_lang ->
    ceq_args (CM := Norm) c c' s1 s2 ->
    ceq_term (CutTModel := Norm) c t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c c' name args t s1 s2 Hin Hargs.
  unfold fo_lang in Hin.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [[[Hin | Hin] | Hin] | Hin].

  (* ===== ott_nat ===== *)
  - revert Hin Hargs.
    vm_compute [ott_nat In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    (* Emptyrec *)
    + intro Hargs.
      inv_args_cons Hargs.
      inv_args_cons Hargs.
      inv_args_cons Hargs.
      inv_args_cons Hargs.
      inv_args_cons Hargs.
      inversion Hargs; subst. clear Hargs.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H5. rewrite eqb_exp_true in H5.
      destruct H5 as [ve [He1 He2]].
      (* Emptyrec: ev_Emptyrec needs ve = vNe ne, and the result neutral
         carries the syntactic G,rA,lA,A from the RESPECTIVE side (s1 vs s2).
         So we can't have a single common witness. ADMITTED. *)
      admit.
    (* Empty *)
    + intro Hargs.
      inv_args_cons Hargs. inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      exact (existT _ (vCode dEmpty) (ev_Empty _ _, ev_Empty _ _)).
    (* suc *)
    + intro Hargs.
      inv_args_cons Hargs.
      inv_args_cons Hargs.
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H3. rewrite eqb_exp_true in H3.
      destruct H3 as [vn [Hn1 Hn2]].
      exact (existT _ (vSuc vn) (ev_suc _ _ _ _ Hn1, ev_suc _ _ _ _ Hn2)).
    (* zero *)
    + intro Hargs.
      inv_args_cons Hargs. inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      exact (existT _ vZero (ev_zero _ _, ev_zero _ _)).
    (* Nat *)
    + intro Hargs.
      inv_args_cons Hargs. inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      exact (existT _ (vCode dNat) (ev_Nat _ _, ev_Nat _ _)).
    + tauto.

  (* ===== ott_base ===== *)
  - revert Hin Hargs.
    vm_compute [ott_base In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    (* El *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* r *)
      inv_args_cons Hargs. (* l *)
      inv_args_cons Hargs. (* e *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      unfold_ceq_in H5. rewrite eqb_exp_true in H5.
      destruct H5 as [ve [He1 He2]].
      (* ve must be vCode T for ev_El to apply. ADMITTED *)
      admit.
    (* U *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* r *)
      inv_args_cons Hargs. (* l *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      (* ev_U gives dU r1 l1 for LHS and dU r2 l2 for RHS.
         These differ unless r1=r2, l1=l2 syntactically. ADMITTED *)
      admit.
    + tauto.

  (* ===== subst_ott ===== *)
  - revert Hin Hargs.
    vm_compute [subst_ott In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    (* hd: ev_hd just looks at head of env, ignores annotation args *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      (* eval_env (ext G2 i2 A2) = vNe(hd G2 i2 A2) :: ...; ev_hd gives head of list *)
      exists (vNe (con "hd" [H2; H4; H6])). split; apply ev_hd.
    (* wkn: ev_wkn pops head, gives tail *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      exists (map weaken_val (eval_env H2)). split; apply ev_wkn.
    (* snoc *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H9. rewrite eqb_exp_true in H9.
      destruct H7 as [rg [Hg1 Hg2]], H9 as [vv [Hv1 Hv2]].
      exact (existT _ (vv :: rg) (ev_snoc _ _ _ _ _ _ _ _ Hg1 Hv1,
                                  ev_snoc _ _ _ _ _ _ _ _ Hg2 Hv2)).
    (* ext: result sort is env; eval_env (ext G1...) ≠ eval_env (ext G2...) in general. ADMITTED *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head.
      (* goal: eval_env (con "ext" s1) = eval_env (con "ext" s2) *)
      (* requires syntactic equality of annotations. ADMITTED *)
      admit.
    (* forget *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      exact (existT _ [] (ev_forget _ _, ev_forget _ _)).
    (* emp: no args, result env *)
    + intro Hargs.
      inversion Hargs; subst.
      unfold_ceq_head. reflexivity.
    (* exp_subst *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H11. rewrite eqb_exp_true in H11.
      destruct H7 as [rg [Hg1 Hg2]], H11 as [vv [Hv1 Hv2]].
      exact (existT _ vv (ev_exp_subst _ _ _ _ _ _ _ _ Hg1 Hv1,
                          ev_exp_subst _ _ _ _ _ _ _ _ Hg2 Hv2)).
    (* ty_subst *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H9. rewrite eqb_ty_true in H9.
      destruct H7 as [rg [Hg1 Hg2]], H9 as [T [HA1 HA2]].
      exact (existT _ T (ev_ty_subst _ _ _ _ _ _ _ _ Hg1 HA1,
                         ev_ty_subst _ _ _ _ _ _ _ _ Hg2 HA2)).
    (* cmp *)
    + intro Hargs.
      inv_args_cons Hargs. (* G1 *)
      inv_args_cons Hargs. (* G2 *)
      inv_args_cons Hargs. (* G3 *)
      inv_args_cons Hargs. (* f *)
      inv_args_cons Hargs. (* g *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H9. rewrite eqb_sub_true in H9.
      destruct H7 as [rf [Hf1 Hf2]], H9 as [rg [Hg1 Hg2]].
      exact (existT _ rg (ev_cmp _ _ _ _ _ _ _ _ Hf1 Hg1,
                          ev_cmp _ _ _ _ _ _ _ _ Hf2 Hg2)).
    (* id *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      exact (existT _ (eval_env H2) (ev_id _ _, ev_id _ _)).
    + tauto.

  (* ===== ott_info ===== *)
  - revert Hin Hargs.
    vm_compute [ott_info In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    all: intro Hargs.
    (* All ott_info formers have sort tyinfo/tlvl/lvl/relevance/ltl *)
    (* Their ceq_term is either unit (no first exp/ty/sub arg) or reflexivity *)
    all: unfold_ceq_head; try exact tt; try reflexivity.
    all: tauto.
Admitted.

(* ================================================================== *)
(* cterm_by: computation rules                                         *)
(* ================================================================== *)

Lemma Norm_cterm_by : forall (c c' : @ctx string) (name : string) e1r e2r tr s1 s2,
    In (name, term_eq_rule c' e1r e2r tr) fo_lang ->
    ceq_args (CM := Norm) c c' s1 s2 ->
    ceq_term (CutTModel := Norm) c tr[/with_names_from c' s2/]
             e1r[/with_names_from c' s1/] e2r[/with_names_from c' s2/].
Proof.
  intros c c' name e1r e2r tr s1 s2 Hin Hargs.
  unfold fo_lang in Hin.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [[[Hin | Hin] | Hin] | Hin].

  (* ===== ott_nat eq rules: Empty subst, suc subst, zero subst, Nat subst ===== *)
  - revert Hin Hargs.
    vm_compute [ott_nat In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    (* Empty subst: exp_subst g Empty = Empty *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rg [Hg1 Hg2]].
      exact (existT _ (vCode dEmpty)
               (ev_exp_subst _ _ _ _ _ _ _ _ Hg1 (ev_Empty _ _),
                ev_Empty _ _)).
    (* suc subst: exp_subst g (suc n) = suc (exp_subst g n) *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* n *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      unfold_ceq_in H7. rewrite eqb_exp_true in H7.
      destruct H5 as [rg [Hg1 Hg2]], H7 as [vn [Hn1 Hn2]].
      exact (existT _ (vSuc vn)
               (ev_exp_subst _ _ _ _ _ _ _ _ Hg1 (ev_suc _ _ _ _ Hn1),
                ev_suc _ _ _ _ (ev_exp_subst _ _ _ _ _ _ _ _ Hg2 Hn2))).
    (* zero subst: exp_subst g zero = zero *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rg [Hg1 Hg2]].
      exact (existT _ vZero
               (ev_exp_subst _ _ _ _ _ _ _ _ Hg1 (ev_zero _ _),
                ev_zero _ _)).
    (* Nat subst: exp_subst g Nat = Nat *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rg [Hg1 Hg2]].
      exact (existT _ (vCode dNat)
               (ev_exp_subst _ _ _ _ _ _ _ _ Hg1 (ev_Nat _ _),
                ev_Nat _ _)).
    + tauto.

  (* ===== ott_base eq rules: El subst, U subst ===== *)
  - revert Hin Hargs.
    vm_compute [ott_base In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    (* El subst: ty_subst g (El e) = El (exp_subst g e) *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* r *)
      inv_args_cons Hargs. (* l *)
      inv_args_cons Hargs. (* e *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      unfold_ceq_in H11. rewrite eqb_exp_true in H11.
      destruct H5 as [rg [Hg1 Hg2]], H11 as [ve [He1 He2]].
      (* ve needs to be vCode T for ev_El to fire. ADMITTED *)
      admit.
    (* U subst: ty_subst g U = U *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* r *)
      inv_args_cons Hargs. (* l *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rg [Hg1 Hg2]].
      (* ev_U gives dU r l which carries syntactic r and l. ADMITTED *)
      admit.
    + tauto.

  (* ===== subst_ott eq rules ===== *)
  - revert Hin Hargs.
    vm_compute [subst_ott In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    (* snoc_wkn_hd: snoc wkn hd = id (ext G i A) *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      exact (existT _ (eval_env (con "ext" [H2; H4; H6]))
               (ev_snoc _ _ _ _ _ _ _ _ (ev_wkn _ _ _ _ _) (ev_hd _ _ _ _),
                ev_id _ _)).
    (* cmp_snoc: cmp f (snoc g v) = snoc (cmp f g) (exp_subst f v) *)
    + intro Hargs.
      inv_args_cons Hargs. (* G1 *)
      inv_args_cons Hargs. (* G2 *)
      inv_args_cons Hargs. (* G3 *)
      inv_args_cons Hargs. (* f *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H9. rewrite eqb_sub_true in H9.
      unfold_ceq_in H13. rewrite eqb_exp_true in H13.
      destruct H7 as [rf [Hf1 Hf2]], H9 as [rg [Hg1 Hg2]], H13 as [vv [Hv1 Hv2]].
      exact (existT _ (vv :: rg)
               (ev_cmp _ _ _ _ _ _ _ _ Hf1 (ev_snoc _ _ _ _ _ _ _ _ Hg1 Hv1),
                ev_snoc _ _ _ _ _ _ _ _ (ev_cmp _ _ _ _ _ _ _ _ Hf2 Hg2)
                                        (ev_exp_subst _ _ _ _ _ _ _ _ Hf2 Hv2))).
    (* snoc_hd: exp_subst (snoc g v) hd = v *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H11. rewrite eqb_exp_true in H11.
      destruct H7 as [rg [Hg1 Hg2]], H11 as [vv [Hv1 Hv2]].
      exact (existT _ vv
               (ev_exp_subst _ _ _ _ _ _ _ _ (ev_snoc _ _ _ _ _ _ _ _ Hg1 Hv1) (ev_hd _ _ _ _),
                Hv2)).
    (* wkn_snoc: cmp (snoc g v) wkn = g *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H11. rewrite eqb_exp_true in H11.
      destruct H7 as [rg [Hg1 Hg2]], H11 as [vv [Hv1 Hv2]].
      exact (existT _ rg
               (ev_cmp _ _ _ _ _ _ _ _ (ev_snoc _ _ _ _ _ _ _ _ Hg1 Hv1) (ev_wkn _ _ _ _ _),
                Hg2)).
    (* id_emp_forget: id emp = forget emp *)
    + intro Hargs.
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      exact (existT _ [] (ev_id _ _, ev_forget _ _)).
    (* cmp_forget: cmp g (forget G') = forget G *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* g *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rg [Hg1 Hg2]].
      exact (existT _ []
               (ev_cmp _ _ _ _ _ _ _ _ Hg1 (ev_forget _ _),
                ev_forget _ _)).
    (* exp_subst_cmp: exp_subst f (exp_subst g v) = exp_subst (cmp f g) v *)
    + intro Hargs.
      inv_args_cons Hargs. (* G1 *)
      inv_args_cons Hargs. (* G2 *)
      inv_args_cons Hargs. (* G3 *)
      inv_args_cons Hargs. (* f *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H9. rewrite eqb_sub_true in H9.
      unfold_ceq_in H13. rewrite eqb_exp_true in H13.
      destruct H7 as [rf [Hf1 Hf2]], H9 as [rg [Hg1 Hg2]], H13 as [vv [Hv1 Hv2]].
      exact (existT _ vv
               (ev_exp_subst _ _ _ _ _ _ _ _ Hf1 (ev_exp_subst _ _ _ _ _ _ _ _ Hg1 Hv1),
                ev_exp_subst _ _ _ _ _ _ _ _ (ev_cmp _ _ _ _ _ _ _ _ Hf2 Hg2) Hv2)).
    (* exp_subst_id: exp_subst id v = v *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inv_args_cons Hargs. (* v *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_exp_true.
      unfold_ceq_in H7. rewrite eqb_exp_true in H7.
      destruct H7 as [vv [Hv1 Hv2]].
      exact (existT _ vv
               (ev_exp_subst _ _ _ _ _ _ _ _ (ev_id _ _) Hv1,
                Hv2)).
    (* ty_subst_cmp: ty_subst f (ty_subst g A) = ty_subst (cmp f g) A *)
    + intro Hargs.
      inv_args_cons Hargs. (* G1 *)
      inv_args_cons Hargs. (* G2 *)
      inv_args_cons Hargs. (* G3 *)
      inv_args_cons Hargs. (* f *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      unfold_ceq_in H7. rewrite eqb_sub_true in H7.
      unfold_ceq_in H9. rewrite eqb_sub_true in H9.
      unfold_ceq_in H11. rewrite eqb_ty_true in H11.
      destruct H7 as [rf [Hf1 Hf2]], H9 as [rg [Hg1 Hg2]], H11 as [T [HA1 HA2]].
      exact (existT _ T
               (ev_ty_subst _ _ _ _ _ _ _ _ Hf1 (ev_ty_subst _ _ _ _ _ _ _ _ Hg1 HA1),
                ev_ty_subst _ _ _ _ _ _ _ _ (ev_cmp _ _ _ _ _ _ _ _ Hf2 Hg2) HA2)).
    (* ty_subst_id: ty_subst id A = A *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* i *)
      inv_args_cons Hargs. (* A *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_ty_true.
      unfold_ceq_in H5. rewrite eqb_ty_true in H5.
      destruct H5 as [T [HA1 HA2]].
      exact (existT _ T
               (ev_ty_subst _ _ _ _ _ _ _ _ (ev_id _ _) HA1,
                HA2)).
    (* cmp_assoc: cmp f (cmp g h) = cmp (cmp f g) h *)
    + intro Hargs.
      inv_args_cons Hargs. (* G1 *)
      inv_args_cons Hargs. (* G2 *)
      inv_args_cons Hargs. (* G3 *)
      inv_args_cons Hargs. (* G4 *)
      inv_args_cons Hargs. (* f *)
      inv_args_cons Hargs. (* g *)
      inv_args_cons Hargs. (* h *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H9. rewrite eqb_sub_true in H9.
      unfold_ceq_in H11. rewrite eqb_sub_true in H11.
      unfold_ceq_in H13. rewrite eqb_sub_true in H13.
      destruct H9 as [rf [Hf1 Hf2]], H11 as [rg [Hg1 Hg2]], H13 as [rh [Hh1 Hh2]].
      exact (existT _ rh
               (ev_cmp _ _ _ _ _ _ _ _ Hf1 (ev_cmp _ _ _ _ _ _ _ _ Hg1 Hh1),
                ev_cmp _ _ _ _ _ _ _ _ (ev_cmp _ _ _ _ _ _ _ _ Hf2 Hg2) Hh2)).
    (* id_left: cmp id f = f *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* f *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rf [Hf1 Hf2]].
      exact (existT _ rf
               (ev_cmp _ _ _ _ _ _ _ _ (ev_id _ _) Hf1,
                Hf2)).
    (* id_right: cmp f id = f *)
    + intro Hargs.
      inv_args_cons Hargs. (* G *)
      inv_args_cons Hargs. (* G' *)
      inv_args_cons Hargs. (* f *)
      inversion Hargs; subst.
      unfold_ceq_head. rewrite eqb_sub_true.
      unfold_ceq_in H5. rewrite eqb_sub_true in H5.
      destruct H5 as [rf [Hf1 Hf2]].
      exact (existT _ rf
               (ev_cmp _ _ _ _ _ _ _ _ Hf1 (ev_id _ _),
                Hf2)).
    + tauto.

  (* ===== ott_info eq rules: next1, next0, ltl_irr ===== *)
  - revert Hin Hargs.
    vm_compute [ott_info In fst snd] in Hin. intro Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as ? ?; subst |]).
    all: intro Hargs.
    (* next1: next L1 = inf : tlvl *)
    (* next0: next L0 = iota L1 : tlvl *)
    (* ltl_irr: p1 = p2 : ltl a b *)
    (* All these have sorts tlvl or ltl (argless or ltl which falls in unit case) *)
    all: try (
      inv_args_cons Hargs; try inv_args_cons Hargs;
      try inv_args_cons Hargs; try inv_args_cons Hargs;
      try (inversion Hargs; subst);
      unfold_ceq_head; try exact tt; try reflexivity).
    all: tauto.
Admitted.

(* ================================================================== *)
(* Final Instance                                                      *)
(* ================================================================== *)

#[export] Instance Norm_ok : CutTModel_ok (CM := Norm) fo_lang.
Proof.
  constructor.
  - exact Norm_cterm_var.
  - exact Norm_cterm_cong.
  - exact Norm_cterm_by.
  - exact Norm_cterm_trans.
  - exact Norm_cterm_sym.
  - exact Norm_cterm_conv.
  - exact Norm_csort_cong.
  - exact Norm_csort_by.
  - exact Norm_csort_trans.
  - exact Norm_csort_sym.
Defined.
