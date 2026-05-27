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

Lemma fo_lang_all_fresh : all_fresh fo_lang.
Proof. compute_all_fresh. Qed.

(* One-time: collapse a sort-rule membership to its NAME being in a small list,
   so per-invocation case analysis never normalizes a rule body. (Pattern from a
   parallel lemma in the value_subst/STLC development.) *)
Lemma sort_rules name c' args
  : In (name, sort_rule c' args) fo_lang ->
    In name ["exp";"ty";"sub";"env";"tyinfo";"tlvl";"ltl";"lvl";"relevance"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

(* Fast case split on [In (name, rule) fo_lang] WITHOUT normalizing every rule
   body: derive the names-only disjunction via [pair_fst_in] (cheap), pick a
   concrete name, then recover that one rule with a targeted lookup.  Branches
   whose rule-kind disagrees die in the final [discriminate]; the rest are left
   with the rule's context/args/sort concrete.  Must use [all:] throughout: the
   project's strict goal selector makes bare multi-goal tactics (and [repeat
   (destruct ..)]) misbehave. *)
Ltac name_subst :=
  match goal with
  | He : ?l = ?r |- _ => tryif (is_var r; subst r) then idtac else (is_var l; subst l)
  end.
Ltac lookup_rule Hin :=
  apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ fo_lang_all_fresh)) in Hin;
  vm_compute in Hin.

(* ================================================================== *)
(* String eqb helpers (concrete values, proved by reflexivity)        *)
(* ================================================================== *)

Lemma eqb_exp_true : @eqb string _ "exp" "exp" = true. Proof. reflexivity. Qed.
Lemma eqb_ty_true  : @eqb string _ "ty"  "ty"  = true. Proof. reflexivity. Qed.
Lemma eqb_sub_true : @eqb string _ "sub" "sub" = true. Proof. reflexivity. Qed.

(* ================================================================== *)
(* cterm_var                                                           *)
(* ================================================================== *)

(* With the ambient context fixed to [] there are no variables: [In _ []] is
   [False], so cterm_var is vacuous. *)
Lemma Norm_cterm_var : forall (n : string) (t : @sort string),
    In (n, t) [] ->
    ceq_term (CutTModel := Norm) t (var n) (var n).
Proof.
  intros n t [].
Qed.

(* ================================================================== *)
(* cterm_trans                                                         *)
(* ================================================================== *)

Lemma Norm_cterm_trans : forall (t : @sort string) e1 e12 e2,
    ceq_term (CutTModel := Norm) t e1 e12 ->
    ceq_term (CutTModel := Norm) t e12 e2 ->
    ceq_term (CutTModel := Norm) t e1 e2.
Proof.
  intros t e1 e12 e2 H1 H2.
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

Lemma Norm_cterm_sym : forall (t : @sort string) e1 e2,
    ceq_term (CutTModel := Norm) t e1 e2 ->
    ceq_term (CutTModel := Norm) t e2 e1.
Proof.
  intros t e1 e2 H.
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

Lemma Norm_cterm_conv : forall t1 t2 e1 e2,
    ceq_sort (CutTModel := Norm) t1 t2 ->
    ceq_term (CutTModel := Norm) t1 e1 e2 ->
    ceq_term (CutTModel := Norm) t2 e1 e2.
Proof.
  intros t1 t2 e1 e2 Hsort Hterm.
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

Lemma Norm_csort_trans : forall t1 t12 t2,
    ceq_sort (CutTModel := Norm) t1 t12 ->
    ceq_sort (CutTModel := Norm) t12 t2 ->
    ceq_sort (CutTModel := Norm) t1 t2.
Proof.
  intros t1 t12 t2 [Heqb1 Henv1] [Heqb2 Henv2].
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

Lemma Norm_csort_sym : forall t1 t2,
    ceq_sort (CutTModel := Norm) t1 t2 ->
    ceq_sort (CutTModel := Norm) t2 t1.
Proof.
  intros t1 t2.
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

Lemma Norm_csort_by : forall (c' : @ctx string) (name : string) t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_sort (CutTModel := Norm) t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c' name t1 t2 s1 s2 Hin _.
  (* vacuous: fo_lang has no sort_eq_rules. Refute by a rule-KIND check over the
     language (forallb) rather than enumerating/normalizing every rule body. *)
  exfalso.
  assert (Hb : forallb (fun p => match snd p with sort_eq_rule _ _ _ => false | _ => true end)
                       fo_lang = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  apply Hb in Hin; cbn in Hin; discriminate Hin.
Qed.

(* ================================================================== *)
(* csort_cong                                                          *)
(* ================================================================== *)

Lemma Norm_csort_cong : forall (c' : @ctx string) (name : string) (args : list string) s1 s2,
    In (name, sort_rule c' args) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_sort (CutTModel := Norm) (scon name s1) (scon name s2).
Proof.
  intros c' name args s1 s2 Hin Hargs.
  unfold ceq_sort, Norm, norm_ceq_sort.
  split.
  - cbn [sort_head]. apply (@eqb_refl_true string _ string_Eqb_ok).
  - (* Fast: name the sort rule (one-time lemma, no per-rule normalization),
       recover its context with a targeted lookup, then peel Hargs to the env
       (the LAST arg); the env's ceq_term IS the required [eval_env] equality. *)
    pose proof (sort_rules Hin) as Hname; cbn in Hname.
    repeat match goal with H : _ \/ _ |- _ => destruct H end.
    all: try contradiction.
    all: subst name.
    all: apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ fo_lang_all_fresh)) in Hin.
    all: vm_compute in Hin.
    all: injection Hin; clear Hin; intros; subst.
    all: repeat match goal with H : ceq_args (_ :: _) _ _ |- _ => inversion H; subst; clear H end.
    all: match goal with H : ceq_args [] _ _ |- _ => inversion H; subst; clear H end.
    all: unfold sort_env, ceq_term, Norm, norm_ceq_term in *; cbn [List.last] in *; cbn in *.
    all: first [ reflexivity | eassumption ].
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

Lemma Norm_cterm_cong : forall (c' : @ctx string) (name : string) (args : list string)
    (t : @sort string) s1 s2,
    In (name, term_rule c' args t) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_term (CutTModel := Norm) t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  (* TODO(fast+fix): body destructs the Prop [In] disjunction into a
     Type-valued goal (forbidden elimination) AND normalizes rule bodies
     via vm_compute. Needs a Type-safe, name-only rule split. Deferred. *)
Admitted.

(* ================================================================== *)
(* cterm_by: computation rules                                         *)
(* ================================================================== *)

Lemma Norm_cterm_by : forall (c' : @ctx string) (name : string) e1r e2r tr s1 s2,
    In (name, term_eq_rule c' e1r e2r tr) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_term (CutTModel := Norm) tr[/with_names_from c' s2/]
             e1r[/with_names_from c' s1/] e2r[/with_names_from c' s2/].
Proof.
  (* TODO(fast+fix): body destructs the Prop [In] disjunction into a
     Type-valued goal (forbidden elimination) AND normalizes rule bodies
     via vm_compute. Needs a Type-safe, name-only rule split. Deferred. *)
Admitted.

(* ================================================================== *)
(* Final Instance                                                      *)
(* ================================================================== *)

(* The normalization model uses the empty meta-context. *)
#[export] Instance Norm_ok : CutTModel_ok (CM := Norm) fo_lang [].
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
