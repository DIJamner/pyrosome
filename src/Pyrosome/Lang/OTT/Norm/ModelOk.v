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

(* Same names-only collapse for the term-formers (used by cterm_cong). *)
Lemma term_rules_names name c' args t
  : In (name, term_rule c' args t) fo_lang ->
    In name ["Emptyrec";"Empty";"suc";"zero";"Nat";"El";"U";"hd";"wkn";"snoc";
             "ext";"forget";"emp";"exp_subst";"ty_subst";"cmp";"id";"info";"next";
             "inf";"iota";"L0<L1";"L1";"L0";"irr";"rel"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

(* ...and for the equation rules (used by cterm_by). *)
Lemma term_eq_rules_names name c' e1 e2 t
  : In (name, term_eq_rule c' e1 e2 t) fo_lang ->
    In name ["Empty subst";"suc subst";"zero subst";"Nat subst";"El subst";
             "U subst";"snoc_wkn_hd";"cmp_snoc";"snoc_hd";"wkn_snoc";"id_emp_forget";
             "cmp_forget";"exp_subst_cmp";"exp_subst_id";"ty_subst_cmp";"ty_subst_id";
             "cmp_assoc";"id_left";"id_right";"next1";"next0";"ltl_irr"].
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
  - destruct (eqb tname "env"); etransitivity; eassumption.
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
  - destruct (eqb tname "env"); symmetry; assumption.
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
  unfold ceq_sort, Norm, norm_ceq_sort, is_env_sort, sort_head in Hsort.
  destruct t1 as [n1 l1], t2 as [n2 l2].
  destruct Hsort as [Heqb Henv].
  pose proof (proj1 (eqb_prop_iff _ _ _) ltac:(rewrite Heqb; exact I)) as Hn.
  subst n2.
  unfold ceq_term, Norm, norm_ceq_term in *.
  destruct l1 as [|G1 r1], l2 as [|G2 r2].
  - exact Hterm.
  - (* l1=[], l2=G2::r2: junk (ill-arity) case; same head, different arg count.
       Hterm is an [nf_info]/[eval_env] equation but the goal wants an eval sigma. *)
    cbn in Hterm |- *.
    destruct (eqb n1 "exp"); [| destruct (eqb n1 "ty"); [| destruct (eqb n1 "sub")]].
    all: try exact tt.
    all: admit.
  - (* l1=G1::r1, l2=[]: symmetric junk case *)
    cbn in Hterm |- *.
    destruct (eqb n1 "exp"); [| destruct (eqb n1 "ty"); [| destruct (eqb n1 "sub")]].
    all: try exact tt.
    all: admit.
  - (* both nonempty: for the env-bearing heads exp/ty/sub, the (true) dispatch
       gives [Henv : eval_env (last l1) = eval_env (last l2)], which transports the
       eval witnesses; other heads land in the [unit] branch. *)
    destruct (eqb n1 "exp") eqn:Hexp.
    + cbn [orb] in Henv.
      destruct Hterm as [v [a b]]. rewrite Henv in a, b.
      exact (existT _ v (a, b)).
    + destruct (eqb n1 "ty") eqn:Hty.
      * cbn [orb] in Henv.
        destruct Hterm as [T [a b]]. rewrite Henv in a, b.
        exact (existT _ T (a, b)).
      * destruct (eqb n1 "sub") eqn:Hsub.
        -- cbn [orb] in Henv.
           destruct Hterm as [r [a b]]. rewrite Henv in a, b.
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
  destruct t1 as [n1 l1], t12 as [n12 l12], t2 as [n2 l2].
  cbn [sort_head] in Heqb1, Heqb2.
  pose proof (proj1 (eqb_prop_iff _ n1 n12) ltac:(rewrite Heqb1; exact I)) as H1.
  pose proof (proj1 (eqb_prop_iff _ n12 n2) ltac:(rewrite Heqb2; exact I)) as H2.
  subst n12; subst n2.
  split.
  - cbn [sort_head]. apply (@eqb_refl_true string _ string_Eqb_ok).
  - (* second component: both branches of the env/static dispatch are plain
       equalities, so transitivity applies to whichever fires. *)
    destruct (is_env_sort n1); etransitivity; eassumption.
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
  cbn [sort_head].
  intros [Heqb Henv].
  pose proof (proj1 (eqb_prop_iff _ n1 n2) ltac:(rewrite Heqb; exact I)) as H.
  subst n2.
  split.
  - cbn [sort_head]. apply (@eqb_refl_true string _ string_Eqb_ok).
  - destruct (is_env_sort n1); symmetry; assumption.
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
    (* For env-bearing sorts (exp/ty/sub) the goal is the env arg's [eval_env]
       equality (eassumption); for the static sort [ltl] it is [map nf_info]
       equality of the lvl args (congruence from their [nf_info] hypotheses);
       nullary sorts close by reflexivity. *)
    all: unfold is_env_sort, ceq_term, Norm, norm_ceq_term in *;
         cbn [List.last map orb] in *; cbn in *.
    all: first [ reflexivity | eassumption | congruence ].
Qed.

(* ================================================================== *)
(* Helpers for cterm_cong  (Type-safe name split)                      *)
(* ================================================================== *)

(* The goal of cterm_cong is Type-valued (a [sigT] for exp/ty/sub heads), so the
   Prop rule-name disjunction cannot be eliminated into it.  We instead dispatch on
   [name] by BOOLEAN tests [eqb name "X"]; the true branch threads concreteness as a
   Prop equation ([name = "X"], [subst]), then recovers the one rule by a targeted
   lookup, peels [ceq_args] to per-argument witnesses, and runs a uniform solver.
   The fall-through (no name matched) is absurd by [existsb] against
   [term_rules_names] — again no disjunction elimination. *)

(* turn [eqb name "X" = true] into [name = "X"] and substitute *)
Ltac concretize_subst :=
  match goal with
  | E : eqb ?nm ?s = true |- _ =>
      let Eq := fresh in
      pose proof (proj1 (eqb_prop_iff _ nm s) ltac:(rewrite E; exact I)) as Eq;
      clear E; subst nm
  end.

(* recover the concrete rule from [name] (all_fresh lookup), then peel ceq_args *)
Ltac recover_peel :=
  match goal with Hin : In _ _ |- _ =>
    apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ fo_lang_all_fresh)) in Hin;
    vm_compute in Hin; injection Hin; clear Hin; intros; subst end;
  repeat match goal with H : ceq_args (_ :: _) _ _ |- _ => inversion H; subst; clear H end;
  try match goal with H : ceq_args [] _ _ |- _ => inversion H; subst; clear H end.

(* uniform witness builder.  Closes the formers whose eval is annotation-free or
   structural-in-the-same-env: exact tt (ltl), reflexivity (emp), econstructor from
   the peeled witnesses (zero/suc/Nat/Empty/hd/wkn/snoc/forget/id), and the info
   formers (info/next/iota/...) whose goal is [f (nf_info e1) = f (nf_info e2)] with
   [nf_info e1 = nf_info e2] in scope. *)
Ltac solve_cong :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  repeat match goal with H : @sigT _ _ |- _ => destruct H as [? [? ?]] end;
  first
    [ exact tt
    | reflexivity
    | solve [eexists; split; econstructor; solve [eassumption | eauto]]
    | solve [repeat match goal with H : @eq (@term string) _ _ |- _ => rewrite H; clear H end;
             reflexivity]
    | solve [congruence] ].

Ltac disp nm :=
  let E := fresh "Eqn" in
  match goal with
  | |- ceq_term _ (con ?name _) _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; solve_cong | ]
  end.

(* blocked formers: recover/peel for shape, then admit (see header below) *)
Ltac dispA nm :=
  let E := fresh "Eqn" in
  match goal with
  | |- ceq_term _ (con ?name _) _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; admit | ]
  end.

Ltac finish_absurd :=
  exfalso;
  match goal with
  | Hin : In (?nm, _) _ |- _ =>
      let Hn := fresh "Hn" in
      let Hex := fresh "Hex" in
      pose proof (term_rules_names Hin) as Hn;
      assert (Hex : existsb (eqb nm)
                ["Emptyrec";"Empty";"suc";"zero";"Nat";"El";"U";"hd";"wkn";"snoc";
                 "ext";"forget";"emp";"exp_subst";"ty_subst";"cmp";"id";"info";"next";
                 "inf";"iota";"L0<L1";"L1";"L0";"irr";"rel"] = true)
        by (apply (proj2 (existsb_exists _ _)); exists nm; split;
            [ exact Hn | apply (@eqb_refl_true string _ string_Eqb_ok) ]);
      cbn in Hex;
      repeat match goal with E : eqb _ _ = false |- _ => rewrite E in Hex end;
      cbn in Hex; discriminate Hex
  end.

(* ================================================================== *)
(* cterm_cong                                                          *)
(* ================================================================== *)

(* PROVEN for the 19 formers whose eval is annotation-free or structural in a single
   environment.  STILL ADMITTED (4 + 3):
   - ext / U / El / Emptyrec: the value domain carries RAW syntactic annotations
     (eval_env's hd-neutral; dU r l; the El code; the Emptyrec neutral), so the
     congruence would need syntactic equality of arguments we only relate
     semantically.  These need the de-Bruijn-level neutral redesign / normalized
     value annotations (El additionally needs an eval rule for El of a neutral).
   - exp_subst / ty_subst / cmp: the inner term is evaluated in the CODOMAIN
     reflecting environment, which requires the substitution/typing lemma
     [eval_sub (eval_env G) g (eval_env G')] not yet available (cf. snoc, which is
     unblocked because its components share the source environment). *)
Lemma Norm_cterm_cong : forall (c' : @ctx string) (name : string) (args : list string)
    (t : @sort string) s1 s2,
    In (name, term_rule c' args t) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_term (CutTModel := Norm) t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hargs.
  dispA "Emptyrec". disp "Empty". disp "suc". disp "zero". disp "Nat".
  dispA "El". dispA "U". disp "hd". disp "wkn". disp "snoc".
  dispA "ext". disp "forget". disp "emp". dispA "exp_subst". dispA "ty_subst".
  dispA "cmp". disp "id". disp "info". disp "next". disp "inf".
  disp "iota". disp "L0<L1". disp "L1". disp "L0". disp "irr". disp "rel".
  finish_absurd.
Admitted.

(* ================================================================== *)
(* cterm_by: computation rules                                         *)
(* ================================================================== *)

(* Dispatch like cterm_cong, but on [name] taken from the [In] hypothesis (the goal
   term is the equation's LHS [e1r], not [con name _]). *)
Ltac solve_by :=
  unfold ceq_term, Norm, norm_ceq_term in *; cbn in *;
  first [ exact tt | reflexivity | solve [congruence] ].

Ltac dispby nm :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; solve_by | ]
  end.

Ltac dispbyA nm :=
  let E := fresh "Eqn" in
  match goal with
  | Hin : In (?name, _) _ |- _ =>
      destruct (eqb name nm) eqn:E; [ concretize_subst; recover_peel; admit | ]
  end.

Ltac finish_absurd_by :=
  exfalso;
  match goal with
  | Hin : In (?nm, _) _ |- _ =>
      let Hn := fresh "Hn" in
      let Hex := fresh "Hex" in
      pose proof (term_eq_rules_names Hin) as Hn;
      assert (Hex : existsb (eqb nm)
                ["Empty subst";"suc subst";"zero subst";"Nat subst";"El subst";
                 "U subst";"snoc_wkn_hd";"cmp_snoc";"snoc_hd";"wkn_snoc";"id_emp_forget";
                 "cmp_forget";"exp_subst_cmp";"exp_subst_id";"ty_subst_cmp";"ty_subst_id";
                 "cmp_assoc";"id_left";"id_right";"next1";"next0";"ltl_irr"] = true)
        by (apply (proj2 (existsb_exists _ _)); exists nm; split;
            [ exact Hn | apply (@eqb_refl_true string _ string_Eqb_ok) ]);
      cbn in Hex;
      repeat match goal with E : eqb _ _ = false |- _ => rewrite E in Hex end;
      cbn in Hex; discriminate Hex
  end.

(* PROVEN: the info equations next0 (next L0 = iota L1) and next1 (next L1 = inf) —
   validated exactly by the nf_info fix — and the proof-irrelevant ltl_irr (the ltl
   sort lands in the [unit] branch).  STILL ADMITTED: the substitution-calculus
   computation rules (exp_subst_id, ty_subst_id, *_cmp, cmp_assoc, id_left/right,
   snoc_*, *_subst, ...), which need the eval relation to validate the equation
   together with the substitution/typing lemma and determinism (cf. cterm_cong's
   blocked composite formers). *)
Lemma Norm_cterm_by : forall (c' : @ctx string) (name : string) e1r e2r tr s1 s2,
    In (name, term_eq_rule c' e1r e2r tr) fo_lang ->
    ceq_args (CM := Norm) c' s1 s2 ->
    ceq_term (CutTModel := Norm) tr[/with_names_from c' s2/]
             e1r[/with_names_from c' s1/] e2r[/with_names_from c' s2/].
Proof.
  intros c' name e1r e2r tr s1 s2 Hin Hargs.
  dispbyA "Empty subst". dispbyA "suc subst". dispbyA "zero subst".
  dispbyA "Nat subst". dispbyA "El subst". dispbyA "U subst".
  dispbyA "snoc_wkn_hd". dispbyA "cmp_snoc". dispbyA "snoc_hd". dispbyA "wkn_snoc".
  dispbyA "id_emp_forget". dispbyA "cmp_forget". dispbyA "exp_subst_cmp".
  dispbyA "exp_subst_id". dispbyA "ty_subst_cmp". dispbyA "ty_subst_id".
  dispbyA "cmp_assoc". dispbyA "id_left". dispbyA "id_right".
  dispby "next1". dispby "next0". dispby "ltl_irr".
  finish_absurd_by.
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
