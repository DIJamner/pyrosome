Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
Require Import WIP.DttModel WIP.DttNormalForms WIP.DttLogRel WIP.DttRSub
  WIP.DttCeq.
Import Core.Notations.

(* =====================================================================
   LAYERS 4b/4c: the [CutTModel_ok] obligations and the assembly.

   STATEMENTS ONLY.  The obligation COUNT for [ott_dtt] (68 rules) is

     cterm_cong   32   one per term_rule
     cterm_by     27   one per term_eq_rule
     csort_cong    9   one per sort_rule
     csort_by      0   the language has NO sort equations
     structural    6   cterm_var, cterm_trans, cterm_sym, cterm_conv,
                       csort_trans, csort_sym
     ----------------
     total        74   (the STLC proof had 16 + 18 + 5 + 6 = 45)

   The 32 [cterm_cong] cases, in the language's own order:
     app_irr  app_rel  lam_irr  lam_rel  Pi_irr  Pi_rel  Emptyrec  Empty
     suc  zero  Nat  El  U  hd  wkn  snoc  ext  forget  emp  exp_subst
     ty_subst  cmp  id  info  next  inf  iota  L0<L1  L1  L0  irr  rel

   The 27 [cterm_by] cases:
     lam_rel subst   Pi_irr beta   Pi_rel beta   Pi_irr subst  Pi_rel subst
     Empty subst     suc subst     zero subst    Nat subst     El subst
     U subst         snoc_wkn_hd   cmp_snoc      snoc_hd       wkn_snoc
     id_emp_forget   cmp_forget    exp_subst_cmp exp_subst_id  ty_subst_cmp
     ty_subst_id     cmp_assoc     id_left       id_right      next1
     next0           ltl_irr

   The 9 [csort_cong] cases: exp  ty  sub  env  tyinfo  tlvl  ltl  lvl
   relevance.  Five are 0-ary and give syntactic equality; [ltl] is proof
   irrelevant; the substantive ones are [sub], [ty], [exp].

   NOTE on where the two halves' difficulty sits, relative to STLC:
     - The 12 index-constructor congruences (info/next/inf/iota/L0<L1/L1/
       L0/irr/rel plus emp/id/forget) and the 4 index equations (next0/
       next1/ltl_irr/id_emp_forget) are essentially free.
     - The substitution-calculus block (ty_subst, exp_subst, snoc, wkn, hd,
       ext, cmp + their 11 equations) is the direct analogue of the STLC
       block, but every statement acquires a type that must itself be
       substituted; the extra work is the [ty_subst_cmp]/[wkn_snoc]
       rewriting that lines the two up.
     - The genuinely new cases are: [U]/[El] (the universe), [Pi_rel]/
       [Pi_irr] (type formers that are TERMS), and the two beta rules.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* The 6 structural obligations                                         *)
(* ------------------------------------------------------------------ *)

(* [cterm_var]: the meta-context is EMPTY.  This device survives unchanged
   from the STLC proof: openness is carried at the object level by the
   environment [G], object-level variables are [hd] and its [wkn]-shifts
   ([VarT] of Layer 1), and [subst_ott] provides exactly the same
   [emp]/[ext]/[wkn]/[hd]/[snoc]/[forget]/[cmp]/[id] shape as
   [value_subst] does for STLC (verified against the compiled language).
   So there is nothing for [cterm_var] to relate. *)
Lemma var_obligation
  : forall n t, In (n, t) (@nil (string * sort)) -> Ceq_term t (var n) (var n).
Proof. intros n t H; destruct H. Qed.

(* [csort_by]: VACUOUS -- [ott_dtt] contains no [sort_eq_rule].  This is
   the one of the four structural generalizations that turns out to be
   EASIER than feared: OTT's "type equality" is term equality at the sort
   [ty], not sort equality. *)
Lemma sort_by_obligation
  : forall c' name t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_sort t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c' name t1 t2 s1 s2 Hin Hargs.
  vm_compute in Hin; repeat (destruct Hin as [Hin|Hin]);
    first [ discriminate | destruct Hin ].
Qed.

(* [cterm_conv], [csort_trans], [csort_sym]: projections, by construction
   of [Ceq_sort]. *)
Lemma term_conv_obligation
  : forall t1 t2 e1 e2, Ceq_sort t1 t2 -> Ceq_term t1 e1 e2 -> Ceq_term t2 e1 e2.
Proof. intros t1 t2 e1 e2 [_ [Hf _]] H; apply Hf; exact H. Qed.

Lemma sort_trans_obligation
  : forall t1 t12 t2, Ceq_sort t1 t12 -> Ceq_sort t12 t2 -> Ceq_sort t1 t2.
Admitted.

Lemma sort_sym_obligation : forall t1 t2, Ceq_sort t1 t2 -> Ceq_sort t2 t1.
Proof. intros t1 t2 [Hs [Hf Hb]]; repeat split; try assumption.
  (* eq_sort is symmetric *)
Admitted.

(* [cterm_trans]/[cterm_sym].  As in Stlc/Ceq.v the semantic conjunct
   constrains only [e1]; the corresponding fact for [e2] is recovered from
   the equation by [RTm_eq]/[RSub_eq]/[RTy_irr]. *)
Lemma term_trans_obligation
  : forall t e1 e12 e2, Ceq_term t e1 e12 -> Ceq_term t e12 e2 -> Ceq_term t e1 e2.
Admitted.

Lemma term_sym_obligation
  : forall t e1 e2, Ceq_term t e1 e2 -> Ceq_term t e2 e1.
Admitted.

(* ------------------------------------------------------------------ *)
(* The 9 sort congruences                                               *)
(* ------------------------------------------------------------------ *)

Lemma sort_cong_obligation
  : forall c' name args s1 s2,
    In (name, sort_rule c' args) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_sort (scon name s1) (scon name s2).
Admitted.

(* The three substantive cases, stated separately since they are what the
   design stands or falls on.  Each is a bi-directional transfer, and each
   should follow from the guarded definitions of Layers 2 and 3 WITHOUT
   any inversion of [eq_sort]. *)

Lemma sort_cong_sub G1 G2 G1' G2'
  : Ceq_term sEnv G1 G2 -> Ceq_term sEnv G1' G2' ->
    Ceq_sort (sSub G1 G1') (sSub G2 G2').
Admitted.

Lemma sort_cong_ty G1 G2 i1 i2
  : Ceq_term sEnv G1 G2 -> Ceq_term sInfo i1 i2 ->
    Ceq_sort (sTy G1 i1) (sTy G2 i2).
Admitted.

Lemma sort_cong_exp G1 G2 i1 i2 A1 A2
  : Ceq_term sEnv G1 G2 -> Ceq_term sInfo i1 i2 ->
    Ceq_term (sTy G1 i1) A1 A2 ->
    Ceq_sort (sExp G1 i1 A1) (sExp G2 i2 A2).
Admitted.

(* ------------------------------------------------------------------ *)
(* The 32 term congruences and the 27 equation instances                *)
(* ------------------------------------------------------------------ *)

Lemma cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Admitted.

Lemma by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/]
             e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Admitted.

(* ------------------------------------------------------------------ *)
(* Assembly                                                             *)
(* ------------------------------------------------------------------ *)

Lemma wf_ctx_nil_dtt : wf_ctx (Model := core_model ott_dtt) [].
Proof. constructor. Qed.

#[export] Instance DttCM_ok : CutTModel_ok (CM := DttCM) ott_dtt [].
Admitted.

(* ------------------------------------------------------------------ *)
(* NORMALIZATION                                                        *)
(*                                                                      *)
(* Same shape as Gluing/Stlc/ModelOk.v's [stlc_unit_normalization]: the    *)
(* model gives content at [e] from well-typedness alone, the semantic     *)
(* conjunct is instantiated at the identity substitution ([RSub_id]),     *)
(* [ty_subst_id]/[exp_subst_id] strip the substitution, and [RTm_escape]  *)
(* delivers the normal form.  The statement is about GENUINELY OPEN       *)
(* terms: openness is carried by the object-level environment [G].        *)
(* ------------------------------------------------------------------ *)

Theorem ott_dtt_normalization G i A e
  : EnvOk G -> TyOk G i A ->
    wf_term ott_dtt [] e (sExp G i A) ->
    exists n, NfET G i A n /\ eq_term ott_dtt [] (sExp G i A) e n.
Admitted.

Theorem ott_dtt_eq_normalization G i A e1 e2
  : EnvOk G -> TyOk G i A ->
    eq_term ott_dtt [] (sExp G i A) e1 e2 ->
    exists n, NfET G i A n
              /\ eq_term ott_dtt [] (sExp G i A) e1 n
              /\ eq_term ott_dtt [] (sExp G i A) e2 n.
Admitted.

(* The type-level corollary, which has no STLC counterpart: every
   well-formed type of the fragment is provably equal to a normal type.
   This is what makes the result a DECIDABILITY-grade statement about
   conversion rather than only about terms. *)
Theorem ott_dtt_ty_normalization G i A
  : EnvOk G -> wf_term ott_dtt [] A (sTy G i) -> InfoNf (ninfo i) ->
    exists A', TyOk G (ninfo i) A'
               /\ eq_term ott_dtt [] (sTy G i) A A'.
Admitted.
