Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel.
Require Import WIP.DttSyntax WIP.DttWf WIP.DttEqns WIP.DttNf WIP.DttNfWf
  WIP.DttLR WIP.DttLRBasics WIP.DttLRCand WIP.DttLRFun WIP.DttInj
  WIP.DttRSub WIP.DttCeq WIP.DttModelStruct WIP.DttRSubOk.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: the [cterm_cong] and [cterm_by]
   obligations for the SUBSTITUTION-CALCULUS fragment of [ott_dtt].

   Ten congruences

       emp  ext  id  forget  cmp  ty_subst  exp_subst  snoc  wkn  hd

   and the thirteen equations of [subst_ott]

       id_left  id_right  cmp_assoc  cmp_forget  id_emp_forget
       ty_subst_id  ty_subst_cmp  exp_subst_id  exp_subst_cmp
       wkn_snoc  snoc_hd  cmp_snoc  snoc_wkn_hd

   Everything goes through WIP/DttCeq.v's constructors and clause lemmas
   and the Layer 2/3 interfaces; [Ceq_term] is inverted by hand nowhere.

   THE TWO SHAPES OF PROOF.

   (A) A CONGRUENCE at a sort with semantic content has to BUILD that
       content out of its arguments'.  For the [sub]/[ty]/[exp] formers
       this is exactly the corresponding sigma-law read backwards: e.g.
       the [cmp] clause asks for [RSubN D G3 (h o (f o g))] and the two
       argument clauses give [RSubN] of [(h o f)] and then of
       [((h o f) o g)], so "cmp_assoc" is what closes the gap.  Uniformly:
       [id]/[forget]/[wkn] use "id_right"/"cmp_forget"/"wkn_snoc",
       [ty_subst]/[exp_subst] use "ty_subst_cmp"/"exp_subst_cmp",
       [snoc] uses "cmp_snoc" and [hd] uses "snoc_hd".

   (B) An EQUATION never builds anything.  Its right-hand side's content
       is obtained by APPLYING THE CONGRUENCES ABOVE to the arguments'
       clauses, and the equation itself is then transported onto the
       left-hand side by [Ceq_*_eq_l] below -- closure of [Ceq_term] under
       provable equality of its LEFT argument.  The [eq_term] instance is
       always taken at the s1-side arguments and its sort converted
       afterwards, which is cheaper than pushing each argument equation
       through the rule.

   WHAT THE FRAGMENT LEANS ON.  Layer 3 is used through [RSubN_id],
   [RSub_proj], [RSub_ext_elim]/[RSub_ext_intro] and [EnvOk_inj]; Layer 2
   through [RTyN]/[RTmN]'s closure lemmas ([RTyN_eq], [RTyN_eq_info],
   [RTmN_eq], [RTmN_eq_info], [RTmN_eq_ty]) and nothing else -- no
   candidate is ever opened.  The one interface this fragment WANTED and
   did not find is a "reducible [snoc]" introduction rule and its inverse
   at the level of [RSubN] (Layer 3 has them only for [RSub], at a
   SYNTACTICALLY normal codomain environment); [RSubN_rep] and
   [ext_normal] below are the two-line bridges that supply it.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* 0.  Glue                                                            *)
(* ================================================================== *)

(* ---- sort conversions for [wf_term] ----------------------------- *)

Lemma wft_conv_sub g G1 G2 G1' G2'
  : wft g (sSub G1 G1') -> eqt sEnv G1 G2 -> eqt sEnv G1' G2' ->
    wft g (sSub G2 G2').
Proof.
  intros; eapply wf_term_conv; [ eassumption | apply sSub_cong; assumption ].
Qed.

Lemma wft_conv_ty A G1 G2 i1 i2
  : wft A (sTy G1 i1) -> eqt sEnv G1 G2 -> eqt sInfo i1 i2 -> wft A (sTy G2 i2).
Proof.
  intros; eapply wf_term_conv; [ eassumption | apply sTy_cong; assumption ].
Qed.

Lemma wft_conv_exp e G1 G2 i1 i2 A1 A2
  : wft e (sExp G1 i1 A1) -> eqt sEnv G1 G2 -> eqt sInfo i1 i2 ->
    eqt (sTy G2 i2) A1 A2 -> wft e (sExp G2 i2 A2).
Proof.
  intros; eapply wf_term_conv; [ eassumption | apply sExp_cong; assumption ].
Qed.

(* ---- the three semantic wrappers, packaged as one conversion ---- *)

Lemma RSubN_conv D G G' g g'
  : RSubN D G g -> eqt sEnv G G' -> eqt (sSub D G') g g' -> RSubN D G' g'.
Proof.
  intros H HG Hg; eapply RSubN_eq; [ eapply RSubN_env; eassumption | exact Hg ].
Qed.

Lemma RTyN_conv D i i' A A'
  : RTyN D i A -> eqt sInfo i i' -> eqt (sTy D i') A A' -> RTyN D i' A'.
Proof.
  intros H Hi HA; eapply RTyN_eq; [ eapply RTyN_eq_info; eassumption | exact HA ].
Qed.

Lemma RTmN_conv D i i' A A' e e'
  : RTmN D i A e -> eqt sInfo i i' -> eqt (sTy D i') A A' ->
    eqt (sExp D i' A') e e' -> RTmN D i' A' e'.
Proof.
  intros H Hi HA He.
  eapply RTmN_eq; [ eapply RTmN_eq_ty; [ eapply RTmN_eq_info; eassumption | exact HA ]
                  | exact He ].
Qed.

(* ---- closure of [Ceq_term] under equality of its LEFT argument --- *)

(* Not provable at [relevance]/[lvl], whose clauses force syntactic
   equality; the four sorts that carry a semantic conjunct are exactly the
   four that need it here. *)

Lemma Ceq_env_eq_l e G1 G2
  : Ceq_term sEnv G1 G2 -> eqt sEnv e G1 -> Ceq_term sEnv e G2.
Proof.
  intros H Heq; apply Ceq_env_e in H as [Ha [G0 [HG0 Heq0]]].
  apply ceq_env; [ eapply eq_term_trans; eassumption | ].
  exists G0; split; [ exact HG0 | eapply eq_term_trans; eassumption ].
Qed.

Lemma Ceq_sub_eq_l G G' e g1 g2
  : Ceq_term (sSub G G') g1 g2 -> eqt (sSub G G') e g1 ->
    Ceq_term (sSub G G') e g2.
Proof.
  intros H Heq; apply Ceq_sub_e in H as [Ha Hb].
  destruct (wft_sub_inv (eqt_wf_l Heq)) as [HwG HwG'].
  apply ceq_sub; [ eapply eq_term_trans; eassumption | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D G)) as Hwh by (apply RSubN_wf; exact Hh).
  apply RSubN_eq with (g := oCmp D G G' h g1); [ apply Hb; assumption | ].
  apply Cmp_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact HwG
    | apply eq_term_refl; exact HwG'
    | apply eq_term_refl; exact Hwh
    | apply eq_term_sym; exact Heq ].
Qed.

Lemma Ceq_ty_eq_l G i e A1 A2
  : Ceq_term (sTy G i) A1 A2 -> eqt (sTy G i) e A1 -> Ceq_term (sTy G i) e A2.
Proof.
  intros H Heq; apply Ceq_ty_e in H as [Ha Hb].
  destruct (wft_ty_inv (eqt_wf_l Heq)) as [HwG Hwi].
  apply ceq_ty; [ eapply eq_term_trans; eassumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G)) as Hwg by (apply RSubN_wf; exact Hg).
  apply RTyN_eq with (A := oTySubst D G g i A1); [ apply Hb; assumption | ].
  apply TySubst_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact HwG
    | apply eq_term_refl; exact Hwg
    | apply eq_term_refl; exact Hwi
    | apply eq_term_sym; exact Heq ].
Qed.

Lemma Ceq_exp_eq_l G i A e e1 e2
  : Ceq_term (sExp G i A) e1 e2 -> eqt (sExp G i A) e e1 ->
    Ceq_term (sExp G i A) e e2.
Proof.
  intros H Heq; apply Ceq_exp_e in H as [Ha Hb].
  destruct (wft_exp_inv (eqt_wf_l Heq)) as [HwG [Hwi HwA]].
  apply ceq_exp; [ eapply eq_term_trans; eassumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D G)) as Hwg by (apply RSubN_wf; exact Hg).
  apply RTmN_eq with (e := oExpSubst D G g i A e1); [ apply Hb; assumption | ].
  apply ExpSubst_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_refl; exact HwG
    | apply eq_term_refl; exact Hwg
    | apply eq_term_refl; exact Hwi
    | apply eq_term_refl; exact HwA
    | apply eq_term_sym; exact Heq ].
Qed.

(* ---- normal representatives ------------------------------------- *)

(* [RSubN] quantifies its representative environment; [EnvOk_inj] pins it
   to any normal environment provably equal to the codomain, which is what
   lets the [RSub] clauses be read at a representative built here. *)
Lemma RSubN_rep D G G0 g
  : RSubN D G g -> EnvOk G0 -> eqt sEnv G G0 -> RSub D G0 g.
Proof.
  intros [G1 (HG1 & Heq1 & HR)] HG0 Heq0.
  assert (G0 = G1) as ->; [ | exact HR ].
  apply EnvOk_inj; [ exact HG0 | exact HG1 | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact Heq0 | exact Heq1 ].
Qed.

(* The right term of an [env] clause has a normal representative too. *)
Lemma Ceq_env_rep G1 G2
  : Ceq_term sEnv G1 G2 -> exists G0, EnvOk G0 /\ eqt sEnv G2 G0.
Proof.
  intro H; apply Ceq_env_e in H as [Ha [G0 [HG0 Heq]]].
  exists G0; split; [ exact HG0 | ].
  eapply eq_term_trans; [ apply eq_term_sym; exact Ha | exact Heq ].
Qed.

(* Reading a [ty] clause at the IDENTITY substitution of a normal
   representative of its environment.  This is the only way content is
   extracted from a type argument in this fragment. *)
Lemma Ceq_ty_at_id G0 G i A1 A2
  : Ceq_term (sTy G i) A1 A2 -> EnvOk G0 -> eqt sEnv G G0 -> RTyN G0 i A1.
Proof.
  intros H HG0 Heq; apply Ceq_ty_e in H as [Ha Hb].
  destruct (wft_ty_inv (eqt_wf_l Ha)) as [HwG Hwi].
  assert (wft G0 sEnv) as HwG0 by (apply EnvOk_wf; exact HG0).
  assert (wft A1 (sTy G0 i)) as HwA1
    by (eapply wft_conv_ty;
        [ eapply eqt_wf_l; exact Ha | exact Heq | apply eq_term_refl; exact Hwi ]).
  assert (RSubN G0 G (oId G0)) as HRS.
  { eapply RSubN_env;
      [ apply RSubN_id; exact HG0 | apply eq_term_sym; exact Heq ]. }
  eapply RTyN_eq; [ apply Hb; [ exact HG0 | exact HRS ] | ].
  eapply eq_term_trans; [ | apply eq_ty_subst_id; assumption ].
  apply TySubst_cong;
    [ apply eq_term_refl; exact HwG0
    | exact Heq
    | apply eq_term_refl; apply wf_Id; exact HwG0
    | apply eq_term_refl; exact Hwi
    | apply eq_term_refl; exact HwA1 ].
Qed.

(* The normal representative of an EXTENDED environment: the workhorse of
   [ext], [snoc], [wkn] and [hd].  Everything the four cases need about it
   is returned at once. *)
Lemma ext_normal G1 G2 i A1 A2
  : Ceq_term sEnv G1 G2 -> Ceq_term (sTy G2 i) A1 A2 ->
    exists G0 i0 A0,
      EnvOk G0 /\ eqt sEnv G2 G0
      /\ eqt sInfo i i0 /\ TyOk G0 i0 A0 /\ eqt (sTy G0 i0) A2 A0
      /\ EnvOk (oExt G0 i0 A0)
      /\ eqt sEnv (oExt G2 i A2) (oExt G0 i0 A0).
Proof.
  intros HG HA.
  destruct (Ceq_env_rep HG) as [G0 [HG0 Heq]].
  pose proof (Ceq_ty_at_id HA HG0 Heq) as [i0 [A0 [P (Hi & HT & HeqA & _)]]].
  apply Ceq_ty_e in HA as [Ha _].
  assert (wft G0 sEnv) as HwG0 by (apply EnvOk_wf; exact HG0).
  assert (eqt (sTy G0 i0) A2 A0) as HeqA2.
  { eapply eq_term_trans; [ | exact HeqA ].
    apply eq_term_sym.
    eapply eq_term_conv; [ exact Ha | apply sTy_cong; assumption ]. }
  exists G0, i0, A0; repeat split; try assumption.
  - apply envok_ext; assumption.
  - apply Ext_cong; assumption.
Qed.

(* ================================================================== *)
(* 1.  The ten congruences                                             *)
(* ================================================================== *)

(* ---- the two environment formers -------------------------------- *)

Lemma cong_emp : Ceq_term sEnv oEmp oEmp.
Proof.
  apply ceq_env; [ apply Emp_cong | ].
  exists oEmp; split; [ apply envok_emp | apply eq_term_refl; apply wf_Emp ].
Qed.

(* The normal environment demanded by the [env] clause is built from the
   components': the tail's own clause supplies a normal environment, and
   the type argument's clause -- read at the IDENTITY substitution of that
   environment, which is reducible by [RSubN_id] -- supplies a normal type
   over it.  That is all [ext_normal] does. *)
Lemma cong_ext Ga Gb i1 i2 A1 A2
  : Ceq_term sEnv Ga Gb -> Ceq_term sInfo i1 i2 -> Ceq_term (sTy Gb i2) A1 A2 ->
    Ceq_term sEnv (oExt Ga i1 A1) (oExt Gb i2 A2).
Proof.
  intros HG Hi HA.
  destruct (ext_normal HG HA)
    as [G0 [i0 [A0 (HG0 & Heq & Hi0 & HT & HeqA & HE & HeqE)]]].
  apply Ceq_env_e in HG as [HGa _].
  apply Ceq_tyinfo_e in Hi as (Hia & _ & _).
  apply Ceq_ty_e in HA as [HAa _].
  assert (eqt sEnv (oExt Ga i1 A1) (oExt Gb i2 A2)) as Hstep
    by (apply Ext_cong; assumption).
  apply ceq_env; [ exact Hstep | ].
  exists (oExt G0 i0 A0); split;
    [ exact HE | eapply eq_term_trans; [ exact Hstep | exact HeqE ] ].
Qed.

(* ---- the substitution formers ----------------------------------- *)

Lemma cong_id Ga Gb
  : Ceq_term sEnv Ga Gb -> Ceq_term (sSub Gb Gb) (oId Ga) (oId Gb).
Proof.
  intro HG; apply Ceq_env_e in HG as [Ha _].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact Ha).
  apply ceq_sub; [ apply Id_cong; exact Ha | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D Gb)) as Hwh by (apply RSubN_wf; exact Hh).
  apply RSubN_eq with (g := h); [ exact Hh | ].
  apply eq_term_sym.
  assert (eqt (sSub D Gb) (oCmp D Gb Gb h (oId Ga)) (oCmp D Gb Gb h (oId Gb)))
    as Hin.
  { apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwb
      | apply eq_term_refl; exact Hwb
      | apply eq_term_refl; exact Hwh
      | apply Id_cong; exact Ha ]. }
  eapply eq_term_trans; [ exact Hin | apply eq_id_right; assumption ].
Qed.

Lemma cong_forget Ga Gb
  : Ceq_term sEnv Ga Gb -> Ceq_term (sSub Gb oEmp) (oForget Ga) (oForget Gb).
Proof.
  intro HG; apply Ceq_env_e in HG as [Ha _].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact Ha).
  apply ceq_sub; [ apply Forget_cong; exact Ha | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D Gb)) as Hwh by (apply RSubN_wf; exact Hh).
  apply RSubN_eq with (g := oForget D).
  - apply RSubN_of_RSub;
      [ apply envok_emp
      | apply RSub_emp_intro; apply eq_term_refl; apply wf_Forget; exact HwD ].
  - apply eq_term_sym.
    assert (eqt (sSub D oEmp)
              (oCmp D Gb oEmp h (oForget Ga)) (oCmp D Gb oEmp h (oForget Gb)))
      as Hin.
    { apply Cmp_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwb
        | apply eq_term_refl; apply wf_Emp
        | apply eq_term_refl; exact Hwh
        | apply Forget_cong; exact Ha ]. }
    eapply eq_term_trans; [ exact Hin | apply eq_cmp_forget; assumption ].
Qed.

(* The composition case: the two argument clauses compose, and
   "cmp_assoc" is exactly the re-association that lets them. *)
Lemma cong_cmp Ga1 Gb1 Ga2 Gb2 Ga3 Gb3 f1 f2 g1 g2
  : Ceq_term sEnv Ga1 Gb1 -> Ceq_term sEnv Ga2 Gb2 -> Ceq_term sEnv Ga3 Gb3 ->
    Ceq_term (sSub Gb1 Gb2) f1 f2 -> Ceq_term (sSub Gb2 Gb3) g1 g2 ->
    Ceq_term (sSub Gb1 Gb3)
      (oCmp Ga1 Ga2 Ga3 f1 g1) (oCmp Gb1 Gb2 Gb3 f2 g2).
Proof.
  intros H1 H2 H3 Hf Hg.
  apply Ceq_env_e in H1 as [Ha1 _]; apply Ceq_env_e in H2 as [Ha2 _];
    apply Ceq_env_e in H3 as [Ha3 _].
  apply Ceq_sub_e in Hf as [Hfa Hfb]; apply Ceq_sub_e in Hg as [Hga Hgb].
  assert (wft Gb1 sEnv) as Hw1 by (eapply eqt_wf_r; exact Ha1).
  assert (wft Gb2 sEnv) as Hw2 by (eapply eqt_wf_r; exact Ha2).
  assert (wft Gb3 sEnv) as Hw3 by (eapply eqt_wf_r; exact Ha3).
  assert (wft f1 (sSub Gb1 Gb2)) as Hwf by (eapply eqt_wf_l; exact Hfa).
  assert (wft g1 (sSub Gb2 Gb3)) as Hwg by (eapply eqt_wf_l; exact Hga).
  apply ceq_sub; [ apply Cmp_cong; assumption | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D Gb1)) as Hwh by (apply RSubN_wf; exact Hh).
  apply RSubN_eq with (g := oCmp D Gb2 Gb3 (oCmp D Gb1 Gb2 h f1) g1);
    [ apply Hgb; [ exact HD | apply Hfb; [ exact HD | exact Hh ] ] | ].
  apply eq_term_sym.
  assert (eqt (sSub D Gb3)
            (oCmp D Gb1 Gb3 h (oCmp Ga1 Ga2 Ga3 f1 g1))
            (oCmp D Gb1 Gb3 h (oCmp Gb1 Gb2 Gb3 f1 g1))) as Hin.
  { apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hw1
      | apply eq_term_refl; exact Hw3
      | apply eq_term_refl; exact Hwh
      | apply Cmp_cong;
        [ exact Ha1 | exact Ha2 | exact Ha3
        | apply eq_term_refl; exact Hwf
        | apply eq_term_refl; exact Hwg ] ]. }
  eapply eq_term_trans; [ exact Hin | apply eq_cmp_assoc; assumption ].
Qed.

(* ---- the two substitution actions -------------------------------- *)

(* [ty_subst] composes two substitutions: the OUTER clause supplies
   [RSubN D G g] and the type argument's own clause is then read at the
   composite [g o g1], which "ty_subst_cmp" identifies with the two-step
   substitution the goal asks about. *)
Lemma cong_ty_subst Ga Gb Ga' Gb' g1 g2 i1 i2 A1 A2
  : Ceq_term sEnv Ga Gb -> Ceq_term sEnv Ga' Gb' ->
    Ceq_term (sSub Gb Gb') g1 g2 -> Ceq_term sInfo i1 i2 ->
    Ceq_term (sTy Gb' i2) A1 A2 ->
    Ceq_term (sTy Gb i2)
      (oTySubst Ga Ga' g1 i1 A1) (oTySubst Gb Gb' g2 i2 A2).
Proof.
  intros HG HG' Hg Hi HA.
  apply Ceq_env_e in HG as [HGa _]; apply Ceq_env_e in HG' as [HGa' _].
  apply Ceq_sub_e in Hg as [Hga Hgb].
  apply Ceq_tyinfo_e in Hi as (Hia & _ & _).
  apply Ceq_ty_e in HA as [HAa HAb].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact HGa).
  assert (wft Gb' sEnv) as Hwb' by (eapply eqt_wf_r; exact HGa').
  assert (wft i2 sInfo) as Hwi by (eapply eqt_wf_r; exact Hia).
  assert (wft g1 (sSub Gb Gb')) as Hwg by (eapply eqt_wf_l; exact Hga).
  assert (wft A1 (sTy Gb' i2)) as HwA by (eapply eqt_wf_l; exact HAa).
  apply ceq_ty; [ apply TySubst_cong; assumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D Gb)) as Hwg' by (apply RSubN_wf; exact Hg).
  apply RTyN_eq with (A := oTySubst D Gb' (oCmp D Gb Gb' g g1) i2 A1);
    [ apply HAb; [ exact HD | apply Hgb; [ exact HD | exact Hg ] ] | ].
  apply eq_term_sym.
  assert (eqt (sTy Gb i2)
            (oTySubst Ga Ga' g1 i1 A1) (oTySubst Gb Gb' g1 i2 A1)) as Hin.
  { apply TySubst_cong;
      [ exact HGa | exact HGa' | apply eq_term_refl; exact Hwg | exact Hia
      | apply eq_term_refl; exact HwA ]. }
  eapply eq_term_trans;
    [ apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwb
      | apply eq_term_refl; exact Hwg'
      | apply eq_term_refl; exact Hwi
      | exact Hin ]
    | apply eq_ty_subst_cmp; assumption ].
Qed.

(* [exp_subst] is the same composition, twice over: once for the type
   ("ty_subst_cmp") and once for the subject ("exp_subst_cmp").  The term
   argument's clause is read at [g o g2] -- the s2-side composite -- so
   that every index of the resulting [RTmN] is already the one the goal
   sort names, and only the two [cmp] laws are left to apply. *)
Lemma cong_exp_subst Ga Gb Ga' Gb' g1 g2 i1 i2 A1 A2 v1 v2
  : Ceq_term sEnv Ga Gb -> Ceq_term sEnv Ga' Gb' ->
    Ceq_term (sSub Gb Gb') g1 g2 -> Ceq_term sInfo i1 i2 ->
    Ceq_term (sTy Gb' i2) A1 A2 -> Ceq_term (sExp Gb' i2 A2) v1 v2 ->
    Ceq_term (sExp Gb i2 (oTySubst Gb Gb' g2 i2 A2))
      (oExpSubst Ga Ga' g1 i1 A1 v1) (oExpSubst Gb Gb' g2 i2 A2 v2).
Proof.
  intros HG HG' Hg Hi HA Hv.
  apply Ceq_env_e in HG as [HGa _]; apply Ceq_env_e in HG' as [HGa' _].
  apply Ceq_sub_e in Hg as [Hga Hgb].
  apply Ceq_tyinfo_e in Hi as (Hia & _ & _).
  apply Ceq_ty_e in HA as [HAa _].
  apply Ceq_exp_e in Hv as [Hva Hvb].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact HGa).
  assert (wft Gb' sEnv) as Hwb' by (eapply eqt_wf_r; exact HGa').
  assert (wft i2 sInfo) as Hwi by (eapply eqt_wf_r; exact Hia).
  assert (wft g2 (sSub Gb Gb')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft A2 (sTy Gb' i2)) as HwA2 by (eapply eqt_wf_r; exact HAa).
  assert (wft v1 (sExp Gb' i2 A2)) as Hwv1 by (eapply eqt_wf_l; exact Hva).
  apply ceq_exp; [ apply ExpSubst_cong; assumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D Gb)) as Hwg by (apply RSubN_wf; exact Hg).
  (* the composite, on the s2 side *)
  assert (RSubN D Gb' (oCmp D Gb Gb' g g2)) as Hcomp.
  { apply RSubN_eq with (g := oCmp D Gb Gb' g g1);
      [ apply Hgb; [ exact HD | exact Hg ] | ].
    apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwb
      | apply eq_term_refl; exact Hwb'
      | apply eq_term_refl; exact Hwg
      | exact Hga ]. }
  (* the type of the goal, folded *)
  assert (eqt (sTy D i2)
            (oTySubst D Gb' (oCmp D Gb Gb' g g2) i2 A2)
            (oTySubst D Gb g i2 (oTySubst Gb Gb' g2 i2 A2))) as Hty
    by (apply eq_term_sym; apply eq_ty_subst_cmp; assumption).
  (* the subject of the goal, folded *)
  assert (eqt (sExp D i2 (oTySubst D Gb g i2 (oTySubst Gb Gb' g2 i2 A2)))
            (oExpSubst D Gb g i2 (oTySubst Gb Gb' g2 i2 A2)
               (oExpSubst Gb Gb' g2 i2 A2 v1))
            (oExpSubst D Gb' (oCmp D Gb Gb' g g2) i2 A2 v1)) as Hsub
    by (apply eq_exp_subst_cmp; assumption).
  assert (eqt (sExp Gb i2 (oTySubst Gb Gb' g2 i2 A2))
            (oExpSubst Gb Gb' g2 i2 A2 v1) (oExpSubst Ga Ga' g1 i1 A1 v1))
    as Hinner.
  { apply eq_term_sym; apply ExpSubst_cong;
      [ exact HGa | exact HGa' | exact Hga | exact Hia | exact HAa
      | apply eq_term_refl; exact Hwv1 ]. }
  apply RTmN_eq with (e := oExpSubst D Gb' (oCmp D Gb Gb' g g2) i2 A2 v1).
  - apply RTmN_eq_ty
      with (A := oTySubst D Gb' (oCmp D Gb Gb' g g2) i2 A2);
      [ apply Hvb; [ exact HD | exact Hcomp ] | exact Hty ].
  - eapply eq_term_trans; [ apply eq_term_sym; exact Hsub | ].
    apply ExpSubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwb
      | apply eq_term_refl; exact Hwg
      | apply eq_term_refl; exact Hwi
      | apply eq_term_refl;
        apply wf_TySubst; [ exact Hwb | exact Hwb' | exact Hwg2 | exact Hwi | exact HwA2 ]
      | exact Hinner ].
Qed.

(* ---- the two projections out of an extended environment ---------- *)

(* [wkn] is [RSub_proj] read at the normal representative of the extended
   environment: [RSubN] hands back SOME normal codomain, [EnvOk_inj] (via
   [RSubN_rep]) identifies it with the one [ext_normal] built, and the
   projection is then Layer 3's. *)
Lemma cong_wkn Ga Gb i1 i2 A1 A2
  : Ceq_term sEnv Ga Gb -> Ceq_term sInfo i1 i2 -> Ceq_term (sTy Gb i2) A1 A2 ->
    Ceq_term (sSub (oExt Gb i2 A2) Gb) (oWkn Ga i1 A1) (oWkn Gb i2 A2).
Proof.
  intros HG Hi HA.
  destruct (ext_normal HG HA)
    as [G0 [i0 [A0 (HG0 & Heq & Hi0 & HT & HeqA & HE & HeqE)]]].
  apply Ceq_env_e in HG as [HGa _].
  apply Ceq_tyinfo_e in Hi as (Hia & _ & _).
  apply Ceq_ty_e in HA as [HAa _].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact HGa).
  assert (wft G0 sEnv) as Hw0 by (apply EnvOk_wf; exact HG0).
  assert (wft i2 sInfo) as Hwi by (eapply eqt_wf_r; exact Hia).
  assert (wft A2 (sTy Gb i2)) as HwA2 by (eapply eqt_wf_r; exact HAa).
  (* the type argument's representative, moved to the s2 sort *)
  assert (eqt (sTy Gb i2) A0 A2) as HeqA'.
  { apply eq_term_sym; eapply eq_term_conv;
      [ exact HeqA
      | apply sTy_cong; [ apply eq_term_sym; exact Heq | apply eq_term_sym; exact Hi0 ] ]. }
  assert (eqt (sSub (oExt Gb i2 A2) Gb) (oWkn G0 i0 A0) (oWkn Ga i1 A1)) as Hwkn.
  { eapply eq_term_trans;
      [ apply Wkn_cong;
        [ apply eq_term_sym; exact Heq
        | apply eq_term_sym; exact Hi0
        | exact HeqA' ]
      | apply eq_term_sym; apply Wkn_cong; assumption ]. }
  apply ceq_sub; [ apply Wkn_cong; assumption | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D (oExt Gb i2 A2))) as Hwh by (apply RSubN_wf; exact Hh).
  eapply RSubN_conv;
    [ apply RSubN_of_RSub;
      [ exact HG0 | apply RSub_proj; eapply RSubN_rep; eassumption ]
    | apply eq_term_sym; exact Heq
    | ].
  apply Cmp_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_sym; exact HeqE
    | apply eq_term_sym; exact Heq
    | apply eq_term_refl; exact Hwh
    | exact Hwkn ].
Qed.

(* [hd] reads the ENTRY of the reducible substitution: [RSub]'s [ext]
   clause presents [g] as a [snoc] whose entry is reducible, and
   "snoc_hd" says the goal's subject IS that entry.  The type moves along
   "ty_subst_cmp" + "wkn_snoc". *)
Lemma cong_hd Ga Gb i1 i2 A1 A2
  : Ceq_term sEnv Ga Gb -> Ceq_term sInfo i1 i2 -> Ceq_term (sTy Gb i2) A1 A2 ->
    Ceq_term (sExp (oExt Gb i2 A2) i2
                (oTySubst (oExt Gb i2 A2) Gb (oWkn Gb i2 A2) i2 A2))
      (oHd Ga i1 A1) (oHd Gb i2 A2).
Proof.
  intros HG Hi HA.
  destruct (ext_normal HG HA)
    as [G0 [i0 [A0 (HG0 & Heq & Hi0 & HT & HeqA & HE & HeqE)]]].
  apply Ceq_env_e in HG as [HGa _].
  apply Ceq_tyinfo_e in Hi as (Hia & _ & _).
  apply Ceq_ty_e in HA as [HAa _].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact HGa).
  assert (wft G0 sEnv) as Hw0 by (apply EnvOk_wf; exact HG0).
  assert (wft i2 sInfo) as Hwi by (eapply eqt_wf_r; exact Hia).
  assert (wft i0 sInfo) as Hwi0 by (eapply wft_ty_info; apply TyOk_wf; exact HT).
  assert (wft A0 (sTy G0 i0)) as HwA0 by (apply TyOk_wf; exact HT).
  assert (wft A2 (sTy Gb i2)) as HwA2 by (eapply eqt_wf_r; exact HAa).
  assert (eqt (sTy Gb i2) A0 A2) as HeqA'.
  { apply eq_term_sym; eapply eq_term_conv;
      [ exact HeqA
      | apply sTy_cong; [ apply eq_term_sym; exact Heq | apply eq_term_sym; exact Hi0 ] ]. }
  (* the two weakened types, and the two head variables *)
  assert (eqt (sTy (oExt Gb i2 A2) i2)
            (oTySubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0)
            (oTySubst (oExt Gb i2 A2) Gb (oWkn Gb i2 A2) i2 A2)) as Htw.
  { apply TySubst_cong;
      [ apply eq_term_sym; exact HeqE
      | apply eq_term_sym; exact Heq
      | apply Wkn_cong;
        [ apply eq_term_sym; exact Heq
        | apply eq_term_sym; exact Hi0
        | exact HeqA' ]
      | apply eq_term_sym; exact Hi0
      | exact HeqA' ]. }
  assert (eqt (sExp (oExt Gb i2 A2) i2
                 (oTySubst (oExt Gb i2 A2) Gb (oWkn Gb i2 A2) i2 A2))
            (oHd G0 i0 A0) (oHd Ga i1 A1)) as Hhdc.
  { eapply eq_term_trans;
      [ apply Hd_cong;
        [ apply eq_term_sym; exact Heq
        | apply eq_term_sym; exact Hi0
        | exact HeqA' ]
      | apply eq_term_sym; apply Hd_cong; assumption ]. }
  apply ceq_exp; [ apply Hd_cong; assumption | ].
  intros D g HD Hg.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft g (sSub D (oExt Gb i2 A2))) as Hwg by (apply RSubN_wf; exact Hg).
  assert (RSub D (oExt G0 i0 A0) g) as Hrs by (eapply RSubN_rep; eassumption).
  apply RSub_ext_elim in Hrs as [g0 [v [Hs [Hg0 Hv]]]].
  pose proof (eqt_wf_r Hs) as Hsn.
  apply wft_Snoc_args in Hsn.
  destruct Hsn as (_ & _ & _ & _ & Hwg0 & Hwv).
  (* the entry IS the goal's subject, by "snoc_hd" *)
  assert (eqt (sExp D i0 (oTySubst D G0 g0 i0 A0))
            (oExpSubst D (oExt G0 i0 A0) (oSnoc D G0 i0 A0 g0 v) i0
               (oTySubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0)
               (oHd G0 i0 A0))
            v) as Hhd
    by (apply eq_snoc_hd; assumption).
  (* the entry's type IS the goal's type *)
  assert (eqt (sTy D i0)
            (oTySubst D (oExt G0 i0 A0) (oSnoc D G0 i0 A0 g0 v) i0
               (oTySubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0))
            (oTySubst D G0 g0 i0 A0)) as Hfold.
  { eapply eq_term_trans;
      [ apply eq_ty_subst_cmp;
        [ exact HwD
        | apply wf_Ext; assumption
        | exact Hw0
        | eapply eqt_wf_r; exact Hs
        | apply wf_Wkn; assumption
        | exact Hwi0
        | exact HwA0 ]
      | ].
    apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hw0
      | apply eq_wkn_snoc; assumption
      | apply eq_term_refl; exact Hwi0
      | apply eq_term_refl; exact HwA0 ]. }
  assert (eqt (sTy D i2)
            (oTySubst D (oExt G0 i0 A0) (oSnoc D G0 i0 A0 g0 v) i0
               (oTySubst (oExt G0 i0 A0) G0 (oWkn G0 i0 A0) i0 A0))
            (oTySubst D (oExt Gb i2 A2) g i2
               (oTySubst (oExt Gb i2 A2) Gb (oWkn Gb i2 A2) i2 A2))) as Hty2.
  { apply TySubst_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_sym; exact HeqE
      | eapply eq_term_conv;
        [ apply eq_term_sym; exact Hs
        | apply sSub_cong;
          [ apply eq_term_refl; exact HwD | apply eq_term_sym; exact HeqE ] ]
      | apply eq_term_sym; exact Hi0
      | exact Htw ]. }
  eapply RTmN_eq;
    [ eapply RTmN_eq_ty;
      [ eapply RTmN_eq_info;
        [ eapply RTmN_eq; [ exact Hv | apply eq_term_sym; exact Hhd ]
        | apply eq_term_sym; exact Hi0 ]
      | eapply eq_term_trans;
        [ eapply eq_term_conv;
          [ apply eq_term_sym; exact Hfold
          | apply sTy_cong;
            [ apply eq_term_refl; exact HwD | apply eq_term_sym; exact Hi0 ] ]
        | exact Hty2 ] ]
    | ].
  apply ExpSubst_cong;
    [ apply eq_term_refl; exact HwD
    | apply eq_term_sym; exact HeqE
    | eapply eq_term_conv;
      [ apply eq_term_sym; exact Hs
      | apply sSub_cong;
        [ apply eq_term_refl; exact HwD | apply eq_term_sym; exact HeqE ] ]
    | apply eq_term_sym; exact Hi0
    | exact Htw
    | exact Hhdc ].
Qed.

(* ---- the extension of a substitution ----------------------------- *)

(* [snoc] is the only case that BUILDS an [RSub] at an [ext]: the tail
   comes from the substitution argument's clause (read at the composite,
   then transported to the representative environment by [RSubN_rep]) and
   the entry from the term argument's, whose type is folded onto the
   representative by "ty_subst_cmp".  "cmp_snoc" is what turns the
   composite [h o <g,v>] into the [snoc] that [RSub]'s clause demands. *)
Lemma cong_snoc Ga Gb Ga' Gb' i1 i2 A1 A2 g1 g2 v1 v2
  : Ceq_term sEnv Ga Gb -> Ceq_term sEnv Ga' Gb' -> Ceq_term sInfo i1 i2 ->
    Ceq_term (sTy Gb' i2) A1 A2 -> Ceq_term (sSub Gb Gb') g1 g2 ->
    Ceq_term (sExp Gb i2 (oTySubst Gb Gb' g2 i2 A2)) v1 v2 ->
    Ceq_term (sSub Gb (oExt Gb' i2 A2))
      (oSnoc Ga Ga' i1 A1 g1 v1) (oSnoc Gb Gb' i2 A2 g2 v2).
Proof.
  intros HG HG' Hi HA Hg Hv.
  destruct (ext_normal HG' HA)
    as [G0 [i0 [A0 (HG0 & Heq & Hi0 & HT & HeqA & HE & HeqE)]]].
  apply Ceq_env_e in HG as [HGa _]; apply Ceq_env_e in HG' as [HGa' _].
  apply Ceq_tyinfo_e in Hi as (Hia & _ & _).
  apply Ceq_ty_e in HA as [HAa _].
  apply Ceq_sub_e in Hg as [Hga Hgb].
  apply Ceq_exp_e in Hv as [Hva Hvb].
  assert (wft Gb sEnv) as Hwb by (eapply eqt_wf_r; exact HGa).
  assert (wft Gb' sEnv) as Hwb' by (eapply eqt_wf_r; exact HGa').
  assert (wft G0 sEnv) as Hw0 by (apply EnvOk_wf; exact HG0).
  assert (wft i2 sInfo) as Hwi by (eapply eqt_wf_r; exact Hia).
  assert (wft i0 sInfo) as Hwi0 by (eapply wft_ty_info; apply TyOk_wf; exact HT).
  assert (wft A0 (sTy G0 i0)) as HwA0 by (apply TyOk_wf; exact HT).
  assert (wft A2 (sTy Gb' i2)) as HwA2 by (eapply eqt_wf_r; exact HAa).
  assert (wft g2 (sSub Gb Gb')) as Hwg2 by (eapply eqt_wf_r; exact Hga).
  assert (wft v1 (sExp Gb i2 (oTySubst Gb Gb' g2 i2 A2))) as Hwv1
    by (eapply eqt_wf_l; exact Hva).
  assert (wft (oExt Gb' i2 A2) sEnv) as HwE by (apply wf_Ext; assumption).
  apply ceq_sub; [ apply Snoc_cong; assumption | ].
  intros D h HD Hh.
  assert (wft D sEnv) as HwD by (apply EnvOk_wf; exact HD).
  assert (wft h (sSub D Gb)) as Hwh by (apply RSubN_wf; exact Hh).
  (* the tail, at the representative environment *)
  assert (RSubN D Gb' (oCmp D Gb Gb' h g2)) as Hcomp.
  { apply RSubN_eq with (g := oCmp D Gb Gb' h g1);
      [ apply Hgb; [ exact HD | exact Hh ] | ].
    apply Cmp_cong;
      [ apply eq_term_refl; exact HwD
      | apply eq_term_refl; exact Hwb
      | apply eq_term_refl; exact Hwb'
      | apply eq_term_refl; exact Hwh
      | exact Hga ]. }
  assert (wft (oCmp D Gb Gb' h g2) (sSub D G0)) as Hwc
    by (eapply wft_conv_sub;
        [ apply RSubN_wf; exact Hcomp
        | apply eq_term_refl; exact HwD
        | exact Heq ]).
  assert (RSub D G0 (oCmp D Gb Gb' h g2)) as Htail
    by (eapply RSubN_rep; [ exact Hcomp | exact HG0 | exact Heq ]).
  (* the entry, with its type folded onto the representative *)
  assert (eqt (sTy D i0)
            (oTySubst D Gb h i2 (oTySubst Gb Gb' g2 i2 A2))
            (oTySubst D G0 (oCmp D Gb Gb' h g2) i0 A0)) as Hety.
  { eapply eq_term_trans;
      [ eapply eq_term_conv;
        [ apply eq_ty_subst_cmp; assumption
        | apply sTy_cong; [ apply eq_term_refl; exact HwD | exact Hi0 ] ]
      | apply TySubst_cong;
        [ apply eq_term_refl; exact HwD
        | exact Heq
        | apply eq_term_refl; exact Hwc
        | exact Hi0
        | exact HeqA ] ]. }
  assert (RTmN D i0 (oTySubst D G0 (oCmp D Gb Gb' h g2) i0 A0)
            (oExpSubst D Gb h i2 (oTySubst Gb Gb' g2 i2 A2) v1)) as Hentry.
  { eapply RTmN_eq_ty;
      [ eapply RTmN_eq_info; [ apply Hvb; [ exact HD | exact Hh ] | exact Hi0 ]
      | exact Hety ]. }
  assert (wft (oExpSubst D Gb h i2 (oTySubst Gb Gb' g2 i2 A2) v1)
            (sExp D i0 (oTySubst D G0 (oCmp D Gb Gb' h g2) i0 A0))) as Hwe.
  { eapply wft_conv_exp;
      [ apply wf_ExpSubst; try assumption;
        apply wf_TySubst; assumption
      | apply eq_term_refl; exact HwD
      | exact Hi0
      | exact Hety ]. }
  (* assemble *)
  exists (oExt G0 i0 A0); split; [ exact HE | split; [ exact HeqE | ] ].
  apply RSub_ext_intro.
  exists (oCmp D Gb Gb' h g2),
         (oExpSubst D Gb h i2 (oTySubst Gb Gb' g2 i2 A2) v1).
  split; [ | split; [ exact Htail | exact Hentry ] ].
  assert (eqt (sSub D (oExt Gb' i2 A2))
            (oCmp D Gb (oExt Gb' i2 A2) h (oSnoc Ga Ga' i1 A1 g1 v1))
            (oSnoc D Gb' i2 A2 (oCmp D Gb Gb' h g2)
               (oExpSubst D Gb h i2 (oTySubst Gb Gb' g2 i2 A2) v1))) as Hstep.
  { eapply eq_term_trans;
      [ apply Cmp_cong;
        [ apply eq_term_refl; exact HwD
        | apply eq_term_refl; exact Hwb
        | apply eq_term_refl; exact HwE
        | apply eq_term_refl; exact Hwh
        | apply Snoc_cong;
          [ exact HGa | exact HGa' | exact Hia | exact HAa | exact Hga
          | apply eq_term_refl; exact Hwv1 ] ]
      | apply eq_cmp_snoc; assumption ]. }
  eapply eq_term_trans;
    [ eapply eq_term_conv;
      [ exact Hstep
      | apply sSub_cong; [ apply eq_term_refl; exact HwD | exact HeqE ] ]
    | ].
  apply Snoc_cong;
    [ apply eq_term_refl; exact HwD
    | exact Heq
    | exact Hi0
    | exact HeqA
    | apply eq_term_refl; exact Hwc
    | apply eq_term_refl; exact Hwe ].
Qed.

(* ================================================================== *)
(* 2.  The congruence dispatcher                                       *)
(* ================================================================== *)

(* WIP/DttModelIdx.v's idiom: the rule NAME is pinned first and the [In]
   premise computed afterwards, so each case costs one rule rather than a
   32-way split. *)

Ltac subst_pin :=
  match goal with
  | [ Hin : In _ ott_dtt |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
         | [ H : ceq_args (_::_) _ _ |- _ ] => inversion H; subst; clear H
         | [ H : ceq_args [] _ _ |- _ ] => inversion H; subst; clear H
         end;
  cbn [ceq_term ceq_sort DttCM] in *.

Lemma subst_cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    (name = "emp" \/ name = "ext" \/ name = "id" \/ name = "forget"
     \/ name = "cmp" \/ name = "ty_subst" \/ name = "exp_subst"
     \/ name = "snoc" \/ name = "wkn" \/ name = "hd") ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    Ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hname Hargs.
  destruct Hname
    as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    subst_pin.
  - (* emp *) apply cong_emp.
  - (* ext *) apply cong_ext; assumption.
  - (* id *) apply cong_id; assumption.
  - (* forget *) apply cong_forget; assumption.
  - (* cmp *) apply cong_cmp; assumption.
  - (* ty_subst *) apply cong_ty_subst; assumption.
  - (* exp_subst *) apply cong_exp_subst; assumption.
  - (* snoc *) apply cong_snoc; assumption.
  - (* wkn *) apply cong_wkn; assumption.
  - (* hd *) apply cong_hd; assumption.
Qed.
