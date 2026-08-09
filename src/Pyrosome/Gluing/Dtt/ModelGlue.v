Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel SyntacticModel.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.NfTyping
  Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.LogRelBasics Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.Ceq
  Pyrosome.Gluing.Dtt.ModelStruct.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4b: THE GLUE THE FOUR RULE FRAGMENTS SHARE.

   src/Pyrosome/Gluing/Dtt/ModelIdx.v, ModelBase.v, ModelSubst.v and
   ModelPi.v were developed independently, and each grew its own copy of
   the same handful of transports and conversions -- in several cases
   byte-identical in statement AND proof, in others identical up to
   alpha-renaming or the order of two hypotheses.  There was never any
   content in the split: all four fragments already sit on ModelStruct.v,
   so a shared file costs nothing.

   WHAT IS HERE.

   (1) The clause transports specialised to a REFLEXIVE index: [ceq_*_eq_l]
       moves a clause across a provable equality of its LEFT term (which
       costs one transport of the semantic conjunct), [ceq_exp_eq_r] across
       one of its RIGHT term (which is free -- the semantic conjunct does
       not mention it), and [ceq_refl_r] / [ceq_clause_r] read the clause
       at the right-hand term.  All three [ceq_*_eq_l] are corollaries of
       ModelStruct.v's [ceq_*_transport], which is the one place the
       [RSubN_env] / [R*_eq_info] / [RTmN_eq_ty] / [R*_eq] chain is spelled
       out.

   (2) The sort conversions for [wf_term] ([wft_conv_*]), which is what a
       [cterm_by] case needs to retype an s2-side argument at the s1-side
       sort the language's own equation is stated at.

   (3) The two info spellings of a level-0 universe.  "Nat" concludes at
       [iCode L0 = rel (next L0)] while "Nat subst" is stated at
       [rel (iota L1)], and "Empty"/"Empty subst" the other way round;
       [Pi_irr] states its codomain code at [rel (iota L1)] where the rest
       of the binder fragment uses [iCode L0].  "next0" says the two are
       the same info, and these four lemmas are the only place that is paid
       for.  ModelBase.v and ModelPi.v had reached [eq_U_subst_iota1] by
       two independent routes.

   (4) THE EQUATION RECIPE, WHICH WAS ALREADY PROVED GENERICALLY.  Both the
       substitution fragment and the binder fragment independently arrived
       at the same three moves for a [cterm_by] case -- instantiate the
       LANGUAGE's equation at the s1-side arguments, convert its sort to
       the s2-side one the obligation demands, and hand the result to
       [ceq_*_eq_l] -- and each paid for the first two with a per-rule
       retyping prelude, ten to fifty lines long, whose only purpose was to
       feed the instantiation.  But that is exactly
       src/Pyrosome/Gluing/SyntacticModel.v's [synm_cterm_by], proved once
       and generically.  The only thing missing was a bridge:
       [Ceq_term_eqt] forgets a clause down to its [eq_term] conjunct (at
       the two rigid index sorts, where the clause is an identity plus a
       normal form, the equation is [eq_term_refl]), [Ceq_args_syn] lifts
       that pointwise over [ceq_args], and [dtt_eqt_by] / [dtt_eqt_cong]
       are the two obligations read in the syntactic model.  Every
       [cterm_by] case now gets its [eq_term] conjunct for free and only
       has to supply the RIGHT-hand side's [Ceq_term], which is one
       congruence of its own fragment.

       NB the maximally general version -- one that also MANUFACTURED the
       right-hand side's reflexive [Ceq_term] -- would need a substitution
       closure lemma for [Ceq_term], which is precisely what the cut-free
       [CutTModel] interface exists to avoid.

   The rule-pinning tactics [pin_lookup] / [rule_pin] / [pin_name] are also
   shared, but they live in ModelStruct.v because ModelStruct.v's own two
   sort obligations use them.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).
Local Notation wft := (wf_term ott_dtt []).

(* ================================================================== *)
(* 1.  Reading a clause at its RIGHT term                              *)
(* ================================================================== *)

(* [Ceq_term]'s semantic conjunct constrains only the LEFT term, so a
   reflexive instance at the RIGHT one is not immediate -- it is one use of
   symmetry (which recovers the missing half from the equation) and one of
   transitivity. *)
Lemma ceq_refl_r t e1 e2 : Ceq_term t e1 e2 -> Ceq_term t e2 e2.
Proof. intro H; exact (term_trans_obligation (term_sym_obligation H) H). Qed.

(* The [exp] clause for the right-hand term, which is what every "run the
   argument's clause at the right-hand argument" step wants. *)
Lemma ceq_clause_r G i A e1 e2
  : Ceq_term (sExp G i A) e1 e2 ->
    forall D g, EnvOk D -> RSubN D G g ->
      RTmN D i (oTySubst D G g i A) (oExpSubst D G g i A e2).
Proof. intro H; exact (proj2 (Ceq_exp_e (ceq_refl_r H))). Qed.

(* Replacing the RIGHT term by a provably equal one is free: the semantic
   conjunct does not mention it. *)
Lemma ceq_exp_eq_r G i A e1 e2 e3
  : Ceq_term (sExp G i A) e1 e2 -> eqt (sExp G i A) e2 e3 ->
    Ceq_term (sExp G i A) e1 e3.
Proof.
  intros H Heq; apply Ceq_exp_e in H as [Ha Hb].
  apply ceq_exp; [ eapply eq_term_trans; eassumption | exact Hb ].
Qed.

(* ================================================================== *)
(* 2.  Replacing the LEFT term                                         *)
(* ================================================================== *)

(* One transport of the semantic conjunct each; all three are
   ModelStruct.v's [ceq_*_transport] with the indices held reflexive.  Not
   available at [relevance]/[lvl], whose clauses force SYNTACTIC equality;
   the sorts that carry a semantic conjunct are exactly the ones that need
   it. *)

Lemma ceq_sub_eq_l G G' g1 g2 g3
  : eqt (sSub G G') g1 g2 -> Ceq_term (sSub G G') g2 g3 ->
    Ceq_term (sSub G G') g1 g3.
Proof.
  intros Heq Hc.
  destruct (wft_sub_inv (eqt_wf_l Heq)) as [HwG HwG'].
  eapply ceq_sub_transport;
    [ apply eq_term_refl; exact HwG
    | apply eq_term_refl; exact HwG'
    | exact Heq
    | apply eq_term_refl; eapply eqt_wf_r; exact (proj1 (Ceq_sub_e Hc))
    | exact Hc ].
Qed.

Lemma ceq_ty_eq_l G i A1 A2 A3
  : eqt (sTy G i) A1 A2 -> Ceq_term (sTy G i) A2 A3 ->
    Ceq_term (sTy G i) A1 A3.
Proof.
  intros Heq Hc.
  destruct (wft_ty_inv (eqt_wf_l Heq)) as [HwG Hwi].
  eapply ceq_ty_transport;
    [ apply eq_term_refl; exact HwG
    | apply eq_term_refl; exact Hwi
    | exact Heq
    | apply eq_term_refl; eapply eqt_wf_r; exact (proj1 (Ceq_ty_e Hc))
    | exact Hc ].
Qed.

Lemma ceq_exp_eq_l G i A e1 e2 e3
  : eqt (sExp G i A) e1 e2 -> Ceq_term (sExp G i A) e2 e3 ->
    Ceq_term (sExp G i A) e1 e3.
Proof.
  intros Heq Hc.
  destruct (wft_exp_inv (eqt_wf_l Heq)) as [HwG [Hwi HwA]].
  eapply ceq_exp_transport;
    [ apply eq_term_refl; exact HwG
    | apply eq_term_refl; exact Hwi
    | apply eq_term_refl; exact HwA
    | exact Heq
    | apply eq_term_refl; eapply eqt_wf_r; exact (proj1 (Ceq_exp_e Hc))
    | exact Hc ].
Qed.

(* ================================================================== *)
(* 3.  Sort conversions for [wf_term]                                  *)
(* ================================================================== *)

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

(* A type equation is stated at the s2-side sort ([ceq_args] delivers it
   there); these two move it, and a [wf_term] along with it, back to the
   s1-side sort the language's equations are instantiated at. *)

Lemma eqt_conv_ty_l G1 G2 i1 i2 A1 A2
  : eqt sEnv G1 G2 -> eqt sInfo i1 i2 -> eqt (sTy G2 i2) A1 A2 ->
    eqt (sTy G1 i1) A1 A2.
Proof.
  intros; eapply eq_term_conv;
    [ eassumption | apply eq_sort_sym; apply sTy_cong; assumption ].
Qed.

Lemma wft_conv_exp_l e G1 G2 i1 i2 A1 A2
  : wft e (sExp G2 i2 A2) -> eqt sEnv G1 G2 -> eqt sInfo i1 i2 ->
    eqt (sTy G2 i2) A1 A2 -> wft e (sExp G1 i1 A1).
Proof.
  intros He HG Hi HA; eapply wft_conv_exp;
    [ exact He
    | apply eq_term_sym; exact HG
    | apply eq_term_sym; exact Hi
    | apply eq_term_sym; eapply eqt_conv_ty_l; eassumption ].
Qed.

(* ================================================================== *)
(* 4.  The two info spellings of a level-0 universe                    *)
(* ================================================================== *)

Lemma wf_U0_iota1 G r
  : wft G sEnv -> wft r sRelevance ->
    wft (oU G r oL0) (sTy G (oInfo oRel (oIota oL1))).
Proof.
  intros HG Hr; eapply wf_term_conv;
    [ apply wf_U; [ exact HG | exact Hr | apply wf_L0 ] | ].
  apply eq_sort_ty_cong; [ apply eq_term_refl; exact HG | apply eq_info_next0 ].
Qed.

Lemma eq_sort_U0 G r
  : wft G sEnv -> wft r sRelevance ->
    eq_sort ott_dtt [] (sCode G r oL0)
      (sExp G (oInfo oRel (oIota oL1)) (oU G r oL0)).
Proof.
  intros HG Hr; apply eq_sort_exp_cong;
    [ apply eq_term_refl; exact HG
    | apply eq_info_next0
    | apply eq_term_refl; apply wf_U0_iota1; assumption ].
Qed.

(* "U subst" with the substituted universe SPELLED at [rel (iota L1)] but
   CONCLUDING at [iCode L0]: the shape [Pi_irr]'s codomain wants. *)
Lemma eq_U_subst_i1c G G' g r
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') -> wft r sRelevance ->
    eqt (sTy G (iCode oL0))
      (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' r oL0)) (oU G r oL0).
Proof.
  intros HG HG' Hg Hr.
  assert (wft (oU G' r oL0) (sTy G' (iCode oL0))) as HU'
      by (apply wf_U; [ exact HG' | exact Hr | apply wf_L0 ]).
  eapply eq_term_trans.
  - apply TySubst_cong
      with (G1 := G) (G2 := G) (G1' := G') (G2' := G') (g1 := g) (g2 := g)
           (i1 := oInfo oRel (oIota oL1)) (i2 := iCode oL0)
           (A1 := oU G' r oL0) (A2 := oU G' r oL0);
      [ apply eq_term_refl; exact HG
      | apply eq_term_refl; exact HG'
      | apply eq_term_refl; exact Hg
      | apply eq_term_sym; apply eq_info_next0
      | apply eq_term_refl; exact HU' ].
  - apply eq_U_subst;
      [ exact HG | exact HG' | exact Hg | exact Hr | apply wf_L0 ].
Qed.

(* The same, concluding at [rel (iota L1)] -- the spelling the rules "Nat"
   and "Empty" put a level-0 universe at. *)
Lemma eq_U_subst_iota1 G G' g r
  : wft G sEnv -> wft G' sEnv -> wft g (sSub G G') -> wft r sRelevance ->
    eqt (sTy G (oInfo oRel (oIota oL1)))
      (oTySubst G G' g (oInfo oRel (oIota oL1)) (oU G' r oL0))
      (oU G r oL0).
Proof.
  intros HG HG' Hg Hr.
  eapply eq_term_conv;
    [ apply eq_U_subst_i1c; assumption
    | apply sTy_cong;
      [ apply eq_term_refl; exact HG | apply eq_info_next0 ] ].
Qed.

(* ================================================================== *)
(* 5.  The equation recipe, from the syntactic model                   *)
(* ================================================================== *)

(* A clause forgets to its [eq_term] conjunct.  Seven of the nine carry one
   outright; [relevance] and [lvl] are RIGID, so their clause is a
   syntactic identity plus a normal form and the equation is reflexivity
   at [RelNf_wf]/[LvlNf_wf]. *)
Lemma Ceq_term_eqt t e1 e2 : Ceq_term t e1 e2 -> eqt t e1 e2.
Proof.
  destruct 1; try assumption.
  - apply eq_term_refl; apply RelNf_wf; assumption.
  - apply eq_term_refl; apply LvlNf_wf; assumption.
Qed.

(* ... pointwise, which is exactly a [ceq_args] of the SYNTACTIC model. *)
Lemma Ceq_args_syn c' s1 s2
  : ceq_args (CM := DttCM) c' s1 s2 ->
    ceq_args (CM := SynM ott_dtt []) c' s1 s2.
Proof.
  induction 1.
  - constructor.
  - constructor; [ assumption | ].
    apply Ceq_term_eqt; assumption.
Qed.

Lemma dtt_eq_args c' s1 s2
  : ceq_args (CM := DttCM) c' s1 s2 ->
    eq_args (Model := core_model ott_dtt) [] c' s1 s2.
Proof. intro H; apply synm_ceq_args, Ceq_args_syn, H. Qed.

(* THE [eq_term] CONJUNCT OF EVERY [cterm_by] OBLIGATION, for free. *)
Lemma dtt_eqt_by c' name e1 e2 t s1 s2
  : In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    eqt t[/with_names_from c' s2/]
        e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros Hin Hargs; apply Ceq_args_syn in Hargs.
  eapply synm_cterm_by; [ exact ott_dtt_wf | exact Hin | exact Hargs ].
Qed.

(* ... and of every [cterm_cong] one. *)
Lemma dtt_eqt_cong c' name args t s1 s2
  : In (name, term_rule c' args t) ott_dtt ->
    ceq_args (CM := DttCM) c' s1 s2 ->
    eqt t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof. intros Hin Hargs; exact (ott_dtt_cong_inst Hin (dtt_eq_args Hargs)). Qed.
