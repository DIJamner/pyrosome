Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac.
From Pyrosome Require Import Theory.Core Tools.Matches.
Require Import Pyrosome.Gluing.Dtt.Syntax.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1: the equational toolkit for [ott_dtt].

   The analogue of Gluing/Stlc/Eqns.v for the dependent theory of
   src/Pyrosome/Lang/OTT/.

   Each of the language's 28 equations is repackaged here as a directly
   usable lemma: the equation instance is stated with explicit term
   arguments in the abbreviation vocabulary of src/Pyrosome/Gluing/Dtt/Syntax.v ([oCmp],
   [oSnoc], [oExpSubst], [sTy], [sExp], ...), and carries exactly the
   well-formedness hypotheses the instantiation needs -- one [wf_term] per
   variable of the rule's context, at that variable's sort, already
   instantiated by the preceding arguments.  The congruence rule of every
   one of the 32 term constructors gets the same treatment.

   [Tools.Matches.eredex_steps_with] does the actual instantiation: given a
   rule name it looks the rule up in [ott_dtt] and infers, by unification
   against the goal, the substitution that turns the rule's LHS/RHS into
   the goal's; all that is left is to discharge the resulting
   well-formedness side conditions.  Because that unification goes through
   [vm_compute], the abbreviations of Syntax.v (which are transparent
   [Definition]s) are transparent to it: we never have to unfold by hand.

   ------------------------------------------------------------------
   A WARNING ABOUT [tyinfo] ARGUMENTS, for every later layer.

   [tlvl] has the two equations [next L0 = iota L1] and [next L1 = inf].
   The rules of [ott_dtt] were elaborated at different times and DO NOT
   agree, syntactically, on which representative they use.  Every
   statement below therefore uses EXACTLY the info term of the compiled
   rule it repackages, even when a neighbouring rule writes the same info
   differently.  The mismatches that actually occur are:

     - term rule "Nat"    concludes at [info rel (next L0)]   (= iCode L0)
       but eq rule "Nat subst" concludes at [info rel (iota L1)];
     - term rule "Empty"  concludes at [info rel (iota L1)]
       but eq rule "Empty subst" concludes at [info rel (next L0)];
     - "Pi_irr" and "Pi_irr subst" and "Pi_irr beta" put the codomain code
       [B] at [info rel (iota L1)], while "lam_irr" and "app_irr" put it
       at [info rel (next L0)].

   These are equal sorts (by "next0"), but they are not the same TERM, so
   a lemma stated with the wrong one will simply not apply.

   THIS IS NOT AN AUTHORING BUG, AND WRITING THE IDEAL REPRESENTATION DOES
   NOT FIX IT.  Lang/OTT/Nat.v already writes [info rel (next L0)]
   uniformly in all four of the Nat/Empty rules above.  [infer_rule] does
   not treat the written conclusion sort as authoritative: it loads the
   sort into an e-graph, saturates, and re-EXTRACTS a representative with
   [TypeInference.mk_weight], which charges 1 per non-hole atom.  The two
   spellings both cost 4, so the winner is an arbitrary tie-break -- and it
   depends on the AMBIENT LANGUAGE, not on the rule.  Checked both ways:
   elaborated in isolation, "Empty" comes out [next L0] whichever spelling
   is written (the two prerules elaborate to the IDENTICAL rule); elaborated
   inside Nat.v's [Derive], after Nat/zero/suc have been pushed, it comes
   out [iota L1].  See design.md section 9a.

   The bridge is [eq_next0] below, lifted to the sorts by
   [NfTyping.eq_info_next0] and the [wft_c2i]/[wft_i2c] pair of
   NfWk.v -- not, as a first pass tried, by running the e-graph on each
   instance.
   ===================================================================== *)

(* A rule's context is well formed, since the language is.
   [eredex_steps_with] leaves exactly this goal (headed by the rule's own,
   unsubstituted context) whenever the built substitution doesn't already
   settle it via [cleanup_auto_elab]. *)
Lemma ott_dtt_rule_ctx_wf n r
  : named_list_lookup_err ott_dtt n = Some r ->
    wf_ctx (Model := core_model ott_dtt) (Rule.get_ctx r).
Proof.
  intro Hlook.
  pose proof (rule_in_wf (l_pre := []) _ _ ott_dtt_wf
                (named_list_lookup_err_in _ _ (eq_sym Hlook))) as Hr.
  rewrite app_nil_r in Hr.
  destruct r; cbn in *; inversion Hr; subst; assumption.
Qed.

Ltac wf_subst_solve :=
  repeat first [ simple apply wf_subst_nil
               | simple eapply wf_subst_cons
               | progress cbn [combine map fst]
               | progress cbn [Model.wf_term core_model]
               | eassumption ].

(* [eredex_steps_with] leaves either one goal ([wf_ctx], when the built
   substitution is itself trivial) or two ([wf_subst] then [wf_ctx]); the
   plain semicolon below runs the combined solver on every goal it leaves,
   whichever shape that turns out to be. *)
Ltac estep nm :=
  eredex_steps_with ott_dtt nm;
  first [ solve [ wf_subst_solve ]
        | exact (ott_dtt_rule_ctx_wf nm eq_refl) ].

(* Instantiating a term rule's congruence. *)
Lemma ott_dtt_cong_inst (name : string) c' args t' (s1 s2 : list term)
  : In (name, term_rule c' args t') ott_dtt ->
    eq_args (Model := core_model ott_dtt) [] c' s1 s2 ->
    eq_term ott_dtt [] t'[/with_names_from c' s2/]
      (con name s1) (con name s2).
Proof.
  intros Hin Hargs.
  eapply term_con_congruence.
  - exact Hin.
  - right; reflexivity.
  - apply ott_dtt_wf.
  - exact Hargs.
Qed.

Ltac eq_args_solve :=
  repeat apply eq_args_cons;
  first [ apply eq_args_nil | eassumption ].

(* [named_list_lookup_err_in ... eq_refl] pins the rule's [term_rule] shape
   to the concrete value [named_list_lookup_err ott_dtt nm] reduces to;
   [refine] (unlike [apply]) propagates that expected-type information down
   into the hole, so the reduction actually fires instead of getting stuck
   on an uninstantiated evar. *)
Ltac cong_step nm s1 s2 :=
  refine (ott_dtt_cong_inst (named_list_lookup_err_in ott_dtt nm eq_refl)
            (s1 := s1) (s2 := s2) _);
  eq_args_solve.

(* Instantiating a SORT rule's congruence -- the same thing one level up.
   Of [ott_dtt]'s nine sorts only [sub], [ty] and [exp] take arguments, so
   the three congruences below are the whole story. *)
Lemma ott_dtt_sort_cong_inst (name : string) c' args (s1 s2 : list term)
  : In (name, sort_rule c' args) ott_dtt ->
    eq_args (Model := core_model ott_dtt) [] c' s1 s2 ->
    eq_sort ott_dtt [] (scon name s1) (scon name s2).
Proof.
  intros Hin Hargs.
  eapply sort_con_congruence; try typeclasses eauto;
    [ exact Hin | apply ott_dtt_wf | exact Hargs ].
Qed.

Ltac scong_step nm s1 s2 :=
  refine (ott_dtt_sort_cong_inst (named_list_lookup_err_in ott_dtt nm eq_refl)
            (s1 := s1) (s2 := s2) _);
  eq_args_solve.

Lemma sSub_cong G1 G2 G1' G2'
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sEnv G1' G2' ->
    eq_sort ott_dtt [] (sSub G1 G1') (sSub G2 G2').
Proof. intros; scong_step "sub" [G1'; G1] [G2'; G2]. Qed.

Lemma sTy_cong G1 G2 i1 i2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_sort ott_dtt [] (sTy G1 i1) (sTy G2 i2).
Proof. intros; scong_step "ty" [i1; G1] [i2; G2]. Qed.

Lemma sExp_cong G1 G2 i1 i2 A1 A2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2 i2) A1 A2 ->
    eq_sort ott_dtt [] (sExp G1 i1 A1) (sExp G2 i2 A2).
Proof. intros; scong_step "exp" [A1; i1; G1] [A2; i2; G2]. Qed.

(* ================================================================== *)
(* ott_info: relevance, levels, type levels                            *)
(* ================================================================== *)

(* [ltl] is a proof-irrelevant order relation: any two witnesses agree. *)
Lemma eq_ltl_irr a b p1 p2
  : wf_term ott_dtt [] a sLvl ->
    wf_term ott_dtt [] b sLvl ->
    wf_term ott_dtt [] p1 (sLtl a b) ->
    wf_term ott_dtt [] p2 (sLtl a b) ->
    eq_term ott_dtt [] (sLtl a b) p1 p2.
Proof. intros; estep "ltl_irr". Qed.

Lemma eq_next0 : eq_term ott_dtt [] sTlvl (oNext oL0) (oIota oL1).
Proof. estep "next0". Qed.

Lemma eq_next1 : eq_term ott_dtt [] sTlvl (oNext oL1) oInf.
Proof. estep "next1". Qed.

(* ================================================================== *)
(* subst_ott: the substitution calculus                                *)
(* ================================================================== *)

Lemma eq_id_right G G' f
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] f (sSub G G') ->
    eq_term ott_dtt [] (sSub G G') (oCmp G G' G' f (oId G')) f.
Proof. intros; estep "id_right". Qed.

Lemma eq_id_left G G' f
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] f (sSub G G') ->
    eq_term ott_dtt [] (sSub G G') (oCmp G G G' (oId G) f) f.
Proof. intros; estep "id_left". Qed.

Lemma eq_cmp_assoc G1 G2 G3 G4 f g h
  : wf_term ott_dtt [] G1 sEnv ->
    wf_term ott_dtt [] G2 sEnv ->
    wf_term ott_dtt [] G3 sEnv ->
    wf_term ott_dtt [] G4 sEnv ->
    wf_term ott_dtt [] f (sSub G1 G2) ->
    wf_term ott_dtt [] g (sSub G2 G3) ->
    wf_term ott_dtt [] h (sSub G3 G4) ->
    eq_term ott_dtt [] (sSub G1 G4)
      (oCmp G1 G2 G4 f (oCmp G2 G3 G4 g h))
      (oCmp G1 G3 G4 (oCmp G1 G2 G3 f g) h).
Proof. intros; estep "cmp_assoc". Qed.

Lemma eq_ty_subst_id G i A
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G i) ->
    eq_term ott_dtt [] (sTy G i) (oTySubst G G (oId G) i A) A.
Proof. intros; estep "ty_subst_id". Qed.

Lemma eq_ty_subst_cmp G1 G2 G3 f g i A
  : wf_term ott_dtt [] G1 sEnv ->
    wf_term ott_dtt [] G2 sEnv ->
    wf_term ott_dtt [] G3 sEnv ->
    wf_term ott_dtt [] f (sSub G1 G2) ->
    wf_term ott_dtt [] g (sSub G2 G3) ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G3 i) ->
    eq_term ott_dtt [] (sTy G1 i)
      (oTySubst G1 G2 f i (oTySubst G2 G3 g i A))
      (oTySubst G1 G3 (oCmp G1 G2 G3 f g) i A).
Proof. intros; estep "ty_subst_cmp". Qed.

Lemma eq_exp_subst_id G i A v
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G i) ->
    wf_term ott_dtt [] v (sExp G i A) ->
    eq_term ott_dtt [] (sExp G i A) (oExpSubst G G (oId G) i A v) v.
Proof. intros; estep "exp_subst_id". Qed.

(* Note the conclusion sort: the two-step substitution of [A] is NOT
   collapsed on the right, so the sort is stated at the LEFT-hand side's
   type.  (The two are equal by [ty_subst_cmp], but not syntactically.) *)
Lemma eq_exp_subst_cmp G1 G2 G3 f g i A v
  : wf_term ott_dtt [] G1 sEnv ->
    wf_term ott_dtt [] G2 sEnv ->
    wf_term ott_dtt [] G3 sEnv ->
    wf_term ott_dtt [] f (sSub G1 G2) ->
    wf_term ott_dtt [] g (sSub G2 G3) ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G3 i) ->
    wf_term ott_dtt [] v (sExp G3 i A) ->
    eq_term ott_dtt []
      (sExp G1 i (oTySubst G1 G2 f i (oTySubst G2 G3 g i A)))
      (oExpSubst G1 G2 f i (oTySubst G2 G3 g i A) (oExpSubst G2 G3 g i A v))
      (oExpSubst G1 G3 (oCmp G1 G2 G3 f g) i A v).
Proof. intros; estep "exp_subst_cmp". Qed.

Lemma eq_cmp_forget G G' g
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    eq_term ott_dtt [] (sSub G oEmp)
      (oCmp G G' oEmp g (oForget G')) (oForget G).
Proof. intros; estep "cmp_forget". Qed.

Lemma eq_id_emp_forget
  : eq_term ott_dtt [] (sSub oEmp oEmp) (oId oEmp) (oForget oEmp).
Proof. estep "id_emp_forget". Qed.

(* The four [snoc] equations.  [snoc]'s argument order is
   [oSnoc G G' i A g v] -- the extended VALUE comes last in the
   abbreviation but FIRST in the underlying [con] list, unlike the STLC
   language where the type came between the substitution and the value. *)

Lemma eq_wkn_snoc G G' g i A v
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G' i) ->
    wf_term ott_dtt [] v (sExp G i (oTySubst G G' g i A)) ->
    eq_term ott_dtt [] (sSub G G')
      (oCmp G (oExt G' i A) G' (oSnoc G G' i A g v) (oWkn G' i A)) g.
Proof. intros; estep "wkn_snoc". Qed.

(* The type argument of the outer [exp_subst] is [A] weakened -- that is
   the sort [hd] actually lives at, and it is not simplified away. *)
Lemma eq_snoc_hd G G' g i A v
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G' i) ->
    wf_term ott_dtt [] v (sExp G i (oTySubst G G' g i A)) ->
    eq_term ott_dtt [] (sExp G i (oTySubst G G' g i A))
      (oExpSubst G (oExt G' i A) (oSnoc G G' i A g v) i
         (oTySubst (oExt G' i A) G' (oWkn G' i A) i A) (oHd G' i A))
      v.
Proof. intros; estep "snoc_hd". Qed.

Lemma eq_cmp_snoc G1 G2 G3 f g i A v
  : wf_term ott_dtt [] G1 sEnv ->
    wf_term ott_dtt [] G2 sEnv ->
    wf_term ott_dtt [] G3 sEnv ->
    wf_term ott_dtt [] f (sSub G1 G2) ->
    wf_term ott_dtt [] g (sSub G2 G3) ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G3 i) ->
    wf_term ott_dtt [] v (sExp G2 i (oTySubst G2 G3 g i A)) ->
    eq_term ott_dtt [] (sSub G1 (oExt G3 i A))
      (oCmp G1 G2 (oExt G3 i A) f (oSnoc G2 G3 i A g v))
      (oSnoc G1 G3 i A (oCmp G1 G2 G3 f g)
         (oExpSubst G1 G2 f i (oTySubst G2 G3 g i A) v)).
Proof. intros; estep "cmp_snoc". Qed.

Lemma eq_snoc_wkn_hd G i A
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] i sInfo ->
    wf_term ott_dtt [] A (sTy G i) ->
    eq_term ott_dtt [] (sSub (oExt G i A) (oExt G i A))
      (oSnoc (oExt G i A) G i A (oWkn G i A) (oHd G i A))
      (oId (oExt G i A)).
Proof. intros; estep "snoc_wkn_hd". Qed.

(* ================================================================== *)
(* ott_base: the Tarski universe                                       *)
(* ================================================================== *)

Lemma eq_U_subst G G' g r l
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] r sRelevance ->
    wf_term ott_dtt [] l sLvl ->
    eq_term ott_dtt [] (sTy G (iCode l))
      (oTySubst G G' g (iCode l) (oU G' r l)) (oU G r l).
Proof. intros; estep "U subst". Qed.

Lemma eq_El_subst G G' g r l e
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] r sRelevance ->
    wf_term ott_dtt [] l sLvl ->
    wf_term ott_dtt [] e (sCode G' r l) ->
    eq_term ott_dtt [] (sTy G (iEl r l))
      (oTySubst G G' g (iEl r l) (oEl G' r l e))
      (oEl G r l (oExpSubst G G' g (iCode l) (oU G' r l) e)).
Proof. intros; estep "El subst". Qed.

(* ================================================================== *)
(* ott_nat                                                             *)
(* ================================================================== *)

(* CAREFUL: "Nat subst" is stated at info [rel (iota L1)], whereas the
   term rule "Nat" concludes at info [rel (next L0)].  Both name the same
   sort (by "next0") but the terms differ, so [sCode] -- which is defined
   with [iCode], i.e. [next] -- is deliberately NOT used here. *)
Lemma eq_Nat_subst G G' g
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    eq_term ott_dtt []
      (sExp G (oInfo oRel (oIota oL1)) (oU G oRel oL0))
      (oExpSubst G G' g (oInfo oRel (oIota oL1)) (oU G' oRel oL0) (oNat G'))
      (oNat G).
Proof. intros; estep "Nat subst". Qed.

Lemma eq_zero_subst G G' g
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    eq_term ott_dtt [] (sElt G oRel oL0 (oNat G))
      (oExpSubst G G' g (iEl oRel oL0) (oEl G' oRel oL0 (oNat G')) (oZero G'))
      (oZero G).
Proof. intros; estep "zero subst". Qed.

Lemma eq_suc_subst G G' g n
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] n (sElt G' oRel oL0 (oNat G')) ->
    eq_term ott_dtt [] (sElt G oRel oL0 (oNat G))
      (oExpSubst G G' g (iEl oRel oL0) (oEl G' oRel oL0 (oNat G')) (oSuc G' n))
      (oSuc G
         (oExpSubst G G' g (iEl oRel oL0) (oEl G' oRel oL0 (oNat G')) n)).
Proof. intros; estep "suc subst". Qed.

(* CAREFUL, mirror image of "Nat subst": "Empty subst" is stated at info
   [rel (next L0)] (= [iCode L0], hence [sCode]) whereas the term rule
   "Empty" concludes at info [rel (iota L1)]. *)
Lemma eq_Empty_subst G G' g
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    eq_term ott_dtt [] (sCode G oIrr oL0)
      (oExpSubst G G' g (iCode oL0) (oU G' oIrr oL0) (oEmpty G'))
      (oEmpty G).
Proof. intros; estep "Empty subst". Qed.

(* ================================================================== *)
(* ott_pi                                                              *)
(* ================================================================== *)

(* The substitution of a CODE [F : sCode G' rF lF] along [g : sub G G'].
   This shape occurs three times in every binder commutation (once as the
   new domain code, once inside [oExtC] for the new context, and once
   inside [oLift]), so it gets a name.  It is exactly the [Fg] of
   [Syntax.oLift]. *)
Definition oCodeSubst (G G' g rF lF F : term) : term :=
  oExpSubst G G' g (iCode lF) (oU G' rF lF) F.

(* [Pi_rel subst]: pushing [g] under the binder lifts it with [oLift]
   (the [under'] of the surface presentation), and the domain code of the
   result is [F[g]], so the target context of the lifted substitution is
   [oExtC G rF lF F[g]]. *)
Lemma eq_Pi_rel_subst G G' g rF lF lG F B
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] rF sRelevance ->
    wf_term ott_dtt [] lF sLvl ->
    wf_term ott_dtt [] lG sLvl ->
    wf_term ott_dtt [] F (sCode G' rF lF) ->
    wf_term ott_dtt [] B (sCode (oExtC G' rF lF F) oRel lG) ->
    eq_term ott_dtt [] (sCode G oRel lG)
      (oExpSubst G G' g (iCode lG) (oU G' oRel lG) (oPiRel G' rF lF lG F B))
      (oPiRel G rF lF lG (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iCode lG) (oU (oExtC G' rF lF F) oRel lG) B)).
Proof. intros; estep "Pi_rel subst". Qed.

(* CAREFUL: the codomain code [B] of [Pi_irr] lives at info
   [rel (iota L1)] here (and in the term rule "Pi_irr" and in
   "Pi_irr beta"), but at [rel (next L0)] in "lam_irr" and "app_irr". *)
Lemma eq_Pi_irr_subst G G' g rF lF F B
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] rF sRelevance ->
    wf_term ott_dtt [] lF sLvl ->
    wf_term ott_dtt [] F (sCode G' rF lF) ->
    wf_term ott_dtt [] B
      (sExp (oExtC G' rF lF F) (oInfo oRel (oIota oL1))
         (oU (oExtC G' rF lF F) oIrr oL0)) ->
    eq_term ott_dtt []
      (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0))
      (oExpSubst G G' g (oInfo oRel (oIota oL1)) (oU G' oIrr oL0)
         (oPiIrr G' rF lF F B))
      (oPiIrr G rF lF (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (oInfo oRel (oIota oL1)) (oU (oExtC G' rF lF F) oIrr oL0) B)).
Proof. intros; estep "Pi_irr subst". Qed.

(* Note the conclusion sort: the type of a [lam_rel] is [El (Pi_rel ...)]
   SUBSTITUTED along [g]; the rule does not push that substitution in. *)
Lemma eq_lam_rel_subst G G' g rF lF lG F B t
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] G' sEnv ->
    wf_term ott_dtt [] g (sSub G G') ->
    wf_term ott_dtt [] rF sRelevance ->
    wf_term ott_dtt [] lF sLvl ->
    wf_term ott_dtt [] lG sLvl ->
    wf_term ott_dtt [] F (sCode G' rF lF) ->
    wf_term ott_dtt [] B (sCode (oExtC G' rF lF F) oRel lG) ->
    wf_term ott_dtt [] t (sElt (oExtC G' rF lF F) oRel lG B) ->
    eq_term ott_dtt []
      (sExp G (iEl oRel lG)
         (oTySubst G G' g (iEl oRel lG)
            (oEl G' oRel lG (oPiRel G' rF lF lG F B))))
      (oExpSubst G G' g (iEl oRel lG)
         (oEl G' oRel lG (oPiRel G' rF lF lG F B))
         (oLamRel G' rF lF lG F B t))
      (oLamRel G rF lF lG (oCodeSubst G G' g rF lF F)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iCode lG) (oU (oExtC G' rF lF F) oRel lG) B)
         (oExpSubst (oExtC G rF lF (oCodeSubst G G' g rF lF F))
            (oExtC G' rF lF F) (oLift G G' g rF lF F)
            (iEl oRel lG) (oEl (oExtC G' rF lF F) oRel lG B) t)).
Proof. intros; estep "lam_rel subst". Qed.

Lemma eq_Pi_rel_beta G rF lF lG F B t a
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] rF sRelevance ->
    wf_term ott_dtt [] lF sLvl ->
    wf_term ott_dtt [] lG sLvl ->
    wf_term ott_dtt [] F (sCode G rF lF) ->
    wf_term ott_dtt [] B (sCode (oExtC G rF lF F) oRel lG) ->
    wf_term ott_dtt [] t (sElt (oExtC G rF lF F) oRel lG B) ->
    wf_term ott_dtt [] a (sElt G rF lF F) ->
    eq_term ott_dtt [] (sAppRelConcl G rF lF lG F B a)
      (oAppRel G rF lF lG F B (oLamRel G rF lF lG F B t) a)
      (oExpSubst G (oExtC G rF lF F) (oInst G rF lF F a)
         (iEl oRel lG) (oEl (oExtC G rF lF F) oRel lG B) t).
Proof. intros; estep "Pi_rel beta". Qed.

Lemma eq_Pi_irr_beta G rF lF F B t a
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] rF sRelevance ->
    wf_term ott_dtt [] lF sLvl ->
    wf_term ott_dtt [] F (sCode G rF lF) ->
    wf_term ott_dtt [] B
      (sExp (oExtC G rF lF F) (oInfo oRel (oIota oL1))
         (oU (oExtC G rF lF F) oIrr oL0)) ->
    wf_term ott_dtt [] t (sElt (oExtC G rF lF F) oIrr oL0 B) ->
    wf_term ott_dtt [] a (sElt G rF lF F) ->
    eq_term ott_dtt [] (sAppIrrConcl G rF lF F B a)
      (oAppIrr G rF lF F B (oLamIrr G rF lF F B t) a)
      (oExpSubst G (oExtC G rF lF F) (oInst G rF lF F a)
         (iEl oIrr oL0) (oEl (oExtC G rF lF F) oIrr oL0 B) t).
Proof. intros; estep "Pi_irr beta". Qed.

(* [Pi_rel eta].  The left-hand side is [lam_rel (app_rel (f[wkn]) hd)]
   with everything weakened by one binder:
     - [oWkn G (iEl rF lF) (oEl G rF lF F)] is the weakening off
       [gext := oExtC G rF lF F];
     - the domain code of the lambda's own binder is [F] weakened, i.e.
       [oCodeSubst gext G wkn F];
     - the codomain code is [B] transported along [oLift gext G wkn ...],
       which is precisely the lifting of that weakening.
   This is the one rule of [ott_dtt] that was added pre-elaborated
   ([Lang/OTT/Pi.v]'s [pi_rel_eta_rule], pushed with [push_rule]); the
   statement below is its verbatim reading. *)
Lemma eq_Pi_rel_eta G rF lF lG F B f
  : wf_term ott_dtt [] G sEnv ->
    wf_term ott_dtt [] rF sRelevance ->
    wf_term ott_dtt [] lF sLvl ->
    wf_term ott_dtt [] lG sLvl ->
    wf_term ott_dtt [] F (sCode G rF lF) ->
    wf_term ott_dtt [] B (sCode (oExtC G rF lF F) oRel lG) ->
    wf_term ott_dtt [] f (sElt G oRel lG (oPiRel G rF lF lG F B)) ->
    eq_term ott_dtt [] (sElt G oRel lG (oPiRel G rF lF lG F B))
      (oLamRel G rF lF lG F B
         (oAppRel (oExtC G rF lF F) rF lF lG
            (oCodeSubst (oExtC G rF lF F) G
               (oWkn G (iEl rF lF) (oEl G rF lF F)) rF lF F)
            (oExpSubst
               (oExtC (oExtC G rF lF F) rF lF
                  (oCodeSubst (oExtC G rF lF F) G
                     (oWkn G (iEl rF lF) (oEl G rF lF F)) rF lF F))
               (oExtC G rF lF F)
               (oLift (oExtC G rF lF F) G
                  (oWkn G (iEl rF lF) (oEl G rF lF F)) rF lF F)
               (iCode lG) (oU (oExtC G rF lF F) oRel lG) B)
            (oExpSubst (oExtC G rF lF F) G
               (oWkn G (iEl rF lF) (oEl G rF lF F))
               (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) f)
            (oHd G (iEl rF lF) (oEl G rF lF F))))
      f.
Proof. intros; estep "Pi_rel eta". Qed.

(* ================================================================== *)
(* Congruences                                                         *)
(* ================================================================== *)

(* Note the asymmetry: the sorts of the later hypotheses, and of the
   conclusion, are instantiated at the RIGHT-hand arguments.  That is what
   [eq_args] provides and what [term_con_congruence] concludes.

   The explicit argument lists passed to [cong_step] are the rule's [con]
   lists, i.e. the rule context read MOST-RECENT-FIRST. *)

(* ---- ott_info ---- *)

Lemma Rel_cong : eq_term ott_dtt [] sRelevance oRel oRel.
Proof. cong_step "rel" (@nil term) (@nil term). Qed.

Lemma Irr_cong : eq_term ott_dtt [] sRelevance oIrr oIrr.
Proof. cong_step "irr" (@nil term) (@nil term). Qed.

Lemma L0_cong : eq_term ott_dtt [] sLvl oL0 oL0.
Proof. cong_step "L0" (@nil term) (@nil term). Qed.

Lemma L1_cong : eq_term ott_dtt [] sLvl oL1 oL1.
Proof. cong_step "L1" (@nil term) (@nil term). Qed.

Lemma Lt01_cong : eq_term ott_dtt [] (sLtl oL0 oL1) oLt01 oLt01.
Proof. cong_step "L0<L1" (@nil term) (@nil term). Qed.

Lemma Inf_cong : eq_term ott_dtt [] sTlvl oInf oInf.
Proof. cong_step "inf" (@nil term) (@nil term). Qed.

Lemma Iota_cong l1 l2
  : eq_term ott_dtt [] sLvl l1 l2 ->
    eq_term ott_dtt [] sTlvl (oIota l1) (oIota l2).
Proof. intros; cong_step "iota" [l1] [l2]. Qed.

Lemma Next_cong l1 l2
  : eq_term ott_dtt [] sLvl l1 l2 ->
    eq_term ott_dtt [] sTlvl (oNext l1) (oNext l2).
Proof. intros; cong_step "next" [l1] [l2]. Qed.

Lemma Info_cong r1 r2 l1 l2
  : eq_term ott_dtt [] sRelevance r1 r2 ->
    eq_term ott_dtt [] sTlvl l1 l2 ->
    eq_term ott_dtt [] sInfo (oInfo r1 l1) (oInfo r2 l2).
Proof. intros; cong_step "info" [l1; r1] [l2; r2]. Qed.

(* ---- subst_ott ---- *)

Lemma Emp_cong : eq_term ott_dtt [] sEnv oEmp oEmp.
Proof. cong_step "emp" (@nil term) (@nil term). Qed.

Lemma Ext_cong G1 G2 i1 i2 A1 A2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2 i2) A1 A2 ->
    eq_term ott_dtt [] sEnv (oExt G1 i1 A1) (oExt G2 i2 A2).
Proof. intros; cong_step "ext" [A1; i1; G1] [A2; i2; G2]. Qed.

Lemma Id_cong G1 G2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] (sSub G2 G2) (oId G1) (oId G2).
Proof. intros; cong_step "id" [G1] [G2]. Qed.

Lemma Forget_cong G1 G2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] (sSub G2 oEmp) (oForget G1) (oForget G2).
Proof. intros; cong_step "forget" [G1] [G2]. Qed.

Lemma Cmp_cong X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2
  : eq_term ott_dtt [] sEnv X1 Y1 ->
    eq_term ott_dtt [] sEnv X2 Y2 ->
    eq_term ott_dtt [] sEnv X3 Y3 ->
    eq_term ott_dtt [] (sSub Y1 Y2) f1 f2 ->
    eq_term ott_dtt [] (sSub Y2 Y3) g1 g2 ->
    eq_term ott_dtt [] (sSub Y1 Y3)
      (oCmp X1 X2 X3 f1 g1) (oCmp Y1 Y2 Y3 f2 g2).
Proof. intros; cong_step "cmp" [g1; f1; X3; X2; X1] [g2; f2; Y3; Y2; Y1]. Qed.

Lemma TySubst_cong G1 G2 G1' G2' g1 g2 i1 i2 A1 A2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sEnv G1' G2' ->
    eq_term ott_dtt [] (sSub G2 G2') g1 g2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2' i2) A1 A2 ->
    eq_term ott_dtt [] (sTy G2 i2)
      (oTySubst G1 G1' g1 i1 A1) (oTySubst G2 G2' g2 i2 A2).
Proof.
  intros;
    cong_step "ty_subst" [A1; i1; g1; G1'; G1] [A2; i2; g2; G2'; G2].
Qed.

Lemma ExpSubst_cong G1 G2 G1' G2' g1 g2 i1 i2 A1 A2 v1 v2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sEnv G1' G2' ->
    eq_term ott_dtt [] (sSub G2 G2') g1 g2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2' i2) A1 A2 ->
    eq_term ott_dtt [] (sExp G2' i2 A2) v1 v2 ->
    eq_term ott_dtt [] (sExp G2 i2 (oTySubst G2 G2' g2 i2 A2))
      (oExpSubst G1 G1' g1 i1 A1 v1) (oExpSubst G2 G2' g2 i2 A2 v2).
Proof.
  intros;
    cong_step "exp_subst"
      [v1; A1; i1; g1; G1'; G1] [v2; A2; i2; g2; G2'; G2].
Qed.

(* [snoc]'s context is [v; g; A; i; G'; G]: the extended value comes
   FIRST, and the substitution comes BEFORE the type. *)
Lemma Snoc_cong G1 G2 G1' G2' i1 i2 A1 A2 g1 g2 v1 v2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sEnv G1' G2' ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2' i2) A1 A2 ->
    eq_term ott_dtt [] (sSub G2 G2') g1 g2 ->
    eq_term ott_dtt [] (sExp G2 i2 (oTySubst G2 G2' g2 i2 A2)) v1 v2 ->
    eq_term ott_dtt [] (sSub G2 (oExt G2' i2 A2))
      (oSnoc G1 G1' i1 A1 g1 v1) (oSnoc G2 G2' i2 A2 g2 v2).
Proof.
  intros;
    cong_step "snoc" [v1; g1; A1; i1; G1'; G1] [v2; g2; A2; i2; G2'; G2].
Qed.

Lemma Wkn_cong G1 G2 i1 i2 A1 A2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2 i2) A1 A2 ->
    eq_term ott_dtt [] (sSub (oExt G2 i2 A2) G2)
      (oWkn G1 i1 A1) (oWkn G2 i2 A2).
Proof. intros; cong_step "wkn" [A1; i1; G1] [A2; i2; G2]. Qed.

Lemma Hd_cong G1 G2 i1 i2 A1 A2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sInfo i1 i2 ->
    eq_term ott_dtt [] (sTy G2 i2) A1 A2 ->
    eq_term ott_dtt []
      (sExp (oExt G2 i2 A2) i2
         (oTySubst (oExt G2 i2 A2) G2 (oWkn G2 i2 A2) i2 A2))
      (oHd G1 i1 A1) (oHd G2 i2 A2).
Proof. intros; cong_step "hd" [A1; i1; G1] [A2; i2; G2]. Qed.

(* ---- ott_base ---- *)

Lemma U_cong G1 G2 r1 r2 l1 l2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance r1 r2 ->
    eq_term ott_dtt [] sLvl l1 l2 ->
    eq_term ott_dtt [] (sTy G2 (iCode l2)) (oU G1 r1 l1) (oU G2 r2 l2).
Proof. intros; cong_step "U" [l1; r1; G1] [l2; r2; G2]. Qed.

Lemma El_cong G1 G2 r1 r2 l1 l2 e1 e2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance r1 r2 ->
    eq_term ott_dtt [] sLvl l1 l2 ->
    eq_term ott_dtt [] (sCode G2 r2 l2) e1 e2 ->
    eq_term ott_dtt [] (sTy G2 (iEl r2 l2))
      (oEl G1 r1 l1 e1) (oEl G2 r2 l2 e2).
Proof. intros; cong_step "El" [e1; l1; r1; G1] [e2; l2; r2; G2]. Qed.

(* ---- ott_nat ---- *)

(* The term rule "Nat" concludes at [iCode L0] (i.e. info [rel (next L0)]);
   compare [eq_Nat_subst], which is stated at [rel (iota L1)]. *)
Lemma Nat_cong G1 G2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] (sCode G2 oRel oL0) (oNat G1) (oNat G2).
Proof. intros; cong_step "Nat" [G1] [G2]. Qed.

Lemma Zero_cong G1 G2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] (sElt G2 oRel oL0 (oNat G2)) (oZero G1) (oZero G2).
Proof. intros; cong_step "zero" [G1] [G2]. Qed.

Lemma Suc_cong G1 G2 n1 n2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] (sElt G2 oRel oL0 (oNat G2)) n1 n2 ->
    eq_term ott_dtt [] (sElt G2 oRel oL0 (oNat G2))
      (oSuc G1 n1) (oSuc G2 n2).
Proof. intros; cong_step "suc" [n1; G1] [n2; G2]. Qed.

(* Mirror image of [Nat_cong]: the term rule "Empty" concludes at
   info [rel (iota L1)], while [eq_Empty_subst] is stated at [iCode L0]. *)
Lemma Empty_cong G1 G2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
      (oEmpty G1) (oEmpty G2).
Proof. intros; cong_step "Empty" [G1] [G2]. Qed.

Lemma Emptyrec_cong G1 G2 rA1 rA2 lA1 lA2 A1 A2 e1 e2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rA1 rA2 ->
    eq_term ott_dtt [] sLvl lA1 lA2 ->
    eq_term ott_dtt [] (sCode G2 rA2 lA2) A1 A2 ->
    eq_term ott_dtt [] (sElt G2 oIrr oL0 (oEmpty G2)) e1 e2 ->
    eq_term ott_dtt [] (sElt G2 rA2 lA2 A2)
      (oEmptyrec G1 rA1 lA1 A1 e1) (oEmptyrec G2 rA2 lA2 A2 e2).
Proof.
  intros;
    cong_step "Emptyrec" [e1; A1; lA1; rA1; G1] [e2; A2; lA2; rA2; G2].
Qed.

(* ---- ott_pi ---- *)

Lemma PiRel_cong G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rF1 rF2 ->
    eq_term ott_dtt [] sLvl lF1 lF2 ->
    eq_term ott_dtt [] sLvl lG1 lG2 ->
    eq_term ott_dtt [] (sCode G2 rF2 lF2) F1 F2 ->
    eq_term ott_dtt [] (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    eq_term ott_dtt [] (sCode G2 oRel lG2)
      (oPiRel G1 rF1 lF1 lG1 F1 B1) (oPiRel G2 rF2 lF2 lG2 F2 B2).
Proof.
  intros;
    cong_step "Pi_rel" [B1; F1; lG1; lF1; rF1; G1] [B2; F2; lG2; lF2; rF2; G2].
Qed.

(* CAREFUL: the codomain code [B] of the term rule "Pi_irr" lives at info
   [rel (iota L1)], NOT at [iCode L0]. *)
Lemma PiIrr_cong G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rF1 rF2 ->
    eq_term ott_dtt [] sLvl lF1 lF2 ->
    eq_term ott_dtt [] (sCode G2 rF2 lF2) F1 F2 ->
    eq_term ott_dtt []
      (sExp (oExtC G2 rF2 lF2 F2) (oInfo oRel (oIota oL1))
         (oU (oExtC G2 rF2 lF2 F2) oIrr oL0)) B1 B2 ->
    eq_term ott_dtt [] (sExp G2 (oInfo oRel (oIota oL1)) (oU G2 oIrr oL0))
      (oPiIrr G1 rF1 lF1 F1 B1) (oPiIrr G2 rF2 lF2 F2 B2).
Proof.
  intros;
    cong_step "Pi_irr" [B1; F1; lF1; rF1; G1] [B2; F2; lF2; rF2; G2].
Qed.

Lemma LamRel_cong G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2 t1 t2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rF1 rF2 ->
    eq_term ott_dtt [] sLvl lF1 lF2 ->
    eq_term ott_dtt [] sLvl lG1 lG2 ->
    eq_term ott_dtt [] (sCode G2 rF2 lF2) F1 F2 ->
    eq_term ott_dtt [] (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    eq_term ott_dtt [] (sElt (oExtC G2 rF2 lF2 F2) oRel lG2 B2) t1 t2 ->
    eq_term ott_dtt [] (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
      (oLamRel G1 rF1 lF1 lG1 F1 B1 t1) (oLamRel G2 rF2 lF2 lG2 F2 B2 t2).
Proof.
  intros;
    cong_step "lam_rel" [t1; B1; F1; lG1; lF1; rF1; G1]
      [t2; B2; F2; lG2; lF2; rF2; G2].
Qed.

(* Here [B] IS at [iCode L0] (unlike in [PiIrr_cong]). *)
Lemma LamIrr_cong G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 t1 t2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rF1 rF2 ->
    eq_term ott_dtt [] sLvl lF1 lF2 ->
    eq_term ott_dtt [] (sCode G2 rF2 lF2) F1 F2 ->
    eq_term ott_dtt [] (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0) B1 B2 ->
    eq_term ott_dtt [] (sElt (oExtC G2 rF2 lF2 F2) oIrr oL0 B2) t1 t2 ->
    eq_term ott_dtt [] (sElt G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2))
      (oLamIrr G1 rF1 lF1 F1 B1 t1) (oLamIrr G2 rF2 lF2 F2 B2 t2).
Proof.
  intros;
    cong_step "lam_irr" [t1; B1; F1; lF1; rF1; G1]
      [t2; B2; F2; lF2; rF2; G2].
Qed.

Lemma AppRel_cong G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2 f1 f2 a1 a2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rF1 rF2 ->
    eq_term ott_dtt [] sLvl lF1 lF2 ->
    eq_term ott_dtt [] sLvl lG1 lG2 ->
    eq_term ott_dtt [] (sCode G2 rF2 lF2) F1 F2 ->
    eq_term ott_dtt [] (sCode (oExtC G2 rF2 lF2 F2) oRel lG2) B1 B2 ->
    eq_term ott_dtt [] (sElt G2 oRel lG2 (oPiRel G2 rF2 lF2 lG2 F2 B2))
      f1 f2 ->
    eq_term ott_dtt [] (sElt G2 rF2 lF2 F2) a1 a2 ->
    eq_term ott_dtt [] (sAppRelConcl G2 rF2 lF2 lG2 F2 B2 a2)
      (oAppRel G1 rF1 lF1 lG1 F1 B1 f1 a1)
      (oAppRel G2 rF2 lF2 lG2 F2 B2 f2 a2).
Proof.
  intros;
    cong_step "app_rel" [a1; f1; B1; F1; lG1; lF1; rF1; G1]
      [a2; f2; B2; F2; lG2; lF2; rF2; G2].
Qed.

Lemma AppIrr_cong G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 f1 f2 a1 a2
  : eq_term ott_dtt [] sEnv G1 G2 ->
    eq_term ott_dtt [] sRelevance rF1 rF2 ->
    eq_term ott_dtt [] sLvl lF1 lF2 ->
    eq_term ott_dtt [] (sCode G2 rF2 lF2) F1 F2 ->
    eq_term ott_dtt [] (sCode (oExtC G2 rF2 lF2 F2) oIrr oL0) B1 B2 ->
    eq_term ott_dtt [] (sElt G2 oIrr oL0 (oPiIrr G2 rF2 lF2 F2 B2)) f1 f2 ->
    eq_term ott_dtt [] (sElt G2 rF2 lF2 F2) a1 a2 ->
    eq_term ott_dtt [] (sAppIrrConcl G2 rF2 lF2 F2 B2 a2)
      (oAppIrr G1 rF1 lF1 F1 B1 f1 a1) (oAppIrr G2 rF2 lF2 F2 B2 f2 a2).
Proof.
  intros;
    cong_step "app_irr" [a1; f1; B1; F1; lF1; rF1; G1]
      [a2; f2; B2; F2; lF2; rF2; G2].
Qed.
