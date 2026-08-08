Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Tools.ComputeWf Tools.Matches
  Tools.EGraph.ComputeWf.
From Pyrosome Require Import Elab.Elab.
From Pyrosome.Lang Require Import Subst.
From Pyrosome.Lang.OTT Require Import Base Nat Pi.
Require Import WIP.DttSyntax.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 1: the well-formedness (typing) toolkit.

   The analogue of the first ~235 lines of Gluing/Stlc/NormalForms.v, but
   for [ott_dtt] instead of [stlc_unit]: one introduction lemma per
   term_rule, the four sort-inversion lemmas, and the [dtt_wf] hint
   database / [wfa] solver that later layers use to discharge routine
   typing side conditions.

   EVERY statement below was read off the COMPILED language (see
   WIP/DttDump-style `Compute (named_list_lookup_err ott_dtt "app_rel")`),
   never off the surface notation.  Three traps are worth spelling out,
   because later layers will trip on them:

   (1) ARGUMENT ORDER.  A rule's context is stored MOST-RECENT-FIRST and
       [con]'s argument list follows that order, so e.g. [snoc]'s con list
       is [v;g;A;i;G';G].  The [o*] abbreviations in DttSyntax.v already
       absorb this; the hypotheses below are listed in DEPENDENCY order
       (oldest context entry first), which is the reverse.

   (2) THE TWO SPELLINGS OF THE "CODE" INFO.  A code at level [l] lives at
       info [info rel (next l)] ([iCode l]); an element of an [r,l]-type
       lives at [info r (iota l)] ([iEl r l]).  The equation "next0" makes
       [next L0 = iota L1], and the OTT elaborator did NOT pick a single
       representative: it left

         Nat      : exp G (info rel (next L0)) (U G rel L0)      <- iCode L0
         Empty    : exp G (info rel (iota L1)) (U G irr L0)      <- NOT iCode!
         Pi_irr   : exp G (info rel (iota L1)) (U G irr L0)      <- NOT iCode!
         Pi_irr's B  at info rel (iota L1)
         lam_irr's B at info rel (next L0)   (= iCode L0, i.e. sCode _ irr L0)
         app_irr's B at info rel (next L0)

       So [Pi_irr] and [lam_irr] demand their [B] at DIFFERENT (but
       provably equal) infos.  Consequently, building [lam_irr G rF lF F B]
       from a [B] that was produced by whatever typed it at [iota L1]
       requires a CONVERSION through "next0" -- this toolkit deliberately
       does NOT hide that: each [wf_*] lemma states exactly the info its
       rule states, and callers must insert [wf_term_conv] themselves.
       Likewise [wf_Empty]/[wf_PiIrr] conclude at [info rel (iota L1)],
       which is *not* [sCode G oIrr oL0].

   (3) [zero]/[suc] are at [info rel (iota L0)] (they are ELEMENTS), while
       [Nat] is at [info rel (next L0)] (it is a CODE).  Only [Nat] is a
       [sCode].
   ===================================================================== *)

Notation term := (@Term.term string).
Notation sort := (@Term.sort string).
Notation ctx := (@Term.ctx string).

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* ------------------------------------------------------------------ *)
(* Tactic glue                                                          *)
(* ------------------------------------------------------------------ *)

(* Normalize the subject/sort of a [wf_term] goal (they are typically
   presented as [t[/with_names_from c' s/]] by [wf_term_by']); the language
   itself is deliberately left alone. *)
Ltac norm_wf_goal :=
  match goal with
  | [|- wf_term ?l ?c ?e ?t] =>
      let c' := eval vm_compute in c in
      let e' := eval vm_compute in e in
      let t' := eval vm_compute in t in
      change_no_check (wf_term l c' e' t')
  end.

Ltac wf_args_solve :=
  repeat first
    [ simple apply wf_args_nil
    | simple eapply wf_args_cons
    | progress cbn [Model.wf_term core_model]
    | progress norm_wf_goal
    | eassumption ].

(* [wf_by name] : close a [wf_term ott_dtt [] (con name s) t] goal by the
   language's rule for [name], leaving the argument obligations. *)
Ltac wf_by name :=
  eapply wf_term_by' with (n := name);
  [ solve_in | wf_args_solve | left; vm_compute; reflexivity ].

(* ------------------------------------------------------------------ *)
(* ott_info: relevance, levels, type-levels, the info bundle            *)
(* ------------------------------------------------------------------ *)

Lemma wf_Rel : wft oRel sRelevance.
Proof. wf_by "rel". Qed.

Lemma wf_Irr : wft oIrr sRelevance.
Proof. wf_by "irr". Qed.

Lemma wf_L0 : wft oL0 sLvl.
Proof. wf_by "L0". Qed.

Lemma wf_L1 : wft oL1 sLvl.
Proof. wf_by "L1". Qed.

(* [ltl]'s context is [("b",lvl);("a",lvl)] and the scon list is [b;a],
   i.e. [sLtl a b] -- the constant "L0<L1" therefore inhabits [sLtl L0 L1]. *)
Lemma wf_Lt01 : wft oLt01 (sLtl oL0 oL1).
Proof. wf_by "L0<L1". Qed.

Lemma wf_Iota l : wft l sLvl -> wft (oIota l) sTlvl.
Proof. intros; wf_by "iota". Qed.

Lemma wf_Inf : wft oInf sTlvl.
Proof. wf_by "inf". Qed.

Lemma wf_Next l : wft l sLvl -> wft (oNext l) sTlvl.
Proof. intros; wf_by "next". Qed.

Lemma wf_Info r l
  : wft r sRelevance ->
    wft l sTlvl ->
    wft (oInfo r l) sInfo.
Proof. intros; wf_by "info". Qed.

(* ------------------------------------------------------------------ *)
(* subst_ott: the substitution calculus                                 *)
(* ------------------------------------------------------------------ *)

Lemma wf_Emp : wft oEmp sEnv.
Proof. wf_by "emp". Qed.

Lemma wf_Ext G i A
  : wft G sEnv ->
    wft i sInfo ->
    wft A (sTy G i) ->
    wft (oExt G i A) sEnv.
Proof. intros; wf_by "ext". Qed.

Lemma wf_Id G : wft G sEnv -> wft (oId G) (sSub G G).
Proof. intros; wf_by "id". Qed.

Lemma wf_Forget G : wft G sEnv -> wft (oForget G) (sSub G oEmp).
Proof. intros; wf_by "forget". Qed.

Lemma wf_Cmp G1 G2 G3 f g
  : wft G1 sEnv ->
    wft G2 sEnv ->
    wft G3 sEnv ->
    wft f (sSub G1 G2) ->
    wft g (sSub G2 G3) ->
    wft (oCmp G1 G2 G3 f g) (sSub G1 G3).
Proof. intros; wf_by "cmp". Qed.

Lemma wf_TySubst G G' g i A
  : wft G sEnv ->
    wft G' sEnv ->
    wft g (sSub G G') ->
    wft i sInfo ->
    wft A (sTy G' i) ->
    wft (oTySubst G G' g i A) (sTy G i).
Proof. intros; wf_by "ty_subst". Qed.

(* Note the conclusion: the substituted TYPE appears in the sort, so an
   [exp_subst] is typed at [ty_subst ...], never at a pre-normalized sort. *)
Lemma wf_ExpSubst G G' g i A v
  : wft G sEnv ->
    wft G' sEnv ->
    wft g (sSub G G') ->
    wft i sInfo ->
    wft A (sTy G' i) ->
    wft v (sExp G' i A) ->
    wft (oExpSubst G G' g i A v) (sExp G i (oTySubst G G' g i A)).
Proof. intros; wf_by "exp_subst". Qed.

(* [snoc]'s value argument is typed at the SUBSTITUTED type
   [ty_subst G G' g i A], not at [A] -- this is the single most common
   source of conversion obligations downstream. *)
Lemma wf_Snoc G G' i A g v
  : wft G sEnv ->
    wft G' sEnv ->
    wft i sInfo ->
    wft A (sTy G' i) ->
    wft g (sSub G G') ->
    wft v (sExp G i (oTySubst G G' g i A)) ->
    wft (oSnoc G G' i A g v) (sSub G (oExt G' i A)).
Proof. intros; wf_by "snoc". Qed.

Lemma wf_Wkn G i A
  : wft G sEnv ->
    wft i sInfo ->
    wft A (sTy G i) ->
    wft (oWkn G i A) (sSub (oExt G i A) G).
Proof. intros; wf_by "wkn". Qed.

(* [hd]'s sort is the WEAKENED type [A[wkn]], spelled out as a [ty_subst]. *)
Lemma wf_Hd G i A
  : wft G sEnv ->
    wft i sInfo ->
    wft A (sTy G i) ->
    wft (oHd G i A)
      (sExp (oExt G i A) i (oTySubst (oExt G i A) G (oWkn G i A) i A)).
Proof. intros; wf_by "hd". Qed.

(* ------------------------------------------------------------------ *)
(* ott_base: the Tarski universe                                        *)
(* ------------------------------------------------------------------ *)

(* [U G r l] is a TYPE (a [ty]), at the code info [iCode l]. *)
Lemma wf_U G r l
  : wft G sEnv ->
    wft r sRelevance ->
    wft l sLvl ->
    wft (oU G r l) (sTy G (iCode l)).
Proof. intros; wf_by "U". Qed.

(* [El G r l e] decodes the code [e : sCode G r l] into a [ty] at [iEl r l]. *)
Lemma wf_El G r l e
  : wft G sEnv ->
    wft r sRelevance ->
    wft l sLvl ->
    wft e (sCode G r l) ->
    wft (oEl G r l e) (sTy G (iEl r l)).
Proof. intros; wf_by "El". Qed.

(* ------------------------------------------------------------------ *)
(* ott_nat                                                              *)
(* ------------------------------------------------------------------ *)

(* [Nat] is a CODE: info [rel (next L0)] = [iCode L0]. *)
Lemma wf_Nat G : wft G sEnv -> wft (oNat G) (sCode G oRel oL0).
Proof. intros; wf_by "Nat". Qed.

(* [zero]/[suc] are ELEMENTS: info [rel (iota L0)] = [iEl rel L0]. *)
Lemma wf_Zero G : wft G sEnv -> wft (oZero G) (sElt G oRel oL0 (oNat G)).
Proof. intros; wf_by "zero". Qed.

Lemma wf_Suc G n
  : wft G sEnv ->
    wft n (sElt G oRel oL0 (oNat G)) ->
    wft (oSuc G n) (sElt G oRel oL0 (oNat G)).
Proof. intros; wf_by "suc". Qed.

(* TRAP: [Empty] is a code for an IRRELEVANT L0 type, but the elaborator
   left its info as [rel (iota L1)], NOT as [iCode L0 = rel (next L0)].
   The two are equal only by the "next0" equation, so this conclusion is
   deliberately NOT written as [sCode G oIrr oL0]. *)
Lemma wf_Empty G
  : wft G sEnv ->
    wft (oEmpty G) (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0)).
Proof. intros; wf_by "Empty". Qed.

Lemma wf_Emptyrec G rA lA A e
  : wft G sEnv ->
    wft rA sRelevance ->
    wft lA sLvl ->
    wft A (sCode G rA lA) ->
    wft e (sElt G oIrr oL0 (oEmpty G)) ->
    wft (oEmptyrec G rA lA A e) (sElt G rA lA A).
Proof. intros; wf_by "Emptyrec". Qed.

(* ------------------------------------------------------------------ *)
(* ott_pi                                                               *)
(* ------------------------------------------------------------------ *)

(* Every binder rule extends the context by [oExtC G rF lF F], i.e.
   [ext G (info rF (iota lF)) (El G rF lF F)]. *)

Lemma wf_PiRel G rF lF lG F B
  : wft G sEnv ->
    wft rF sRelevance ->
    wft lF sLvl ->
    wft lG sLvl ->
    wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oRel lG) ->
    wft (oPiRel G rF lF lG F B) (sCode G oRel lG).
Proof. intros; wf_by "Pi_rel". Qed.

(* TRAP (see the header): [Pi_irr]'s codomain [B] is demanded at info
   [rel (iota L1)] -- NOT at [sCode _ oIrr oL0 = rel (next L0)], which is
   what [lam_irr] and [app_irr] demand.  The conclusion is at the same
   [rel (iota L1)]. *)
Lemma wf_PiIrr G rF lF F B
  : wft G sEnv ->
    wft rF sRelevance ->
    wft lF sLvl ->
    wft F (sCode G rF lF) ->
    wft B (sExp (oExtC G rF lF F) (oInfo oRel (oIota oL1))
             (oU (oExtC G rF lF F) oIrr oL0)) ->
    wft (oPiIrr G rF lF F B) (sExp G (oInfo oRel (oIota oL1)) (oU G oIrr oL0)).
Proof. intros; wf_by "Pi_irr". Qed.

Lemma wf_LamRel G rF lF lG F B t
  : wft G sEnv ->
    wft rF sRelevance ->
    wft lF sLvl ->
    wft lG sLvl ->
    wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oRel lG) ->
    wft t (sElt (oExtC G rF lF F) oRel lG B) ->
    wft (oLamRel G rF lF lG F B t) (sElt G oRel lG (oPiRel G rF lF lG F B)).
Proof. intros; wf_by "lam_rel". Qed.

(* TRAP: here [B] is demanded at [sCode _ oIrr oL0] (info [rel (next L0)]),
   whereas the [oPiIrr] appearing in the CONCLUSION was, as a rule, built
   from a [B] at [rel (iota L1)].  Both spellings denote the same info, but
   pushing a [B] from one lemma into the other needs a "next0" conversion. *)
Lemma wf_LamIrr G rF lF F B t
  : wft G sEnv ->
    wft rF sRelevance ->
    wft lF sLvl ->
    wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oIrr oL0) ->
    wft t (sElt (oExtC G rF lF F) oIrr oL0 B) ->
    wft (oLamIrr G rF lF F B t) (sElt G oIrr oL0 (oPiIrr G rF lF F B)).
Proof. intros; wf_by "lam_irr". Qed.

(* [app_rel]'s conclusion sort is a [ty_subst] of an [El] along the
   instantiating substitution [<id, a>]; [sAppRelConcl] (DttSyntax.v) is
   that sort verbatim.  It is NOT beta-reduced -- no [ty_subst] is pushed
   in -- so downstream reasoning must go through the substitution
   commutations. *)
Lemma wf_AppRel G rF lF lG F B f a
  : wft G sEnv ->
    wft rF sRelevance ->
    wft lF sLvl ->
    wft lG sLvl ->
    wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oRel lG) ->
    wft f (sElt G oRel lG (oPiRel G rF lF lG F B)) ->
    wft a (sElt G rF lF F) ->
    wft (oAppRel G rF lF lG F B f a) (sAppRelConcl G rF lF lG F B a).
Proof. intros; wf_by "app_rel". Qed.

Lemma wf_AppIrr G rF lF F B f a
  : wft G sEnv ->
    wft rF sRelevance ->
    wft lF sLvl ->
    wft F (sCode G rF lF) ->
    wft B (sCode (oExtC G rF lF F) oIrr oL0) ->
    wft f (sElt G oIrr oL0 (oPiIrr G rF lF F B)) ->
    wft a (sElt G rF lF F) ->
    wft (oAppIrr G rF lF F B f a) (sAppIrrConcl G rF lF F B a).
Proof. intros; wf_by "app_irr". Qed.

(* ------------------------------------------------------------------ *)
(* Sort inversion                                                       *)
(* ------------------------------------------------------------------ *)

(* Every sort former ([sub]/[ty]/[exp]/[ltl]) is introduced by a SINGLE
   rule of [ott_dtt], so inverting [wf_sort] on a concrete sort recovers
   plain well-formedness of its index arguments with no side conditions.
   This is what makes the logical-relation layers side-condition-free:
   given a judgement at [exp G i A], inverting the SORT of either side is
   enough to reconstruct [wft G sEnv], [wft i sInfo] and [wft A (sTy G i)]. *)

Lemma eqt_wf_sort t e1 e2 : eqt t e1 e2 -> wf_sort ott_dtt [] t.
Proof.
  intro H; eapply eq_term_wf_sort; try typeclasses eauto;
    [ exact ott_dtt_wf | constructor | exact H ].
Qed.

Lemma wft_wf_sort e t : wft e t -> wf_sort ott_dtt [] t.
Proof. intro H; eapply eqt_wf_sort; apply eq_term_refl; exact H. Qed.

(* Normalize the SORT of every [wf_term] hypothesis.  The indices recovered
   from [wf_args_cons] come out as [t[/with_names_from c' s/]], and -- unlike
   in the STLC development -- plain [assumption] does NOT see through that
   here (the [Substable] instance's projection blocks conversion), so we
   rewrite the sorts with [vm_compute] first.  The [lazymatch ... => fail]
   guard makes the [repeat] terminate: a hypothesis whose sort is already
   normal is skipped, and when every hypothesis is skipped the outer [match]
   fails and the [repeat] stops. *)
Ltac norm_wf_hyps :=
  repeat match goal with
    | [ Hh : wf_term ?l ?c ?e ?t |- _ ] =>
        let t' := eval vm_compute in t in
        lazymatch t' with
        | t => fail
        | _ => change_no_check (wf_term l c e t') in Hh
        end
    end.

(* As in the STLC development, except for [norm_wf_hyps] and the fact that
   [exp] has THREE indices, so the final step is [repeat split] rather than a
   single [split]. *)
Ltac sort_inv H :=
  inversion H; subst;
  match goal with
  | [ Hin : In _ ott_dtt |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
         (* [Model.wf_args] must be QUALIFIED here: with the OTT/Lang imports
            in scope the bare name [wf_args] no longer resolves to the
            [Model] one that [wf_sort_by] actually produces, and the match
            would silently never fire. *)
         | [ Ha : Model.wf_args _ (_::_) _ |- _ ] => inversion Ha; subst; clear Ha
         end;
  cbn [Model.wf_term core_model] in *;
  norm_wf_hyps;
  repeat split; assumption.

Lemma wf_sort_sub_inv G G'
  : wf_sort ott_dtt [] (sSub G G') -> wft G sEnv /\ wft G' sEnv.
Proof. unfold sSub; intro H; sort_inv H. Qed.

Lemma wf_sort_ty_inv G i
  : wf_sort ott_dtt [] (sTy G i) -> wft G sEnv /\ wft i sInfo.
Proof. unfold sTy; intro H; sort_inv H. Qed.

Lemma wf_sort_exp_inv G i A
  : wf_sort ott_dtt [] (sExp G i A) ->
    wft G sEnv /\ wft i sInfo /\ wft A (sTy G i).
Proof. unfold sExp; intro H; sort_inv H. Qed.

Lemma wf_sort_ltl_inv a b
  : wf_sort ott_dtt [] (sLtl a b) -> wft a sLvl /\ wft b sLvl.
Proof. unfold sLtl; intro H; sort_inv H. Qed.

Lemma wft_sub_inv G G' g : wft g (sSub G G') -> wft G sEnv /\ wft G' sEnv.
Proof. intro H; apply wf_sort_sub_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_ty_inv G i A : wft A (sTy G i) -> wft G sEnv /\ wft i sInfo.
Proof. intro H; apply wf_sort_ty_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_exp_inv G i A e
  : wft e (sExp G i A) -> wft G sEnv /\ wft i sInfo /\ wft A (sTy G i).
Proof. intro H; apply wf_sort_exp_inv; eapply wft_wf_sort; exact H. Qed.

Lemma wft_ltl_inv a b p : wft p (sLtl a b) -> wft a sLvl /\ wft b sLvl.
Proof. intro H; apply wf_sort_ltl_inv; eapply wft_wf_sort; exact H. Qed.

(* ------------------------------------------------------------------ *)
(* The [dtt_wf] hint database and the [wfa] solver                      *)
(* ------------------------------------------------------------------ *)

#[export] Hint Resolve
  wf_Rel wf_Irr wf_L0 wf_L1 wf_Lt01 wf_Iota wf_Inf wf_Next wf_Info
  wf_Emp wf_Ext wf_Id wf_Forget wf_Cmp wf_TySubst wf_ExpSubst wf_Snoc
  wf_Wkn wf_Hd
  wf_U wf_El
  wf_Nat wf_Zero wf_Suc wf_Empty wf_Emptyrec
  wf_PiRel wf_PiIrr wf_LamRel wf_LamIrr wf_AppRel wf_AppIrr
  : dtt_wf.

(* The sort-formation rules, so that [wf_sort] goals are discharged too.
   [sEnv]/[sRelevance]/[sLvl]/[sTlvl]/[sInfo] are nullary sorts; the four
   indexed ones need their indices, which [eauto] finds from [dtt_wf]. *)
Lemma wf_sort_env : wf_sort ott_dtt [] sEnv.
Proof. eapply wf_sort_by; [ solve_in | repeat constructor ]. Qed.

Lemma wf_sort_relevance : wf_sort ott_dtt [] sRelevance.
Proof. eapply wf_sort_by; [ solve_in | repeat constructor ]. Qed.

Lemma wf_sort_lvl : wf_sort ott_dtt [] sLvl.
Proof. eapply wf_sort_by; [ solve_in | repeat constructor ]. Qed.

Lemma wf_sort_tlvl : wf_sort ott_dtt [] sTlvl.
Proof. eapply wf_sort_by; [ solve_in | repeat constructor ]. Qed.

Lemma wf_sort_info : wf_sort ott_dtt [] sInfo.
Proof. eapply wf_sort_by; [ solve_in | repeat constructor ]. Qed.

(* The indexed sort formers.  Their [wf_args] obligations are exactly the
   index-typing hypotheses, presented as [t[/.../]]; [norm_wf_goal] puts
   them back in [s*] form so that [eassumption] closes them. *)
Ltac wf_sort_by name :=
  eapply wf_sort_by with (n := name); [ solve_in | wf_args_solve ].

Lemma wf_sort_sub G G'
  : wft G sEnv -> wft G' sEnv -> wf_sort ott_dtt [] (sSub G G').
Proof. intros; wf_sort_by "sub". Qed.

Lemma wf_sort_ty G i
  : wft G sEnv -> wft i sInfo -> wf_sort ott_dtt [] (sTy G i).
Proof. intros; wf_sort_by "ty". Qed.

Lemma wf_sort_exp G i A
  : wft G sEnv -> wft i sInfo -> wft A (sTy G i) ->
    wf_sort ott_dtt [] (sExp G i A).
Proof. intros; wf_sort_by "exp". Qed.

Lemma wf_sort_ltl a b
  : wft a sLvl -> wft b sLvl -> wf_sort ott_dtt [] (sLtl a b).
Proof. intros; wf_sort_by "ltl". Qed.

#[export] Hint Resolve
  wf_sort_env wf_sort_relevance wf_sort_lvl wf_sort_tlvl wf_sort_info
  wf_sort_sub wf_sort_ty wf_sort_exp wf_sort_ltl : dtt_wf.

(* Derived shapes that occur constantly in the binder rules; without these
   [eauto] would have to unfold [sCode]/[sElt]/[oExtC] itself. *)
Lemma wf_sCode G r l
  : wft G sEnv -> wft r sRelevance -> wft l sLvl ->
    wf_sort ott_dtt [] (sCode G r l).
Proof.
  intros; unfold sCode, iCode; apply wf_sort_exp;
    auto using wf_Info, wf_Rel, wf_Next, wf_U.
Qed.

Lemma wf_sElt G r l e
  : wft G sEnv -> wft r sRelevance -> wft l sLvl -> wft e (sCode G r l) ->
    wf_sort ott_dtt [] (sElt G r l e).
Proof.
  intros; unfold sElt, iEl; apply wf_sort_exp;
    auto using wf_Info, wf_Iota, wf_El.
Qed.

Lemma wf_ExtC G rF lF F
  : wft G sEnv -> wft rF sRelevance -> wft lF sLvl -> wft F (sCode G rF lF) ->
    wft (oExtC G rF lF F) sEnv.
Proof.
  intros; unfold oExtC, iEl; apply wf_Ext;
    auto using wf_Info, wf_Iota, wf_El.
Qed.

#[export] Hint Resolve wf_sCode wf_sElt wf_ExtC : dtt_wf.

(* [wfa] : the routine well-formedness solver for later layers.  Unlike the
   STLC version (which was a hand-ordered [repeat first [...]]), the DTT
   rules are genuinely dependent -- e.g. [wf_El] needs [wft e (sCode G r l)]
   whose [r]/[l] are not determined by the goal -- so plain [eauto] with the
   database, which backtracks, is the right tool.  The [unfold] preamble
   exposes the [s*]/[o*] abbreviations that the goal may be phrased with. *)
Ltac wfa :=
  repeat (intros
          || (progress unfold sCode, sElt, oExtC, iCode, iEl in * )
          || eassumption);
  eauto 8 with dtt_wf.
