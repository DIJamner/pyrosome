(* Soundness of the e-graph SIMPLIFIER [egraph_simpl] (and, via the
   renaming bridge in Automation.v, of [egraph_simpl']).

   [egraph_simpl] adds a term to a fresh e-graph, saturates against a
   compiled rule_set until the subject's weight drops, and extracts the
   cheapest representative of the subject's e-class.  Soundness says the
   extracted term is [eq_term]-equal to the input.  The proof is the
   one-term analogue of [ReducingCong.egraph_reducing_equal_step_sound_strong]
   (empty egraph sound -> [add_open_term] -> [get_analysis] -> [rebuild] ->
   [saturate_until], each preserving/extending the interpretation), followed
   by [ReducingCong.denote_extract_eq] for the read-back. *)

Set Implicit Arguments.

From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.

From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsSaturate SemanticsAreUnified.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs Theorems SchedSat ReducingCong.

(* [Pyrosome.Tools.EGraph.Defs.size] is the analysis every egraph in this
   development runs; it is not registered in the instance database (its
   [Instance] declaration is section-local), so re-register it here to let
   the [analysis V V (option positive)] arguments below be inferred. *)
#[local] Existing Instance Pyrosome.Tools.EGraph.Defs.size.

Section SimplSound.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.
  Context (V_map : forall A, map.map V A)
    (V_map_plus : ExtraMaps.map_plus V_map)
    (V_map_ok : forall A, map.ok (V_map A))
    (V_map_plus_ok : ExtraMaps.map_plus_ok V_map)
    (V_trie : forall A, map.map (list V) A)
    (V_trie_ok : forall A, map.ok (V_trie A)).
  Context (succ : V -> V) (V_leb : V -> V -> bool) (sort_of : V) (lt : V -> V -> Prop).
  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).
  Context (spaced_list_intersect
            : forall B, WithDefault B -> (B -> B -> B) ->
                        ne_list (V_trie B * list bool) -> V_trie B).
  Context (l : lang V) (wfl : wf_lang l) (sort_of_fresh : fresh sort_of l).

  Local Notation lang_model := (lang_model V sort_of l).
  Local Notation sound :=
    (egraph_sound_for_interpretation V V V_map V_map V_trie (option positive) lang_model).
  Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie (option positive)).

  Local Notation rs_saturation_hyps rs :=
    (@SchedSat.rs_saturation_hyps V V_Eqb V_default V_map V_map_plus V_trie succ V_leb lt
       (option positive) (size V) spaced_list_intersect lang_model rs).

  (* Soundness of the simplifier: the extracted term is equal to the input.
     The proof chains empty-egraph soundness -> [add_open_term] (places the
     subject class [x], denoting [a]) -> [get_analysis] -> [rebuild] ->
     [saturate_until] (extends the interpretation), then reads the result back
     with [denote_extract_eq] and converts to [a]'s declared sort. *)
  Theorem egraph_simpl_sound
    (rws : rule_set V V V_map V_map) (rfuel fuel efuel : nat)
    (a e' : term V) (ta : sort V) :
    wf_term l [] a ta ->
    rs_saturation_hyps rws ->
    egraph_simpl V_map_plus V_trie succ V_leb sort_of spaced_list_intersect
      l rws rfuel fuel efuel a = Result.Success e' ->
    eq_term l [] ta a e'.
  Proof.
    intros Ha Hrs Hsucc.
    unfold egraph_simpl in Hsucc.
    cbn [Mbind Mret StateMonad.state_monad fst snd] in Hsucc.
    (* name the four sequential state steps exactly as they occur in [Hsucc] *)
    lazymatch type of Hsucc with
    | context [ add_open_term ?su ?so ?ll ?ws ?wc ?sub ?e0 ?g0 ] =>
        set (G0 := g0) in *;
        destruct (add_open_term su so ll ws wc sub e0 G0) as [x ea] eqn:Haa
    end.
    destruct (get_analysis V V V_map V_map V_trie (option positive) x ea) as [w e1] eqn:Hga.
    destruct (rebuild rfuel e1) as [u e2] eqn:Hrb.
    lazymatch type of Hsucc with
    | context [ saturate_until ?su ?vd ?vl ?sli ?rf ?win ?rs ?p ?f ?g0 ] =>
        destruct (saturate_until su vd vl sli rf win rs p f g0) as [res g] eqn:Hsat
    end.
    (* --- the egraph [g] is sound and [x] denotes [a] --- *)
    pose proof (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok V_map
                  V_map_ok V_trie (option positive) lang_model) as Hempty.
    change (empty_egraph V_default (option positive)) with G0 in Hempty.
    destruct Hempty as [Hok0 Hsnd0].
    assert (Hsub : forall (e:term V),
               e [/ with_names_from (@nil (V*sort V)) (@nil (term V)) /] = e)
      by (intro; cbn [with_names_from]; apply term_subst_nil).
    pose proof (@add_open_term_sound V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                  succ sort_of lt lt_asymmetric lt_succ lt_trans (option positive) (size V)
                  l wfl sort_of_fresh true [] [] [] a ta) as Hpa.
    specialize (Hpa ltac:(constructor) Ha ltac:(constructor) (eq_refl) map.empty);
      unfold vc in Hpa.
    specialize (Hpa G0).
    rewrite Haa in Hpa.
    unfold open_term_post in Hpa.
    specialize (Hpa Hok0 Hsnd0 ltac:(cbn; trivial)).
    destruct Hpa as [i1 [ Hext1 Hrel1 ] ].
    cbn [fst snd] in Hext1, Hrel1.
    rewrite Hsub in Hrel1.
    destruct Hext1 as [ Hok_ea [ Hextmap1 [ Hsnd_ea Hkey1 ] ] ].
    pose proof (@lang_model_ok V V_Eqb V_Eqb_ok sort_of l sort_of_fresh wfl) as Hmok.
    pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive)
                  (size V) lang_model x ea i1 Hok_ea Hsnd_ea) as Hg1.
    rewrite Hga in Hg1; cbn [snd] in Hg1; destruct Hg1 as [Hok_e1 Hsnd_e1].
    pose proof (@rebuild_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                  V_map V_map_ok V_map V_map_ok V_trie V_trie_ok (option positive) (size V)
                  lang_model Hmok (fun _ => True) rfuel e1 Hok_e1) as Hrbs.
    rewrite Hrb in Hrbs; cbn [snd] in Hrbs; destruct Hrbs as [Hok_e2 Hiff2].
    assert (Hsnd_e2 : sound i1 e2) by (apply (Hiff2 i1); exact Hsnd_e1).
    (* the termination predicate only reads the analysis, so it preserves
       ok/soundness *)
    assert (HP : forall ee ii, egraph_ok ee -> sound ii ee ->
                 egraph_ok (snd (weight_less_than (V_map:=V_map) (V_trie:=V_trie) x w ee))
                 /\ sound ii (snd (weight_less_than (V_map:=V_map) (V_trie:=V_trie) x w ee))).
    { intros ee ii Hoke Hsnde; unfold weight_less_than;
        cbn [Mbind Mret StateMonad.state_monad].
      pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive)
                    (size V) lang_model x ee ii Hoke Hsnde) as Hp1.
      destruct (get_analysis V V V_map V_map V_trie (option positive) x ee) as [a1 e1'] eqn:He1'.
      cbn [snd] in Hp1; destruct Hp1 as [ Hok1 Hsnd1 ]; cbn [fst snd].
      split; assumption. }
    destruct Hrs as [Hconst Hrules].
    pose proof (@saturate_until_sound V V_Eqb V_Eqb_ok lt succ V_default V_leb V V_Eqb V_Eqb_ok
                  V_map V_map_plus V_map_plus_ok V_map_ok V_map V_map_plus V_map_ok
                  V_trie V_trie_ok (option positive) V_map_plus_ok spaced_list_intersect
                  (size V) lang_model Hmok lt_asymmetric lt_succ lt_trans
                  0 rfuel rws (weight_less_than (V_map:=V_map) (V_trie:=V_trie) x w) HP Hconst Hrules
                  fuel i1 e2 Hok_e2 Hsnd_e2) as Hss.
    rewrite Hsat in Hss.
    destruct Hss as [ Hok_g [ i2 [ Hext2 Hsnd_g ] ] ].
    assert (Hlift : forall (ii ii' : V_map (domain V lang_model)) (xx:V) dd,
               map.extends ii' ii ->
               option_relation (domain_eq V lang_model) (map.get ii xx) (Some dd) ->
               option_relation (domain_eq V lang_model) (map.get ii' xx) (Some dd)).
    { intros ii ii' xx dd Hext Hor.
      unfold option_relation in *.
      destruct (map.get ii xx) as [v|] eqn:Hgv.
      - rewrite (Hext _ _ Hgv); exact Hor.
      - discriminate Hor. }
    pose proof (Hlift i1 i2 x (inl a) Hext2 Hrel1) as Hrel.
    (* --- read back --- *)
    destruct (@denote_extract_eq V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                succ sort_of lt l wfl g i2 efuel x a e' Hok_g Hsnd_g Hrel Hsucc) as [s Heq].
    (* transport to the input's declared sort *)
    apply (eq_term_conv Heq).
    apply (term_sorts_eq wfl ltac:(constructor)
             (eq_term_wf_l wfl ltac:(constructor) Heq) Ha).
  Qed.

End SimplSound.

(* ================================================================== *)
(* Renaming-side helpers for [egraph_simpl'].                          *)
(*                                                                    *)
(* [egraph_simpl'] renames the (closed) language and subject term into *)
(* the positive world, runs [egraph_simpl] there, and maps the         *)
(* EXTRACTED term back with [unrename_term] + [con_to_var].  Unlike    *)
(* [egraph_reducing_equal'], whose two terms are both renamed FORWARD, *)
(* the result here is only known to be positive-world well-formed, so  *)
(* the reverse lift needs (a) that the extracted term is [term_bound]  *)
(* in the renaming -- true because all its constructors are symbols of *)
(* the renamed language -- and (b) that [con_to_var] agrees with       *)
(* [ClosedCore.rtv] on it, which holds for closed terms.               *)
(* ================================================================== *)

From Stdlib Require Import PArith.BinPos.
From Utils Require Import PosListMap.
From Pyrosome.Theory Require Import ClosedCore.
From Pyrosome.Tools Require Import AllConstructors PosRenaming PosRenamingProperties.
From Pyrosome.Tools.EGraph Require Import RenamingCoincide.

(* [Eqb_ok positive] exists only as a [#[local]] instance in
   PosRenamingProperties, so re-establish it here (locally). *)
#[local] Instance pos_Eqb_ok : Eqb_ok PosListMap.positive_Eqb.
Proof. intros a b; unfold eqb, PosListMap.positive_Eqb; destruct (Pos.eqb_spec a b); auto. Qed.

Section RenamingHelpers.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  (* Every symbol of a bound language is itself bound. *)
  Lemma pbound_of_lang_bound (r : renaming V) (lp : lang positive) (n : positive) :
    lang_bound r lp -> In n (map fst lp) -> pbound r n.
  Proof.
    intros Hlb Hin.
    apply in_map_iff in Hin; destruct Hin as [ [n' rr] [Heq Hin] ]; cbn in Heq; subst n'.
    exact (proj1 (in_all _ _ _ Hlb Hin)).
  Qed.

  (* A term well-formed in the (bound) positive language is bound: its
     constructors are language symbols, and it has no variables. *)
  Lemma term_bound_of_wf (r : renaming V) (lp : lang positive)
    (ep : Term.term positive) (tp : Term.sort positive) :
    lang_bound r lp -> wf_lang lp -> wf_term lp [] ep tp -> term_bound r ep.
  Proof.
    intros Hlb Hwfl Hwf.
    pose proof (wf_term_all_constructors Hwf) as Hac.
    pose proof (wf_term_implies_ws (wf_lang_implies_ws_noext Hwfl) Hwf) as Hws.
    clear Hwf Hwfl.
    revert Hac Hws.
    induction ep as [x | n args IHargs];
      cbn [all_constructors term_bound]; cbn [well_scoped ws_term].
    - intros _ Hin; destruct Hin.
    - intros [Hn Hall] Hws.
      split; [ exact (pbound_of_lang_bound r lp n Hlb Hn) | ].
      revert IHargs Hall Hws; clear.
      induction args as [|a args' IH]; cbn [all]; [ tauto | ].
      intros [IHa IHrest] [Ha Hrest] [Hwsa Hwsrest].
      split; [ exact (IHa Ha Hwsa) | exact (IH IHrest Hrest Hwsrest) ].
  Qed.

  (* [con_to_var] (the e-graph readback) and [ClosedCore.rtv] agree on
     closed terms: both replace exactly the constructors named in the
     context by variables, and they differ only in the (unreachable)
     variable case. *)
  Lemma con_to_var_is_rtv (c : Term.ctx V) (ep : Term.term V) :
    well_scoped ([] : list V) ep -> con_to_var (map fst c) ep = rtv c ep.
  Proof.
    induction ep as [x | n args IHargs];
      cbn [con_to_var rtv]; cbn [well_scoped ws_term].
    - intros Hin; destruct Hin.
    - intros Hws.
      case_match; [ reflexivity | ].
      f_equal.
      revert IHargs Hws; clear.
      induction args as [|a args' IH]; cbn [all map]; [ reflexivity | ].
      intros [IHa IHrest] [Hwsa Hwsrest].
      rewrite (IHa Hwsa), (IH IHrest Hwsrest); reflexivity.
  Qed.

  (* The reverse lift for a RESULT term: an equality the e-graph proved in
     the positive, closed world between the renamed subject [ep] and an
     arbitrary (bound) positive term [e2p] lifts to an equality in the
     original open world, with the result read back by [con_to_var]. *)
  Lemma reverse_eq_term_lift_result
      (l : lang V) (c : Term.ctx V) (t : Term.sort V) (e : Term.term V)
      (r : renaming V) (lp : lang positive) (tp : Term.sort positive)
      (ep e2p : Term.term positive)
    : wf_lang l ->
      wf_ctx (Model:=core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      wf_term l c e t ->
      renaming_ok r ->
      lang_bound r lp ->
      sort_bound r tp ->
      term_bound r ep ->
      term_bound r e2p ->
      wf_lang lp ->
      unrename_lang r lp = ClosedCore.ctx_to_rules c ++ l ->
      unrename_term r ep = vtr e ->
      unrename_sort r tp = svtr t ->
      eq_term lp [] tp ep e2p ->
      eq_term l c t e (con_to_var (map fst c) (unrename_term r e2p)).
  Proof.
    intros wfl wfc Hdisj He Hrok Hbl Hbt Hbe Hbe2 Hwflp Hul Hue Hut Heq.
    pose proof (wf_lang_concat wfl (ctx_to_rules_wf wfl wfc Hdisj)) as Hwfl'.
    pose proof (eq_term_wf_sort wfl wfc (eq_term_refl He)) as Hwfsort.
    pose proof (unrename_preserves_eq_term Hrok Heq Hbl
                  ltac:(exact I) Hbt Hbe Hbe2 Hwflp ltac:(constructor)) as Hun.
    rewrite Hul, Hue, Hut in Hun.
    replace (unrename_ctx r []) with (@nil (V * sort V)) in Hun by reflexivity.
    (* the unrenamed result is closed, so [con_to_var] is [rtv] *)
    pose proof (eq_term_wf_r Hwfl' ltac:(constructor) Hun) as Hwfres.
    rewrite (con_to_var_is_rtv c (unrename_term r e2p)
               (wf_term_implies_ws (wf_lang_implies_ws_noext Hwfl') Hwfres)).
    pose proof (eq_rtv wfl wfc Hwfl' Hdisj) as Hall_rtv.
    destruct Hall_rtv as [Hsrt Hall_rtv1].
    destruct Hall_rtv1 as [Het Hall_rtv2].
    pose proof (Het (svtr t) (vtr e) (unrename_term r e2p) Hun) as Hrtv.
    rewrite (srtv_svtr_wf wfl wfc Hdisj Hwfsort) in Hrtv.
    rewrite (rtv_vtr_wf wfl wfc Hdisj He) in Hrtv.
    exact Hrtv.
  Qed.

End RenamingHelpers.

(* ================================================================== *)
(* The positive-side saturation hypotheses for a single built          *)
(* rule_set (the Phase-6 obligation, specialized to [egraph_simpl],    *)
(* which runs ONE rule_set rather than a schedule).  Same derivation   *)
(* as the [schedule_sound] conjunct of [egraph_reducing_equal'_to_pos]: *)
(* [msr_of_build_rule_set] + [rs_saturation_const_conjunct] +          *)
(* [compiled_rules_run1iter_rule_hyps].                                *)
(* ================================================================== *)

From Stdlib Require Import NArith.
From Utils Require Import TrieMap FullPosTrie FullPosTrieConv TrieMapFold.
From Utils.EGraph Require Import QcAlignment QueryOptSound.
From Pyrosome.Tools.EGraph Require Import AdapterGlue.

Lemma pos_lt_asym : Asymmetric Pos.lt.
Proof. intros x y h1 h2; exact (Pos.lt_irrefl x (Pos.lt_trans _ _ _ h1 h2)). Qed.

Lemma build_rule_set_saturation_hyps
  (Lp posX : lang positive) (rf : nat)
  (rs : rule_set positive positive TrieMap.trie_map TrieMap.trie_map) :
  wf_lang Lp ->
  fresh PosListMap.sort_of Lp ->
  incl posX Lp ->
  PositiveInstantiation.build_rule_set rf posX Lp = Result.Success rs ->
  @SchedSat.rs_saturation_hyps positive PosListMap.positive_Eqb PosListMap.positive_default
    TrieMap.trie_map TrieMap.ptree_map_plus (@FullPosTrie.full_pos_trie_map)
    Pos.succ Pos.leb Pos.lt (option positive) (size positive) (@fpt_spaced_intersect)
    (Theorems.lang_model positive PosListMap.sort_of Lp) rs.
Proof.
  intros HwfLp Hsof Hincl Hbrs.
  unfold PositiveInstantiation.build_rule_set in Hbrs.
  destruct (@AdapterGlue.msr_of_build_rule_set
              positive PosListMap.positive_Eqb pos_Eqb_ok PosListMap.positive_default
              TrieMap.trie_map TrieMap.ptree_map_plus (fun A => @TrieMapFold.trie_map_ok A)
              (@FullPosTrie.full_pos_trie_map) (fun A => @FullPosTrie.full_pos_trie_map_ok A)
              Pos.succ Pos.leb PosListMap.sort_of Pos.lt pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
              Lp HwfLp Hsof rf posX rs Hincl Hbrs)
    as (seqs & Hrs_eq & Hmsr).
  pose proof (@Theorems.lang_model_ok positive PosListMap.positive_Eqb pos_Eqb_ok
                PosListMap.sort_of Lp Hsof HwfLp) as Hmok.
  rewrite Hrs_eq.
  unfold SchedSat.rs_saturation_hyps.
  split.
  - intros e i Hok Hsnd.
    exact (@QueryOptSound.rs_saturation_const_conjunct
             positive PosListMap.positive_Eqb pos_Eqb_ok Pos.lt Pos.succ
             PosListMap.positive_default Pos.leb
             positive PosListMap.positive_Eqb pos_Eqb_ok
             TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
             TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
             (@FullPosTrie.full_pos_trie_map) (fun A => @FullPosTrie.full_pos_trie_map_ok A)
             (option positive) (size positive)
             (Theorems.lang_model positive PosListMap.sort_of Lp)
             Hmok pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
             rf seqs Hmsr i e Hok Hsnd).
  - intros w e er Hin_er.
    apply (@QueryOptSound.compiled_rules_run1iter_rule_hyps
             positive PosListMap.positive_Eqb pos_Eqb_ok Pos.lt Pos.succ
             PosListMap.positive_default Pos.leb
             positive PosListMap.positive_Eqb pos_Eqb_ok
             TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
             TrieMap.trie_map TrieMap.ptree_map_plus
             (fun A => @TrieMapFold.trie_map_ok A)
             (@FullPosTrie.full_pos_trie_map)
             pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
             TrieMap.ptree_map_plus_ok
             (@fpt_spaced_intersect)
             (option positive) (size positive)
             w
             (Theorems.lang_model positive PosListMap.sort_of Lp)
             Hmok rf seqs er e Hmsr Hin_er).
    + exact (QcAlignment.trie_join_H9_sn rf seqs er Hin_er e w).
    + exact (QcAlignment.trie_join_H10_sn rf seqs er Hin_er e w).
Qed.
