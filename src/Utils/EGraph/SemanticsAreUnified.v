(* are_unified / get_analysis soundness lemmas, split out of Semantics.v
   (Section WithMap) to keep that file smaller.  Stated at top level with the
   egraph + model context as explicit arguments; signatures match the
   section-closed forms consumed by Theorems / ReducingCong / Automation /
   QueryOptSound. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.


  Lemma are_unified_sound
    (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
    (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
    (symbol : Type) (symbol_map : forall A, map.map symbol A)
    (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
    (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
    (x1 x2 : idx) (e : instance idx symbol symbol_map idx_map idx_trie analysis_result) :
    (exists l, union_find_ok lt e.(equiv) l) ->
    Sep.has_key x1 e.(equiv).(parent) ->
    Sep.has_key x2 e.(equiv).(parent) ->
    fst (@are_unified _ Eqb_idx _ _ _ _ _ x1 x2 e) = true ->
    uf_rel_PER idx (idx_map idx) (idx_map nat) e.(equiv) x1 x2.
  Proof.
    intros Hok Hk1 Hk2 Hunified.
    unfold are_unified in Hunified.
    cbn [Mbind Mret StateMonad.state_monad] in Hunified.
    pose proof (@find_preserves_fields_strong idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result x1 e Hok Hk1) as Hf1.
    destruct (@find idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result x1 e) as [r1 e1] eqn:Hfind1.
    cbn [fst snd] in Hf1, Hunified.
    destruct Hf1 as (Hok1 & Hfp1 & Hrel1).
    destruct Hfp1 as (_ & _ & _ & _ & _ & Hkiff1 & Hiff1).
    assert (Hk2_e1 : Sep.has_key x2 (parent (equiv e1))) by (apply Hkiff1; exact Hk2).
    pose proof (@find_preserves_fields_strong idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result x2 e1 Hok1 Hk2_e1) as Hf2.
    destruct (@find idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result x2 e1) as [r2 e2] eqn:Hfind2.
    cbn [fst snd] in Hf2, Hunified.
    destruct Hf2 as (Hok2 & Hfp2 & Hrel2).
    pose proof (eqb_spec r1 r2) as Hr. rewrite Hunified in Hr. subst r2.
    destruct Hfp2 as (_ & _ & _ & _ & _ & Hkiff2 & Hiff2).
    apply (proj1 (Hiff2 r1 x1)) in Hrel1.
    assert (Hx1x2 : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e2) x1 x2)
      by (eapply PER_clo_trans; [apply PER_clo_sym; exact Hrel1 | exact Hrel2]).
    apply (proj2 (Hiff1 x1 x2)). apply (proj2 (Hiff2 x1 x2)). exact Hx1x2.
  Qed.

  Lemma are_unified_eq_sound
    (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
    (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
    (symbol : Type) (symbol_map : forall A, map.map symbol A)
    (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
    (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
    (m : model symbol)
    (x1 x2 : idx) (e : instance idx symbol symbol_map idx_map idx_trie analysis_result)
    (i : idx_map (domain symbol m)) :
    egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
    egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
    Sep.has_key x1 e.(equiv).(parent) ->
    Sep.has_key x2 e.(equiv).(parent) ->
    fst (@are_unified _ Eqb_idx _ _ _ _ _ x1 x2 e) = true ->
    eq_sound_for_model idx symbol idx_map m i x1 x2.
  Proof.
    intros Hok Hsnd Hk1 Hk2 Hu.
    apply (rel_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e Hsnd).
    apply (@are_unified_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result x1 x2 e); try assumption.
    apply (egraph_equiv_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e Hok).
  Qed.

  Lemma are_unified_preserves_ok_sound
    (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
    (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
    (symbol : Type) (symbol_map : forall A, map.map symbol A)
    (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
    (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
    (m : model symbol)
    (x1 x2 : idx) (e : instance idx symbol symbol_map idx_map idx_trie analysis_result)
    (i : idx_map (domain symbol m)) :
    egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
    egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
    egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result (snd (@are_unified _ Eqb_idx _ _ _ _ _ x1 x2 e))
    /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i (snd (@are_unified _ Eqb_idx _ _ _ _ _ x1 x2 e)).
  Proof.
    intros Hok Hsnd.
    unfold are_unified.
    cbn [Mbind Mret StateMonad.state_monad].
    pose proof (@find_denote_iff idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result m x1 e Hok) as Hf1.
    destruct (@find idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result x1 e) as [r1 e1] eqn:Hfind1.
    cbn [snd] in Hf1.
    destruct Hf1 as [Hok1 Hde1].
    pose proof (@find_denote_iff idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result m x2 e1 Hok1) as Hf2.
    destruct (@find idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result x2 e1) as [r2 e2] eqn:Hfind2.
    cbn [snd] in Hf2.
    destruct Hf2 as [Hok2 Hde2].
    cbn [snd].
    split; [exact Hok2|].
    apply (Hde2 i). apply (Hde1 i). exact Hsnd.
  Qed.

  Lemma get_analysis_preserves_ok_sound
    (idx : Type) (lt : idx -> idx -> Prop) (symbol : Type)
    (symbol_map : forall A, map.map symbol A) (idx_map : forall A, map.map idx A)
    (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
    (H : analysis idx symbol analysis_result) (m : model symbol)
    (x : idx) (e : instance idx symbol symbol_map idx_map idx_trie analysis_result)
    (i : idx_map (domain symbol m)) :
    egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
    egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
    egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result (snd (get_analysis idx symbol symbol_map idx_map idx_trie analysis_result x e))
    /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i (snd (get_analysis idx symbol symbol_map idx_map idx_trie analysis_result x e)).
  Proof.
    intros Hok Hsnd.
    pose proof (@get_analysis_denote_iff idx lt symbol symbol_map idx_map idx_trie analysis_result H m x e Hok) as [Hok' Hiff].
    split.
    - exact Hok'.
    - apply Hiff. exact Hsnd.
  Qed.

  Lemma eq_sound_to_domain_eq
    (idx symbol : Type) (idx_map : forall A, map.map idx A)
    (m : model symbol) (Hm : model_ok symbol m)
    (i : idx_map (domain symbol m)) (x1 x2 : idx) (d1 d2 : domain symbol m) :
    eq_sound_for_model idx symbol idx_map m i x1 x2 ->
    option_relation (domain_eq symbol m) (map.get i x1) (Some d1) ->
    option_relation (domain_eq symbol m) (map.get i x2) (Some d2) ->
    domain_eq symbol m d1 d2.
  Proof.
    intros Hes Hd1 Hd2.
    unfold option_relation in Hd1, Hd2.
    destruct (map.get i x1) as [a1|] eqn:G1; [|exfalso; discriminate Hd1].
    destruct (map.get i x2) as [a2|] eqn:G2; [|exfalso; discriminate Hd2].
    unfold eq_sound_for_model in Hes. rewrite G1, G2 in Hes. cbn [Is_Some_satisfying] in Hes.
    transitivity a1; [symmetry; exact Hd1|].
    transitivity a2; [exact Hes | exact Hd2].
  Qed.
