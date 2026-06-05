From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface Map.Properties.
From coqutil Require Import Datatypes.Result.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs Theorems.

Section Scratch.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.
  Context (V_map : forall A, map.map V A)
    (V_map_plus : ExtraMaps.map_plus V_map)
    (V_map_ok : forall A, map.ok (V_map A))
    (V_map_plus_ok : ExtraMaps.map_plus_ok V_map)
    (V_trie : forall A, map.map (list V) A)
    (V_trie_ok : forall A, map.ok (V_trie A)).
  Context (succ : V -> V) (sort_of : V) (lt : V -> V -> Prop).
  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).
  Context (l : Rule.lang V) (wfl : wf_lang l) (sort_of_fresh : fresh sort_of l).

  Local Notation lang_model := (lang_model V sort_of l).
  Local Notation sound :=
    (egraph_sound_for_interpretation V V V_map V_map V_trie (option positive) lang_model).
  Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie (option positive)).

  (* Clean reduction lemmas for the [stateT (V_map term) result] monad. *)
  Lemma stateT_result_bind {A B} (f : A -> stateT (V_map (term V)) result B)
    (m : stateT (V_map (term V)) result A) (s : V_map (term V)) :
    Mbind f m s = match m s with
                  | Success p => f (fst p) (snd p)
                  | Failure e => Failure e
                  end.
  Proof. cbn. unfold Basics.compose. destruct (m s) as [ [a s'] | e]; reflexivity. Qed.

  Lemma stateT_result_ret {A} (a : A) (s : V_map (term V)) :
    (Mret a : stateT (V_map (term V)) result A) s = Success (a, s).
  Proof. reflexivity. Qed.

  Section ExtractFixed.
    Context (g : instance V V V_map V_map V_trie (option positive)).
    Context (interp : V_map (term V + sort V)).
    Context (Hsnd : sound interp g).

    Definition cache_sound (cache : V_map (term V)) : Prop :=
      forall k v, map.get cache k = Some v ->
        exists ek t, map.get interp k = Some (inl ek) /\ eq_term l [] t v ek.

    Lemma list_extract_sound
      (rec : V -> stateT (V_map (term V)) Result.result (term V))
      (Hrec : forall x cache e cache' e_x,
        cache_sound cache -> map.get interp x = Some (inl e_x) ->
        rec x cache = Result.Success (e, cache') ->
        cache_sound cache' /\ exists t, eq_term l [] t e e_x) :
      forall args args_terms cache children cache',
        list_Mmap (map.get interp) args = Some (map inl args_terms) ->
        cache_sound cache ->
        list_Mmap rec args cache = Result.Success (children, cache') ->
        cache_sound cache'
        /\ all2 (fun child e => exists t, eq_term l [] t child e) children args_terms.
    Proof.
      induction args as [|a args0 IHargs]; intros args_terms cache children cache' Hget Hcache Hmmap.
      - cbn in Hmmap. injection Hmmap; intros; subst children cache'.
        cbn in Hget. destruct args_terms as [|et args_terms0]; [ | cbn in Hget; discriminate ].
        split; [ exact Hcache | cbn; exact I ].
      - cbn [list_Mmap] in Hget, Hmmap.
        destruct (map.get interp a) as [d_a|] eqn:Hia; cbn [Mbind option_monad] in Hget; [ | discriminate ].
        destruct (list_Mmap (map.get interp) args0) as [ds|] eqn:Hds; cbn [Mbind Mret option_monad] in Hget; [ | discriminate ].
        injection Hget; intro Heq_dads.
        destruct args_terms as [|e_a args_terms0]; [ cbn in Heq_dads; discriminate | ].
        cbn [map] in Heq_dads. injection Heq_dads; intros Hds_eq Hda_eq.
        rewrite stateT_result_bind in Hmmap.
        destruct (rec a cache) as [ [c_a cache1] | err1 ] eqn:Hreca; [ cbn [fst snd] in Hmmap | discriminate ].
        rewrite stateT_result_bind in Hmmap.
        destruct (list_Mmap rec args0 cache1) as [ [cs cache2] | err2 ] eqn:Hlm; [ cbn [fst snd] in Hmmap | discriminate ].
        rewrite stateT_result_ret in Hmmap.
        injection Hmmap; intros Hcache'_eq Hchildren_eq; subst children cache'.
        assert (Hia' : map.get interp a = Some (inl e_a)) by (rewrite Hia, Hda_eq; reflexivity).
        destruct (Hrec a cache c_a cache1 e_a Hcache Hia' Hreca) as [Hcache1 Hhead].
        assert (Hds' : Some ds = Some (map inl args_terms0)) by (rewrite Hds_eq; reflexivity).
        destruct (IHargs args_terms0 cache1 cs cache2 Hds' Hcache1 Hlm) as [Hcache2 Htail].
        split; [ exact Hcache2 | ].
        cbn [all2]. split; [ exact Hhead | exact Htail ].
    Qed.

    Lemma extractF_sound
      (rec : V -> stateT (V_map (term V)) Result.result (term V))
      (Hrec : forall x cache e cache' e_x,
        cache_sound cache -> map.get interp x = Some (inl e_x) ->
        rec x cache = Result.Success (e, cache') ->
        cache_sound cache' /\ exists t, eq_term l [] t e e_x) :
      forall x cache e cache' e_x,
        cache_sound cache -> map.get interp x = Some (inl e_x) ->
        memoizeF (extract_weightedF g) rec x cache = Result.Success (e, cache') ->
        cache_sound cache' /\ exists t, eq_term l [] t e e_x.
    Proof.
      intros x cache e cache' e_x Hcache Hix Hmemo.
      unfold memoizeF in Hmemo.
      rewrite stateT_result_bind in Hmemo.
      unfold stateT_get in Hmemo.
      cbn [fst snd] in Hmemo.
      destruct (map.get cache x) as [v|] eqn:Hcx.
      - cbn [Mret result_monad fst snd] in Hmemo.
        rewrite Hcx in Hmemo.
        rewrite stateT_result_ret in Hmemo.
        injection Hmemo; intros Hc' He; subst e cache'.
        destruct (Hcache x v Hcx) as (ek & t & Hek & Heqv).
        rewrite Hix in Hek. injection Hek; intro Hekx; subst ek.
        split; [ exact Hcache | exists t; exact Heqv ].
      - cbn [Mret result_monad fst snd] in Hmemo.
        rewrite Hcx in Hmemo.
        rewrite stateT_result_bind in Hmemo.
        unfold extract_weightedF in Hmemo.
        destruct (map.get (select_optimal_nodes V_map V_trie oP_le (analyses g) (db g)) x) as [ [x_f x_args] | ] eqn:Hopt;
          cbn [result_of_option_else] in Hmemo; [ | cbn in Hmemo; discriminate ].
        rewrite stateT_result_bind in Hmemo.
        cbn [lift stateT_trans Mbind Mret result_monad fst snd] in Hmemo.
        rewrite stateT_result_bind in Hmemo.
        destruct (list_Mmap rec x_args cache) as [ [children0 cache_mid] | err ] eqn:Hlm;
          [ cbn [fst snd] in Hmemo | cbn [fst snd] in Hmemo; discriminate ].
        rewrite stateT_result_ret in Hmemo.
        cbn [fst snd] in Hmemo.
        rewrite stateT_result_bind in Hmemo.
        unfold stateT_put in Hmemo.
        cbn [Mret result_monad fst snd] in Hmemo.
        rewrite stateT_result_ret in Hmemo.
        injection Hmemo; intros Hcache'_eq He_eq; subst e cache'.
        pose proof (select_optimal_nodes_sound V V_map V_map_ok V_trie V_trie_ok (option positive) oP_le (analyses g) (db g) x x_f x_args Hopt) as Hatomdb.
        destruct Hsnd as [Hwf_interp Hexact Hatom_interp Hrel].
        pose proof (Hatom_interp (Build_atom x_f x_args x) Hatomdb) as Hatomsnd.
        unfold atom_sound_for_model, Is_Some_satisfying in Hatomsnd.
        cbn [atom_args atom_ret atom_fn] in Hatomsnd.
        change (domain V lang_model) with (term V + sort V)%type in Hatomsnd.
        destruct (list_Mmap (map.get interp) x_args) as [arg_doms|] eqn:Hld;
          cbn beta iota in Hatomsnd; [ | contradiction ].
        rewrite Hix in Hatomsnd.
        change (interprets_to V lang_model) with (lang_model_interprets_to V sort_of l) in Hatomsnd.
        inversion Hatomsnd as [ | | f0 args0 e0 t0 Heqterm Hf0 Hargs0 He0 ]; subst.
        destruct (list_extract_sound rec Hrec x_args args0 cache children0 cache_mid Hld Hcache Hlm) as [Hcache_mid Hall].
        pose proof (eq_term_wf_l wfl ltac:(constructor) Heqterm) as Hwfcon.
        apply WfCutElim.invert_wf_term_con in Hwfcon.
        destruct Hwfcon as (c & rule_args & t_rule & Hin & Hwfargs0 & Ht0).
        assert (Hwfc : wf_ctx (Model:=core_model l) c) by eauto with lang_core.
        assert (Hall2 : all2 (lang_model_eq V l) (map inl args0) (map inl children0))
          by (clear -Hall; revert args0 Hall; induction children0 as [|c0 cs' IH];
              intros [|a0 args0'] Hall; cbn in Hall |- *; try contradiction; auto;
              destruct Hall as [ [t Ht] Hrest ]; split;
              [ econstructor; apply eq_term_sym; exact Ht | apply IH; exact Hrest ]).
        pose proof (all2_model_eq_eq_args V l wfl args0 children0 c Hwfargs0 Hwfc Hall2) as Heqargs.
        pose proof (term_con_congruence x_f rule_args t_rule Hin (or_intror eq_refl) wfl Heqargs) as Hcong.
        assert (Hwf1 : wf_term l [] (con x_f args0) (t_rule [/with_names_from c children0 /]))
          by (apply (eq_term_wf_l wfl ltac:(constructor) Hcong)).
        assert (Hwf2 : wf_term l [] (con x_f args0) t0)
          by (apply (eq_term_wf_l wfl ltac:(constructor) Heqterm)).
        assert (Hsorteq : eq_sort l [] (t_rule [/with_names_from c children0 /]) t0)
          by (apply (term_sorts_eq wfl ltac:(constructor) Hwf1 Hwf2)).
        assert (Hfinal : eq_term l [] t0 (con x_f children0) e_x)
          by (eapply eq_term_trans;
              [ exact (eq_term_conv (eq_term_sym Hcong) Hsorteq) | exact Heqterm ]).
        split.
        + intros k v Hk.
          destruct (eqb k x) eqn:Hkx; pose proof (eqb_spec k x) as Hkxs; rewrite Hkx in Hkxs.
          ++ subst k. rewrite map.get_put_same in Hk. injection Hk; intro Hv; subst v.
             exists e_x, t0. split; [ exact Hix | exact Hfinal ].
          ++ rewrite map.get_put_diff in Hk; [ | congruence ]. exact (Hcache k v Hk).
        + exists t0. exact Hfinal.
    Qed.

    Lemma extract_weighted'_sound :
      forall efuel x cache e cache' e_x,
        cache_sound cache -> map.get interp x = Some (inl e_x) ->
        extract_weighted' g efuel x cache = Result.Success (e, cache') ->
        cache_sound cache' /\ exists t, eq_term l [] t e e_x.
    Proof.
      induction efuel as [|n IHn]; intros x cache e cache' e_x Hcache Hix Hext.
      - cbn [extract_weighted' decr] in Hext.
        eapply (extractF_sound default); [ | exact Hcache | exact Hix | exact Hext ].
        intros x0 cache0 e0 cache0' e_x0 _ _ Hd. cbn in Hd. discriminate Hd.
      - cbn [extract_weighted' decr] in Hext.
        eapply (extractF_sound (extract_weighted' g n)); [ exact IHn | exact Hcache | exact Hix | exact Hext ].
    Qed.

    Lemma extract_weighted_sound (efuel : nat) (x : V) (e : term V) (e_x : term V) :
      map.get interp (snd (UnionFind.find (equiv g) x)) = Some (inl e_x) ->
      extract_weighted g efuel x = Result.Success e ->
      exists t, eq_term l [] t e e_x.
    Proof.
      intros Hix Hext.
      unfold extract_weighted in Hext.
      cbn [Mbind Mret] in Hext.
      destruct (extract_weighted' g efuel (snd (UnionFind.find (equiv g) x)) map.empty)
        as [ [e0 cache0] | err ] eqn:Hext'; cbn [Mbind Mret result_monad fst] in Hext;
        [ | discriminate ].
      injection Hext; intro He; subst e0.
      assert (Hcache0 : cache_sound map.empty)
        by (intros k v Hk; rewrite map.get_empty in Hk; discriminate).
      destruct (extract_weighted'_sound efuel _ map.empty e cache0 e_x Hcache0 Hix Hext')
        as [ _ Heq ].
      exact Heq.
    Qed.

  End ExtractFixed.

End Scratch.

Section CongWf.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}.
  Context (l : Rule.lang V) (wfl : wf_lang l).

  Lemma select_inj_args_wf (c' : ctx V) inj_args (s1 s2 : list (term V)) subgoals :
    @select_inj_args V V_Eqb c' inj_args s1 s2 = Some subgoals ->
    wf_args (Model:=core_model l) [] s1 c' ->
    wf_args (Model:=core_model l) [] s2 c' ->
    all (fun p => (exists sa, wf_term l [] (fst p) sa)
                  /\ (exists sb, wf_term l [] (snd p) sb)) subgoals.
  Proof.
  Admitted.

  Lemma cong_subgoals_preserves_wf inj_list (e1 e2 : term V) (ta tb : sort V) :
    wf_term l [] e1 ta -> wf_term l [] e2 tb ->
    all (fun p => (exists sa, wf_term l [] (fst p) sa)
                  /\ (exists sb, wf_term l [] (snd p) sb))
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)).
  Proof.
  Admitted.

End CongWf.

Section CongMain.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.
  Context (V_map : forall A, map.map V A)
    (V_map_plus : ExtraMaps.map_plus V_map)
    (V_map_ok : forall A, map.ok (V_map A))
    (V_map_plus_ok : ExtraMaps.map_plus_ok V_map)
    (V_trie : forall A, map.map (list V) A)
    (V_trie_ok : forall A, map.ok (V_trie A)).
  Context (succ : V -> V) (sort_of : V) (lt : V -> V -> Prop).
  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).
  Context (spaced_list_intersect
            : forall B, WithDefault B -> (B -> B -> B) ->
                        ne_list (V_trie B * list bool) -> V_trie B).
  Context (l : Rule.lang V) (wfl : wf_lang l) (sort_of_fresh : fresh sort_of l).

  Local Notation lang_model := (lang_model V sort_of l).
  Local Notation sound :=
    (egraph_sound_for_interpretation V V V_map V_map V_trie (option positive) lang_model).
  Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie (option positive)).

  Lemma find_root_denote (g : instance V V V_map V_map V_trie (option positive))
    (interp : V_map (term V + sort V)) (x : V) (d : term V + sort V) :
    egraph_ok g -> sound interp g -> map.get interp x = Some d ->
    exists d', map.get interp (snd (UnionFind.find (equiv g) x)) = Some d'
               /\ domain_eq V lang_model d' d.
  Proof.
    intros Hok Hsnd Hx.
    assert (Hkey : Sep.has_key x (parent (equiv g)))
      by (apply (interpretation_exact _ _ _ _ _ _ _ _ _ Hsnd x);
          change (domain V lang_model) with (term V + sort V)%type; rewrite Hx; exact I).
    pose proof (find_preserves_fields_strong V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie (option positive) x g (egraph_equiv_ok _ _ _ _ _ _ _ _ Hok) Hkey) as Hf.
    destruct (find x g) as [r g'] eqn:Hfind.
    cbn [fst snd] in Hf.
    destruct Hf as (Hok' & Hfp & Hrel).
    destruct Hfp as (_ & _ & _ & _ & _ & Hkiff & Hiff).
    apply (proj2 (Hiff r x)) in Hrel.
    pose proof (rel_interpretation _ _ _ _ _ _ _ _ _ Hsnd r x Hrel) as Heqs.
    unfold eq_sound_for_model, Is_Some_satisfying in Heqs.
    change (domain V lang_model) with (term V + sort V)%type in Heqs.
    rewrite Hx in Heqs.
    destruct (map.get interp r) as [r'|] eqn:Hr; [ | contradiction ].
    assert (Hreq : snd (UnionFind.find (equiv g) x) = r)
      by (unfold find in Hfind; destruct (UnionFind.find (equiv g) x) as [uf' v'] eqn:Huf;
          cbn [snd] in Hfind |- *; congruence).
    exists r'. rewrite Hreq, Hr. split; [ reflexivity | exact Heqs ].
  Qed.

  Lemma list_Miter_all_success {A} (f : A -> Result.result unit) (xs : list A) :
    list_Miter f xs = Result.Success tt -> forall a, In a xs -> f a = Result.Success tt.
  Proof.
    induction xs as [|a0 xs' IH]; intros Hm a Hin.
    - inversion Hin.
    - cbn [list_Miter] in Hm.
      destruct (f a0) as [u|err] eqn:Hfa0; cbn [Mbind Mret result_monad] in Hm; [ | discriminate ].
      destruct Hin as [Heq | Hin'].
      + subst a. destruct u. exact Hfa0.
      + exact (IH Hm a Hin').
  Qed.

  Lemma eq_term_ex_trans (a b c : term V) :
    (exists s, eq_term l [] s a b) -> (exists s, eq_term l [] s b c) ->
    exists s, eq_term l [] s a c.
  Proof.
    intros [s1 H1] [s2 H2]. exists s1.
    eapply eq_term_trans; [ exact H1 | ].
    eapply eq_term_conv; [ exact H2 | ].
    apply eq_sort_sym.
    eapply term_sorts_eq;
      [ exact wfl | constructor
      | eapply eq_term_wf_r; [ exact wfl | exact H1 ]
      | eapply eq_term_wf_l; [ exact wfl | exact H2 ] ].
  Qed.

  Lemma eq_term_ex_sym (a b : term V) :
    (exists s, eq_term l [] s a b) -> exists s, eq_term l [] s b a.
  Proof. intros [s H]. exists s. apply eq_term_sym; exact H. Qed.

  Lemma denote_extract_eq (g : instance V V V_map V_map V_trie (option positive))
    (interp : V_map (term V + sort V)) (efuel : nat) (z : V) (ez efz : term V) :
    egraph_ok g -> sound interp g ->
    option_relation (domain_eq V lang_model) (map.get interp z) (Some (inl ez)) ->
    extract_weighted g efuel z = Result.Success efz ->
    exists s, eq_term l [] s ez efz.
  Proof.
    intros Hokg Hsndg Hrz Hexz.
    destruct (map.get interp z) as [dz|] eqn:Hiz; [ | unfold option_relation in Hrz; discriminate Hrz ].
    unfold option_relation in Hrz.
    destruct (find_root_denote g interp z dz Hokg Hsndg Hiz) as (dz' & Hfz & Hdeq).
    change (domain_eq V lang_model) with (lang_model_eq V l) in Hrz, Hdeq.
    inversion Hrz as [ edz ezr srz Htermr Hr1 Hr2 | ]; subst.
    inversion Hdeq as [ ex edzd sdq Htermd Hd1 Hd2 | ]; subst.
    destruct (Theorems.extract_weighted_sound V V_map V_map_ok V_trie V_trie_ok sort_of l wfl g interp Hsndg efuel z efz ex Hfz Hexz) as [te Hee].
    apply (eq_term_ex_trans ez ex efz).
    - apply (eq_term_ex_trans ez edz ex).
      + apply eq_term_ex_sym. exists srz. exact Htermr.
      + apply eq_term_ex_sym. exists sdq. exact Htermd.
    - apply eq_term_ex_sym. exists te. exact Hee.
  Qed.

  Lemma egraph_reducing_cong_sound
    (schedule : list (nat * rule_set V V V_map V_map))
    (rfuel sat_fuel efuel : nat) :
    Theorems.schedule_sound_real V V_map V_map_plus V_trie succ sort_of lt spaced_list_intersect l schedule ->
    forall red_fuel inj goals,
      (forall a b, In (a,b) goals -> (exists ta, wf_term l [] a ta) /\ (exists tb, wf_term l [] b tb)) ->
      egraph_reducing_cong V_map_plus V_trie succ sort_of spaced_list_intersect l schedule rfuel sat_fuel efuel red_fuel inj goals = Result.Success tt ->
      forall a b, In (a,b) goals -> exists s, eq_term l [] s a b.
  Proof.
    intros Hsched red_fuel.
    induction red_fuel as [|rf IHrf]; intros inj goals Hwfgoals Hsucc a b Hin.
    - cbn [egraph_reducing_cong] in Hsucc. discriminate.
    - cbn [egraph_reducing_cong] in Hsucc.
      assert (Hgoals' : forall e1 e2, In (e1,e2) (flat_map (cong_subgoals l inj) goals) -> exists s, eq_term l [] s e1 e2).
      + intros e1 e2 Hin'.
        pose proof (list_Miter_all_success _ _ Hsucc (e1,e2) Hin') as Hproc.
        apply in_flat_map in Hin'. destruct Hin' as [ [a0 b0] [Hin0 Hinsub] ].
        destruct (Hwfgoals a0 b0 Hin0) as [ [ta0 Hwfa0] [tb0 Hwfb0] ].
        pose proof (Theorems.cong_subgoals_preserves_wf V l wfl inj a0 b0 ta0 tb0 Hwfa0 Hwfb0) as Hwfsub.
        pose proof (in_all _ _ _ Hwfsub Hinsub) as Hwfp.
        cbn [fst snd] in Hwfp. destruct Hwfp as [ [se1 Hwfe1] [se2 Hwfe2] ].
        cbn beta iota in Hproc.
        pose proof (Theorems.egraph_reducing_equal_step_sound_strong V V_map V_map_plus V_map_ok V_map_plus_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans spaced_list_intersect l wfl sort_of_fresh schedule rfuel sat_fuel e1 e2 se1 se2 Hwfe1 Hwfe2 Hsched) as Hstrong.
        revert Hproc Hstrong.
        destruct (egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect l schedule rfuel sat_fuel e1 e2) as [ [ [res x] y] g].
        intros Hproc [i [Hokg [Hsndg [Hr1 Hr2] ] ] ].
        destruct res; [ | discriminate Hproc ].
        assert (Hisx : Is_Some (map.get i x)) by (unfold option_relation in Hr1; destruct (map.get i x); [ exact I | discriminate Hr1 ]).
        assert (Hisy : Is_Some (map.get i y)) by (unfold option_relation in Hr2; destruct (map.get i y); [ exact I | discriminate Hr2 ]).
        assert (Hkx : Sep.has_key x (parent (equiv g))) by (exact (interpretation_exact _ _ _ _ _ _ _ _ _ Hsndg x Hisx)).
        assert (Hky : Sep.has_key y (parent (equiv g))) by (exact (interpretation_exact _ _ _ _ _ _ _ _ _ Hsndg y Hisy)).
        destruct (are_unified x y g) as [unified pf] eqn:Hau.
        destruct unified.
        * pose proof (are_unified_eq_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie (option positive) lang_model x y g i Hokg Hsndg Hkx Hky ltac:(rewrite Hau; reflexivity)) as Hes.
          eapply (Theorems.eq_sound_to_eq_term V V_map sort_of l sort_of_fresh wfl i x y e1 e2 Hes); [ exact Hr1 | exact Hr2 ].
        * destruct (extract_weighted g efuel x) as [e1'|err1] eqn:Hex; cbn [Mbind Mret result_monad] in Hproc; [ | discriminate ].
          destruct (extract_weighted g efuel y) as [e2'|err2] eqn:Hey; cbn [Mbind Mret result_monad] in Hproc; [ | discriminate ].
          pose proof (denote_extract_eq g i efuel x e1 e1' Hokg Hsndg Hr1 Hex) as He1.
          pose proof (denote_extract_eq g i efuel y e2 e2' Hokg Hsndg Hr2 Hey) as He2.
          assert (Hwfrec : forall aa bb, In (aa,bb) [(e1',e2')] -> (exists ta, wf_term l [] aa ta) /\ (exists tb, wf_term l [] bb tb))
            by (intros aa bb Hinp; destruct Hinp as [Heqp | Hf]; [ | inversion Hf ];
                injection Heqp as Haa Hbb; subst; split;
                [ destruct He1 as [s1 H1]; exists s1; exact (eq_term_wf_r wfl ltac:(constructor) H1)
                | destruct He2 as [s2 H2]; exists s2; exact (eq_term_wf_r wfl ltac:(constructor) H2) ]).
          pose proof (IHrf inj [(e1',e2')] Hwfrec Hproc e1' e2' (or_introl eq_refl)) as He12.
          apply (eq_term_ex_trans e1 e1' e2); [ exact He1 | ].
          apply (eq_term_ex_trans e1' e2' e2); [ exact He12 | ].
          apply eq_term_ex_sym. exact He2.
      + destruct (Hwfgoals a b Hin) as [ [ta Hwfa] [tb Hwfb] ].
        apply (Theorems.cong_subgoals_sound_ex V l wfl inj a b ta tb Hwfa Hwfb).
        apply all_via_in_local.
        intros p Hp. destruct p as [e1 e2].
        apply (Hgoals' e1 e2).
        apply in_flat_map. exists (a,b). split; [ exact Hin | exact Hp ].
  Qed.

  Lemma egraph_reducing_equal_sound_generic
    (schedule : list (nat * rule_set V V V_map V_map))
    (rfuel sat_fuel efuel red_fuel : nat) inj (e1 e2 : term V) (t : sort V) :
    wf_term l [] e1 t -> wf_term l [] e2 t ->
    Theorems.schedule_sound_real V V_map V_map_plus V_trie succ sort_of lt spaced_list_intersect l schedule ->
    egraph_reducing_cong V_map_plus V_trie succ sort_of spaced_list_intersect l schedule rfuel sat_fuel efuel red_fuel inj [(e1,e2)] = Result.Success tt ->
    eq_term l [] t e1 e2.
  Proof.
    intros Hwf1 Hwf2 Hsched Hsucc.
    assert (Hwfg : forall a b, In (a,b) [(e1,e2)] -> (exists ta, wf_term l [] a ta) /\ (exists tb, wf_term l [] b tb))
      by (intros aa bb Hinp; destruct Hinp as [Heqp | Hf]; [ | inversion Hf ];
          injection Heqp as Ha Hb; subst; split; [ exists t; exact Hwf1 | exists t; exact Hwf2 ]).
    destruct (egraph_reducing_cong_sound schedule rfuel sat_fuel efuel Hsched red_fuel inj [(e1,e2)] Hwfg Hsucc e1 e2 (or_introl eq_refl)) as [s Heq].
    eapply eq_term_conv; [ exact Heq | ].
    eapply (term_sorts_eq (e := e1)); [ exact wfl | constructor | exact (eq_term_wf_l wfl ltac:(constructor) Heq) | exact Hwf1 ].
  Qed.
  (* CONGMAIN-END-MARKER *)
End CongMain.
