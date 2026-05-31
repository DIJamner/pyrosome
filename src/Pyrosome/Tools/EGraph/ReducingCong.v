From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsAreUnified.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
From Pyrosome.Theory Require WfCutElim.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph Require Import Theorems.

#[local] Hint Resolve Properties.map.extends_refl : utils.
#[local] Hint Rewrite combine_map_fst_snd : utils.

(* ============================================================== *)
(* Soundness of one [egraph_reducing_equal_step] (Phase 4).        *)
(* ============================================================== *)
Section ReducingStep.
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
  Context (l : lang V) (wfl : wf_lang l) (sort_of_fresh : fresh sort_of l).

    Local Notation lang_model := (lang_model V sort_of l).
    Local Notation sound :=
      (egraph_sound_for_interpretation V V V_map V_map V_trie (option positive) lang_model).
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie (option positive)).

    (* ============================================================== *)
    (* Extraction soundness (Phase 5 keystone).                       *)
    (* [select_optimal_nodes] picks, per e-class, an optimal db node; *)
    (* a node it records for class [out] really is a db row for that  *)
    (* class -- i.e. [atom_in_db].  Pure nested-[map.fold] reasoning.  *)
    (* ============================================================== *)
    Lemma select_optimal_nodes_correct (X : Type) (le : X -> X -> bool)
      (analyses : V_map X) (db : Utils.EGraph.Defs.db_map V V V_map V_trie X)
      (out f : V) (args : list V) :
      map.get (@Pyrosome.Tools.EGraph.Defs.select_optimal_nodes V V_map V_trie X le analyses db) out = Some (f, args) ->
      exists tbl r,
        map.get db f = Some tbl
        /\ map.get tbl args = Some r
        /\ Utils.EGraph.Defs.entry_value V X r = out.
    Proof.
      unfold Pyrosome.Tools.EGraph.Defs.select_optimal_nodes.
      set (process_row := fun f0 (acc : V_map (V * list V)) args0 (row : Utils.EGraph.Defs.db_entry V X) =>
        let out0 := Utils.EGraph.Defs.entry_value _ _ row in
        let ra := Utils.EGraph.Defs.entry_analysis _ _ row in
        match map.get analyses out0 with
        | None => acc
        | Some a => if le ra a then map.put acc out0 (f0, args0) else acc
        end).
      set (process_table := fun (acc : V_map (V * list V)) f0 (tbl : V_trie (Utils.EGraph.Defs.db_entry V X)) =>
        map.fold (process_row f0) acc tbl).
      eapply (@map.fold_spec V (V_trie (Utils.EGraph.Defs.db_entry V X)) (V_map _) (V_map_ok _)
        (V_map (V * list V))
        (fun (db_partial : V_map (V_trie (Utils.EGraph.Defs.db_entry V X))) (acc : V_map (V * list V)) =>
                forall out' f' args',
                  map.get acc out' = Some (f', args') ->
                  exists tbl r,
                    map.get db_partial f' = Some tbl
                    /\ map.get tbl args' = Some r
                    /\ Utils.EGraph.Defs.entry_value _ _ r = out')
        process_table map.empty).
      - intros out' f' args' Hget.
        rewrite map.get_empty in Hget. discriminate.
      - intros f0 tbl0 db_partial acc Hnotf0 IH_outer.
        unfold process_table.
        eapply (@map.fold_spec (list V) (Utils.EGraph.Defs.db_entry V X) (V_trie _) (V_trie_ok _)
          (V_map (V * list V))
          (fun (tbl_partial : V_trie (Utils.EGraph.Defs.db_entry V X)) (acc' : V_map (V * list V)) =>
                  forall out' f' args',
                    map.get acc' out' = Some (f', args') ->
                    exists tbl r,
                      map.get (map.put db_partial f0 tbl_partial) f' = Some tbl
                      /\ map.get tbl args' = Some r
                      /\ Utils.EGraph.Defs.entry_value _ _ r = out')
          (process_row f0) acc).
        + intros out' f' args' Hget.
          destruct (IH_outer out' f' args' Hget) as (tbl & r & H1 & H2 & H3).
          exists tbl, r.
          refine (conj _ (conj H2 H3)).
          rewrite map.get_put_diff; [ exact H1 | intro Heq; subst; rewrite Hnotf0 in H1; discriminate ].
        + intros args0 row0 tbl_partial acc' Hnot_args0 IH_inner.
          assert (Htransport : forall (o2 f2 : V) (a2 : list V) tbl_src rr,
            map.get (map.put db_partial f0 tbl_partial) f2 = Some tbl_src ->
            map.get tbl_src a2 = Some rr ->
            Utils.EGraph.Defs.entry_value V X rr = o2 ->
            exists tbl r0,
              map.get (map.put db_partial f0 (map.put tbl_partial args0 row0)) f2 = Some tbl
              /\ map.get tbl a2 = Some r0 /\ Utils.EGraph.Defs.entry_value V X r0 = o2).
          * intros o2 f2 a2 tbl_src rr Hf Hargs Hev.
            destruct (eqb f2 f0) eqn:Hb; pose proof (eqb_spec f2 f0) as Hsp; rewrite Hb in Hsp.
            -- subst f2. rewrite map.get_put_same in Hf. injection Hf; intro Hts; subst tbl_src.
               exists (map.put tbl_partial args0 row0), rr.
               rewrite map.get_put_same.
               refine (conj eq_refl (conj _ Hev)).
               rewrite map.get_put_diff; [ exact Hargs | intro He; subst a2; rewrite Hnot_args0 in Hargs; discriminate ].
            -- exists tbl_src, rr.
               rewrite map.get_put_diff in Hf; [ | exact Hsp ].
               rewrite map.get_put_diff; [ refine (conj Hf (conj Hargs Hev)) | exact Hsp ].
          * unfold process_row.
            destruct (map.get analyses (Utils.EGraph.Defs.entry_value V X row0)) as [a|] eqn:Hanalysis.
            -- destruct (le (Utils.EGraph.Defs.entry_analysis V X row0) a) eqn:Hle.
               ++ intros out' f' args' Hget'.
                  destruct (eqb out' (Utils.EGraph.Defs.entry_value V X row0)) eqn:Hbo;
                    pose proof (eqb_spec out' (Utils.EGraph.Defs.entry_value V X row0)) as Hso; rewrite Hbo in Hso.
                  ** subst out'. rewrite map.get_put_same in Hget'.
                     injection Hget'; intros Ha Hf2; subst f' args'.
                     exists (map.put tbl_partial args0 row0), row0.
                     rewrite map.get_put_same.
                     refine (conj eq_refl (conj _ eq_refl)).
                     apply map.get_put_same.
                  ** rewrite map.get_put_diff in Hget'; [ | exact Hso ].
                     destruct (IH_inner out' f' args' Hget') as (tbl_src & rr & Hf & Hargs & Hev).
                     exact (Htransport out' f' args' tbl_src rr Hf Hargs Hev).
               ++ intros out' f' args' Hget'.
                  destruct (IH_inner out' f' args' Hget') as (tbl_src & rr & Hf & Hargs & Hev).
                  exact (Htransport out' f' args' tbl_src rr Hf Hargs Hev).
            -- intros out' f' args' Hget'.
               destruct (IH_inner out' f' args' Hget') as (tbl_src & rr & Hf & Hargs & Hev).
               exact (Htransport out' f' args' tbl_src rr Hf Hargs Hev).
    Qed.

    Lemma select_optimal_nodes_sound (X : Type) (le : X -> X -> bool)
      (analyses : V_map X) (db : Utils.EGraph.Defs.db_map V V V_map V_trie X)
      (out f : V) (args : list V) :
      map.get (@Pyrosome.Tools.EGraph.Defs.select_optimal_nodes V V_map V_trie X le analyses db) out = Some (f, args) ->
      atom_in_db V V V_map V_trie X (Build_atom f args out) db.
    Proof.
      intro H. apply select_optimal_nodes_correct in H.
      destruct H as (tbl & r & Htbl & Hr & Hev).
      unfold atom_in_db, Is_Some_satisfying; cbn.
      rewrite Htbl, Hr. exact Hev.
    Qed.

    (* ============================================================== *)
    (* Extraction soundness, part 2 (Phase 5 keystone).               *)
    (* [extract_weighted] reads a term out of an e-class that is      *)
    (* [eq_term]-equal to whatever that class denotes under [interp]. *)
    (* Fuel + memoization induction over the analysis extraction.     *)
    (* ============================================================== *)

    (* Clean reduction lemmas for the [stateT (V_map term) result] monad. *)
    Lemma stateT_result_bind {A B} (f : A -> stateT (V_map (term V)) Result.result B)
      (m : stateT (V_map (term V)) Result.result A) (s : V_map (term V)) :
      Mbind f m s = match m s with
                    | Success p => f (fst p) (snd p)
                    | Failure e => Failure e
                    end.
    Proof. cbn. unfold Basics.compose. destruct (m s) as [ [a s'] | e]; reflexivity. Qed.

    Lemma stateT_result_ret {A} (a : A) (s : V_map (term V)) :
      (Mret a : stateT (V_map (term V)) Result.result A) s = Success (a, s).
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
          pose proof (select_optimal_nodes_sound (option positive) oP_le (analyses g) (db g) x x_f x_args Hopt) as Hatomdb.
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

    (* The real [schedule_sound] content (Phase 3<->6 interface): every
       compiled rule_set in [schedule] satisfies the per-rule_set
       saturation hypotheses under [lang_model l].  This is exactly the
       [Hsched] hypothesis that [scheduled_saturate_until_sound] needs;
       it is discharged downstream from [build_rule_set] +
       [optimize_sequent_forward] + [pt_spaced_intersect_correct]. *)
    Definition schedule_sound_real
      (schedule : list (nat * rule_set V V V_map V_map)) : Prop :=
      forall n rs, In (n, rs) schedule ->
        @rs_saturation_hyps V V_Eqb V_default V_map V_map_plus V_trie succ lt
          (option positive) (depth V) spaced_list_intersect lang_model rs.

    (* Stronger form, exposing the resulting egraph's soundness and the input
       denotations regardless of [res]/[are_unified].  Chains: [empty] sound
       -> [add_open_term] x2 (places [a],[b]) -> [get_analysis] x2 (weight
       reads, preserve) -> [rebuild] (preserve) -> [scheduled_saturate_until]
       (extends interp, preserve; predicate HP via
       [get_analysis_preserves]/[are_unified_preserves]).  Used by
       [egraph_reducing_cong_sound]'s extract-and-recurse branch, which reads
       terms back from [g]. *)
    Lemma egraph_reducing_equal_step_sound_strong
      (schedule : list (nat * rule_set V V V_map V_map))
      (rfuel sat_fuel : nat)
      (a b : term V) (ta tb : sort V) :
      wf_term l [] a ta -> wf_term l [] b tb ->
      schedule_sound_real schedule ->
      let '(res, x1, x2, g) :=
        egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect
          l schedule rfuel sat_fuel a b in
      exists i,
        egraph_ok g /\ sound i g
        /\ option_relation (domain_eq V lang_model) (map.get i x1) (Some (inl a))
        /\ option_relation (domain_eq V lang_model) (map.get i x2) (Some (inl b)).
    Proof.
      intros Ha Hb Hsched.
      unfold egraph_reducing_equal_step.
      cbn [Mbind Mret StateMonad.state_monad fst snd].
      destruct (add_open_term succ sort_of l true false [] a (empty_egraph default (option positive))) as [x1 ea] eqn:Haa.
      destruct (add_open_term succ sort_of l true false [] b ea) as [x2 eb] eqn:Hab.
      destruct (get_analysis V V V_map V_map V_trie (option positive) x1 eb) as [w1 e1] eqn:Hga1.
      destruct (get_analysis V V V_map V_map V_trie (option positive) x2 e1) as [w2 e2] eqn:Hga2.
      destruct (rebuild rfuel e2) as [u e3] eqn:Hrb.
      match goal with
      | |- context [scheduled_saturate_until ?vmp ?sc ?sli ?rf ?sch ?p ?sf ?e] =>
          destruct (scheduled_saturate_until vmp sc sli rf sch p sf e) as [res g] eqn:Hsat
      end.
      cbn [fst snd].
      pose proof (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok V_map V_map_ok V_trie (option positive) lang_model) as Hempty.
      destruct Hempty as [Hok0 Hsnd0].
      assert (Hsub : forall (e:term V), e [/ with_names_from (@nil (V*sort V)) (@nil (term V)) /] = e) by (intro; cbn [with_names_from]; apply term_subst_nil).
      pose proof (@add_open_term_sound V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans (option positive) (depth V) l wfl sort_of_fresh true [] [] [] a ta) as Hpa.
      specialize (Hpa ltac:(constructor) Ha ltac:(constructor) (eq_refl) map.empty); unfold vc in Hpa.
      assert (Haa' : add_open_term succ sort_of l true false [] a (empty_egraph V_default (option positive)) = (x1, ea)) by (exact Haa).
      specialize (Hpa (empty_egraph V_default (option positive))).
      rewrite Haa' in Hpa.
      unfold open_term_post in Hpa.
      specialize (Hpa Hok0 Hsnd0 ltac:(cbn; trivial)).
      destruct Hpa as [i1 [ Hext1 Hrel1 ] ].
      cbn [fst snd] in Hext1, Hrel1.
      rewrite Hsub in Hrel1.
      destruct Hext1 as [ Hok_ea [ Hextmap1 [ Hsnd_ea Hkey1 ] ] ].
      pose proof (@add_open_term_sound V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans (option positive) (depth V) l wfl sort_of_fresh true [] [] [] b tb) as Hpb.
      specialize (Hpb ltac:(constructor) Hb ltac:(constructor) (eq_refl) i1); unfold vc in Hpb.
      specialize (Hpb ea).
      rewrite Hab in Hpb.
      unfold open_term_post in Hpb.
      specialize (Hpb Hok_ea Hsnd_ea ltac:(cbn; trivial)).
      destruct Hpb as [i2 [ Hext2 Hrel2 ] ].
      cbn [fst snd] in Hext2, Hrel2.
      rewrite Hsub in Hrel2.
      destruct Hext2 as [ Hok_eb [ Hextmap2 [ Hsnd_eb Hkey2 ] ] ].
      assert (Hlift : forall (ii ii' : V_map (domain V lang_model)) (xx:V) dd,
         map.extends ii' ii -> option_relation (domain_eq V lang_model) (map.get ii xx) (Some dd) ->
         option_relation (domain_eq V lang_model) (map.get ii' xx) (Some dd)).
      { intros ii ii' xx dd Hext Hor.
        unfold option_relation in *.
        destruct (map.get ii xx) as [v|] eqn:Hgv.
        - rewrite (Hext _ _ Hgv); exact Hor.
        - discriminate Hor. }
      pose proof (@lang_model_ok V V_Eqb V_Eqb_ok sort_of l sort_of_fresh wfl) as Hmok.
      pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x1 eb i2 Hok_eb Hsnd_eb) as Hg1.
      rewrite Hga1 in Hg1; cbn [snd] in Hg1; destruct Hg1 as [Hok_e1 Hsnd_e1].
      pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x2 e1 i2 Hok_e1 Hsnd_e1) as Hg2.
      rewrite Hga2 in Hg2; cbn [snd] in Hg2; destruct Hg2 as [Hok_e2 Hsnd_e2].
      pose proof (@rebuild_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok (option positive) (depth V) lang_model Hmok (fun _ => True) rfuel e2 Hok_e2) as Hrbs.
      rewrite Hrb in Hrbs; cbn [snd] in Hrbs; destruct Hrbs as [Hok_e3 Hiff3].
      assert (Hsnd_e3 : sound i2 e3) by (apply (Hiff3 i2); exact Hsnd_e2).
      match type of Hsat with
      | scheduled_saturate_until _ _ _ _ _ ?p _ _ = _ => set (pred := p) in *
      end.
      assert (HP : forall ee ii, egraph_ok ee -> sound ii ee -> egraph_ok (snd (pred ee)) /\ sound ii (snd (pred ee)))
        by (intros ee ii Hoke Hsnde; subst pred; unfold weight_less_than;
            cbn [Mbind Mret StateMonad.state_monad];
            pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x1 ee ii Hoke Hsnde) as Hp1;
            destruct (get_analysis V V V_map V_map V_trie (option positive) x1 ee) as [a1 e1'] eqn:He1';
            cbn [snd] in Hp1; destruct Hp1 as [ Hok1 Hsnd1 ]; cbn [fst snd];
            destruct (oP_lt a1 w1);
            [ cbn [snd]; split; assumption | ];
            cbn [fst snd];
            pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x2 e1' ii Hok1 Hsnd1) as Hp2;
            destruct (get_analysis V V V_map V_map V_trie (option positive) x2 e1') as [a2 e2'] eqn:He2';
            cbn [snd] in Hp2; destruct Hp2 as [ Hok2 Hsnd2 ];
            destruct (oP_lt a2 w2);
            [ cbn [snd]; split; assumption | ];
            pose proof (@are_unified_preserves_ok_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie (option positive) lang_model x1 x2 e2' ii Hok2 Hsnd2) as Hau;
            destruct Hau as [ Hoku Hsndu ]; split; assumption).
      pose proof (@scheduled_saturate_until_sound V V_Eqb V_Eqb_ok V_default V_map V_map_plus V_map_ok V_trie V_trie_ok succ lt lt_asymmetric lt_succ lt_trans V_map_plus_ok (option positive) (depth V) spaced_list_intersect lang_model Hmok rfuel pred HP schedule Hsched sat_fuel i2 e3 Hok_e3 Hsnd_e3) as Hss.
      rewrite Hsat in Hss.
      destruct Hss as [ Hok_g [ i3 [ Hext3 Hsnd_g ] ] ].
      pose proof (Hlift i2 i3 x1 (inl a) Hext3 (Hlift i1 i2 x1 (inl a) Hextmap2 Hrel1)) as Hr1g.
      pose proof (Hlift i2 i3 x2 (inl b) Hext3 Hrel2) as Hr2g.
      exists i3.
      split; [ exact Hok_g | ].
      split; [ exact Hsnd_g | ].
      split; [ exact Hr1g | exact Hr2g ].
    Qed.

    (* The [res = true] / [are_unified] corollary used directly to decide
       equality: from the strong form's [g] soundness + denotations,
       [are_unified_eq_sound] -> [eq_sound_to_eq_term] -> conversion to the
       wanted sort ([term_sorts_eq]/[eq_term_conv]). *)
    Lemma egraph_reducing_equal_step_sound
      (schedule : list (nat * rule_set V V V_map V_map))
      (rfuel sat_fuel : nat)
      (a b : term V) (t : sort V) :
      wf_term l [] a t -> wf_term l [] b t ->
      schedule_sound_real schedule ->
      let '(res, x1, x2, g) :=
        egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect
          l schedule rfuel sat_fuel a b in
      res = true -> fst (Defs.are_unified x1 x2 g) = true -> eq_term l [] t a b.
    Proof.
      intros Ha Hb Hsched.
      pose proof (egraph_reducing_equal_step_sound_strong schedule rfuel sat_fuel a b t t Ha Hb Hsched) as Hstrong.
      revert Hstrong.
      destruct (egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect
                  l schedule rfuel sat_fuel a b) as [ [ [ res x1 ] x2 ] g ].
      intros [ i3 [ Hok_g [ Hsnd_g [ Hr1g Hr2g ] ] ] ] Hres Hunified.
      assert (Hisx1 : Is_Some (map.get i3 x1)) by (unfold option_relation in Hr1g; destruct (map.get i3 x1); [exact I | discriminate Hr1g]).
      assert (Hisx2 : Is_Some (map.get i3 x2)) by (unfold option_relation in Hr2g; destruct (map.get i3 x2); [exact I | discriminate Hr2g]).
      pose proof Hsnd_g as Hsnd_gc.
      destruct Hsnd_gc as [ _ Hexact _ _ ].
      assert (Hk1 : Sep.has_key x1 (UnionFind.parent (equiv g))) by (apply Hexact; exact Hisx1).
      assert (Hk2 : Sep.has_key x2 (UnionFind.parent (equiv g))) by (apply Hexact; exact Hisx2).
      pose proof (@are_unified_eq_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie (option positive) lang_model x1 x2 g i3 Hok_g Hsnd_g Hk1 Hk2 Hunified) as Hes.
      pose proof (@eq_sound_to_eq_term V V_Eqb V_Eqb_ok V_map sort_of l sort_of_fresh wfl i3 x1 x2 a b Hes Hr1g Hr2g) as Het.
      destruct Het as [ t' Heq ].
      eapply eq_term_conv; [ exact Heq | ].
      eapply term_sorts_eq with (e := a); eauto using eq_term_wf_l with lang_core.
    Qed.

End ReducingStep.

(* ============================================================== *)
(* Soundness of [cong_subgoals] (Phase 5, syntactic).             *)
(* If every pair produced by [cong_subgoals]/[select_inj_args] is  *)
(* [eq_term] (at some sort), the original goal is [eq_term] at its *)
(* sort -- by reconstructing [eq_args] (dependent arg-sort         *)
(* reconciliation, as in [all2_model_eq_eq_args]) + congruence.    *)
(* ============================================================== *)
Section CongSubgoals.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}.
  Context (l : lang V) (wfl : wf_lang l).

  Notation term := (@term V).
  Notation sort := (@sort V).
  Notation ctx := (@ctx V).

  Notation eq_args l := (eq_args (Model:= core_model l)).
  Notation wf_args l := (wf_args (Model:= core_model l)).
  Notation wf_ctx l := (wf_ctx (Model:= core_model l)).

  Lemma select_inj_args_sound (c' : ctx) inj_args (s1 s2 : list term) subgoals :
    @select_inj_args V V_Eqb c' inj_args s1 s2 = Some subgoals ->
    wf_ctx l c' ->
    wf_args l [] s1 c' ->
    wf_args l [] s2 c' ->
    all (fun p => let '(a,b) := p in exists s, eq_term l [] s a b) subgoals ->
    eq_args l [] c' s1 s2.
  Proof.
    intros Hsel Hwfc Hwfs1 Hwfs2 Hall.
    revert inj_args s2 subgoals Hsel Hwfs2 Hall.
    induction Hwfs1; intros inj_args s2 subgoals Hsel Hwfs2 Hall.
    - (* nil case: c' = [], s1 = [] *)
      destruct inj_args as [|x inj_t].
      + simpl in Hsel. inversion Hsel; subst. inversion Hwfs2; subst. constructor.
      + simpl in Hsel. discriminate.
    - (* cons case: c' = (name, t) :: c'_tail, s1 = e :: s *)
      rename c' into c'_tail.
      rename name into x'.
      rename t into ty.
      rename e into e1.
      rename s into s1_t.
      destruct s2 as [|e2 s2_t]. { inversion Hwfs2. }
      inversion Hwfs2 as [|xn' e2' t' Hwft2 Hwfs2_t xneq]; subst.
      rename H0 into Hwfs2_tail.
      destruct inj_args as [|x inj_t].
      { simpl in Hsel.
        case_match; try discriminate.
        inversion Hsel; subst.
        basic_utils_crush.
        assert (Hwfc_t : wf_ctx l c'_tail) by (inversion Hwfc; eauto).
        constructor.
        { eapply eq_args_refl; eauto. eapply core_model_ok; eauto. }
        { eapply eq_term_refl; eauto. }
      }
      simpl in Hsel.
      destruct (eqb x x') eqn:Hxx'.
      { destruct (select_inj_args c'_tail inj_t s1_t s2_t) as [rest|] eqn:Hrest.
        { simpl in Hsel. inversion Hsel; subst.
          simpl in Hall. destruct Hall as [ [se Hhead] Htail].
          assert (Hwfc_t : wf_ctx l c'_tail) by (inversion Hwfc; eauto).
          pose proof (IHHwfs1 Hwfc_t inj_t s2_t rest Hrest Hwfs2_tail Htail) as IH.
          constructor.
          { exact IH. }
          { eapply eq_term_conv; [ exact Hhead |].
            eapply term_sorts_eq; eauto using wf_ctx_nil.
            eapply eq_term_wf_r; eauto using wf_ctx_nil. }
        }
        { simpl in Hsel. discriminate. }
      }
      destruct (eqb e1 e2) eqn:He12.
      { basic_utils_crush.
        assert (Hwfc_t : wf_ctx l c'_tail) by (inversion Hwfc; eauto).
        pose proof (IHHwfs1 Hwfc_t (x :: inj_t) s2_t subgoals Hsel Hwfs2_tail Hall) as IH.
        constructor.
        { exact IH. }
        { eapply eq_term_refl; eauto. }
      }
      { discriminate. }
  Qed.

  Lemma cong_subgoals_sound inj_list (e1 e2 : term) (t : sort) :
    wf_term l [] e1 t -> wf_term l [] e2 t ->
    all (fun p => let '(a,b) := p in exists s, eq_term l [] s a b)
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)) ->
    eq_term l [] t e1 e2.
  Proof.
    intros Hwf1 Hwf2 Hall.
    unfold cong_subgoals in Hall.
    destruct e1 as [x1 | n1 s1], e2 as [x2 | n2 s2]; simpl in Hall.
    1-3: (destruct Hall as [ [se Heq] _];
          eapply eq_term_conv; [ exact Heq |];
          eapply term_sorts_eq; eauto using wf_ctx_nil;
          eapply eq_term_wf_r; eauto using wf_ctx_nil).
    (* con/con case *)
    destruct (eqb n1 n2) eqn:Hn12;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    pose proof (@eqb_spec _ _ V_Eqb_ok n1 n2) as Hn12eq.
    rewrite Hn12 in Hn12eq. subst n2.
    destruct (named_list_lookup_err inj_list n1) as [inj_args|] eqn:Hinj;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    destruct (named_list_lookup_err l n1) as [r|] eqn:Hl1;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    destruct r as [ | c args t_rule | |];
    try (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil).
    (* term_rule case *)
    destruct (select_inj_args c inj_args s1 s2) as [subs|] eqn:Hselect;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    assert (Hin1 : In (n1, term_rule c args t_rule) l) by
      (apply named_list_lookup_err_in; auto).
    apply WfCutElim.invert_wf_term_con in Hwf1.
    destruct Hwf1 as (c1 & args1 & t1 & Hinwf1 & Hwfargs1 & Ht1or1).
    apply WfCutElim.invert_wf_term_con in Hwf2.
    destruct Hwf2 as (c2 & args2 & t2 & Hinwf2 & Hwfargs2 & Ht2or2).
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf1 Hin1) as Heq1.
    inversion Heq1; subst c1 args1 t1; clear Heq1.
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf2 Hin1) as Heq2.
    inversion Heq2; subst c2 args2 t2; clear Heq2.
    assert (Hwfc : wf_ctx l c) by (eauto with lang_core).
    eapply select_inj_args_sound in Hselect; eauto.
    eapply eq_term_conv.
    { eapply term_con_congruence; eauto. }
    { destruct Ht2or2 as [Ht2 | Ht2].
      + exact Ht2.
      + subst. eapply eq_sort_refl.
        eapply wf_sort_subst_monotonicity; eauto.
        * eapply term_rule_in_sort_wf; eauto.
        * eapply wf_subst_from_wf_args; eauto. }
  Qed.

  (* Existential-sort variant: the two sides may be wf at *different* sorts
     (the dependent argument sorts that arise in the cong recursion).  We
     conclude [eq_term] at *some* sort; the final conversion to a specific
     target sort is done by the caller ([egraph_reducing_equal_sound]). *)
  Lemma cong_subgoals_sound_ex inj_list (e1 e2 : term) (ta tb : sort) :
    wf_term l [] e1 ta -> wf_term l [] e2 tb ->
    all (fun p => let '(a,b) := p in exists s, eq_term l [] s a b)
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)) ->
    exists s, eq_term l [] s e1 e2.
  Proof.
    intros Hwf1 Hwf2 Hall.
    unfold cong_subgoals in Hall.
    destruct e1 as [x1 | n1 s1], e2 as [x2 | n2 s2]; simpl in Hall.
    1-3: (destruct Hall as [ [se Heq] _]; exists se; exact Heq).
    (* con/con case *)
    destruct (eqb n1 n2) eqn:Hn12;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    pose proof (@eqb_spec _ _ V_Eqb_ok n1 n2) as Hn12eq.
    rewrite Hn12 in Hn12eq. subst n2.
    destruct (named_list_lookup_err inj_list n1) as [inj_args|] eqn:Hinj;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    destruct (named_list_lookup_err l n1) as [r|] eqn:Hl1;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    destruct r as [ | c args t_rule | |];
    try (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq).
    (* term_rule case *)
    destruct (select_inj_args c inj_args s1 s2) as [subs|] eqn:Hselect;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    assert (Hin1 : In (n1, term_rule c args t_rule) l) by
      (apply named_list_lookup_err_in; auto).
    apply WfCutElim.invert_wf_term_con in Hwf1.
    destruct Hwf1 as (c1 & args1 & t1 & Hinwf1 & Hwfargs1 & Ht1or1).
    apply WfCutElim.invert_wf_term_con in Hwf2.
    destruct Hwf2 as (c2 & args2 & t2 & Hinwf2 & Hwfargs2 & Ht2or2).
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf1 Hin1) as Heq1.
    inversion Heq1; subst c1 args1 t1; clear Heq1.
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf2 Hin1) as Heq2.
    inversion Heq2; subst c2 args2 t2; clear Heq2.
    assert (Hwfc : wf_ctx l c) by (eauto with lang_core).
    eapply select_inj_args_sound in Hselect; eauto.
    eexists. eapply term_con_congruence; [ exact Hin1 | right; reflexivity | exact wfl | exact Hselect ].
  Qed.

  (* Each pair produced by [select_inj_args] has both components well-formed
     (they are arguments of the well-formed input terms). *)
  Lemma select_inj_args_wf (c' : ctx) inj_args (s1 s2 : list term) subgoals :
    @select_inj_args V V_Eqb c' inj_args s1 s2 = Some subgoals ->
    wf_args l [] s1 c' ->
    wf_args l [] s2 c' ->
    all (fun p => (exists sa, wf_term l [] (fst p) sa)
                  /\ (exists sb, wf_term l [] (snd p) sb)) subgoals.
  Proof.
    intros Hsel Hwfs1 Hwfs2.
    revert inj_args s2 subgoals Hsel Hwfs2.
    induction Hwfs1 as [| s1tl ctl nm e1 tyhd Hwfe1 Hwftail IHwf]; intros inj_args s2 subgoals Hsel Hwfs2.
    - destruct inj_args as [|x inj_t]; simpl in Hsel; [ inversion Hsel; subst; cbn; exact I | discriminate ].
    - destruct s2 as [|e2 s2tl]; [ inversion Hwfs2 | ].
      inversion Hwfs2; subst.
      destruct inj_args as [|x inj_t].
      + simpl in Hsel. case_match; [ | discriminate ]. inversion Hsel; subst. cbn. exact I.
      + simpl in Hsel.
        destruct (eqb x nm) eqn:Hxx'.
        * destruct (select_inj_args ctl inj_t s1tl s2tl) as [rest|] eqn:Hrest; [ | discriminate ].
          simpl in Hsel. inversion Hsel; subst.
          cbn [all]. split.
          -- split; eexists; eassumption.
          -- exact (IHwf inj_t s2tl rest Hrest ltac:(eassumption)).
        * destruct (eqb e1 e2) eqn:He12; [ | discriminate ].
          exact (IHwf (x :: inj_t) s2tl subgoals Hsel ltac:(eassumption)).
  Qed.

  (* Every pair in [cong_subgoals] of a goal has well-formed components. *)
  Lemma cong_subgoals_preserves_wf inj_list (e1 e2 : term) (ta tb : sort) :
    wf_term l [] e1 ta -> wf_term l [] e2 tb ->
    all (fun p => (exists sa, wf_term l [] (fst p) sa)
                  /\ (exists sb, wf_term l [] (snd p) sb))
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)).
  Proof.
    intros Hwf1 Hwf2.
    unfold cong_subgoals.
    destruct e1 as [x1 | n1 s1], e2 as [x2 | n2 s2];
      try (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]).
    destruct (eqb n1 n2) eqn:Hn12;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    pose proof (@eqb_spec _ _ V_Eqb_ok n1 n2) as Hn12eq. rewrite Hn12 in Hn12eq. subst n2.
    destruct (named_list_lookup_err inj_list n1) as [inj_args|] eqn:Hinj;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    destruct (named_list_lookup_err l n1) as [r|] eqn:Hl1;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    destruct r as [ | c args t_rule | | ];
      try (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]).
    destruct (select_inj_args c inj_args s1 s2) as [subs|] eqn:Hselect;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    assert (Hin1 : In (n1, term_rule c args t_rule) l) by (apply named_list_lookup_err_in; auto).
    apply WfCutElim.invert_wf_term_con in Hwf1.
    destruct Hwf1 as (c1 & args1 & t1 & Hinwf1 & Hwfargs1 & _).
    apply WfCutElim.invert_wf_term_con in Hwf2.
    destruct Hwf2 as (c2 & args2 & t2 & Hinwf2 & Hwfargs2 & _).
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf1 Hin1) as Heq1.
    inversion Heq1; subst c1 args1 t1; clear Heq1.
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf2 Hin1) as Heq2.
    inversion Heq2; subst c2 args2 t2; clear Heq2.
    exact (select_inj_args_wf c inj_args s1 s2 subs Hselect Hwfargs1 Hwfargs2).
  Qed.

End CongSubgoals.

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
    eapply (term_sorts_eq (e := b));
      [ exact wfl | constructor
      | exact (eq_term_wf_r wfl ltac:(constructor) H1)
      | exact (eq_term_wf_l wfl ltac:(constructor) H2) ].
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
    destruct (extract_weighted_sound V V_map V_map_ok V_trie V_trie_ok sort_of l wfl g interp Hsndg efuel z efz ex Hfz Hexz) as [te Hee].
    apply (eq_term_ex_trans ez ex efz).
    - apply (eq_term_ex_trans ez edz ex).
      + apply eq_term_ex_sym. exists srz. exact Htermr.
      + apply eq_term_ex_sym. exists sdq. exact Htermd.
    - apply eq_term_ex_sym. exists te. exact Hee.
  Qed.

  Lemma egraph_reducing_cong_sound
    (schedule : list (nat * rule_set V V V_map V_map))
    (rfuel sat_fuel efuel : nat) :
    schedule_sound_real V V_map V_map_plus V_trie succ sort_of lt spaced_list_intersect l schedule ->
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
        pose proof (cong_subgoals_preserves_wf V l wfl inj a0 b0 ta0 tb0 Hwfa0 Hwfb0) as Hwfsub.
        pose proof (in_all _ _ _ Hwfsub Hinsub) as Hwfp.
        cbn [fst snd] in Hwfp. destruct Hwfp as [ [se1 Hwfe1] [se2 Hwfe2] ].
        cbn beta iota in Hproc.
        pose proof (egraph_reducing_equal_step_sound_strong V V_map V_map_plus V_map_ok V_map_plus_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans spaced_list_intersect l wfl sort_of_fresh schedule rfuel sat_fuel e1 e2 se1 se2 Hwfe1 Hwfe2 Hsched) as Hstrong.
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
          eapply (eq_sound_to_eq_term V V_map sort_of l sort_of_fresh wfl i x y e1 e2 Hes); [ exact Hr1 | exact Hr2 ].
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
        apply (cong_subgoals_sound_ex V l wfl inj a b ta tb Hwfa Hwfb).
        apply all_via_in_local.
        intros p Hp. destruct p as [e1 e2].
        apply (Hgoals' e1 e2).
        apply in_flat_map. exists (a,b). split; [ exact Hin | exact Hp ].
  Qed.

  Lemma egraph_reducing_equal_sound_generic
    (schedule : list (nat * rule_set V V V_map V_map))
    (rfuel sat_fuel efuel red_fuel : nat) inj (e1 e2 : term V) (t : sort V) :
    wf_term l [] e1 t -> wf_term l [] e2 t ->
    schedule_sound_real V V_map V_map_plus V_trie succ sort_of lt spaced_list_intersect l schedule ->
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
