(* union-semantics / exec_clause / allocate-existential soundness, split out
   of Semantics.v (Section WithMap).  The 5 externally-used lemmas (consumed by
   SemanticsExecConst and Theorems) keep their exact section-closed signatures;
   the 3 internal helpers live in a local Section. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

Section Slice.
  Context
    {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
    {lt : idx -> idx -> Prop} {idx_succ : idx -> idx} {idx_zero : WithDefault idx}
    {symbol : Type} {Eqb_symbol : Eqb symbol} {Eqb_symbol_ok : Eqb_ok Eqb_symbol}
    {symbol_map : forall A, map.map symbol A} {symbol_map_ok : forall A, map.ok (symbol_map A)}
    {idx_map : forall A, map.map idx A} {idx_map_ok : forall A, map.ok (idx_map A)}
    {idx_trie : forall A, map.map (list idx) A} {idx_trie_ok : forall A, map.ok (idx_trie A)}
    {analysis_result : Type} {H : analysis idx symbol analysis_result}
    {m : model symbol} {Hm : model_ok symbol m}.
  Existing Instance idx_zero.
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_ok := (egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_sound_for_interpretation := (egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m).
  Notation union_find := (union_find idx (idx_map idx) (idx_map nat)).
  Notation uf_rel_PER := (uf_rel_PER idx (idx_map idx) (idx_map nat)).

  Lemma list_Mmap_env_iU
    (env0 : idx_map idx) (i0 : idx_map (domain symbol m))
    (a_src0 : idx_map (domain symbol m)) (args0 : list idx) :
    (forall j, In j args0 ->
       exists v, map.get env0 j = Some v /\ map.get i0 v = map.get a_src0 j) ->
    list_Mmap (map.get i0)
      (map (fun x => unwrap_with_default (map.get env0 x)) args0) =
    list_Mmap (map.get a_src0) args0.
  Proof.
    intros Henv0.
    induction args0 as [|j js IH]; cbn; [ reflexivity | ].
    destruct (Henv0 j (or_introl eq_refl)) as (v & Hg & Hi).
    rewrite Hg. cbn. rewrite Hi.
    rewrite IH; [ reflexivity | ].
    intros k Hk. apply Henv0. right. exact Hk.
  Qed.

  Lemma all2_uf_rel_has_key
    (uf : union_find) (l xs ys : list idx) :
    union_find_ok lt uf l ->
    all2 (uf_rel_PER uf) xs ys ->
    all (fun v => Sep.has_key v (parent uf)) ys ->
    all (fun v => Sep.has_key v (parent uf)) xs.
  Proof.
    intros Hok.
    revert ys.
    induction xs as [|x xs' IH]; intros ys Hall2 Hky.
    - cbn. tauto.
    - destruct ys as [|y ys']; cbn in Hall2; [ tauto | ].
      destruct Hall2 as [Hrel Hall2'].
      cbn in Hky. destruct Hky as [Hky_y Hky_ys].
      cbn. split.
      + edestruct (uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok) as [Hk _]; [ exact Hok | exact Hrel | ]. exact Hk.
      + eapply IH; [ exact Hall2' | exact Hky_ys ].
  Qed.

  Lemma has_key_to_domain
    (m0 : model symbol) (i0 : idx_map (domain symbol m0)) (e0 : instance)
    (Hsnd0 : Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m0 i0 e0)
    (v : idx)
    (Hkv : Sep.has_key v (parent (equiv e0)))
    : exists d, map.get i0 v = Some d.
  Proof.
    unfold Sep.has_key in Hkv.
    destruct (map.get (parent (equiv e0)) v) as [vr|] eqn:Hgv; [ | tauto ].
    assert (Hperv : uf_rel_PER (equiv e0) v v).
    { unfold uf_rel_PER.
      eapply PER_clo_trans;
        [ apply PER_clo_base; exact Hgv
        | apply PER_clo_sym; apply PER_clo_base; exact Hgv ]. }
    pose proof (rel_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m0 i0 e0 Hsnd0 v v Hperv) as Heqv.
    unfold eq_sound_for_model in Heqv.
    destruct (map.get i0 v) as [d|] eqn:Hgiv.
    - exact (ex_intro _ d eq_refl).
    - exact (False_rect _ Heqv).
  Qed.

End Slice.

(* ===== External (top-level, explicit binders) ===== *)

Lemma allocate_existential_vars_sound
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type) (m : model symbol)
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  (a_src : idx_map (domain symbol m))
  (wvars : list idx)
  : forall (i : idx_map (domain symbol m)) (env0 : idx_map idx),
    List.NoDup wvars ->
    (forall w, In w wvars -> map.get env0 w = None) ->
    (forall w, In w wvars ->
               exists d, map.get a_src w = Some d /\ domain_wf symbol m d) ->
    vc (allocate_existential_vars idx idx_succ symbol symbol_map idx_map idx_trie analysis_result wvars env0)
      (fun e_in res =>
         Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_in ->
         Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e_in ->
         Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result (snd res) /\
         exists i',
           map.extends i' i /\
           Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i' (snd res) /\
           (forall x v, map.get env0 x = Some v -> map.get (fst res) x = Some v) /\
           (forall x, In x wvars ->
                      exists v d,
                        map.get (fst res) x = Some v /\
                        map.get a_src x = Some d /\
                        map.get i' v = Some d /\
                        Sep.has_key v (snd res).(equiv).(parent)) /\
           (forall x, Sep.has_key x e_in.(equiv).(parent) ->
                      Sep.has_key x (snd res).(equiv).(parent))).
Proof.
  induction wvars as [|x wvars' IH]; intros i0 env0 Hnodup Hfresh Hdom.
  - (* base case: wvars = [] *)
    unfold allocate_existential_vars, list_Mfoldl.
    unfold vc; intros e_in; cbn [Mret StateMonad.state_monad fst snd].
    intros Hok Hsnd.
    split; [exact Hok|].
    exists i0. split; [intros k v0 Hg; exact Hg|].
    split; [exact Hsnd|].
    split; [intros x0 v0 Hg; exact Hg|].
    split; [intros x0 Hin; contradiction|].
    intros x0 Hx0; exact Hx0.
  - (* inductive case: x :: wvars' *)
    inversion Hnodup as [|?? Hnotin Hnodup']; subst.
    assert (Hfresh_x : map.get env0 x = None)
      by (apply Hfresh; left; reflexivity).
    assert (Hfresh' : forall w, In w wvars' -> map.get env0 w = None)
      by (intros w Hw; apply Hfresh; right; exact Hw).
    assert (Hdom' : forall w, In w wvars' ->
                              exists d, map.get a_src w = Some d /\ domain_wf symbol m d)
      by (intros w Hw; apply Hdom; right; exact Hw).
    assert (Hdx : exists d, map.get a_src x = Some d /\ domain_wf symbol m d)
      by (apply Hdom; left; reflexivity).
    destruct Hdx as (d_x & Ha_src_x & Hwf_dx).
    unfold allocate_existential_vars, list_Mfoldl.
    fold (list_Mfoldl (M:=state (Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result)) (A:=idx) (B:=idx_map idx)).
    unfold vc; intros e_in.
    cbn [Mbind StateMonad.state_monad Mret].
    destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e_in)
      as [v_x e1] eqn:Halloc_eq.
    cbn [fst snd].
    intros Hok Hsnd.
    (* Apply alloc_sound for v_x: gives i1 = map.put i0 v_x d_x *)
    pose proof (alloc_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result m Hlti Hlts Hltt i0 d_x Hwf_dx Hwf_dx) as Hals.
    unfold vc in Hals. specialize (Hals e_in).
    rewrite Halloc_eq in Hals. cbn [fst snd] in Hals.
    destruct Hals as (Hok1 & Hsnd1 & _Hi_vx_none & _Hk_vx_none & Hkv_x &
                      Hpres1 & _Hdb1 & _Hpar1 & _Hwl1); auto.
    (* i1 = map.put i0 v_x d_x *)
    set (i1 := map.put i0 v_x d_x).
    (* Derive preconditions for IH: write vars in wvars' not in (put env0 x v_x) *)
    assert (Hfresh_put : forall w, In w wvars' -> map.get (map.put env0 x v_x) w = None).
    { intros w Hw.
      rewrite map.get_put_diff.
      - apply Hfresh'. exact Hw.
      - intro Heq. subst w. exact (Hnotin Hw). }
    (* Apply IH for (wvars', i1, map.put env0 x v_x, e1) *)
    pose proof (IH i1 (map.put env0 x v_x) Hnodup' Hfresh_put Hdom') as IH1.
    unfold allocate_existential_vars, list_Mfoldl in IH1.
    fold (list_Mfoldl (M:=state (Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result)) (A:=idx) (B:=idx_map idx)) in IH1.
    unfold vc in IH1. specialize (IH1 e1).
    destruct IH1 as (Hok2 & i2 & Hi2ext1 & Hsnd2 & Henv2 & Hwvars2 & Hpres2); auto.
    split; [exact Hok2|].
    (* i' = i2 extends i1 = map.put i0 v_x d_x extends i0 *)
    exists i2.
    assert (Hi2ext0 : map.extends i2 i0).
    { intros k vk Hg.
      apply Hi2ext1.
      unfold i1. rewrite map.get_put_diff.
      - exact Hg.
      - intro Heq. subst k.
        (* v_x is NOT in i0 (from alloc_sound) but map.get i0 k = Some vk — contradiction *)
        rewrite _Hi_vx_none in Hg. discriminate. }
    split; [exact Hi2ext0|].
    split; [exact Hsnd2|].
    split.
    { (* env0 entries preserved *)
      intros x0 v0 Hg0.
      apply Henv2.
      rewrite map.get_put_diff.
      - exact Hg0.
      - intro Heq. subst x0. rewrite Hfresh_x in Hg0. discriminate. }
    split.
    { (* each write var in (x :: wvars') has its fresh idx in result env *)
      intros x0 Hin0.
      destruct Hin0 as [Heq | Hin'].
      - (* x0 = x: use alloc for v_x *)
        subst x0.
        (* IH env preservation: put env0 x v_x maps x to v_x, result preserves it *)
        assert (Hxv : map.get (map.put env0 x v_x) x = Some v_x)
          by apply map.get_put_same.
        apply Henv2 in Hxv.
        (* map.get i2 v_x = Some d_x because i2 extends i1 and i1 v_x = Some d_x *)
        assert (Hi1_vx : map.get i1 v_x = Some d_x).
        { unfold i1. apply map.get_put_same. }
        apply Hi2ext1 in Hi1_vx.
        exists v_x, d_x.
        split; [exact Hxv|].
        split; [exact Ha_src_x|].
        split; [exact Hi1_vx|].
        apply Hpres2. exact Hkv_x.
      - (* In x0 wvars': from IH *)
        destruct (Hwvars2 x0 Hin') as (v0 & d0 & Hgv0 & Hasrc0 & Hi2_v0 & Hkey0).
        exists v0, d0.
        exact (conj Hgv0 (conj Hasrc0 (conj Hi2_v0 Hkey0))). }
    { (* parent keys monotone *)
      intros x0 Hx0. apply Hpres2. apply Hpres1. exact Hx0. }
Qed.

Lemma exec_clause_sound
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (Eqb_symbol : Eqb symbol) (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
  (symbol_map : forall A, map.map symbol A) (symbol_map_ok : forall A, map.ok (symbol_map A))
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (idx_trie_ok : forall A, map.ok (idx_trie A))
  (analysis_result : Type) (Hanalysis : analysis idx symbol analysis_result) (m : model symbol)
  (Hm : model_ok symbol m)
  (i : idx_map (domain symbol m))
  (env : idx_map idx) (c : atom idx symbol) (a_src : idx_map (domain symbol m))
  (e : Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result) :
  Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
  Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
  (forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
     exists v, map.get env x = Some v
               /\ Sep.has_key v (parent (equiv e))
               /\ map.get i v = map.get a_src x) ->
  atom_sound_for_model idx symbol idx_map m a_src c ->
  match exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env c e with
  | (_, e') =>
      Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e'
      /\ Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e'
      /\ (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
  end.
Proof.
  intros Hok Hsound Henv Hatom_src.
  unfold exec_clause.
  cbn [Mbind Mret StateMonad.state_monad].
  set (args_vals := map (fun x => unwrap_with_default (map.get env x)) (atom_args c)).
  set (out_val := unwrap_with_default (map.get env (atom_ret c))).
  assert (Henv_args : forall j, In j (atom_args c) ->
    exists v, map.get env j = Some v /\ Sep.has_key v (parent (equiv e)) /\ map.get i v = map.get a_src j).
  { intros j Hj. apply Henv. right. exact Hj. }
  destruct (Henv (atom_ret c) (or_introl eq_refl)) as (vr & Hgvr & Hkr & Hivr).
  assert (Hkey_args : all (fun v => Sep.has_key v (parent (equiv e))) args_vals).
  { unfold args_vals.
    assert (H_ka : forall (xs : list idx),
      (forall j, In j xs -> exists v, map.get env j = Some v /\ Sep.has_key v (parent (equiv e))) ->
      all (fun v => Sep.has_key v (parent (equiv e))) (map (fun x => unwrap_with_default (map.get env x)) xs)).
    { induction xs as [|x xs' IH]; cbn; [ tauto | ].
      intros Hxs. split.
      { destruct (Hxs x (or_introl eq_refl)) as (v & Hg & Hk). rewrite Hg. exact Hk. }
      { apply IH. intros y Hy. apply Hxs. right. exact Hy. } }
    apply H_ka. intros j Hj. destruct (Henv_args j Hj) as (v & Hg & Hk & _).
    exact (ex_intro _ v (conj Hg Hk)). }
  assert (Hkey_out : Sep.has_key out_val (parent (equiv e))).
  { unfold out_val. rewrite Hgvr. exact Hkr. }
  unfold atom_sound_for_model in Hatom_src.
  cbn [atom_args atom_ret atom_fn] in Hatom_src.
  destruct (list_Mmap (map.get a_src) (atom_args c)) as [doms|] eqn:Hdoms;
    cbn [Is_Some_satisfying] in Hatom_src; [ | tauto ].
  destruct (map.get a_src (atom_ret c)) as [out_dom|] eqn:Hout_dom;
    cbn [Is_Some_satisfying] in Hatom_src; [ | tauto ].
  assert (Hi_args_vals : list_Mmap (map.get i) args_vals = Some doms).
  { rewrite <- Hdoms. unfold args_vals.
    apply (list_Mmap_env_iU env i a_src (atom_args c)).
    intros j Hj. destruct (Henv_args j Hj) as (v & Hg & _ & Hiv).
    exact (ex_intro _ v (conj Hg Hiv)). }
  assert (Hi_out_val : map.get i out_val = Some out_dom).
  { unfold out_val. rewrite Hgvr. cbn. exact Hivr. }
  destruct Hok as [Heqok Hwlok Hparok Hdbkok].
  destruct Heqok as [roots Hroots].
  assert (Hok_e : Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e).
  { constructor; [ exact (ex_intro _ roots Hroots) | exact Hwlok | exact Hparok | exact Hdbkok ]. }
  pose proof (@list_Mmap_find_preserves_fields_strong idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result args_vals) as Hlm.
  unfold vc in Hlm. specialize (Hlm e).
  destruct (list_Mmap find args_vals e) as [args_vals' e1] eqn:Hlma.
  cbn [fst snd] in Hlm.
  destruct (Hlm (ex_intro _ roots Hroots) Hkey_args) as (Hex1 & Hfp01 & Hall_args').
  assert (Hkey_out_e1 : Sep.has_key out_val (parent (equiv e1))).
  { destruct Hfp01 as (_ & _ & _ & _ & _ & Hkey_iff & _). apply Hkey_iff. exact Hkey_out. }
  pose proof (@find_preserves_fields_strong idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result out_val) as Hfind_out.
  unfold vc in Hfind_out. specialize (Hfind_out e1).
  destruct (find out_val e1) as [out_val' e2] eqn:Hfinoa.
  cbn [fst snd] in Hfind_out.
  destruct (Hfind_out Hex1 Hkey_out_e1) as (Hex2 & Hfp12 & Huf_out).
  cbn [fst snd atom_fn].
  assert (Hfp02 : fields_preserved idx symbol symbol_map idx_map idx_trie analysis_result e e2).
  { exact (fields_preserved_trans idx lt idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result e e1 e2 Hfp01 Hfp12). }
  assert (Hok2 : Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e2).
  { exact (fields_preserved_egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e e2 Hok_e Hfp02 Hex2). }
  assert (Hsound2 : Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e2).
  { eapply fields_preserved_sound_for_interpretation; eassumption. }
  assert (Hall2 : all2 (uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e2)) args_vals' args_vals).
  { destruct Hfp12 as (_ & _ & _ & _ & _ & _ & Huf_iff).
    eapply all2_impl; [ | exact Hall_args' ].
    intros x y Hxy. apply Huf_iff. exact Hxy. }
  pose proof (args_rel_interpretation idx lt idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result m i e2 (conj Hok2 Hsound2) args_vals' args_vals Hall2) as Hrel_args.
  rewrite Hi_args_vals in Hrel_args.
  destruct (list_Mmap (map.get i) args_vals') as [doms'|] eqn:Hdoms'.
  2: { cbn in Hrel_args. discriminate. }
  cbn [option_relation] in Hrel_args.
  assert (Hrel_out : eq_sound_for_model idx symbol idx_map m i out_val' out_val).
  { apply (rel_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e2 Hsound2). exact Huf_out. }
  unfold eq_sound_for_model in Hrel_out.
  rewrite Hi_out_val in Hrel_out.
  destruct (map.get i out_val') as [out_dom'|] eqn:Hout_val';
    cbn [Is_Some_satisfying] in Hrel_out; [ | tauto ].
  assert (Hatom_i : atom_sound_for_model idx symbol idx_map m i
    {| atom_fn := atom_fn c; atom_args := args_vals'; atom_ret := out_val' |}).
  { unfold atom_sound_for_model. cbn [atom_args atom_ret atom_fn].
    rewrite Hdoms'. cbn [Is_Some_satisfying].
    rewrite Hout_val'. cbn [Is_Some_satisfying].
    eapply (@interprets_to_preserved symbol m Hm); [ exact Hatom_src | | ].
    - apply (all2_Symmetric (R:=domain_eq symbol m)). exact Hrel_args.
    - apply (PER_Symmetric (R:=domain_eq symbol m) out_dom' out_dom). exact Hrel_out. }
  destruct Hex2 as [roots2 Hroots2].
  assert (Hkey_all2 : all (fun v => Sep.has_key v (parent (equiv e2))) args_vals).
  { destruct Hfp02 as (_ & _ & _ & _ & _ & Hkey_iff & _).
    eapply all_wkn; [ | exact Hkey_args ].
    intros v _. apply Hkey_iff. }
  assert (Hkey_args2 : all (fun v => Sep.has_key v (parent (equiv e2))) args_vals').
  { exact (all2_uf_rel_has_key (idx_succ:=idx_succ) _ _ _ _ Hroots2 Hall2 Hkey_all2). }
  assert (Hkey_out2 : Sep.has_key out_val' (parent (equiv e2))).
  { edestruct (uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok) as [Hk _]; [ exact Hroots2 | exact Huf_out | ]. exact Hk. }
  pose proof (@update_entry_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result Hanalysis m Hm i {| atom_fn := atom_fn c; atom_args := args_vals'; atom_ret := out_val' |}) as Hue.
  unfold vc in Hue. specialize (Hue e2).
  destruct (update_entry {| atom_fn := atom_fn c; atom_args := args_vals'; atom_ret := out_val' |} e2)
    as [u e'] eqn:Hue_eq.
  cbn [snd] in Hue |- *.
  specialize (Hue Hok2).
  specialize (Hue Hsound2).
  specialize (Hue ltac:(intros x Hx; cbn [atom_args] in Hx; exact (in_all _ _ _ Hkey_args2 Hx))).
  specialize (Hue Hkey_out2).
  specialize (Hue Hatom_i).
  destruct Hue as (Hok' & Hsound' & Hkeys').
  split; [ exact Hok' | ].
  split; [ exact Hsound' | ].
  intros z Hz. apply Hkeys'.
  destruct Hfp02 as (_ & _ & _ & _ & _ & Hkey_iff & _).
  apply Hkey_iff. exact Hz.
Qed.

Lemma union_extends_keys_sem
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
  (Hanalysis : analysis idx symbol analysis_result)
  (x y : idx) (e_in : Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result)
  (Hroots_in : exists roots, union_find_ok lt (equiv e_in) roots)
  (Hkx : Sep.has_key x (parent (equiv e_in)))
  (Hky : Sep.has_key y (parent (equiv e_in)))
  (z : idx)
  (Hz : Sep.has_key z (parent (equiv e_in)))
  : Sep.has_key z (parent (equiv (snd (Defs.union x y e_in)))).
Proof.
  destruct Hroots_in as [roots Hroots].
  pose proof (union_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result x y) as Hus.
  unfold vc in Hus. specialize (Hus e_in).
  destruct (Defs.union x y e_in) as [v_u e_u] eqn:Hu.
  cbn [snd] in Hus |- *.
  destruct (Hus (ex_intro _ roots Hroots) Hkx Hky) as
    (_ & Hroots' & Hper & _).
  destruct Hroots' as [roots' Hroots'].
  (* Build uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_in) z z from has_key *)
  unfold Sep.has_key in Hz.
  destruct (map.get (parent (equiv e_in)) z) as [vr|] eqn:Hgz; [ | tauto ].
  assert (Hzz_in : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_in) z z).
  { unfold uf_rel_PER.
    eapply PER_clo_trans;
      [ apply PER_clo_base; exact Hgz
      | apply PER_clo_sym; apply PER_clo_base; exact Hgz ]. }
  (* Lift to union_closure_PER *)
  assert (Hzz_clo : union_closure_PER (uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_in)) (singleton_rel x y) z z).
  { unfold union_closure_PER. apply PER_clo_base. left. exact Hzz_in. }
  (* Cross the iff2 to get uf_rel_PER in e_u *)
  assert (Hzz_u : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) z z) by (apply Hper; exact Hzz_clo).
  (* Use uf_rel_PER_has_key to recover has_key *)
  exact (proj1 (uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok _ roots' _ _ Hroots' Hzz_u)).
Qed.

Lemma union_preserves_egraph_ok_sem
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
  (Hanalysis : analysis idx symbol analysis_result)
  (x y : idx) (e_in : Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result)
  (Hok_in : Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_in)
  (Hkx : Sep.has_key x (parent (equiv e_in)))
  (Hky : Sep.has_key y (parent (equiv e_in)))
  : Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result (snd (Defs.union x y e_in)).
Proof.
  pose proof (union_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result x y) as Hus.
  unfold vc in Hus. specialize (Hus e_in).
  destruct (Defs.union x y e_in) as [v_u e_u] eqn:Hu.
  cbn [snd] in Hus |- *.
  destruct Hok_in as [Heqok Hwlok Hparok Hdbkok].
  destruct Heqok as [roots Hroots].
  destruct (Hus (ex_intro _ roots Hroots) Hkx Hky) as
    (Hdb_u & Hroots' & Hper & Hpar_u & Hwl_u & _).
  destruct Hroots' as [roots' Hroots'].
  (* Key monotonicity helper *)
  assert (Hkm : forall z, Sep.has_key z (parent (equiv e_in)) ->
                           Sep.has_key z (parent (equiv e_u)))
    by (intros z Hz;
        unfold Sep.has_key in Hz;
        destruct (map.get (parent (equiv e_in)) z) as [vr|] eqn:Hgz; [|tauto];
        assert (Hzz_u : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) z z)
          by (apply (proj1 (Hper z z));
              unfold union_closure_PER; apply PER_clo_base; left;
              unfold uf_rel_PER; eapply PER_clo_trans;
                [apply PER_clo_base; exact Hgz | apply PER_clo_sym; apply PER_clo_base; exact Hgz]);
        exact (proj1 (uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok _ roots' _ _ Hroots' Hzz_u))).
  (* Hper_lift: old PER implies new PER *)
  assert (Hper_lift : forall i1 i2,
    uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_in) i1 i2 -> uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) i1 i2)
    by (intros i1 i2 Hi12; apply Hper;
        unfold union_closure_PER; apply PER_clo_base; left; exact Hi12).
  constructor.
  - (* egraph_equiv_ok *)
    exact (ex_intro _ roots' Hroots').
  - (* worklist_ok *)
    destruct Hwl_u as [Hwl_same | Hwl_new].
    + rewrite Hwl_same. eapply all_wkn; [ | exact Hwlok ].
      intros ent _ Hp. destruct ent as [old new improved | xa];
        cbn in *; [ apply Hper_lift; exact Hp | exact I ].
    + destruct Hwl_new as (v_old & v_new & improved & Hwl_eq & Hper_old & Hper_new).
      rewrite Hwl_eq. cbn. split.
      * assert (Hr_xy : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) x y)
          by (apply Hper; apply PER_clo_base; right; unfold singleton_rel; split; reflexivity).
        unfold uf_rel_PER in *.
        eapply PER_clo_trans; [ exact Hper_old | ].
        eapply PER_clo_trans; [ exact Hr_xy | ].
        apply PER_clo_sym. exact Hper_new.
      * eapply all_wkn; [ | exact Hwlok ].
        intros ent2 _ Hp2. destruct ent2 as [old2 new2 improved2 | xa2];
          cbn in *; [ apply Hper_lift; exact Hp2 | exact I ].
  - (* parents_ok *)
    rewrite <- Hpar_u.
    intros x_p s_p Hgs.
    specialize (Hparok _ _ Hgs).
    eapply all_wkn; [ | exact Hparok ].
    intros b _ Hbup.
    destruct Hbup as (bb & Hca & Hbain).
    destruct Hca as (Hfn & Hargs & Hret).
    exists bb. split.
    + unfold atom_canonical_equiv. split; [ exact Hfn | ]. split.
      * revert Hargs. generalize (atom_args b), (atom_args bb).
        intros l1 l2. revert l2.
        induction l1 as [| w ws IH]; destruct l2 as [| z zs];
          cbn; auto; try tauto.
        intros [Hw Hws]. split; [apply Hper_lift; exact Hw | apply IH; exact Hws].
      * apply Hper_lift. exact Hret.
    + unfold atom_in_egraph. rewrite <- Hdb_u. exact Hbain.
  - (* db_idxs_in_equiv *)
    rewrite <- Hdb_u. intros b Hb.
    specialize (Hdbkok _ Hb).
    destruct Hdbkok as [Hka Hkr]. split.
    + eapply all_wkn; [ | exact Hka ].
      intros j _ Hj. apply Hkm. exact Hj.
    + apply Hkm. exact Hkr.
Qed.

Lemma union_preserves_sound_sem
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
  (Hanalysis : analysis idx symbol analysis_result) (m : model symbol)
  (Hm : model_ok symbol m)
  (x y : idx)
  (i0 : idx_map (domain symbol m)) (e_in : Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result)
  (Hok_in : Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_in)
  (Hsnd_in : Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i0 e_in)
  (Hkx : Sep.has_key x (parent (equiv e_in)))
  (Hky : Sep.has_key y (parent (equiv e_in)))
  (Heq_xy : eq_sound_for_model idx symbol idx_map m i0 x y)
  : Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i0 (snd (Defs.union x y e_in)).
Proof.
  pose proof (union_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result x y) as Hus.
  unfold vc in Hus. specialize (Hus e_in).
  destruct (Defs.union x y e_in) as [v_u e_u] eqn:Hu.
  cbn [snd] in Hus |- *.
  destruct Hok_in as [Heqok Hwlok Hparok Hdbkok].
  destruct Heqok as [roots Hroots].
  destruct (Hus (ex_intro _ roots Hroots) Hkx Hky) as
    (Hdb_u & Hroots' & Hper & _ & _ & _).
  destruct Hroots' as [roots' Hroots'].
  destruct Hsnd_in as [Hi_wf Hi_exact Hi_atom Hi_rel].
  (* Key monotonicity helper *)
  assert (Hkm : forall z, Sep.has_key z (parent (equiv e_in)) ->
                           Sep.has_key z (parent (equiv e_u)))
    by (intros z Hz;
        unfold Sep.has_key in Hz;
        destruct (map.get (parent (equiv e_in)) z) as [vr|] eqn:Hgz; [|tauto];
        assert (Hzz_u : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) z z)
          by (apply (proj1 (Hper z z));
              unfold union_closure_PER; apply PER_clo_base; left;
              unfold uf_rel_PER; eapply PER_clo_trans;
                [apply PER_clo_base; exact Hgz | apply PER_clo_sym; apply PER_clo_base; exact Hgz]);
        exact (proj1 (uf_rel_PER_has_key idx Eqb_idx Eqb_idx_ok lt idx_zero idx_map idx_map_ok _ roots' _ _ Hroots' Hzz_u))).
  constructor.
  - (* idx_interpretation_wf: unchanged interpretation *)
    exact Hi_wf.
  - (* interpretation_exact: keys extended via Hkm *)
    intros z Hz. apply Hkm. apply Hi_exact. exact Hz.
  - (* atom_interpretation: db preserved *)
    intros a Ha. apply Hi_atom.
    unfold atom_in_egraph. rewrite Hdb_u. exact Ha.
  - (* rel_interpretation: lift the closure *)
    intros i1 i2 Hi12.
    apply Hper in Hi12.
    induction Hi12 as [a b H1 | a b c IHab Hab IHbc Hbc | a b IHab Hab].
    + destruct H1 as [Hold | Hnew].
      * apply Hi_rel. exact Hold.
      * destruct Hnew as [Hax Hby]; subst. exact Heq_xy.
    + eapply eq_sound_for_model_trans; eauto.
    + eapply eq_sound_for_model_Symmetric; eauto.
Qed.
