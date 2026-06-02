(* [B4] rebuild_canon assembly: connects the B3 union-pass to the full `rebuild`.
   Split out of Semantics.v (Section WithMap) to keep that file smaller.  Stated
   at top level with the egraph context as explicit/implicit arguments;
   good_worklist and rebuild_canon keep the exact section-closed signatures
   (all-explicit ctx incl. the model m) expected by the F1c discharge. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.


(* D1: list_Mmap canonicalize_worklist_entry is the identity when   *)
(* every union_repair entry's new_idx is a root.                    *)
Lemma list_Mmap_canon_wl_id
  {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {symbol : Type}
  {symbol_map : forall A, map.map symbol A}
  {idx_map : forall A, map.map idx A}
  {idx_trie : forall A, map.map (list idx) A}
  {analysis_result : Type}
  l
  : vc (list_Mmap (canonicalize_worklist_entry idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result) l)
      (fun e res =>
         (forall old new_idx b, In (@union_repair idx old new_idx b) l ->
                            map.get e.(equiv).(parent) new_idx = Some new_idx) ->
         snd res = e /\ fst res = l).
Proof.
  induction l as [|a l IH].
  - unfold vc, list_Mmap, Mret, StateMonad.state_monad. intros e _. cbn [fst snd]. auto.
  - destruct a as [old new_idx b | j].
    + (* union_repair case *)
      unfold vc. intros e Hroots_e.
      cbn [list_Mmap canonicalize_worklist_entry Mbind Mret StateMonad.state_monad fst snd].
      assert (Hnew_root : map.get e.(equiv).(parent) new_idx = Some new_idx).
      { apply (Hroots_e old new_idx b). left. reflexivity. }
      rewrite (@find_root_identity _ _ _ _ _ _ _ _ e new_idx Hnew_root).
      unfold vc in IH. specialize (IH e).
      assert (Hroots_tail : forall old0 new_idx0 b0, In (@union_repair idx old0 new_idx0 b0) l ->
                  map.get e.(equiv).(parent) new_idx0 = Some new_idx0).
      { intros old0 new_idx0 b0 Hin. apply (Hroots_e old0 new_idx0 b0). right. exact Hin. }
      specialize (IH Hroots_tail).
      destruct IH as [IHsnd IHfst].
      destruct (list_Mmap (canonicalize_worklist_entry idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result) l e) as [xs e'] eqn:Hlm.
      cbn [fst snd] in IHsnd, IHfst |- *.
      split; [exact IHsnd | f_equal; exact IHfst].
    + (* analysis_repair case *)
      unfold vc. intros e Hroots_e.
      cbn [list_Mmap canonicalize_worklist_entry Mbind Mret StateMonad.state_monad fst snd].
      unfold vc in IH. specialize (IH e).
      assert (Hroots_tail : forall old0 new_idx0 b0, In (@union_repair idx old0 new_idx0 b0) l ->
                  map.get e.(equiv).(parent) new_idx0 = Some new_idx0).
      { intros old0 new_idx0 b0 Hin. apply (Hroots_e old0 new_idx0 b0). right. exact Hin. }
      specialize (IH Hroots_tail).
      destruct IH as [IHsnd IHfst].
      destruct (list_Mmap (canonicalize_worklist_entry idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result) l e) as [xs e'] eqn:Hlm.
      cbn [fst snd] in IHsnd, IHfst |- *.
      split; [exact IHsnd | f_equal; exact IHfst].
Qed.

(* D2: worklist_dedup is the identity on a list of union_repair      *)
(* entries with pairwise distinct olds (same old => same entry).     *)
Lemma worklist_dedup_id
  {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  l
  : (forall a, In a l -> exists old new_idx b, a = @union_repair idx old new_idx b) ->
    List.NoDup l ->
    (forall old1 new1 b1 old2 new2 b2,
       In (@union_repair idx old1 new1 b1) l ->
       In (@union_repair idx old2 new2 b2) l ->
       old1 = old2 -> new1 = new2 /\ b1 = b2) ->
    worklist_dedup idx Eqb_idx l = l.
Proof.
  induction l as [|a l IH].
  - intros; reflexivity.
  - intros Hall_ur Hnodup Hdist_old.
    cbn [worklist_dedup].
    destruct (Hall_ur a (or_introl eq_refl)) as (old & new_idx & b & Heqa). subst a.
    inversion Hnodup as [|? ? Hnotin Hnodup_l]. subst.
    assert (Hall_ur_l : forall x, In x l -> exists o n bb, x = @union_repair idx o n bb).
    { intros x Hx. exact (Hall_ur x (or_intror Hx)). }
    assert (Hdist_l : forall old1 new1 b1 old2 new2 b2,
       In (@union_repair idx old1 new1 b1) l ->
       In (@union_repair idx old2 new2 b2) l ->
       old1 = old2 -> new1 = new2 /\ b1 = b2).
    { intros old1 new1 b1 old2 new2 b2 H1 H2 Heq.
      exact (Hdist_old old1 new1 b1 old2 new2 b2 (or_intror H1) (or_intror H2) Heq). }
    specialize (IH Hall_ur_l Hnodup_l Hdist_l). rewrite IH.
    destruct (List.existsb (entry_subsumed_by idx Eqb_idx (union_repair idx old new_idx b)) l) eqn:Hexb.
    * exfalso.
      rewrite List.existsb_exists in Hexb.
      destruct Hexb as (x & Hx_in & Hx_sub).
      destruct (Hall_ur_l x Hx_in) as (old' & new' & b' & Heqx). subst x.
      cbn [entry_subsumed_by] in Hx_sub.
      apply andb_prop in Hx_sub as [Hxold _].
      pose proof (eqb_spec old old') as Hspec; rewrite Hxold in Hspec.
      destruct (Hdist_old old new_idx b old' new' b' (or_introl eq_refl) (or_intror Hx_in) Hspec) as [Hnew Hb].
      subst. apply Hnotin. exact Hx_in.
    * reflexivity.
Qed.

(* D3: good_worklist: the structural precondition that rebuild_canon *)
(* requires on the worklist.                                          *)
Definition good_worklist
  (idx symbol : Type)
  (symbol_map : forall A, map.map symbol A)
  (idx_map : forall A, map.map idx A)
  (idx_trie : forall A, map.map (list idx) A)
  (analysis_result : Type)
  (e : instance idx symbol symbol_map idx_map idx_trie analysis_result)
  (ed_list : list (entry_data idx symbol)) : Prop :=
     e.(worklist) = map (ed_to_entry _ _) ed_list
  /\ List.NoDup ed_list
  /\ all (@good_ed _ _ _ _ _ _ e) ed_list
  /\ (forall dj dk, In dj ed_list -> In dk ed_list -> dj <> dk -> @ed_disjoint _ _ dj dk)
  /\ @db_inv _ _ _ _ _ _ (fun _ => False) e
  /\ (forall b, @atom_in_db _ _ _ _ _ b e.(db) -> ~ @is_root _ _ _ _ _ _ e (atom_ret b) ->
                exists d, In d ed_list /\ atom_fn b = atom_fn (ed_atom _ _ d)
                  /\ atom_args b = atom_args (ed_atom _ _ d)).

(* Helper: NoDup (map ed_to_entry ed_list) from NoDup ed_list + pairwise disjoint olds. *)
Local Lemma NoDup_map_ed_to_entry
  {idx symbol : Type}
  ed_list
  (Hnodup : List.NoDup ed_list)
  (Hdisj : forall dj dk, In dj ed_list -> In dk ed_list -> dj <> dk -> @ed_disjoint idx symbol dj dk)
  : List.NoDup (map (ed_to_entry idx symbol) ed_list).
Proof.
  induction ed_list as [|d0 rest IH].
  - constructor.
  - inversion Hnodup as [|? ? Hnotin_d0 Hnodup_rest]. subst.
    constructor.
    + intro Hin_map.
      apply in_map_iff in Hin_map.
      destruct Hin_map as (dk & Hdk_eq & Hdk_in).
      unfold ed_to_entry in Hdk_eq. injection Hdk_eq as Hold_eq _ _.
      assert (Hd0_ne_dk : d0 <> dk).
      { intros Heq. subst dk. exact (Hnotin_d0 Hdk_in). }
      pose proof (Hdisj d0 dk (or_introl eq_refl) (or_intror Hdk_in) Hd0_ne_dk) as Hdisj_0k.
      destruct Hdisj_0k as (_ & Hne_old & _).
      exact (Hne_old Hold_eq).
    + apply IH.
      * exact Hnodup_rest.
      * intros dj dk Hdj Hdk Hne.
        exact (Hdisj dj dk (or_intror Hdj) (or_intror Hdk) Hne).
Qed.

(* Direct: worklist_dedup (map ed_to_entry ed_list) is the identity  *)
(* given NoDup ed_list + pairwise disjoint olds.                     *)
Local Lemma worklist_dedup_ed_list
  {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
  {symbol : Type}
  ed_list
  (Hnodup : List.NoDup ed_list)
  (Hdisj : forall dj dk, In dj ed_list -> In dk ed_list -> dj <> dk -> @ed_disjoint idx symbol dj dk)
  : worklist_dedup idx Eqb_idx (map (ed_to_entry idx symbol) ed_list) = map (ed_to_entry idx symbol) ed_list.
Proof.
  induction ed_list as [|d0 rest IH].
  - reflexivity.
  - inversion Hnodup as [|? ? Hnotin_d0 Hnodup_rest]. subst.
    cbn [map worklist_dedup].
    assert (HIH : worklist_dedup idx Eqb_idx (map (ed_to_entry idx symbol) rest) = map (ed_to_entry idx symbol) rest).
    { apply IH.
      - exact Hnodup_rest.
      - intros dj dk Hdj Hdk Hne.
        exact (Hdisj dj dk (or_intror Hdj) (or_intror Hdk) Hne). }
    rewrite HIH.
    assert (Hexb : List.existsb (entry_subsumed_by idx Eqb_idx (ed_to_entry idx symbol d0)) (map (ed_to_entry idx symbol) rest) = false).
    { apply Bool.not_true_iff_false. rewrite existsb_exists.
      intros (x & Hx & Hfx).
      apply in_map_iff in Hx.
      destruct Hx as (dk & Hdk_eq & Hdk_in).
      subst x.
      unfold ed_to_entry, entry_subsumed_by in Hfx.
      apply andb_prop in Hfx as [Hxold _].
      pose proof (eqb_spec (ed_old _ _ d0) (ed_old _ _ dk)) as Hspec.
      rewrite Hxold in Hspec.
      assert (Hd0_ne_dk : d0 <> dk).
      { intros Heq. subst dk. exact (Hnotin_d0 Hdk_in). }
      pose proof (Hdisj d0 dk (or_introl eq_refl) (or_intror Hdk_in) Hd0_ne_dk) as Hdisj_0k.
      destruct Hdisj_0k as (_ & Hne_old & _).
      exact (Hne_old (eq_sym Hspec)). }
    rewrite Hexb. reflexivity.
Qed.

(* The main assembly: given a good_worklist precondition, rebuild    *)
(* (S fuel) establishes db_inv(True) and preserves roots.           *)
Lemma rebuild_canon
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (Eqb_symbol : Eqb symbol) (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
  (symbol_map : forall A, map.map symbol A) (symbol_map_ok : forall A, map.ok (symbol_map A))
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (idx_trie_ok : forall A, map.ok (idx_trie A))
  (analysis_result : Type) (HA : analysis idx symbol analysis_result)
  (m : model symbol) (Hm : model_ok symbol m)
  fuel e1 ed_list
  : @egraph_ok _ lt _ _ _ _ _ e1 ->
    good_worklist idx symbol symbol_map idx_map idx_trie analysis_result e1 ed_list ->
    @db_inv _ _ _ _ _ _ (fun _ => True) (snd (rebuild (S fuel) e1))
    /\ (forall z, @is_root _ _ _ _ _ _ e1 z -> @is_root _ _ _ _ _ _ (snd (rebuild (S fuel) e1)) z)
    /\ (forall b, @atom_in_db _ _ _ _ _ b (snd (rebuild (S fuel) e1)).(db) ->
           exists a, @atom_in_db _ _ _ _ _ a e1.(db)
             /\ a.(atom_fn) = b.(atom_fn) /\ a.(atom_args) = b.(atom_args)).
Proof.
  intros Hok1 Hgwl.
  destruct Hgwl as (Hwl_eq & Hnodup & Hall_good & Hdisj & Hdbinv & Hcov).
  cbn [rebuild].
  unfold pull_worklist. cbn [Mbind StateMonad.state_monad fst snd].
  rewrite Hwl_eq.
  destruct (map (ed_to_entry _ _) ed_list) as [| w wl'] eqn:Hmap_ed.
  - (* Case 1: todo = [] => immediate return, snd = e1 with worklist:=[] *)
    cbn [Mret StateMonad.state_monad snd].
    assert (Hed_nil : ed_list = []).
    { destruct ed_list as [|d rest]; [reflexivity | discriminate Hmap_ed]. }
    subst ed_list. clear Hall_good Hnodup Hdisj.
    (* e1 with worklist:=[] has same db/equiv as e1 *)
    (* db_inv(True): from db_inv(False) e1 + coverage = [] *)
    assert (Hdbinv_true : @db_inv _ _ _ _ _ _ (fun _ => True) e1).
    { unfold db_inv. intros b Hb.
      split.
      - exact (proj1 (Hdbinv b Hb)).
      - intros _.
        apply Decidable.not_not.
        + unfold Decidable.decidable, is_root.
          destruct (map.get (parent (equiv e1)) (atom_ret b)) as [r|].
          * destruct (eqb (atom_ret b) r) eqn:Heqb_r.
            -- left. pose proof (eqb_spec (atom_ret b) r) as Hspec2.
               rewrite Heqb_r in Hspec2. congruence.
            -- right. intro Heq. injection Heq as Heq'.
               pose proof (eqb_spec (atom_ret b) r) as Hspec2.
               rewrite Heqb_r in Hspec2. exact (Hspec2 (eq_sym Heq')).
          * right. intro Hnone. discriminate Hnone.
        + intro Hnonroot.
          destruct (Hcov b Hb Hnonroot) as (d & Hd_in & _). exact Hd_in. }
    split; [|split].
    + (* db_inv(True) of snd = e1 with worklist:=[] *)
      unfold db_inv in *. intros b Hb. cbn [db equiv] in *.
      exact (Hdbinv_true b Hb).
    + (* roots_mono *)
      intros z Hz. unfold is_root in *. cbn [equiv]. exact Hz.
    + (* reverse image: db unchanged from e1 *)
      intros b Hb. cbn [db] in Hb.
      exists b. split; [exact Hb | split; reflexivity].
  - (* Case 2: todo = w::wl' => main path through D1/D2/B3 *)
    (* State e' after pull_worklist: worklist:=[], db/equiv/parents = e1's *)
    set (e' := {| db := db e1; equiv := equiv e1; parents := parents e1;
                  epoch := epoch e1; worklist := []; analyses := analyses e1;
                  log := log idx symbol symbol_map idx_map idx_trie analysis_result e1 |}).
    fold e'.
    (* egraph_ok e' *)
    assert (Hok' : @egraph_ok _ lt _ _ _ _ _ e').
    { destruct Hok1 as [Heq_ok Hwl_ok Hpa_ok Hdb_ok].
      constructor; cbn; [exact Heq_ok | exact I | exact Hpa_ok | exact Hdb_ok]. }
    (* All ed_new are roots in e' (= roots in e1) *)
    assert (Hnew_roots : forall old new_idx b_val,
              In (@union_repair idx old new_idx b_val) (w :: wl') ->
              map.get e'.(equiv).(parent) new_idx = Some new_idx).
    { intros old new_idx b_val Hin.
      rewrite <- Hmap_ed in Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as (d & Hd_eq & Hd_in).
      unfold ed_to_entry in Hd_eq. injection Hd_eq as Hold Hnew _.
      rewrite <- Hnew. cbn [equiv].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 (@in_all _ (@good_ed _ _ _ _ _ _ e1) ed_list d Hall_good Hd_in)))))). }
    (* D1: list_Mmap_canon_wl_id => todo' = w::wl', state = e' *)
    pose proof (@list_Mmap_canon_wl_id idx Eqb_idx Eqb_idx_ok symbol symbol_map idx_map idx_trie analysis_result (w :: wl')) as HD1. unfold vc in HD1.
    specialize (HD1 e' Hnew_roots).
    destruct (list_Mmap (canonicalize_worklist_entry idx Eqb_idx symbol symbol_map idx_map idx_trie analysis_result) (w :: wl') e') as [todo' e''] eqn:Hmmap.
    cbn [fst snd] in HD1. destruct HD1 as [HD1_snd HD1_fst]. subst e'' todo'.
    (* D2 via worklist_dedup_ed_list: worklist_dedup (map ed_to_entry ed_list) = map ed_to_entry ed_list *)
    rewrite <- Hmap_ed.
    rewrite (worklist_dedup_ed_list ed_list Hnodup Hdisj).
    rewrite Hmap_ed.
    (* Now apply B3: list_Miter_repair_union_pass *)
    (* Establish union_pass_inv e1 e' ed_list *)
    assert (Hinv0 : @union_pass_inv _ lt _ _ _ _ _ e1 e' ed_list).
    { unfold union_pass_inv.
      refine (conj Hok' (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
      - intros z Hz. unfold is_root in *. cbn [equiv]. exact Hz.
      - exact I. (* worklist e' = [] all analysis_repair *)
      - (* db_inv(False) e': same as e1 *)
        unfold db_inv in *. intros b Hb. cbn [db equiv] in *. exact (Hdbinv b Hb).
      - (* all good_ed e' ed_list: good_ed is about db/equiv/parents which are same *)
        eapply all_wkn; [| exact Hall_good].
        intros d _ Hgood_d. unfold good_ed in *. cbn [db equiv parents] in *.
        exact Hgood_d.
      - exact Hdisj.
      - intros b Hb Hnonroot. cbn [db equiv] in *.
        exact (Hcov b Hb Hnonroot).
      - (* reverse image e1 → e': db unchanged *)
        intros b Hb. cbn [db] in Hb. exists b. split; [exact Hb | split; reflexivity]. }
    (* Apply list_Miter_repair_union_pass *)
    pose proof (@list_Miter_repair_union_pass idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result HA m Hm e1 ed_list Hnodup) as HB3.
    unfold vc in HB3. specialize (HB3 e').
    rewrite Hmap_ed in HB3.
    destruct (list_Miter (repair) (w :: wl') e') as [u_mit e_mid] eqn:Hmit.
    cbn [fst snd] in HB3.
    specialize (HB3 Hinv0).
    (* HB3 : union_pass_inv e1 e_mid nil *)
    (* Extract db_inv(True) e_mid and roots_mono e1 e_mid *)
    pose proof (@union_pass_inv_db_inv_true _ _ _ lt _ _ _ _ _ e1 e_mid HB3) as Hdbinv_mid.
    destruct HB3 as (_ & Hroots_mid & Hwl_mid_ar & _ & _ & _ & _ & Hrev_mid).
    (* Apply rebuild fuel e_mid: analysis-only worklist *)
    pose proof (@rebuild_preserves_atom_in_db idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_trie idx_trie_ok analysis_result HA fuel) as HRB_db.
    unfold vc in HRB_db. specialize (HRB_db e_mid Hwl_mid_ar).
    pose proof (@rebuild_analysis_only_preserves_equiv idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_trie idx_trie_ok analysis_result HA fuel) as HRB_eq.
    unfold vc in HRB_eq. specialize (HRB_eq e_mid Hwl_mid_ar).
    destruct (rebuild fuel e_mid) as [u_rb eF] eqn:Hrb.
    cbn [snd] in HRB_db, HRB_eq |- *.
    destruct HRB_db as [Hdb_iff _].
    (* Show that the whole computation's final state IS eF *)
    assert (Hfinal : snd ((@! (list_Miter (repair) (w :: wl')); (rebuild fuel)) e') = eF).
    { cbn [Mbind Mseq StateMonad.state_monad fst snd].
      rewrite Hmit. cbn [fst snd]. rewrite Hrb. reflexivity. }
    split; [|split].
    + (* db_inv(True) eF *)
      unfold db_inv. intros b Hb.
      rewrite Hfinal in Hb.
      assert (Hb_mid : @atom_in_db _ _ _ _ _ b e_mid.(db)).
      { apply Hdb_iff. exact Hb. }
      rewrite Hfinal, HRB_eq.
      exact (Hdbinv_mid b Hb_mid).
    + (* roots_mono e1 eF *)
      intros z Hz.
      unfold is_root.
      rewrite Hfinal.
      rewrite HRB_eq.
      exact (Hroots_mid z Hz).
    + (* reverse image e1 → eF: via analysis-phase db preservation then union-pass reverse image *)
      intros b Hb.
      rewrite Hfinal in Hb.
      assert (Hb_mid : @atom_in_db _ _ _ _ _ b e_mid.(db)).
      { apply Hdb_iff. exact Hb. }
      exact (Hrev_mid b Hb_mid).
Qed.
