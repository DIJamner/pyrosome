From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface Map.Properties.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.

Set Implicit Arguments.

Section Scratch.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.
  Context (V_map : forall A, map.map V A)
    (V_map_plus : ExtraMaps.map_plus V_map)
    (V_map_ok : forall A, map.ok (V_map A))
    (V_trie : forall A, map.map (list V) A)
    (V_trie_ok : forall A, map.ok (V_trie A)).

  Context (X : Type)
          (le : X -> X -> bool)
          (analyses : V_map X).

  Notation db_entry := (EGraph.Defs.db_entry V X).
  Notation db_map := (EGraph.Defs.db_map V V (V_map) (V_trie) X).

  Lemma select_optimal_nodes_correct
        (db : db_map) (out f : V) (args : list V) :
    map.get (@Pyrosome.Tools.EGraph.Defs.select_optimal_nodes V V_map V_trie X le analyses db) out = Some (f, args) ->
    exists tbl r,
      map.get db f = Some tbl
      /\ map.get tbl args = Some r
      /\ EGraph.Defs.entry_value _ _ r = out.
  Proof.
    unfold Pyrosome.Tools.EGraph.Defs.select_optimal_nodes.
    set (process_row := fun f0 (acc : V_map (V * list V)) args0 (row : db_entry) =>
      let out0 := EGraph.Defs.entry_value _ _ row in
      let ra := EGraph.Defs.entry_analysis _ _ row in
      match map.get analyses out0 with
      | None => acc
      | Some a => if le ra a then map.put acc out0 (f0, args0) else acc
      end).
    set (process_table := fun (acc : V_map (V * list V)) f0 (tbl : V_trie db_entry) =>
      map.fold (process_row f0) acc tbl).
    eapply (@map.fold_spec V (V_trie db_entry) (V_map _) (V_map_ok _)
      (V_map (V * list V))
      (fun (db_partial : V_map (V_trie db_entry)) (acc : V_map (V * list V)) =>
              forall out' f' args',
                map.get acc out' = Some (f', args') ->
                exists tbl r,
                  map.get db_partial f' = Some tbl
                  /\ map.get tbl args' = Some r
                  /\ EGraph.Defs.entry_value _ _ r = out')
      process_table map.empty).
    - (* Base: empty accumulator *)
      intros out' f' args' Hget.
      rewrite map.get_empty in Hget. discriminate.
    - (* Outer step *)
      intros f0 tbl0 db_partial acc Hnotf0 IH_outer.
      unfold process_table.
      eapply (@map.fold_spec (list V) db_entry (V_trie _) (V_trie_ok _)
        (V_map (V * list V))
        (fun (tbl_partial : V_trie db_entry) (acc' : V_map (V * list V)) =>
                forall out' f' args',
                  map.get acc' out' = Some (f', args') ->
                  exists tbl r,
                    map.get (map.put db_partial f0 tbl_partial) f' = Some tbl
                    /\ map.get tbl args' = Some r
                    /\ EGraph.Defs.entry_value _ _ r = out')
        (process_row f0) acc).
      + (* Inner base *)
        intros out' f' args' Hget.
        destruct (IH_outer out' f' args' Hget) as (tbl & r & H1 & H2 & H3).
        exists tbl, r.
        refine (conj _ (conj H2 H3)).
        rewrite map.get_put_diff; [ exact H1 | intro Heq; subst; rewrite Hnotf0 in H1; discriminate ].
      + (* Inner step *)
        intros args0 row0 tbl_partial acc' Hnot_args0 IH_inner.
        assert (Htransport : forall (o2 f2 : V) (a2 : list V) tbl_src rr,
          map.get (map.put db_partial f0 tbl_partial) f2 = Some tbl_src ->
          map.get tbl_src a2 = Some rr ->
          EGraph.Defs.entry_value V X rr = o2 ->
          exists tbl r0,
            map.get (map.put db_partial f0 (map.put tbl_partial args0 row0)) f2 = Some tbl
            /\ map.get tbl a2 = Some r0 /\ EGraph.Defs.entry_value V X r0 = o2).
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
          destruct (map.get analyses (EGraph.Defs.entry_value V X row0)) as [a|] eqn:Hanalysis.
          -- destruct (le (EGraph.Defs.entry_analysis V X row0) a) eqn:Hle.
             ++ intros out' f' args' Hget'.
                destruct (eqb out' (EGraph.Defs.entry_value V X row0)) eqn:Hbo;
                  pose proof (eqb_spec out' (EGraph.Defs.entry_value V X row0)) as Hso; rewrite Hbo in Hso.
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

  Lemma select_optimal_nodes_sound
        (db : db_map) (out f : V) (args : list V) :
    map.get (@Pyrosome.Tools.EGraph.Defs.select_optimal_nodes V V_map V_trie X le analyses db) out = Some (f, args) ->
    atom_in_db V V V_map V_trie X (Build_atom f args out) db.
  Proof.
    intro H. apply select_optimal_nodes_correct in H.
    destruct H as (tbl & r & Htbl & Hr & Hev).
    unfold atom_in_db, Is_Some_satisfying; cbn.
    rewrite Htbl, Hr. exact Hev.
  Qed.

End Scratch.
