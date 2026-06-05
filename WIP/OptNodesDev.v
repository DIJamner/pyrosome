From Stdlib Require Import Lists.List.
Import ListNotations.
From coqutil Require Import Map.Interface Map.Properties.
From Utils Require Import Utils ExtraMaps.
From Utils.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph Require Import Defs.

Set Implicit Arguments.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}
          (V_map : forall A, map.map V A)
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
    map.get (Pyrosome.Tools.EGraph.Defs.select_optimal_nodes le analyses db) out = Some (f, args) ->
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
    (* Use fold_spec on the outer fold (over db : V_map (V_trie db_entry)).
       Invariant: for all out f args in the accumulator, there exist tbl r
       with map.get db_partial f = Some tbl /\ map.get tbl args = Some r /\ entry_value r = out.
       (We use db_partial = map.put ... to build up to db.)
    *)
    apply (map.fold_spec
      (map := V_map _)
      (map_ok := V_map_ok _)
      (P := fun (db_partial : V_map (V_trie db_entry)) (acc : V_map (V * list V)) =>
              forall out' f' args',
                map.get acc out' = Some (f', args') ->
                exists tbl r,
                  map.get db_partial f' = Some tbl
                  /\ map.get tbl args' = Some r
                  /\ EGraph.Defs.entry_value _ _ r = out')
      (f := process_table)
      (r0 := map.empty)).
    - (* Base: empty accumulator *)
      intros out' f' args' Hget.
      rewrite map.get_empty in Hget. discriminate.
    - (* Outer step: visiting f0 ↦ tbl0, accumulator goes from acc to
         process_table acc f0 tbl0 = map.fold (process_row f0) acc tbl0 *)
      intros f0 tbl0 db_partial acc Hnotf0 IH_outer.
      unfold process_table.
      (* Apply fold_spec on the inner fold (over tbl0 : V_trie db_entry).
         Inner invariant: for all out' f' args' in acc', there exist tbl r with
           map.get (put db_partial f0 tbl0) f' = Some tbl /\ map.get tbl args' = Some r /\ entry_value r = out'.
         Note: the inner fold_spec's P is on (tbl_partial : V_trie db_entry, acc' : V_map (V*list V)).
         At each step, tbl_partial grows; when entry_value row0 ↦ (f0,args0) is put into acc',
         we witness with map.get tbl_partial' args0 = Some row0 via get_put_same,
         where tbl_partial' = put tbl_partial args0 row0. Since the final tbl_partial = tbl0,
         entries from the inner fold have witness in tbl0.
      *)
      apply (map.fold_spec
        (map := V_trie _)
        (map_ok := V_trie_ok _)
        (P := fun (tbl_partial : V_trie db_entry) (acc' : V_map (V * list V)) =>
                forall out' f' args',
                  map.get acc' out' = Some (f', args') ->
                  exists tbl r,
                    map.get (map.put db_partial f0 tbl_partial) f' = Some tbl
                    /\ map.get tbl args' = Some r
                    /\ EGraph.Defs.entry_value _ _ r = out')
        (f := process_row f0)
        (r0 := acc)).
      + (* Inner base: acc' = acc (unchanged), tbl_partial = empty *)
        intros out' f' args' Hget.
        destruct (IH_outer out' f' args' Hget) as (tbl & r & H1 & H2 & H3).
        exists tbl, r. split; [|split; [exact H2|exact H3]].
        (* map.get (put db_partial f0 empty) f' = Some tbl *)
        (* We know map.get db_partial f' = Some tbl, and f' ≠ f0
           (because map.get db_partial f0 = None from Hnotf0, and f0 ↦ tbl0 fresh,
            so if f' = f0 then map.get db_partial f' = None ≠ Some tbl) *)
        destruct (eqb_spec f' f0) as [Heq|Hne].
        * subst f'. rewrite Hnotf0 in H1. discriminate.
        * rewrite map.get_put_diff; [exact H1|exact Hne].
      + (* Inner step: visiting (args0, row0), tbl_partial → put tbl_partial args0 row0 *)
        intros args0 row0 tbl_partial acc' Hnot_args0 IH_inner.
        unfold process_row.
        destruct (map.get analyses (EGraph.Defs.entry_value _ _ row0)) as [a|] eqn:Hanalysis.
        * destruct (le (EGraph.Defs.entry_analysis _ _ row0) a) eqn:Hle.
          -- (* put branch: map.put acc' (entry_value row0) (f0, args0) *)
             intros out' f' args' Hget'.
             destruct (eqb_spec out' (EGraph.Defs.entry_value _ _ row0)) as [Heq|Hne].
             ++ (* out' = entry_value row0 *)
                subst out'.
                rewrite map.get_put_same in Hget'.
                injection Hget'; intros Hargs_eq Hf_eq; subst f' args'.
                exists (map.put tbl_partial args0 row0), row0.
                split; [|split; [|reflexivity]].
                ** apply map.get_put_same.
                ** apply map.get_put_same.
             ++ (* out' ≠ entry_value row0 *)
                rewrite map.get_put_diff in Hget'; [|exact Hne].
                destruct (IH_inner out' f' args' Hget') as (tbl & r & H1 & H2 & H3).
                exists tbl, r. split; [|split; [exact H2|exact H3]].
                (* map.get (put db_partial f0 (put tbl_partial args0 row0)) f' = Some tbl
                   from: map.get (put db_partial f0 tbl_partial) f' = Some tbl
                   Since: put (put db_partial f0 tbl_partial) ≠ put (put db_partial f0 (put tbl_p args0 row0))
                   for f' ... we need to connect these.
                   If f' = f0: both give the tbl_partial or put tbl_partial args0 row0.
                   If f' ≠ f0: both give map.get db_partial f'. *)
                destruct (eqb_spec f' f0) as [Heq|Hne2].
                ** subst f'.
                   rewrite map.get_put_same in H1. injection H1; intro; subst tbl.
                   rewrite map.get_put_same. reflexivity.
                ** rewrite map.get_put_diff; [|exact Hne2].
                   rewrite map.get_put_diff in H1; [exact H1|exact Hne2].
          -- (* no-put branch, use IH_inner *)
             intros out' f' args' Hget'.
             destruct (IH_inner out' f' args' Hget') as (tbl & r & H1 & H2 & H3).
             exists tbl, r. split; [|split; [exact H2|exact H3]].
             destruct (eqb_spec f' f0) as [Heq|Hne].
             ++ subst f'.
                rewrite map.get_put_same in H1. injection H1; intro; subst tbl.
                rewrite map.get_put_same. reflexivity.
             ++ rewrite map.get_put_diff; [|exact Hne].
                rewrite map.get_put_diff in H1; [exact H1|exact Hne].
        * (* no-put branch, use IH_inner *)
          intros out' f' args' Hget'.
          destruct (IH_inner out' f' args' Hget') as (tbl & r & H1 & H2 & H3).
          exists tbl, r. split; [|split; [exact H2|exact H3]].
          destruct (eqb_spec f' f0) as [Heq|Hne].
          ++ subst f'.
             rewrite map.get_put_same in H1. injection H1; intro; subst tbl.
             rewrite map.get_put_same. reflexivity.
          ++ rewrite map.get_put_diff; [|exact Hne].
             rewrite map.get_put_diff in H1; [exact H1|exact Hne].
    - (* Apply the full invariant: P db (fold process_table empty db).
         But fold_spec gives P m (fold f r0 m) for any m; so we get
         P db (fold process_table empty db).
         Then use the hypothesis that map.get (fold ...) out = Some (f, args). *)
      (* Wait - actually fold_spec's conclusion is: forall m, P m (fold f r0 m)
         So after applying fold_spec, we get:
         - a goal for the base case
         - a goal for the step case
         Then the overall goal is proved by applying fold_spec to db.
         But we need to apply fold_spec and use the result.

         Hmm, looking at the structure more carefully: map.fold_spec returns
         P m (fold f r0 m) for all m. But we're using `apply` so it matches
         the goal. Let me reconsider the goal structure.

         The goal is: map.get (map.fold process_table map.empty db) out = Some (f, args) ->
                       exists tbl r, ...

         If I `apply map.fold_spec`, it would try to unify the goal with
         `P m (fold f r0 m)` which doesn't match.

         I need to first get the invariant about the fold result, then use it.
         Let me use `pose proof` instead. *)
      exact TODO.
  Admitted.

End WithVar.
