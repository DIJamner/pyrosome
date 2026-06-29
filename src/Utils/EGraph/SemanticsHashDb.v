From Stdlib Require Import Lists.List Classes.RelationClasses.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

(* [hash_entry] reverse characterisation: any atom in the result db is either
   the newly inserted atom [Build_atom f args (fst res)] or was already present
   in the input db.  Only needs all-root args and a union-find-ok witness
   (no rank/db_inv hypotheses). *)
Section HashDbReverse.

Context
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (Eqb_symbol : Eqb symbol) (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
  (symbol_map : forall A, map.map symbol A)
  (symbol_map_plus : map_plus symbol_map)
  (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus)
  (symbol_map_ok : forall A, map.ok (symbol_map A))
  (idx_map : forall A, map.map idx A)
  (idx_map_plus : map_plus idx_map)
  (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A)
  (idx_trie_ok : forall A, map.ok (idx_trie A))
  (idx_trie_plus : map_plus idx_trie)
  (analysis_result : Type)
  (HA : analysis idx symbol analysis_result).

Existing Instance idx_zero.
Existing Instance HA.

Notation instance :=
  (instance idx symbol symbol_map idx_map idx_trie analysis_result).
Notation atom_in_db :=
  (atom_in_db idx symbol symbol_map idx_trie analysis_result).
Notation union_find_ok :=
  (union_find_ok lt).

Lemma hash_entry_db_reverse
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  (f : symbol) (args : list idx)
  : vc (hash_entry idx_succ f args)
      (fun e_in res =>
         (exists roots, union_find_ok e_in.(equiv) roots) ->
         all (fun x => map.get e_in.(equiv).(parent) x = Some x) args ->
         forall b,
           atom_in_db b (snd res).(db) ->
           b = Build_atom f args (fst res)
           \/ atom_in_db b e_in.(db)).
Proof.
  unfold vc, hash_entry.
  intros e_in.
  cbn [Mbind StateMonad.state_monad].
  intros Hroots_ex Hargs_roots.
  rewrite (list_Mmap_find_roots_identity idx Eqb_idx Eqb_idx_ok symbol symbol_map
             idx_map idx_trie analysis_result args e_in Hargs_roots).
  cbn [fst snd].
  pose proof (db_lookup_pure idx symbol symbol_map idx_map idx_trie analysis_result
                f args e_in) as Hlk.
  cbn beta in Hlk.
  destruct (db_lookup idx symbol symbol_map idx_map idx_trie analysis_result f args e_in)
    as [mout e_lk] eqn:Hlkeq.
  cbn [fst snd] in Hlk |- *.
  destruct Hlk as [He_eq Hlk2]. subst e_lk.
  destruct mout as [r|]; cbn beta iota; cbn [fst snd].
  - (* Hit case: db unchanged, Mret r *)
    cbn [Mret StateMonad.state_monad fst snd].
    intros b Hb. right. exact Hb.
  - (* Miss case: alloc r then db_set inserts (f, args, r) *)
    cbn [Mbind StateMonad.state_monad].
    destruct Hroots_ex as [roots Hroots].
    pose proof (alloc_struct idx Eqb_idx Eqb_idx_ok lt idx_succ symbol symbol_map
                  idx_map idx_map_ok idx_trie analysis_result Hlti Hlts Hltt) as Halloc.
    unfold vc in Halloc. specialize (Halloc e_in).
    destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e_in)
      as [r e_alloc] eqn:Halloc_eq.
    cbn [fst snd] in Halloc.
    specialize (Halloc roots Hroots).
    destruct Halloc as (Hok_alloc & Hr_fresh & Hr_key & Hkeys_alloc & Hdb_alloc
                        & Hpar_alloc & Hwl_alloc).
    (* Peel db_set *)
    unfold db_set. cbn [atom_fn atom_args atom_ret].
    cbn [Mbind StateMonad.state_monad fst snd].
    pose proof (get_analyses_preserves_fields idx lt idx_succ idx_zero symbol symbol_map
                  idx_map idx_trie analysis_result args e_alloc) as Hga.
    destruct (get_analyses idx symbol symbol_map idx_map idx_trie
                analysis_result args e_alloc) as [arg_as e_ga] eqn:Hge.
    cbn [fst snd] in Hga. destruct Hga as (Hdb_ga & Heq_ga & Hpa_ga).
    destruct (update_analyses idx symbol symbol_map idx_map idx_trie
                analysis_result r
                (analyze idx symbol analysis_result (Build_atom f args r) arg_as)
                e_ga) as [_u e_ua] eqn:Hue.
    assert (Hdb_ua : e_ua.(db) = e_ga.(db))
      by (unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; reflexivity).
    destruct (db_set' idx Eqb_idx symbol symbol_map idx_map idx_trie
                analysis_result (Build_atom f args r)
                (analyze idx symbol analysis_result (Build_atom f args r) arg_as)
                e_ua) as [_v e_db] eqn:Hde.
    cbn [fst snd]. unfold Mret. cbn [StateMonad.state_monad fst snd].
    unfold db_set' in Hde; injection Hde as _ Hde'; subst e_db.
    (* db chain: e_ua.db = e_ga.db = e_alloc.db = e_in.db *)
    assert (Hdb_chain : e_ua.(db) = e_in.(db)) by congruence.
    intros b Hb.
    (* Case analysis on map_update *)
    unfold atom_in_db, Is_Some_satisfying, map_update in Hb; cbn in Hb.
    destruct b as [bfn bargs bret]; cbn in Hb.
    destruct (map.get e_ua.(db) f) as [tbl|] eqn:Htbl.
    + (* f already had a table in e_ua.db *)
      eqb_case bfn f.
      * (* bfn = f *)
        rewrite map.get_put_same in Hb; cbn in Hb.
        eqb_case bargs args.
        -- (* bargs = args: new atom *)
           rewrite map.get_put_same in Hb; cbn in Hb.
           left. subst. reflexivity.
        -- (* bargs <> args: old atom *)
           rewrite map.get_put_diff in Hb by auto.
           right. unfold atom_in_db, Is_Some_satisfying; cbn.
           rewrite <- Hdb_chain. rewrite Htbl. cbn. exact Hb.
      * (* bfn <> f: unaffected *)
        rewrite map.get_put_diff in Hb by auto.
        right. unfold atom_in_db, Is_Some_satisfying; cbn.
        rewrite <- Hdb_chain. exact Hb.
    + (* f had no table: fresh table created *)
      eqb_case bfn f.
      * (* bfn = f *)
        rewrite map.get_put_same in Hb; cbn in Hb.
        eqb_case bargs args.
        -- (* bargs = args: new atom *)
           rewrite map.get_put_same in Hb; cbn in Hb.
           left. subst. reflexivity.
        -- (* bargs <> args: fresh table has only args key, so None *)
           rewrite map.get_put_diff in Hb by auto.
           unfold default in Hb.
           rewrite map.get_empty in Hb. cbn in Hb. destruct Hb.
      * (* bfn <> f: unaffected *)
        rewrite map.get_put_diff in Hb by auto.
        right. unfold atom_in_db, Is_Some_satisfying; cbn.
        rewrite <- Hdb_chain. exact Hb.
Qed.

End HashDbReverse.
