(* The F1c survival cluster, split out of Semantics.v (Section WithMap).
   rebuild_success_iff_drained / canonical_uptoequiv_present / L_survive_canonical'
   are 0-axiom; L_survive_canonical is the project's single intentional Admitted
   axiom (consumed by Theorems' rebuild_survives_canonical) -- ISOLATED HERE so the
   one admit lives in its own file.  See [[project-l-survive-canonical]]. *)
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
    {symbol_map : forall A, map.map symbol A} {symbol_map_plus : map_plus symbol_map}
    {symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus} {symbol_map_ok : forall A, map.ok (symbol_map A)}
    {idx_map : forall A, map.map idx A} {idx_map_plus : map_plus idx_map} {idx_map_ok : forall A, map.ok (idx_map A)}
    {idx_trie : forall A, map.map (list idx) A} {idx_trie_ok : forall A, map.ok (idx_trie A)} {idx_trie_plus : map_plus idx_trie}
    {analysis_result : Type} {idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus}
    {spaced_list_intersect : forall B, WithDefault B -> (B -> B -> B) -> ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B)}
    {H : analysis idx symbol analysis_result} {m : model symbol} {Hm : model_ok symbol m}.
  Existing Instance idx_zero.
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_ok := (egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result).
  Notation atom := (atom idx symbol).
  Notation db_inv := (db_inv idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation db_injective := (db_injective idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation atom_in_egraph_up_to_equiv := (atom_in_egraph_up_to_equiv idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_equiv_ok := (egraph_equiv_ok idx lt symbol symbol_map idx_map idx_trie analysis_result).
  Notation rebuild_survives_side :=
    (rebuild_survives_side idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero
       symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok
       idx_map idx_map_ok idx_trie idx_trie_ok analysis_result m).

  (* [rebuild] returns [Success tt] exactly when it drained the worklist:
     a successful run terminated on the empty-worklist branch, so the
     resulting instance has an empty worklist. *)
  (* A fully-canonical atom (all-root args + root ret) that is present
     [up_to_equiv] in a [db_inv]-well-rooted egraph is present verbatim:
     the canonically-equivalent db witness [a'] has, by [db_inv], all-root
     args and (under the trivial guard) a root ret, so each PER-pair of
     roots is an equality ([roots_uf_rel_eq]); hence [a = a']. *)
  Lemma canonical_uptoequiv_present (e : instance) (a : atom)
    : egraph_ok e ->
      db_inv (fun _ => True) e ->
      atom_in_egraph_up_to_equiv a e ->
      all (fun x => map.get e.(equiv).(parent) x = Some x) a.(atom_args) ->
      map.get e.(equiv).(parent) a.(atom_ret) = Some a.(atom_ret) ->
      atom_in_egraph a e.
  Proof.
    intros Hok Hinv Hup Hargs Hret.
    unfold atom_in_egraph in *.
    unfold atom_in_egraph_up_to_equiv in Hup.
    destruct Hup as (aw & Hceq & Hin').
    pose proof (egraph_equiv_ok _ Hok) as Heq0.
    destruct Heq0 as (roots & Huf).
    pose proof (Hinv aw Hin') as Hinvaw.
    destruct Hinvaw as (Hargs' & Hret').
    specialize (Hret' I).
    unfold atom_canonical_equiv in Hceq.
    destruct Hceq as (Hf & Hall2 & Hretrel).
    assert (Hreteq : atom_ret a = atom_ret aw).
    { eapply roots_uf_rel_eq; eauto. }
    assert (Hargseq : atom_args a = atom_args aw).
    { revert Hall2 Hargs Hargs'.
      generalize (atom_args a) as la.
      generalize (atom_args aw) as lb.
      intro lb; induction lb as [|hb tb IHb]; intros la Hall2 Hra Hrb.
      - destruct la; cbn in Hall2; [ reflexivity | contradiction ].
      - destruct la as [|ha ta]; cbn in Hall2; [ contradiction | ].
        destruct Hall2 as [Hh Ht].
        cbn in Hra, Hrb.
        destruct Hra as [Hrha Hrta].
        destruct Hrb as [Hrhb Hrtb].
        f_equal.
        + eapply roots_uf_rel_eq; eauto.
        + apply IHb; assumption. }
    destruct a as [fa arga reta]; destruct aw as [fb argb retb]; cbn in *.
    subst. exact Hin'.
  Qed.

  (* L_survive_canonical' — the REDUCED survival lemma = (T) [rebuild_survives_side]
     composed with (F) [canonical_uptoequiv_present].  Instead of [db_injective e]
     + canonicality wrt [e] (the FALSE-at-n=0 form), it asks for [db_inv (fun _ =>
     True)] of the REBUILT egraph [eF := snd (rebuild n e)] and canonicality
     (all-root args + root ret) wrt [eF].  (T) transports [a]'s up-to-equiv
     presence from [e] to [eF] (and gives [egraph_ok eF]); (F) then materialises
     the verbatim canonical [a] in [eF].  The caller (add_ctx discharge) supplies
     [db_inv (True) eF] and the eF-canonicality from the known add_ctx structure. *)
  Lemma L_survive_canonical' n (e : instance) (a : atom)
    : egraph_ok e ->
      atom_in_egraph_up_to_equiv a e ->
      db_inv (fun _ => True) (snd (rebuild n e)) ->
      all (fun x => map.get (snd (rebuild n e)).(equiv).(parent) x = Some x) a.(atom_args) ->
      map.get (snd (rebuild n e)).(equiv).(parent) a.(atom_ret) = Some a.(atom_ret) ->
      atom_in_egraph a (snd (rebuild n e)).
  Proof.
    intros Hok Hup Hinv Hargs Hret.
    destruct (rebuild_survives_side (a :: nil) n e Hok (conj Hup I)) as [Hok_F Hall_F].
    cbn [all] in Hall_F. destruct Hall_F as [Hup_F _].
    eapply canonical_uptoequiv_present;
      [exact Hok_F | exact Hinv | exact Hup_F | exact Hargs | exact Hret].
  Qed.

End Slice.

(* NOTE: the former [L_survive_canonical] axiom (Admitted) was ELIMINATED.
   Its sole consumer [rebuild_survives_canonical] (Theorems.v) is now
   derived 0-axiom from [rebuild_canon] + [L_survive_canonical'] using the
   [good_worklist] witness established by [add_ctx_good_worklist]. *)
