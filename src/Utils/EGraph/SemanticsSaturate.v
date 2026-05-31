(* Saturation soundness (run1iter / saturate_until), split out of Semantics.v
   (Section WithMap) to keep that file smaller.  The internal lemmas live in a
   local Section with the egraph+model context; run1iter_rule_hyps and
   saturate_until_sound keep their exact section-closed signatures (explicit
   ctx) for the Theorems-side scheduled-saturation soundness. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics.
Import Monad.StateMonad.

Section Slice.
  Context
    {idx : Type}
    {Eqb_idx : Eqb idx}
    {Eqb_idx_ok : Eqb_ok Eqb_idx}
    {lt : idx -> idx -> Prop}
    {idx_succ : idx -> idx}
    {idx_zero : WithDefault idx}
    {symbol : Type}
    {Eqb_symbol : Eqb symbol}
    {Eqb_symbol_ok : Eqb_ok Eqb_symbol}
    {symbol_map : forall A, map.map symbol A}
    {symbol_map_plus : map_plus symbol_map}
    {symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus}
    {symbol_map_ok : forall A, map.ok (symbol_map A)}
    {idx_map : forall A, map.map idx A}
    {idx_map_plus : map_plus idx_map}
    {idx_map_ok : forall A, map.ok (idx_map A)}
    {idx_trie : forall A, map.map (list idx) A}
    {idx_trie_ok : forall A, map.ok (idx_trie A)}
    {idx_trie_plus : map_plus idx_trie}
    {analysis_result : Type}
    {idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus}
    {H : analysis idx symbol analysis_result}
    {spaced_list_intersect
      : forall B, WithDefault B -> (B -> B -> B) ->
                  ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B)}
    {m : model symbol}
    {Hm : model_ok symbol m}.

  Existing Instance idx_zero.

  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).

  Notation egraph_ok := (egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_sound_for_interpretation :=
    (egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m).

  (* increment_epoch_preserves *)
  Lemma increment_epoch_preserves (e : instance) :
    (egraph_ok e -> egraph_ok (snd (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e)))
    /\ (forall i, egraph_sound_for_interpretation i e -> egraph_sound_for_interpretation i (snd (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e))).
  Proof.
    destruct e as [db equiv parents epoch worklist analyses log].
    cbn [increment_epoch snd].
    split.
    - intro Hok; destruct Hok as [Heq Hwl Hp Hdb]; constructor; assumption.
    - intros i Hs; destruct Hs as [Hwf Hex Hai Hrel]; constructor; assumption.
  Qed.

  (* run1iter_rule_hyps — external, explicit ctx binders *)
  Definition run1iter_rule_hyps
    (idx : Type) (Eqb_idx : Eqb idx) (idx_zero : WithDefault idx)
    (symbol : Type) (symbol_map : forall A, map.map symbol A)
    (symbol_map_plus : map_plus symbol_map)
    (idx_map : forall A, map.map idx A) (idx_map_plus : map_plus idx_map)
    (idx_trie : forall A, map.map (list idx) A) (analysis_result : Type)
    (spaced_list_intersect
      : forall B, WithDefault B -> (B -> B -> B) ->
                  ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B))
    (m : model symbol)
    (q : rule_set idx symbol symbol_map idx_map)
    (inst : Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result)
    (r : erule idx symbol) : Prop :=
    let db_tries := fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                           idx_map idx_map_plus idx_trie analysis_result q inst) in
    List.NoDup (query_vars idx symbol r)
    /\ List.NoDup (write_vars idx symbol r)
    /\ erule_sound idx idx_zero symbol symbol_map idx_map m (query_clauses idx symbol symbol_map idx_map q) r
    /\ (forall fsym nptr cvars,
         In (Build_erule_query_ptr idx symbol fsym nptr cvars)
            (uncurry cons (query_clause_ptrs idx symbol r)) ->
         exists q_f cargs cv (Pf : idx -> bool),
           map.get (query_clauses idx symbol symbol_map idx_map q) fsym = Some q_f
           /\ map.get q_f nptr = Some (cargs, cv)
           /\ cvars = filter Pf (query_vars idx symbol r)
           /\ (forall t, In t cargs -> t < List.length cvars)
           /\ cv < List.length cvars)
    /\ (forall x, In x (query_vars idx symbol r) ->
         exists a, In a (query_atoms idx idx_zero symbol symbol_map idx_map (query_clauses idx symbol symbol_map idx_map q) r)
                   /\ In x (atom_ret a :: atom_args a))
    /\ (forall x, In x (write_vars idx symbol r) -> ~ In x (query_vars idx symbol r))
    /\ (forall c, In c (write_clauses idx symbol r) ->
          forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
          In x (query_vars idx symbol r) \/ In x (write_vars idx symbol r))
    /\ (forall p, In p (write_unifications idx symbol r) ->
          (In (fst p) (query_vars idx symbol r) \/ In (fst p) (write_vars idx symbol r))
          /\ (In (snd p) (query_vars idx symbol r) \/ In (snd p) (write_vars idx symbol r)))
    /\ (forall frontier_n sigma,
         In sigma (intersection_keys idx idx_trie spaced_list_intersect
                     (ne_map (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                                (query_vars idx symbol r) db_tries frontier_n)
                             (query_clause_ptrs idx symbol r))) ->
         List.length (query_vars idx symbol r) = List.length sigma)
    /\ (forall frontier_n sigma,
         In sigma (intersection_keys idx idx_trie spaced_list_intersect
                     (ne_map (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                                (query_vars idx symbol r) db_tries frontier_n)
                             (query_clause_ptrs idx symbol r))) ->
         forall fsym nptr cvars,
         In (Build_erule_query_ptr idx symbol fsym nptr cvars)
            (uncurry cons (query_clause_ptrs idx symbol r)) ->
         map.get (fst (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                         (query_vars idx symbol r) db_tries frontier_n
                         (Build_erule_query_ptr idx symbol fsym nptr cvars)))
                 (map fst (filter snd (combine sigma
                    (variable_flags idx Eqb_idx (query_vars idx symbol r) cvars))))
         = Some tt).

  (* run1iter_sound — internal, implicit ctx *)
  Lemma run1iter_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (rebuild_fuel : nat)
    (i_0 : idx_map (domain symbol m))
    (rs : rule_set idx symbol symbol_map idx_map)
    (e_0 : instance) :
    egraph_ok e_0 ->
    egraph_sound_for_interpretation i_0 e_0 ->
    (forall r, In r (compiled_rules idx symbol symbol_map idx_map rs) ->
       run1iter_rule_hyps idx Eqb_idx idx_zero symbol symbol_map symbol_map_plus
         idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect m rs e_0 r) ->
    match Defs.run1iter idx Eqb_idx idx_succ idx_zero symbol symbol_map symbol_map_plus
            idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect rebuild_fuel rs e_0 with
    | (_, e') => egraph_ok e' /\ exists i', map.extends i' i_0 /\ egraph_sound_for_interpretation i' e'
    end.
  Proof.
    intros Hok_0 Hsnd_0 Hrules.
    unfold Defs.run1iter.
    cbn [Mbind Mseq Mret StateMonad.state_monad].
    destruct (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus idx_map idx_map_plus idx_trie analysis_result rs e_0) as [tries e0'] eqn:Hbt.
    unfold build_tries in Hbt. inversion Hbt as [ [Htries He0'] ]. subst e0'.
    cbn [max_id worklist_empty].
    clear Hbt Htries tries.
    destruct (increment_epoch idx idx_succ symbol symbol_map idx_map idx_trie analysis_result e_0) as [u1 e_1] eqn:Hie.
    pose proof (increment_epoch_preserves e_0) as [Hok1f Hs1f].
    rewrite Hie in Hok1f, Hs1f. cbn [snd] in Hok1f, Hs1f.
    specialize (Hok1f Hok_0).
    set (db_tries := fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus idx_map idx_map_plus idx_trie analysis_result rs e_0)).
    change (map_intersect (build_tries_for_symbol idx Eqb_idx idx_map idx_map_plus idx_trie analysis_result (epoch e_0)) (query_clauses idx symbol symbol_map idx_map rs) (db e_0)) with db_tries.
    pose proof (Hs1f i_0 Hsnd_0) as Hsnd_1.
    assert (Hloop : forall rules e_cur i_cur,
      (forall r, In r rules -> run1iter_rule_hyps idx Eqb_idx idx_zero symbol symbol_map symbol_map_plus
                                  idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect m rs e_0 r) ->
      egraph_ok e_cur -> egraph_sound_for_interpretation i_cur e_cur -> map.extends i_cur i_0 ->
      match list_Miter (process_erule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries) rules e_cur with
      | (_, e') => egraph_ok e' /\ exists i', map.extends i' i_0 /\ egraph_sound_for_interpretation i' e'
      end).
    { induction rules as [|r rules' IH]; intros e_cur i_cur Hrh Hok_cur Hsnd_cur Hext_cur.
      - cbn [list_Miter]. split; [exact Hok_cur|].
        exists i_cur; split; [exact Hext_cur | exact Hsnd_cur].
      - cbn [list_Miter Mseq Mbind StateMonad.state_monad].
        assert (Hin : In r (r :: rules')) by (left; reflexivity).
        pose proof (Hrh r Hin) as Hrhr.
        destruct Hrhr as (Hnd_qv & Hnd_wv & Hrule & Hwf & Hcov & Hdisj & HcovC & HcovU & Hlen & Hsli).
        pose proof (@process_erule_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_plus symbol_map_plus_ok symbol_map_ok idx_map idx_map_plus idx_map_ok idx_trie idx_trie_ok analysis_result idx_map_plus_ok spaced_list_intersect H m Hm Hlti Hlts Hltt i_0 i_cur e_0 rs r e_cur Hsnd_0 Hok_cur Hsnd_cur Hext_cur Hnd_qv Hnd_wv Hrule Hwf Hcov Hdisj HcovC HcovU Hlen Hsli) as Hpe.
        fold db_tries in Hpe.
        destruct (process_erule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries r e_cur) as [u e_mid] eqn:Hpe_eq.
        destruct Hpe as (Hok_mid & i_mid & Hext_mid & Hsnd_mid).
        assert (Hrh' : forall r0, In r0 rules' -> run1iter_rule_hyps idx Eqb_idx idx_zero symbol symbol_map symbol_map_plus
                                                     idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect m rs e_0 r0) by (intros r0 Hr0; apply Hrh; right; exact Hr0).
        pose proof (IH e_mid i_mid Hrh' Hok_mid Hsnd_mid Hext_mid) as HIH.
        destruct (list_Miter (process_erule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries) rules' e_mid) as [u2 e'] eqn:Hlm.
        exact HIH. }
    assert (Hrefl : map.extends i_0 i_0) by apply Properties.map.extends_refl.
    pose proof (Hloop (compiled_rules idx symbol symbol_map idx_map rs) e_1 i_0 Hrules Hok1f Hsnd_1 Hrefl) as Hrl.
    destruct (list_Miter (process_erule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries) (compiled_rules idx symbol symbol_map idx_map rs) e_1) as [u_loop e_2] eqn:Hlm.
    destruct Hrl as (Hok_2 & i_2 & Hext_2 & Hsnd_2).
    pose proof (@rebuild_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result H m Hm (fun _ => True) rebuild_fuel e_2) as Hrb.
    specialize (Hrb Hok_2). destruct Hrb as (Hok_3 & Hde).
    destruct (rebuild rebuild_fuel e_2) as [u3 e_3] eqn:Hrbeq.
    cbn [snd] in Hok_3, Hde.
    split; [exact Hok_3|].
    exists i_2. split; [exact Hext_2|].
    apply (proj1 (Hde i_2)). exact Hsnd_2.
  Qed.

  (* saturate_until'_sound — internal, implicit ctx *)
  Lemma saturate_until'_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (rebuild_fuel : nat)
    (rs : rule_set idx symbol symbol_map idx_map)
    (P : state instance bool)
    (HP : forall e i, egraph_ok e -> egraph_sound_for_interpretation i e ->
            egraph_ok (snd (P e)) /\ egraph_sound_for_interpretation i (snd (P e)))
    (Hrules : forall e r, In r (compiled_rules idx symbol symbol_map idx_map rs) ->
       run1iter_rule_hyps idx Eqb_idx idx_zero symbol symbol_map symbol_map_plus
         idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect m rs e r)
    (fuel : nat) :
    forall (i_0 : idx_map (domain symbol m)) (e_0 : instance),
    egraph_ok e_0 ->
    egraph_sound_for_interpretation i_0 e_0 ->
    match Defs.saturate_until' idx_succ idx_zero spaced_list_intersect rebuild_fuel rs P fuel e_0 with
    | (_, e') => egraph_ok e' /\ exists i', map.extends i' i_0 /\ egraph_sound_for_interpretation i' e'
    end.
  Proof.
    induction fuel as [|fuel IH]; intros i_0 e_0 Hok_0 Hsnd_0.
    - cbn [Defs.saturate_until' Mret StateMonad.state_monad].
      split; [exact Hok_0|]. exists i_0. split; [apply Properties.map.extends_refl | exact Hsnd_0].
    - cbn [Defs.saturate_until'].
      cbn [Mbind Mret StateMonad.state_monad].
      pose proof (HP e_0 i_0 Hok_0 Hsnd_0) as [HokP HsndP].
      destruct (P e_0) as [doneP eP] eqn:HPe.
      cbn [snd] in HokP, HsndP.
      destruct doneP.
      { split; [exact HokP|]. exists i_0. split; [apply Properties.map.extends_refl | exact HsndP]. }
      pose proof (run1iter_sound Hlti Hlts Hltt rebuild_fuel i_0 rs eP HokP HsndP (fun r Hr => Hrules eP r Hr)) as Hri.
      destruct (Defs.run1iter idx Eqb_idx idx_succ idx_zero symbol symbol_map symbol_map_plus idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect rebuild_fuel rs eP) as [nc e2] eqn:Hru.
      destruct Hri as (Hok2 & i_1 & Hext1 & Hsnd2).
      destruct nc.
      { split; [exact Hok2|]. exists i_1. split; [exact Hext1 | exact Hsnd2]. }
      pose proof (IH i_1 e2 Hok2 Hsnd2) as HIH.
      destruct (saturate_until' idx_succ idx_zero spaced_list_intersect rebuild_fuel rs P fuel e2) as [b e_final] eqn:Hsat.
      destruct HIH as (Hok_final & i_f & Hext_f & Hsnd_final).
      split; [exact Hok_final|]. exists i_f.
      split; [eapply map_extends_trans; [exact Hext_f | exact Hext1] | exact Hsnd_final].
  Qed.

End Slice.

(* saturate_until_sound — external, explicit ctx binders, top level *)
Lemma saturate_until_sound
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (Eqb_symbol : Eqb symbol) (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
  (symbol_map : forall A, map.map symbol A) (symbol_map_plus : map_plus symbol_map)
  (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus)
  (symbol_map_ok : forall A, map.ok (symbol_map A))
  (idx_map : forall A, map.map idx A) (idx_map_plus : map_plus idx_map)
  (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A)
  (idx_trie_ok : forall A, map.ok (idx_trie A))
  (analysis_result : Type)
  (idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus)
  (spaced_list_intersect
    : forall B, WithDefault B -> (B -> B -> B) ->
                ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B))
  (H : analysis idx symbol analysis_result)
  (m : model symbol)
  (Hm : model_ok symbol m)
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  (rebuild_fuel : nat)
  (rs : rule_set idx symbol symbol_map idx_map)
  (P : state (Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result) bool)
  (HP : forall e i, Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
          Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result (snd (P e))
          /\ Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i (snd (P e)))
  (Hconst : forall e i, Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
          Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result (snd (process_const_rules idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result rs e))
          /\ exists i', map.extends i' i /\ Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i' (snd (process_const_rules idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result rs e)))
  (Hrules : forall e r, In r (compiled_rules idx symbol symbol_map idx_map rs) ->
     run1iter_rule_hyps idx Eqb_idx idx_zero symbol symbol_map symbol_map_plus
       idx_map idx_map_plus idx_trie analysis_result spaced_list_intersect m rs e r)
  (fuel : nat)
  (i_0 : idx_map (domain symbol m)) (e_0 : Defs.instance idx symbol symbol_map idx_map idx_trie analysis_result) :
  Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_0 ->
  Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i_0 e_0 ->
  match Defs.saturate_until idx_succ idx_zero spaced_list_intersect rebuild_fuel rs P fuel e_0 with
  | (_, e') => Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e'
               /\ exists i', map.extends i' i_0 /\ Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i' e'
  end.
Proof.
  intros Hok_0 Hsnd_0.
  unfold Defs.saturate_until.
  cbn [Mseq Mbind StateMonad.state_monad].
  pose proof (Hconst e_0 i_0 Hok_0 Hsnd_0) as Hc.
  destruct (process_const_rules idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result rs e_0) as [u_c e_a] eqn:Hpc.
  cbn [snd] in Hc.
  destruct Hc as (Hok_a & i_a & Hext_a & Hsnd_a).
  pose proof (@rebuild_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result H m Hm (fun _ => True) rebuild_fuel e_a) as Hrb.
  specialize (Hrb Hok_a). destruct Hrb as (Hok_b & Hde).
  destruct (rebuild rebuild_fuel e_a) as [u_b e_b] eqn:Hrbeq.
  cbn [snd] in Hok_b, Hde.
  pose proof (proj1 (Hde i_a) Hsnd_a) as Hsnd_b.
  pose proof (saturate_until'_sound (spaced_list_intersect:=spaced_list_intersect) (m:=m) Hlti Hlts Hltt rebuild_fuel rs P HP Hrules fuel i_a e_b Hok_b Hsnd_b) as Hsat.
  destruct (saturate_until' idx_succ idx_zero spaced_list_intersect rebuild_fuel rs P fuel e_b) as [b e_final] eqn:Hsf.
  destruct Hsat as (Hok_f & i_f & Hext_f & Hsnd_f).
  split; [exact Hok_f|]. exists i_f.
  split; [eapply map_extends_trans; [exact Hext_f | exact Hext_a] | exact Hsnd_f].
Qed.
