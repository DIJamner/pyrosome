(* process_erule / query-atom soundness, split out of Semantics.v (Section
   WithMap) to keep that file smaller.  Internal lemmas live in a local Section
   with the egraph+model context; process_erule_sound keeps its exact
   section-closed signature, consumed by SemanticsSaturate. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics SemanticsUtil.
Import Monad.StateMonad.

Section Slice.
  Context
    {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}
    {lt : idx -> idx -> Prop} {idx_succ : idx -> idx} {idx_zero : WithDefault idx}
    {symbol : Type} {Eqb_symbol : Eqb symbol} {Eqb_symbol_ok : Eqb_ok Eqb_symbol}
    {symbol_map : forall A, map.map symbol A} {symbol_map_plus : map_plus symbol_map}
    {symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus} {symbol_map_ok : forall A, map.ok (symbol_map A)}
    {idx_map : forall A, map.map idx A} {idx_map_plus : map_plus idx_map} {idx_map_ok : forall A, map.ok (idx_map A)}
    {idx_trie : forall A, map.map (list idx) A} {idx_trie_ok : forall A, map.ok (idx_trie A)}
    {analysis_result : Type} {idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus}
    {spaced_list_intersect
      : forall B, WithDefault B -> (B -> B -> B) -> ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B)}
    {H : analysis idx symbol analysis_result} {m : model symbol} {Hm : model_ok symbol m}.
  Existing Instance idx_zero.
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_ok := (egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_sound_for_interpretation := (egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m).
  Notation atom_sound_for_model := (atom_sound_for_model idx symbol idx_map).
  Notation atom_interpretation := (atom_interpretation idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation idx_interpretation_wf := (idx_interpretation_wf idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation interpretation_exact := (interpretation_exact idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation clause_ptr_atom_in_db := (clause_ptr_atom_in_db idx Eqb_idx Eqb_idx_ok symbol symbol_map symbol_map_plus symbol_map_plus_ok idx_map idx_map_plus idx_trie idx_trie_ok analysis_result idx_map_plus_ok).
  Notation match_clause_correct := (match_clause_correct idx Eqb_idx Eqb_idx_ok).
  Notation project_filter_variable_flags := (project_filter_variable_flags idx Eqb_idx Eqb_idx_ok).
  Notation get_of_list_combine := (get_of_list_combine idx Eqb_idx Eqb_idx_ok idx_map idx_map_ok).
  Notation named_list_lookup_assign_sub := (named_list_lookup_assign_sub idx).
  Notation assign_sub := (assign_sub idx).
  Notation compose_assignment := (compose_assignment idx symbol idx_map m).
  Notation get_compose_assignment := (get_compose_assignment idx Eqb_idx Eqb_idx_ok symbol idx_map idx_map_ok m).
  Notation get_of_list_none := (get_of_list_none idx Eqb_idx Eqb_idx_ok idx_map idx_map_ok).
  Notation get_of_list_in_keys := (get_of_list_in_keys idx Eqb_idx Eqb_idx_ok idx_map idx_map_ok).

  (* Soundness of one reconstructed query atom: if the intersection key
     [sigma] hits the clause trie for pointer (f,n,clause_vars), then the
     matched DB atom (sound under [i]) witnesses that the logical query
     atom [f(clause_vars[cargs]) = clause_vars[cv]] is sound under the
     model assignment [a_q = i o env0]. [a_q] is abstract here, specified
     only by its bind-relationship to [env0 = of_list (combine query_vars
     sigma)]; process_erule'_sound supplies a concrete [a_q]. *)
  Lemma query_clause_ptr_sound
    (i : idx_map (domain symbol m))
    (q : rule_set idx symbol symbol_map idx_map) (inst : instance)
    (query_vars : list idx) (frontier_n : idx) (sigma : list idx)
    (a_q : idx_map (domain symbol m))
    (f : symbol) (n : idx) (clause_vars : list idx)
    (q_f : idx_map (list nat * nat)) (cargs : list nat) (cv : nat)
    (P : idx -> bool) :
    egraph_sound_for_interpretation i inst ->
    List.NoDup query_vars ->
    List.length query_vars = List.length sigma ->
    (forall x, map.get a_q x
       = match map.get (map.of_list (combine query_vars sigma)) x with
         | Some v => map.get i v
         | None => None
         end) ->
    map.get (query_clauses idx symbol symbol_map idx_map q) f = Some q_f ->
    map.get q_f n = Some (cargs, cv) ->
    clause_vars = filter P query_vars ->
    (forall t, In t cargs -> t < List.length clause_vars) ->
    cv < List.length clause_vars ->
    map.get (fst (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                    query_vars
                    (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                            idx_map idx_map_plus idx_trie analysis_result q inst))
                    frontier_n (Build_erule_query_ptr idx symbol f n clause_vars)))
            (map fst (filter snd (combine sigma
               (variable_flags idx Eqb_idx query_vars clause_vars))))
      = Some tt ->
    atom_sound_for_model m a_q
      (Build_atom f (map (fun k => nth k clause_vars idx_zero) cargs)
                    (nth cv clause_vars idx_zero)).
  Proof.
    intros Hsnd Hnd Hlen Ha_q Hqf Hclause Hcvars Hbound_args Hbound_cv Hhit.
    pose proof (clause_ptr_atom_in_db q inst query_vars frontier_n f n clause_vars q_f (cargs,cv) sigma Hqf Hclause Hhit) as Hcp.
    destruct Hcp as [ args_db [ v_db [ Hdb Hmatch ] ] ].
    set (proj := map fst (filter snd (combine sigma (variable_flags idx Eqb_idx query_vars clause_vars)))) in *.
    pose proof (atom_interpretation m i inst Hsnd (Build_atom f args_db v_db) Hdb) as Hdb_snd.
    unfold atom_sound_for_model in Hdb_snd.
    cbn [atom_args atom_ret atom_fn] in Hdb_snd.
    destruct (list_Mmap (map.get i) args_db) as [doms|] eqn:Hdoms; cbn [Is_Some_satisfying] in Hdb_snd; [ | contradiction ].
    destruct (map.get i v_db) as [out|] eqn:Hout; cbn [Is_Some_satisfying] in Hdb_snd; [ | contradiction ].
    pose proof (match_clause_correct idx_zero cargs cv args_db v_db proj Hmatch) as Hmc.
    cbn [map] in Hmc.
    injection Hmc as Hcv_eq Hcargs_eq.
    assert (Hproj : proj = map (fun cvv => named_list_lookup idx_zero (combine query_vars sigma) cvv) clause_vars)
      by (unfold proj; rewrite Hcvars; apply (project_filter_variable_flags P query_vars sigma idx_zero Hnd (eq_sym Hlen))).
    assert (Hincl : incl clause_vars query_vars)
      by (intros x Hx; rewrite Hcvars in Hx; apply filter_In in Hx; destruct Hx as [Hx _]; exact Hx).
    assert (Hkey : forall t, t < length clause_vars ->
      map.get a_q (nth t clause_vars idx_zero)
      = map.get i (named_list_lookup idx_zero (assign_sub proj) t))
      by (intros t Ht; rewrite Ha_q;
          rewrite (get_of_list_combine idx idx_zero query_vars sigma (nth t clause_vars idx_zero) Hnd Hlen)
            by (apply Hincl; apply nth_In; exact Ht);
          f_equal;
          rewrite named_list_lookup_assign_sub by (rewrite Hproj, length_map; exact Ht);
          rewrite Hproj; rewrite nth_error_map; rewrite (nth_error_nth' clause_vars idx_zero Ht);
          cbn [option_map]; reflexivity).
    assert (Hgen : forall cs, (forall k, In k cs -> k < length clause_vars) ->
       list_Mmap (map.get a_q) (map (fun k => nth k clause_vars idx_zero) cs)
       = list_Mmap (map.get i) (map (fun x => named_list_lookup idx_zero (assign_sub proj) x) cs))
      by (intros cs; induction cs as [|c cs' IH]; intros Hb;
          [ reflexivity
          | cbn [list_Mmap map];
            rewrite (Hkey c (Hb c (or_introl eq_refl)));
            rewrite (IH (fun k Hk => Hb k (or_intror Hk)));
            reflexivity ]).
    unfold atom_sound_for_model.
    cbn [atom_args atom_ret atom_fn].
    rewrite (Hgen cargs Hbound_args).
    setoid_rewrite Hcargs_eq.
    setoid_rewrite Hdoms.
    cbn [Is_Some_satisfying].
    setoid_rewrite (Hkey cv Hbound_cv).
    setoid_rewrite Hcv_eq.
    setoid_rewrite Hout.
    cbn [Is_Some_satisfying].
    exact Hdb_snd.
  Qed.

  (* Per-assignment query soundness: for an intersection key [sigma] (whose
     per-clause projections all hit their clause tries, [Hsli]), every
     reconstructed query atom of [r] is sound under [a_q = i o env0]. This
     is the [all (atom_sound_for_model ...) (query_atoms ...)] premise that
     [erule_sound] consumes inside process_erule'_sound. The query-side
     well-formedness ([Hwf]: each clause pointer resolves in [query_clauses]
     to an in-bounds clause whose vars are a filtered subsequence of
     [query_vars]) is discharged downstream from build_rule_set. *)
  Lemma query_atoms_sound
    (i : idx_map (domain symbol m))
    (q : rule_set idx symbol symbol_map idx_map) (inst : instance)
    (r : erule idx symbol) (frontier_n : idx) (sigma : list idx)
    (a_q : idx_map (domain symbol m)) :
    egraph_sound_for_interpretation i inst ->
    List.NoDup (query_vars idx symbol r) ->
    List.length (query_vars idx symbol r) = List.length sigma ->
    (forall x, map.get a_q x
       = match map.get (map.of_list (combine (query_vars idx symbol r) sigma)) x with
         | Some v => map.get i v
         | None => None
         end) ->
    (forall fsym nptr cvars,
       In (Build_erule_query_ptr idx symbol fsym nptr cvars)
          (uncurry cons (query_clause_ptrs idx symbol r)) ->
       exists q_f cargs cv (Pf : idx -> bool),
         map.get (query_clauses idx symbol symbol_map idx_map q) fsym = Some q_f
         /\ map.get q_f nptr = Some (cargs, cv)
         /\ cvars = filter Pf (query_vars idx symbol r)
         /\ (forall t, In t cargs -> t < List.length cvars)
         /\ cv < List.length cvars) ->
    (forall fsym nptr cvars,
       In (Build_erule_query_ptr idx symbol fsym nptr cvars)
          (uncurry cons (query_clause_ptrs idx symbol r)) ->
       map.get (fst (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                       (query_vars idx symbol r)
                       (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                               idx_map idx_map_plus idx_trie analysis_result q inst))
                       frontier_n (Build_erule_query_ptr idx symbol fsym nptr cvars)))
               (map fst (filter snd (combine sigma
                  (variable_flags idx Eqb_idx (query_vars idx symbol r) cvars))))
       = Some tt) ->
    all (atom_sound_for_model m a_q)
        (query_atoms idx idx_zero symbol symbol_map idx_map (query_clauses idx symbol symbol_map idx_map q) r).
  Proof.
    intros Hsnd Hnd Hlen Ha_q Hwf Hsli.
    unfold query_atoms.
    apply all_map_in.
    intros ptr Hptr.
    destruct ptr as [fsym nptr cvars].
    destruct (Hwf fsym nptr cvars Hptr) as (q_f & cargs & cv & Pf & Hqf & Hclause & Hcvars & Hba & Hbcv).
    rewrite Hqf, Hclause.
    apply (query_clause_ptr_sound i q inst (query_vars idx symbol r) frontier_n sigma a_q fsym nptr cvars q_f cargs cv Pf Hsnd Hnd Hlen Ha_q Hqf Hclause Hcvars Hba Hbcv).
    exact (Hsli fsym nptr cvars Hptr).
  Qed.

  (* From query-atom soundness plus query-variable coverage, [a_q] assigns a
     well-formed domain value to every query variable -- erule_sound's first
     premise. [Hcov]: every query var occurs in some reconstructed query atom. *)
  Lemma a_q_wf_query_vars
    (i : idx_map (domain symbol m)) (inst : instance)
    (q : rule_set idx symbol symbol_map idx_map) (r : erule idx symbol)
    (a_q : idx_map (domain symbol m)) (env0 : idx_map idx) :
    egraph_sound_for_interpretation i inst ->
    (forall x, map.get a_q x
       = match map.get env0 x with Some v => map.get i v | None => None end) ->
    all (atom_sound_for_model m a_q) (query_atoms idx idx_zero symbol symbol_map idx_map (query_clauses idx symbol symbol_map idx_map q) r) ->
    (forall x, In x (query_vars idx symbol r) ->
       exists a, In a (query_atoms idx idx_zero symbol symbol_map idx_map (query_clauses idx symbol symbol_map idx_map q) r)
                 /\ In x (atom_ret a :: atom_args a)) ->
    forall x, In x (query_vars idx symbol r) ->
      exists d, map.get a_q x = Some d /\ domain_wf symbol m d.
  Proof.
    intros Hsnd Ha_q Hsound Hcov x Hx.
    destruct (Hcov x Hx) as [ a [ Ha_in Hx_in ] ].
    pose proof (in_all _ _ _ Hsound Ha_in) as Ha_snd.
    unfold atom_sound_for_model in Ha_snd.
    destruct (list_Mmap (map.get a_q) (atom_args a)) as [doms|] eqn:Hdoms;
      cbn [Is_Some_satisfying] in Ha_snd; [|contradiction].
    destruct (map.get a_q (atom_ret a)) as [outv|] eqn:Hret;
      cbn [Is_Some_satisfying] in Ha_snd; [|contradiction].
    assert (Hax : exists d, map.get a_q x = Some d).
    { destruct Hx_in as [Hxret|Hxargs].
      - subst x. exists outv. exact Hret.
      - exact (list_Mmap_get_some _ _ _ _ _ Hdoms x Hxargs). }
    destruct Hax as [ d Hd ].
    exists d. split; [exact Hd|].
    rewrite Ha_q in Hd.
    destruct (map.get env0 x) as [v|] eqn:Henv; [|discriminate].
    exact (idx_interpretation_wf m i inst Hsnd v d Hd).
  Qed.

  (* Soundness of one frontier iteration of a single erule: running
     exec_write over every intersection key preserves egraph_ok and extends
     the interpretation while preserving soundness. [inst] is the build_tries
     snapshot (query atoms come from its db, sound under [i]); the loop runs
     on the evolving [e_start]. The wf bundle ([Hwf], [Hcov], disjointness
     and write-coverage) and the per-key intersection spec ([Hsli]) /
     length ([Hlen]) are discharged downstream from build_rule_set + the
     generic-join intersection correctness (pt_spaced_intersect_correct). *)
  Lemma process_erule'_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (i_snap i_start : idx_map (domain symbol m)) (inst : instance)
    (q : rule_set idx symbol symbol_map idx_map) (r : erule idx symbol)
    (frontier_n : idx) (e_start : instance) :
    let db_tries := fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                           idx_map idx_map_plus idx_trie analysis_result q inst) in
    let tries := ne_map (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                           (query_vars idx symbol r) db_tries frontier_n)
                        (query_clause_ptrs idx symbol r) in
    egraph_sound_for_interpretation i_snap inst ->
    egraph_ok e_start ->
    egraph_sound_for_interpretation i_start e_start ->
    map.extends i_start i_snap ->
    List.NoDup (query_vars idx symbol r) ->
    List.NoDup (write_vars idx symbol r) ->
    erule_sound idx idx_zero symbol symbol_map idx_map m (query_clauses idx symbol symbol_map idx_map q) r ->
    (forall fsym nptr cvars,
       In (Build_erule_query_ptr idx symbol fsym nptr cvars)
          (uncurry cons (query_clause_ptrs idx symbol r)) ->
       exists q_f cargs cv (Pf : idx -> bool),
         map.get (query_clauses idx symbol symbol_map idx_map q) fsym = Some q_f
         /\ map.get q_f nptr = Some (cargs, cv)
         /\ cvars = filter Pf (query_vars idx symbol r)
         /\ (forall t, In t cargs -> t < List.length cvars)
         /\ cv < List.length cvars) ->
    (forall x, In x (query_vars idx symbol r) ->
       exists a, In a (query_atoms idx idx_zero symbol symbol_map idx_map (query_clauses idx symbol symbol_map idx_map q) r)
                 /\ In x (atom_ret a :: atom_args a)) ->
    (forall x, In x (write_vars idx symbol r) -> ~ In x (query_vars idx symbol r)) ->
    (forall c, In c (write_clauses idx symbol r) ->
        forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
        In x (query_vars idx symbol r) \/ In x (write_vars idx symbol r)) ->
    (forall p, In p (write_unifications idx symbol r) ->
        (In (fst p) (query_vars idx symbol r) \/ In (fst p) (write_vars idx symbol r))
        /\ (In (snd p) (query_vars idx symbol r) \/ In (snd p) (write_vars idx symbol r))) ->
    (forall sigma, In sigma (intersection_keys idx idx_trie spaced_list_intersect tries) ->
       List.length (query_vars idx symbol r) = List.length sigma) ->
    (forall sigma, In sigma (intersection_keys idx idx_trie spaced_list_intersect tries) ->
       forall fsym nptr cvars,
       In (Build_erule_query_ptr idx symbol fsym nptr cvars)
          (uncurry cons (query_clause_ptrs idx symbol r)) ->
       map.get (fst (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                       (query_vars idx symbol r) db_tries frontier_n
                       (Build_erule_query_ptr idx symbol fsym nptr cvars)))
               (map fst (filter snd (combine sigma
                  (variable_flags idx Eqb_idx (query_vars idx symbol r) cvars))))
       = Some tt) ->
    match @process_erule' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie
            analysis_result _ spaced_list_intersect db_tries r frontier_n e_start with
    | (_, e') =>
        egraph_ok e'
        /\ exists i', map.extends i' i_snap /\ egraph_sound_for_interpretation i' e'
    end.
  Proof.
    intros db_tries tries Hsnd_inst Hok_start Hsnd_start Hext_start Hnd_qv Hnd_wv Hrule
           Hwf Hcov Hdisj HcovC HcovU Hlen_sig Hsli.
    unfold process_erule'.
    fold tries.
    set (asn := intersection_keys idx idx_trie spaced_list_intersect tries) in *.
    assert (Hloop : forall sigmas,
      (forall sigma, In sigma sigmas -> length (query_vars idx symbol r) = length sigma) ->
      (forall sigma, In sigma sigmas ->
         forall fsym nptr cvars, In (Build_erule_query_ptr idx symbol fsym nptr cvars) (uncurry cons (query_clause_ptrs idx symbol r)) ->
         map.get (fst (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie (query_vars idx symbol r) db_tries frontier_n (Build_erule_query_ptr idx symbol fsym nptr cvars)))
                 (map fst (filter snd (combine sigma (variable_flags idx Eqb_idx (query_vars idx symbol r) cvars)))) = Some tt) ->
      forall e_cur icur, egraph_ok e_cur -> egraph_sound_for_interpretation icur e_cur -> map.extends icur i_snap ->
      match list_Miter (exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result r) sigmas e_cur with
      | (_, e') => egraph_ok e' /\ exists i', map.extends i' i_snap /\ egraph_sound_for_interpretation i' e'
      end).
    { intro sigmas. induction sigmas as [|sigma sigmas' IH];
        intros Hlen_s Hsli_s e_cur icur Hok_cur Hsnd_cur Hext_cur.
      - cbn [list_Miter]. split; [exact Hok_cur|].
        exists icur. split; [exact Hext_cur | exact Hsnd_cur].
      - cbn [list_Miter].
        set (env0 := map.of_list (combine (query_vars idx symbol r) sigma)).
        set (a_q := compose_assignment i_snap env0).
        assert (Ha_q : forall x, map.get a_q x = match map.get env0 x with Some v => map.get i_snap v | None => None end)
          by (intros; apply get_compose_assignment).
        pose proof (query_atoms_sound i_snap q inst r frontier_n sigma a_q Hsnd_inst Hnd_qv
                      (Hlen_s sigma (or_introl eq_refl)) Ha_q Hwf (Hsli_s sigma (or_introl eq_refl))) as Hqsnd.
        pose proof (a_q_wf_query_vars i_snap inst q r a_q env0 Hsnd_inst Ha_q Hqsnd Hcov) as Hawf.
        destruct (Hrule a_q Hawf Hqsnd) as (a_src & Hsrc_qv & Hsrc_wv & Hsrc_c & Hsrc_u).
        pose proof (Hlen_s sigma (or_introl eq_refl)) as Hlen1.
        assert (Hfresh : forall x, In x (write_vars idx symbol r) -> map.get env0 x = None)
          by (intros x Hxw; unfold env0; apply get_of_list_none;
              rewrite (map_combine_fst (query_vars idx symbol r) sigma Hlen1); exact (Hdisj x Hxw)).
        assert (Hcons : forall x v, map.get env0 x = Some v ->
           map.get icur v = map.get a_src x /\ Sep.has_key v (parent (equiv e_cur)))
          by (intros x v Hev;
              assert (Hxq : In x (query_vars idx symbol r))
                by (pose proof (get_of_list_in_keys idx (combine (query_vars idx symbol r) sigma) x v Hev) as Hk;
                    rewrite (map_combine_fst (query_vars idx symbol r) sigma Hlen1) in Hk; exact Hk);
              destruct (Hawf x Hxq) as (d & Haqx & Hwfd);
              assert (Hiv : map.get i_snap v = Some d) by (rewrite Ha_q, Hev in Haqx; exact Haqx);
              assert (Hicurv : map.get icur v = Some d) by (apply Hext_cur; exact Hiv);
              split;
              [ rewrite Hicurv; rewrite (Hsrc_qv x Hxq); exact (eq_sym Haqx)
              | apply (interpretation_exact m icur e_cur Hsnd_cur v); rewrite Hicurv; exact I ]).
        assert (Hcons_c : forall c, In c (write_clauses idx symbol r) ->
           forall x, In x (atom_ret c :: atom_args c) ->
           (exists v, map.get env0 x = Some v) \/ In x (write_vars idx symbol r))
          by (intros c Hc x Hx; destruct (HcovC c Hc x Hx) as [Hq|Hw];
              [ left; exists (named_list_lookup idx_zero (combine (query_vars idx symbol r) sigma) x);
                unfold env0; exact (get_of_list_combine idx idx_zero (query_vars idx symbol r) sigma x Hnd_qv Hlen1 Hq)
              | right; exact Hw ]).
        assert (Hcons_u : forall p, In p (write_unifications idx symbol r) ->
           ((exists v, map.get env0 (fst p) = Some v) \/ In (fst p) (write_vars idx symbol r))
           /\ ((exists v, map.get env0 (snd p) = Some v) \/ In (snd p) (write_vars idx symbol r)))
          by (intros p Hp; destruct (HcovU p Hp) as [Hf Hs]; split;
              [ destruct Hf as [Hq|Hw];
                [ left; exists (named_list_lookup idx_zero (combine (query_vars idx symbol r) sigma) (fst p));
                  unfold env0; exact (get_of_list_combine idx idx_zero (query_vars idx symbol r) sigma (fst p) Hnd_qv Hlen1 Hq)
                | right; exact Hw ]
              | destruct Hs as [Hq|Hw];
                [ left; exists (named_list_lookup idx_zero (combine (query_vars idx symbol r) sigma) (snd p));
                  unfold env0; exact (get_of_list_combine idx idx_zero (query_vars idx symbol r) sigma (snd p) Hnd_qv Hlen1 Hq)
                | right; exact Hw ] ]).
        pose proof (@exec_write_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result H m Hm Hlti Hlts Hltt Hm icur r sigma e_cur a_src
                      Hnd_wv Hfresh Hsrc_wv Hcons Hcons_c Hcons_u Hsrc_c Hsrc_u Hok_cur Hsnd_cur) as Hew.
        cbn [Mseq Mbind Mret StateMonad.state_monad].
        destruct (exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result r sigma e_cur)
          as [u e_mid] eqn:Hew_eq.
        destruct Hew as (Hok_mid & _Hmono & i_mid & Hext_mid & Hsnd_mid).
        assert (Hext_mid_i : map.extends i_mid i_snap)
          by (intros k vv hh; apply Hext_mid; apply Hext_cur; exact hh).
        pose proof (IH (fun s Hs => Hlen_s s (or_intror Hs)) (fun s Hs => Hsli_s s (or_intror Hs))
                      e_mid i_mid Hok_mid Hsnd_mid Hext_mid_i) as HIH.
        destruct (list_Miter (exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result r) sigmas' e_mid)
          as [u2 e'] eqn:Hlm.
        destruct HIH as (Hok' & i' & Hext'_snap & Hsnd').
        split; [exact Hok'|].
        exists i'. split; [exact Hext'_snap | exact Hsnd']. }
    apply (Hloop asn Hlen_sig Hsli e_start i_start Hok_start Hsnd_start Hext_start).
  Qed.

End Slice.

(* Soundness of running a single erule across all its frontier positions:
   process_erule iterates process_erule' over [seq 0 N], threading the
   egraph; each frontier iteration is sound by process_erule'_sound (with
   the fixed snapshot interpretation [i_snap] and the evolving loop
   interpretation). The per-frontier intersection spec / length hold for
   every frontier index. *)
Lemma process_erule_sound
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (Eqb_symbol : Eqb symbol) (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
  (symbol_map : forall A, map.map symbol A) (symbol_map_plus : map_plus symbol_map)
  (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) (symbol_map_ok : forall A, map.ok (symbol_map A))
  (idx_map : forall A, map.map idx A) (idx_map_plus : map_plus idx_map) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (idx_trie_ok : forall A, map.ok (idx_trie A))
  (analysis_result : Type) (idx_map_plus_ok : @map_plus_ok _ _ idx_map_plus)
  (spaced_list_intersect
    : forall B, WithDefault B -> (B -> B -> B) -> ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B))
  (H : analysis idx symbol analysis_result) (m : model symbol) (Hm : model_ok symbol m)
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  (i_snap i_start : idx_map (domain symbol m))
  (inst : instance idx symbol symbol_map idx_map idx_trie analysis_result)
  (q : rule_set idx symbol symbol_map idx_map) (r : erule idx symbol)
  (e_start : instance idx symbol symbol_map idx_map idx_trie analysis_result) :
  let db_tries := fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                         idx_map idx_map_plus idx_trie analysis_result q inst) in
  egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i_snap inst ->
  egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_start ->
  egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i_start e_start ->
  map.extends i_start i_snap ->
  List.NoDup (query_vars idx symbol r) ->
  List.NoDup (write_vars idx symbol r) ->
  erule_sound idx idx_zero symbol symbol_map idx_map m (query_clauses idx symbol symbol_map idx_map q) r ->
  (forall fsym nptr cvars,
     In (Build_erule_query_ptr idx symbol fsym nptr cvars)
        (uncurry cons (query_clause_ptrs idx symbol r)) ->
     exists q_f cargs cv (Pf : idx -> bool),
       map.get (query_clauses idx symbol symbol_map idx_map q) fsym = Some q_f
       /\ map.get q_f nptr = Some (cargs, cv)
       /\ cvars = filter Pf (query_vars idx symbol r)
       /\ (forall t, In t cargs -> t < List.length cvars)
       /\ cv < List.length cvars) ->
  (forall x, In x (query_vars idx symbol r) ->
     exists a, In a (query_atoms idx idx_zero symbol symbol_map idx_map (query_clauses idx symbol symbol_map idx_map q) r)
               /\ In x (atom_ret a :: atom_args a)) ->
  (forall x, In x (write_vars idx symbol r) -> ~ In x (query_vars idx symbol r)) ->
  (forall c, In c (write_clauses idx symbol r) ->
      forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
      In x (query_vars idx symbol r) \/ In x (write_vars idx symbol r)) ->
  (forall p, In p (write_unifications idx symbol r) ->
      (In (fst p) (query_vars idx symbol r) \/ In (fst p) (write_vars idx symbol r))
      /\ (In (snd p) (query_vars idx symbol r) \/ In (snd p) (write_vars idx symbol r))) ->
  (forall frontier_n sigma,
     In sigma (intersection_keys idx idx_trie spaced_list_intersect
                 (ne_map (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                            (query_vars idx symbol r) db_tries frontier_n)
                         (query_clause_ptrs idx symbol r))) ->
     List.length (query_vars idx symbol r) = List.length sigma) ->
  (forall frontier_n sigma,
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
     = Some tt) ->
  match @process_erule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie
          analysis_result _ spaced_list_intersect db_tries r e_start with
  | (_, e') =>
      egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e'
      /\ exists i', map.extends i' i_snap
                    /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i' e'
  end.
Proof.
  intros db_tries Hsnd_inst Hok_start Hsnd_start Hext_start Hnd_qv Hnd_wv Hrule
         Hwf Hcov Hdisj HcovC HcovU Hlen_sig Hsli.
  unfold process_erule.
  assert (Hloop : forall ns,
    forall e_cur icur, egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_cur -> egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m icur e_cur -> map.extends icur i_snap ->
    match list_Miter (fun n => process_erule' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries r (idx_of_nat idx idx_succ idx_zero n)) ns e_cur with
    | (_, e') => egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e' /\ exists i', map.extends i' i_snap /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i' e'
    end).
  { induction ns as [|n ns' IH]; intros e_cur icur Hok_cur Hsnd_cur Hext_cur.
    - cbn [list_Miter]. split; [exact Hok_cur|].
      exists icur. split; [exact Hext_cur | exact Hsnd_cur].
    - cbn [list_Miter].
      pose proof (process_erule'_sound (lt:=lt) (m:=m) (spaced_list_intersect:=spaced_list_intersect) Hlti Hlts Hltt i_snap icur inst q r (idx_of_nat idx idx_succ idx_zero n) e_cur
                    Hsnd_inst Hok_cur Hsnd_cur Hext_cur Hnd_qv Hnd_wv Hrule Hwf Hcov Hdisj HcovC HcovU
                    (Hlen_sig (idx_of_nat idx idx_succ idx_zero n)) (Hsli (idx_of_nat idx idx_succ idx_zero n))) as Hpe.
      cbn [Mseq Mbind Mret StateMonad.state_monad].
      fold db_tries in Hpe.
      destruct (process_erule' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries r (idx_of_nat idx idx_succ idx_zero n) e_cur)
        as [u e_mid] eqn:Hpe_eq.
      destruct Hpe as (Hok_mid & i_mid & Hext_mid & Hsnd_mid).
      pose proof (IH e_mid i_mid Hok_mid Hsnd_mid Hext_mid) as HIH.
      destruct (list_Miter (fun n0 => process_erule' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result spaced_list_intersect db_tries r (idx_of_nat idx idx_succ idx_zero n0)) ns' e_mid)
        as [u2 e'] eqn:Hlm.
      destruct HIH as (Hok' & i' & Hext'_snap & Hsnd').
      split; [exact Hok'|]. exists i'. split; [exact Hext'_snap | exact Hsnd']. }
  apply (Hloop (seq 0 (length (uncurry cons (query_clause_ptrs idx symbol r))))
               e_start i_start Hok_start Hsnd_start Hext_start).
Qed.
