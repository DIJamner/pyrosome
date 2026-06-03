(* exec_write / exec_const / process_const_rules soundness, split out of
   Semantics.v (Section WithMap).  exec_write_sound keeps its exact
   section-closed signature (consumed by SemanticsProcessErule); the 3
   internal items live in a local Section with the egraph+model context. *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations.
From Utils.EGraph Require Import Defs Semantics SemanticsUnionSem.
Import Monad.StateMonad.

(* exec_write_sound at TOP LEVEL with explicit binders reproducing its section type. *)
Lemma exec_write_sound
  (idx : Type) (Eqb_idx : Eqb idx) (Eqb_idx_ok : Eqb_ok Eqb_idx)
  (lt : idx -> idx -> Prop) (idx_succ : idx -> idx) (idx_zero : WithDefault idx)
  (symbol : Type) (Eqb_symbol : Eqb symbol) (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
  (symbol_map : forall A, map.map symbol A) (symbol_map_ok : forall A, map.ok (symbol_map A))
  (idx_map : forall A, map.map idx A) (idx_map_ok : forall A, map.ok (idx_map A))
  (idx_trie : forall A, map.map (list idx) A) (idx_trie_ok : forall A, map.ok (idx_trie A))
  (analysis_result : Type) (H : analysis idx symbol analysis_result) (m : model symbol)
  (Hm_sec : model_ok symbol m)
  (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
  (Hm : model_ok symbol m)
  (i : idx_map (domain symbol m))
  (r : erule idx symbol) (assignment : list idx)
  (e : instance idx symbol symbol_map idx_map idx_trie analysis_result)
  (a_src : idx_map (domain symbol m)) :
  let env0 := map.of_list (combine (query_vars idx symbol r) assignment) in
  List.NoDup (write_vars idx symbol r) ->
  (forall x, In x (write_vars idx symbol r) -> map.get env0 x = None) ->
  (forall x, In x (write_vars idx symbol r) ->
      exists d, map.get a_src x = Some d /\ domain_wf symbol m d) ->
  (forall x v, map.get env0 x = Some v ->
      map.get i v = map.get a_src x /\ Sep.has_key v (parent (equiv e))) ->
  (forall c, In c (write_clauses idx symbol r) ->
      forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
      (exists v, map.get env0 x = Some v) \/ In x (write_vars idx symbol r)) ->
  (forall p, In p (write_unifications idx symbol r) ->
      ((exists v, map.get env0 (fst p) = Some v) \/ In (fst p) (write_vars idx symbol r))
      /\ ((exists v, map.get env0 (snd p) = Some v) \/ In (snd p) (write_vars idx symbol r))) ->
  all (atom_sound_for_model idx symbol idx_map m a_src) (write_clauses idx symbol r) ->
  all (fun p => eq_sound_for_model idx symbol idx_map m a_src (fst p) (snd p)) (write_unifications idx symbol r) ->
  egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e ->
  egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i e ->
  match exec_write idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result r assignment e with
  | (_, e') =>
      egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e'
      /\ (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
      /\ exists i', map.extends i' i
                    /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i' e'
  end.
Proof.
  intros env0 Hnodup Hfresh Hwf_wv Hcons Hcov_c Hcov_u Hsnd_c Hsnd_u Hok Hsnd.
  unfold exec_write.
  pose proof (@allocate_existential_vars_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result m Hlti Hlts Hltt a_src (write_vars idx symbol r) i env0) as Halloc.
  unfold vc in Halloc.
  specialize (Halloc Hnodup Hfresh Hwf_wv e Hok Hsnd).
  destruct (allocate_existential_vars idx idx_succ symbol symbol_map idx_map idx_trie analysis_result (write_vars idx symbol r) env0 e) as [env e1] eqn:Halloc_eq.
  cbn [fst snd] in Halloc.
  destruct Halloc as (Hok1 & i1 & Hext1 & Hsnd1 & Henv0_pres & Hwv_cov & Hmono1).
  fold env0.
  cbn [Mbind Mret StateMonad.state_monad].
  rewrite Halloc_eq.
  cbn [fst snd].
  assert (Hcons1 : forall x,
    ((exists v0, map.get env0 x = Some v0) \/ In x (write_vars idx symbol r)) ->
    exists v, map.get env x = Some v
              /\ Sep.has_key v (parent (equiv e1))
              /\ (forall d, map.get a_src x = Some d -> map.get i1 v = Some d)).
  { intros x [ [v0 Hv0] | Hxw ].
    - exists v0.
      pose proof (Hcons x v0 Hv0) as [Hiv0 Hkv0].
      split; [exact (Henv0_pres x v0 Hv0)|].
      split; [exact (Hmono1 v0 Hkv0)|].
      intros d Hd. apply Hext1. rewrite Hiv0. exact Hd.
    - destruct (Hwv_cov x Hxw) as (v & d' & Henvx & Hasrc & Hi1v & Hkv).
      exists v.
      split; [exact Henvx|].
      split; [exact Hkv|].
      intros d Hd. rewrite Hasrc in Hd. inversion Hd; subst d'. exact Hi1v. }
  assert (Hmmap_in : forall (B:Type) (f : idx -> option B) l l',
    list_Mmap f l = Some l' -> forall x, In x l -> exists b, f x = Some b)
    by (intros B f l; induction l as [|a l IHl]; cbn [list_Mmap]; intros l' Hl x Hx;
        [ contradiction
        | destruct (f a) as [b0|] eqn:Hfa; cbn [Mbind option_monad] in Hl; [|discriminate];
          destruct (list_Mmap f l) as [bl|] eqn:Hfl; cbn [Mbind option_monad] in Hl; [|discriminate];
          destruct Hx as [->|Hx]; [exists b0; exact Hfa | exact (IHl _ eq_refl x Hx)] ]).
  assert (Hcl_cons : forall c, In c (write_clauses idx symbol r) ->
    atom_sound_for_model idx symbol idx_map m a_src c ->
    forall x, In x (atom_ret c :: atom_args c) ->
    exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e1))
              /\ map.get i1 v = map.get a_src x)
    by (intros c Hc Hsndc x Hx;
        destruct (Hcons1 x (Hcov_c c Hc x Hx)) as (v & Henvx & Hkv & Hi1cond);
        exists v; split; [exact Henvx|]; split; [exact Hkv|];
        assert (Hasx : exists d, map.get a_src x = Some d) by
          (unfold atom_sound_for_model in Hsndc;
           destruct (list_Mmap (map.get a_src) (atom_args c)) as [argd|] eqn:Hargd;
             cbn [Is_Some_satisfying] in Hsndc; [|tauto];
           destruct (map.get a_src (atom_ret c)) as [outd|] eqn:Houtd;
             cbn [Is_Some_satisfying] in Hsndc; [|tauto];
           destruct Hx as [Heq|Hxa];
             [ rewrite <- Heq; exists outd; exact Houtd
             | exact (Hmmap_in _ _ _ _ Hargd x Hxa) ]);
        destruct Hasx as [d Hd]; rewrite Hd; apply Hi1cond; exact Hd).
  assert (Hphase2 : forall cs,
    (forall c, In c cs -> atom_sound_for_model idx symbol idx_map m a_src c) ->
    (forall c, In c cs -> forall x, In x (atom_ret c :: atom_args c) ->
       exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e1))
                 /\ map.get i1 v = map.get a_src x) ->
    forall e_cur, egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_cur ->
    egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i1 e_cur ->
    (forall z, Sep.has_key z (parent (equiv e1)) -> Sep.has_key z (parent (equiv e_cur))) ->
    match list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) cs e_cur with
    | (_, e2) => egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e2
                 /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i1 e2
                 /\ (forall z, Sep.has_key z (parent (equiv e_cur)) -> Sep.has_key z (parent (equiv e2)))
    end).
  { induction cs as [|c cs' IHcs]; intros Hsnd_cs Hcons_cs e_cur Hok_cur Hsnd_cur Hmono_cur.
    - cbn [list_Miter]. split; [exact Hok_cur|]. split; [exact Hsnd_cur|]. intros z Hz; exact Hz.
    - cbn [list_Miter].
      assert (Hcc : forall x, In x (atom_ret c :: atom_args c) ->
         exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e_cur))
                   /\ map.get i1 v = map.get a_src x).
      { intros x Hx. destruct (Hcons_cs c (or_introl eq_refl) x Hx) as (v & Hev & Hkv & Hiv).
        exists v. split; [exact Hev|]. split; [exact (Hmono_cur v Hkv)|]. exact Hiv. }
      pose proof (@exec_clause_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result H m Hm i1 env c a_src e_cur Hok_cur Hsnd_cur Hcc
                    (Hsnd_cs c (or_introl eq_refl))) as Hec.
      destruct (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env c e_cur) as [u e_mid] eqn:Hec_eq.
      destruct Hec as (Hok_mid & Hsnd_mid & Hkeys_mid).
      pose proof (IHcs (fun c0 Hc0 => Hsnd_cs c0 (or_intror Hc0))
                       (fun c0 Hc0 => Hcons_cs c0 (or_intror Hc0))
                       e_mid Hok_mid Hsnd_mid
                       (fun z Hz => Hkeys_mid z (Hmono_cur z Hz))) as HIH.
      destruct (list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) cs' e_mid) as [u2 e2] eqn:Hlm2.
      destruct HIH as (Hok2 & Hsnd2 & Hkeys2).
      cbn [Mseq Mbind Mret StateMonad.state_monad].
      rewrite Hec_eq. rewrite Hlm2.
      split; [exact Hok2|]. split; [exact Hsnd2|].
      intros z Hz. apply Hkeys2. apply Hkeys_mid. exact Hz. }
  pose proof (Hphase2 (write_clauses idx symbol r)
    (fun c0 Hc0 => in_all _ _ _ Hsnd_c Hc0)
    (fun c0 Hc0 x0 Hx0 => Hcl_cons c0 Hc0 (in_all _ _ _ Hsnd_c Hc0) x0 Hx0)
    e1 Hok1 Hsnd1 (fun z Hz => Hz)) as Hp2.
  destruct (list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) (write_clauses idx symbol r) e1) as [u2 e2] eqn:Hlm_c.
  destruct Hp2 as (Hok2 & Hsnd2 & Hkeys2).
  cbn [fst snd].
  assert (Hun_cons : forall p, In p (write_unifications idx symbol r) ->
    exists vx vy, map.get env (fst p) = Some vx /\ map.get env (snd p) = Some vy
                  /\ Sep.has_key vx (parent (equiv e1)) /\ Sep.has_key vy (parent (equiv e1))
                  /\ eq_sound_for_model idx symbol idx_map m i1 vx vy).
  { intros p Hp.
    destruct (Hcov_u p Hp) as [Hcx Hcy].
    destruct (Hcons1 (fst p) Hcx) as (vx & Hevx & Hkvx & Hivx).
    destruct (Hcons1 (snd p) Hcy) as (vy & Hevy & Hkvy & Hivy).
    pose proof (in_all _ _ _ Hsnd_u Hp) as Hequ.
    exists vx, vy.
    split; [exact Hevx|]. split; [exact Hevy|]. split; [exact Hkvx|]. split; [exact Hkvy|].
    unfold eq_sound_for_model in Hequ |- *.
    destruct (map.get a_src (fst p)) as [dx|] eqn:Hax; cbn [Is_Some_satisfying] in Hequ; [|tauto].
    destruct (map.get a_src (snd p)) as [dy|] eqn:Hay; cbn [Is_Some_satisfying] in Hequ; [|tauto].
    rewrite (Hivx dx eq_refl). cbn [Is_Some_satisfying].
    rewrite (Hivy dy eq_refl). cbn [Is_Some_satisfying]. exact Hequ. }
  assert (Hphase3 : forall ps,
    (forall p, In p ps -> exists vx vy, map.get env (fst p) = Some vx /\ map.get env (snd p) = Some vy
                  /\ Sep.has_key vx (parent (equiv e1)) /\ Sep.has_key vy (parent (equiv e1))
                  /\ eq_sound_for_model idx symbol idx_map m i1 vx vy) ->
    forall e_cur, egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e_cur ->
    egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i1 e_cur ->
    (forall z, Sep.has_key z (parent (equiv e1)) -> Sep.has_key z (parent (equiv e_cur))) ->
    match list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) ps e_cur with
    | (_, e3) => egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result e3
                 /\ egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m i1 e3
                 /\ (forall z, Sep.has_key z (parent (equiv e_cur)) -> Sep.has_key z (parent (equiv e3)))
    end).
  { induction ps as [|p ps' IHps]; intros Hcons_ps e_cur Hok_cur Hsnd_cur Hmono_cur.
    - cbn [list_Miter]. split; [exact Hok_cur|]. split; [exact Hsnd_cur|]. intros z Hz; exact Hz.
    - cbn [list_Miter]. destruct p as [px py].
      destruct (Hcons_ps (px,py) (or_introl eq_refl)) as (vx & vy & Hevx & Hevy & Hkvx & Hkvy & Hequ).
      cbn [fst snd] in Hevx, Hevy.
      cbn [Mseq Mbind Mret StateMonad.state_monad].
      rewrite Hevx, Hevy. cbn [unwrap_with_default].
      pose proof Hok_cur as Hok_cur2. destruct Hok_cur2 as [Hroots_cur _ _ _].
      pose proof (@union_preserves_egraph_ok_sem idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result H vx vy e_cur Hok_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy)) as Hok_mid.
      pose proof (@union_preserves_sound_sem idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result H m Hm vx vy i1 e_cur Hok_cur Hsnd_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy) Hequ) as Hsnd_mid.
      pose proof (fun z Hz => @union_extends_keys_sem idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result H vx vy e_cur Hroots_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy) z Hz) as Hkeys_mid.
      destruct (Defs.union vx vy e_cur) as [vu e_mid] eqn:Hu_eq.
      cbn [snd] in Hok_mid, Hsnd_mid, Hkeys_mid.
      pose proof (IHps (fun p0 Hp0 => Hcons_ps p0 (or_intror Hp0)) e_mid Hok_mid Hsnd_mid
                   (fun z Hz => Hkeys_mid z (Hmono_cur z Hz))) as HIH.
      destruct (list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) ps' e_mid) as [vu2 e3] eqn:Hlm3.
      destruct HIH as (Hok3 & Hsnd3 & Hkeys3).
      split; [exact Hok3|]. split; [exact Hsnd3|].
      intros z Hz. apply Hkeys3. apply Hkeys_mid. exact Hz. }
  pose proof (Hphase3 (write_unifications idx symbol r) Hun_cons e2 Hok2 Hsnd2 Hkeys2) as Hp3.
  destruct (list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) (write_unifications idx symbol r) e2) as [u3 e3] eqn:Hlm_u.
  destruct Hp3 as (Hok3 & Hsnd3 & Hkeys3).
  split; [exact Hok3|].
  split; [intros z Hz; apply Hkeys3; apply Hkeys2; apply Hmono1; exact Hz|].
  exists i1. split; [exact Hext1|exact Hsnd3].
Qed.

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
    {spaced_list_intersect : forall B, WithDefault B -> (B -> B -> B) -> ne_list (map.rep (map:=idx_trie B) * list bool) -> map.rep (map:=idx_trie B)}
    {H : analysis idx symbol analysis_result} {m : model symbol} {Hm : model_ok symbol m}.
  Existing Instance idx_zero.
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_ok := (egraph_ok idx lt symbol symbol_map idx_map idx_trie analysis_result).
  Notation egraph_sound_for_interpretation := (egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie analysis_result m).

  Lemma exec_const_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (Hm2 : model_ok symbol m)
    (i : idx_map (domain symbol m))
    (r : const_rule idx symbol) (e : instance)
    (a_src : idx_map (domain symbol m)) :
    List.NoDup (const_vars idx symbol r) ->
    (forall x, In x (const_vars idx symbol r) ->
        exists d, map.get a_src x = Some d /\ domain_wf symbol m d) ->
    (forall c, In c (const_clauses idx symbol r) ->
        forall x, In x (c.(atom_ret) :: c.(atom_args)) -> In x (const_vars idx symbol r)) ->
    (forall p, In p (const_unifications idx symbol r) ->
        In (fst p) (const_vars idx symbol r) /\ In (snd p) (const_vars idx symbol r)) ->
    all (atom_sound_for_model idx symbol idx_map m a_src) (const_clauses idx symbol r) ->
    all (fun p => eq_sound_for_model idx symbol idx_map m a_src (fst p) (snd p)) (const_unifications idx symbol r) ->
    egraph_ok e ->
    egraph_sound_for_interpretation i e ->
    match exec_const idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result r e with
    | (_, e') =>
        egraph_ok e'
        /\ (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
        /\ exists i', map.extends i' i
                      /\ egraph_sound_for_interpretation i' e'
    end.
  Proof.
    intros Hnodup Hwf_wv Hcov_c Hcov_u Hsnd_c Hsnd_u Hok Hsnd.
    unfold exec_const.
    pose proof (@allocate_existential_vars_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result m Hlti Hlts Hltt a_src (const_vars idx symbol r) i map.empty) as Halloc.
    unfold vc in Halloc.
    specialize (Halloc Hnodup (fun w _ => map.get_empty w) Hwf_wv e Hok Hsnd).
    destruct (allocate_existential_vars idx idx_succ symbol symbol_map idx_map idx_trie analysis_result (const_vars idx symbol r) map.empty e) as [env e1] eqn:Halloc_eq.
    cbn [fst snd] in Halloc.
    destruct Halloc as (Hok1 & i1 & Hext1 & Hsnd1 & _Henv0_pres & Hwv_cov & Hmono1).
    cbn [Mbind Mret StateMonad.state_monad].
    rewrite Halloc_eq.
    cbn [fst snd].
    assert (Hcons1 : forall x,
      In x (const_vars idx symbol r) ->
      exists v, map.get env x = Some v
                /\ Sep.has_key v (parent (equiv e1))
                /\ (forall d, map.get a_src x = Some d -> map.get i1 v = Some d))
      by (intros x Hxcv;
          destruct (Hwv_cov x Hxcv) as (v & d' & Henvx & Hasrc & Hi1v & Hkv);
          exists v; split; [exact Henvx|]; split; [exact Hkv|];
          intros d Hd; rewrite Hasrc in Hd; inversion Hd; subst d'; exact Hi1v).
    assert (Hmmap_in : forall (B:Type) (f : idx -> option B) l l',
      list_Mmap f l = Some l' -> forall x, In x l -> exists b, f x = Some b)
      by (intros B f l; induction l as [|a l IHl]; cbn [list_Mmap]; intros l' Hl x Hx;
          [ contradiction
          | destruct (f a) as [b0|] eqn:Hfa; cbn [Mbind option_monad] in Hl; [|discriminate];
            destruct (list_Mmap f l) as [bl|] eqn:Hfl; cbn [Mbind option_monad] in Hl; [|discriminate];
            destruct Hx as [->|Hx]; [exists b0; exact Hfa | exact (IHl _ eq_refl x Hx)] ]).
    assert (Hcl_cons : forall c, In c (const_clauses idx symbol r) ->
      atom_sound_for_model idx symbol idx_map m a_src c ->
      forall x, In x (atom_ret c :: atom_args c) ->
      exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e1))
                /\ map.get i1 v = map.get a_src x)
      by (intros c Hc Hsndc x Hx;
          destruct (Hcons1 x (Hcov_c c Hc x Hx)) as (v & Henvx & Hkv & Hi1cond);
          exists v; split; [exact Henvx|]; split; [exact Hkv|];
          assert (Hasx : exists d, map.get a_src x = Some d) by
            (unfold atom_sound_for_model in Hsndc;
             destruct (list_Mmap (map.get a_src) (atom_args c)) as [argd|] eqn:Hargd;
               cbn [Is_Some_satisfying] in Hsndc; [|tauto];
             destruct (map.get a_src (atom_ret c)) as [outd|] eqn:Houtd;
               cbn [Is_Some_satisfying] in Hsndc; [|tauto];
             destruct Hx as [Heq|Hxa];
               [ rewrite <- Heq; exists outd; exact Houtd
               | exact (Hmmap_in _ _ _ _ Hargd x Hxa) ]);
          destruct Hasx as [d Hd]; rewrite Hd; apply Hi1cond; exact Hd).
    assert (Hphase2 : forall cs,
      (forall c, In c cs -> atom_sound_for_model idx symbol idx_map m a_src c) ->
      (forall c, In c cs -> forall x, In x (atom_ret c :: atom_args c) ->
         exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e1))
                   /\ map.get i1 v = map.get a_src x) ->
      forall e_cur, egraph_ok e_cur -> egraph_sound_for_interpretation i1 e_cur ->
      (forall z, Sep.has_key z (parent (equiv e1)) -> Sep.has_key z (parent (equiv e_cur))) ->
      match list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) cs e_cur with
      | (_, e2) => egraph_ok e2 /\ egraph_sound_for_interpretation i1 e2
                   /\ (forall z, Sep.has_key z (parent (equiv e_cur)) -> Sep.has_key z (parent (equiv e2)))
      end)
      by (induction cs as [|c cs' IHcs]; intros Hsnd_cs Hcons_cs e_cur Hok_cur Hsnd_cur Hmono_cur;
          [ cbn [list_Miter]; split; [exact Hok_cur|]; split; [exact Hsnd_cur|]; intros z Hz; exact Hz
          | cbn [list_Miter];
            assert (Hcc : forall x, In x (atom_ret c :: atom_args c) ->
               exists v, map.get env x = Some v /\ Sep.has_key v (parent (equiv e_cur))
                         /\ map.get i1 v = map.get a_src x)
              by (intros x Hx; destruct (Hcons_cs c (or_introl eq_refl) x Hx) as (v & Hev & Hkv & Hiv);
                  exists v; split; [exact Hev|]; split; [exact (Hmono_cur v Hkv)|]; exact Hiv);
            pose proof (@exec_clause_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok analysis_result H m Hm i1 env c a_src e_cur Hok_cur Hsnd_cur Hcc
                          (Hsnd_cs c (or_introl eq_refl))) as Hec;
            destruct (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env c e_cur) as [u e_mid] eqn:Hec_eq;
            destruct Hec as (Hok_mid & Hsnd_mid & Hkeys_mid);
            pose proof (IHcs (fun c0 Hc0 => Hsnd_cs c0 (or_intror Hc0))
                             (fun c0 Hc0 => Hcons_cs c0 (or_intror Hc0))
                             e_mid Hok_mid Hsnd_mid
                             (fun z Hz => Hkeys_mid z (Hmono_cur z Hz))) as HIH;
            destruct (list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) cs' e_mid) as [u2 e2] eqn:Hlm2;
            destruct HIH as (Hok2 & Hsnd2 & Hkeys2);
            cbn [Mseq Mbind Mret StateMonad.state_monad];
            rewrite Hec_eq; rewrite Hlm2;
            split; [exact Hok2|]; split; [exact Hsnd2|];
            intros z Hz; apply Hkeys2; apply Hkeys_mid; exact Hz ]).
    pose proof (Hphase2 (const_clauses idx symbol r)
      (fun c0 Hc0 => in_all _ _ _ Hsnd_c Hc0)
      (fun c0 Hc0 x0 Hx0 => Hcl_cons c0 Hc0 (in_all _ _ _ Hsnd_c Hc0) x0 Hx0)
      e1 Hok1 Hsnd1 (fun z Hz => Hz)) as Hp2.
    destruct (list_Miter (exec_clause idx Eqb_idx idx_zero symbol symbol_map idx_map idx_trie analysis_result env) (const_clauses idx symbol r) e1) as [u2 e2] eqn:Hlm_c.
    destruct Hp2 as (Hok2 & Hsnd2 & Hkeys2).
    cbn [fst snd].
    assert (Hun_cons : forall p, In p (const_unifications idx symbol r) ->
      exists vx vy, map.get env (fst p) = Some vx /\ map.get env (snd p) = Some vy
                    /\ Sep.has_key vx (parent (equiv e1)) /\ Sep.has_key vy (parent (equiv e1))
                    /\ eq_sound_for_model idx symbol idx_map m i1 vx vy)
      by (intros p Hp;
          destruct (Hcov_u p Hp) as [Hcx Hcy];
          destruct (Hcons1 (fst p) Hcx) as (vx & Hevx & Hkvx & Hivx);
          destruct (Hcons1 (snd p) Hcy) as (vy & Hevy & Hkvy & Hivy);
          pose proof (in_all _ _ _ Hsnd_u Hp) as Hequ;
          exists vx, vy;
          split; [exact Hevx|]; split; [exact Hevy|]; split; [exact Hkvx|]; split; [exact Hkvy|];
          unfold eq_sound_for_model in Hequ |- *;
          destruct (map.get a_src (fst p)) as [dx|] eqn:Hax; cbn [Is_Some_satisfying] in Hequ; [|tauto];
          destruct (map.get a_src (snd p)) as [dy|] eqn:Hay; cbn [Is_Some_satisfying] in Hequ; [|tauto];
          rewrite (Hivx dx eq_refl); cbn [Is_Some_satisfying];
          rewrite (Hivy dy eq_refl); cbn [Is_Some_satisfying]; exact Hequ).
    assert (Hphase3 : forall ps,
      (forall p, In p ps -> exists vx vy, map.get env (fst p) = Some vx /\ map.get env (snd p) = Some vy
                    /\ Sep.has_key vx (parent (equiv e1)) /\ Sep.has_key vy (parent (equiv e1))
                    /\ eq_sound_for_model idx symbol idx_map m i1 vx vy) ->
      forall e_cur, egraph_ok e_cur -> egraph_sound_for_interpretation i1 e_cur ->
      (forall z, Sep.has_key z (parent (equiv e1)) -> Sep.has_key z (parent (equiv e_cur))) ->
      match list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) ps e_cur with
      | (_, e3) => egraph_ok e3 /\ egraph_sound_for_interpretation i1 e3
                   /\ (forall z, Sep.has_key z (parent (equiv e_cur)) -> Sep.has_key z (parent (equiv e3)))
      end)
      by (induction ps as [|p ps' IHps]; intros Hcons_ps e_cur Hok_cur Hsnd_cur Hmono_cur;
          [ cbn [list_Miter]; split; [exact Hok_cur|]; split; [exact Hsnd_cur|]; intros z Hz; exact Hz
          | cbn [list_Miter]; destruct p as [px py];
            destruct (Hcons_ps (px,py) (or_introl eq_refl)) as (vx & vy & Hevx & Hevy & Hkvx & Hkvy & Hequ);
            cbn [fst snd] in Hevx, Hevy;
            cbn [Mseq Mbind Mret StateMonad.state_monad];
            rewrite Hevx, Hevy; cbn [unwrap_with_default];
            pose proof Hok_cur as Hok_cur2; destruct Hok_cur2 as [Hroots_cur _ _ _];
            pose proof (@union_preserves_egraph_ok_sem idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result H vx vy e_cur Hok_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy)) as Hok_mid;
            pose proof (@union_preserves_sound_sem idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result H m Hm vx vy i1 e_cur Hok_cur Hsnd_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy) Hequ) as Hsnd_mid;
            pose proof (fun z Hz => @union_extends_keys_sem idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol symbol_map idx_map idx_map_ok idx_trie analysis_result H vx vy e_cur Hroots_cur (Hmono_cur vx Hkvx) (Hmono_cur vy Hkvy) z Hz) as Hkeys_mid;
            destruct (Defs.union vx vy e_cur) as [vu e_mid] eqn:Hu_eq;
            cbn [snd] in Hok_mid, Hsnd_mid, Hkeys_mid;
            pose proof (IHps (fun p0 Hp0 => Hcons_ps p0 (or_intror Hp0)) e_mid Hok_mid Hsnd_mid
                         (fun z Hz => Hkeys_mid z (Hmono_cur z Hz))) as HIH;
            destruct (list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) ps' e_mid) as [vu2 e3] eqn:Hlm3;
            destruct HIH as (Hok3 & Hsnd3 & Hkeys3);
            split; [exact Hok3|]; split; [exact Hsnd3|];
            intros z Hz; apply Hkeys3; apply Hkeys_mid; exact Hz ]).
    pose proof (Hphase3 (const_unifications idx symbol r) Hun_cons e2 Hok2 Hsnd2 Hkeys2) as Hp3.
    destruct (list_Miter (fun '(x,y) => Defs.union (unwrap_with_default (map.get env x)) (unwrap_with_default (map.get env y))) (const_unifications idx symbol r) e2) as [u3 e3] eqn:Hlm_u.
    destruct Hp3 as (Hok3 & Hsnd3 & Hkeys3).
    split; [exact Hok3|].
    split; [intros z Hz; apply Hkeys3; apply Hkeys2; apply Hmono1; exact Hz|].
    exists i1. split; [exact Hext1|exact Hsnd3].
  Qed.

  Definition const_rule_sound (a_src : idx_map (domain symbol m)) (r : const_rule idx symbol) : Prop :=
    List.NoDup (const_vars idx symbol r)
    /\ (forall x, In x (const_vars idx symbol r) -> exists d, map.get a_src x = Some d /\ domain_wf symbol m d)
    /\ (forall c, In c (const_clauses idx symbol r) -> forall x, In x (c.(atom_ret) :: c.(atom_args)) -> In x (const_vars idx symbol r))
    /\ (forall p, In p (const_unifications idx symbol r) -> In (fst p) (const_vars idx symbol r) /\ In (snd p) (const_vars idx symbol r))
    /\ all (atom_sound_for_model idx symbol idx_map m a_src) (const_clauses idx symbol r)
    /\ all (fun p => eq_sound_for_model idx symbol idx_map m a_src (fst p) (snd p)) (const_unifications idx symbol r).

  Lemma process_const_rules_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (Hm2 : model_ok symbol m)
    (rs : rule_set idx symbol symbol_map idx_map)
    (Hcr : forall r, In r (compiled_const_rules idx symbol symbol_map idx_map rs) -> exists a_src, const_rule_sound a_src r) :
    forall (i : idx_map (domain symbol m)) e,
      egraph_ok e ->
      egraph_sound_for_interpretation i e ->
      egraph_ok (snd (process_const_rules idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result rs e))
      /\ exists i', map.extends i' i
                    /\ egraph_sound_for_interpretation i' (snd (process_const_rules idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result rs e)).
  Proof.
    intros i e Hok Hsnd.
    unfold process_const_rules.
    set (crs := compiled_const_rules idx symbol symbol_map idx_map rs).
    assert (Hcr' : forall r, In r crs -> exists a_src, const_rule_sound a_src r)
      by (intros r Hr; exact (Hcr r Hr)).
    clearbody crs.
    revert i e Hok Hsnd.
    induction crs as [|cr crs' IHcrs]; intros i e Hok Hsnd.
    - cbn [list_Miter Mbind Mret StateMonad.state_monad fst snd].
      split; [exact Hok|].
      exists i. split; [apply Properties.map.extends_refl|exact Hsnd].
    - cbn [list_Miter Mbind Mret StateMonad.state_monad fst snd].
      destruct (Hcr' cr (or_introl eq_refl)) as (a_src & Hnd & Hwf & Hcov_c & Hcov_u & Hsnd_c & Hsnd_u).
      pose proof (exec_const_sound Hlti Hlts Hltt Hm2 i cr e a_src Hnd Hwf Hcov_c Hcov_u Hsnd_c Hsnd_u Hok Hsnd) as Hec.
      destruct (exec_const idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result cr e) as [u1 e1] eqn:Hec_eq.
      cbn [fst snd] in Hec.
      destruct Hec as (Hok1 & _Hmono1 & i1 & Hext1 & Hsnd1).
      assert (Hcr'_tail : forall r, In r crs' -> exists a_src, const_rule_sound a_src r)
        by (intros r Hr; exact (Hcr' r (or_intror Hr))).
      pose proof (IHcrs Hcr'_tail i1 e1 Hok1 Hsnd1) as HIH.
      destruct (list_Miter (exec_const idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie analysis_result) crs' e1) as [u2 e2] eqn:Hlm2.
      destruct HIH as (Hok2 & i2 & Hext2 & Hsnd2).
      cbn [Mseq Mbind Mret StateMonad.state_monad fst snd] in *.
      rewrite Hec_eq. cbn [fst snd].
      rewrite Hlm2. cbn [snd].
      split; [exact Hok2|].
      exists i2. split; [exact (map_extends_trans i2 i1 i Hext2 Hext1)|exact Hsnd2].
  Qed.

End Slice.
