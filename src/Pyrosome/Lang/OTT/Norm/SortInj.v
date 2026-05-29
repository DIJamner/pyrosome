Set Implicit Arguments.
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List. Import ListNotations.
Open Scope string. Open Scope list.
From Utils Require Import Utils Permutation.
From Pyrosome.Theory Require Import Core CutFreeInd WfCutElim ModelImpls.
From Pyrosome.Tools Require Import Resolution.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Model ApplyLemmas.
From Pyrosome.Lang.OTT Require Import Base Nat.
Import Core.Notations.

(* ===== Basic facts about fo_lang ===== *)

Lemma fo_wf_lang : wf_lang fo_lang.
Proof. unfold fo_lang. prove_by_lang_db. Qed.

Lemma fo_all_fresh : all_fresh fo_lang.
Proof. compute_all_fresh. Qed.

(* Helper: no sort_eq_rule in fo_lang *)
Lemma fo_no_sort_eq (name : string) c' t1 t2 :
    In (name, sort_eq_rule c' t1 t2) fo_lang -> False.
Proof.
  intro Hin.
  assert (Hb : forallb (fun p => match snd p with sort_eq_rule _ _ _ => false | _ => true end)
                       fo_lang = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  apply Hb in Hin. cbn in Hin. discriminate Hin.
Qed.

(* Helper: no env-headed sort in any term_eq_rule conclusion *)
Lemma fo_no_env_term_eq (rname : string) c' e1 e2 shead sargs :
    In (rname, term_eq_rule c' e1 e2 (scon shead sargs)) fo_lang ->
    shead <> "env".
Proof.
  intro Hin.
  assert (Hb : forallb (fun p => match snd p with
                                 | term_eq_rule _ _ _ (scon nm _) =>
                                     negb (String.eqb nm "env")
                                 | _ => true
                                 end) fo_lang = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  apply Hb in Hin. cbn in Hin.
  intro Heq. subst shead.
  cbn in Hin. discriminate Hin.
Qed.

(* ===== Sort Injectivity (Lemma 1) ===== *)

Definition Pinj (t1 t2 : sort string) : Prop :=
  forall n s1, t1 = scon n s1 ->
    exists s2 c' args, t2 = scon n s2
                    /\ In (n, sort_rule c' args) fo_lang
                    /\ eq_args (Model := core_model fo_lang) [] c' s1 s2.

Section SortInj.
  Let l : lang string := fo_lang.
  Let wfl : wf_lang l := fo_wf_lang.
  Let c : @ctx string := [].
  Let wfc : wf_ctx (Model := core_model l) c := wf_ctx_nil.

  Lemma eq_sort_inj : forall t1 t2,
      eq_sort l c t1 t2 -> Pinj t1 t2.
  Proof.
    intros t1 t2 H.
    enough (Hind : (forall t t0, eq_sort l c t t0 -> Pinj t t0) /\
                   (forall s t t0, eq_term l c s t t0 -> True) /\
                   (forall c0 s s0, eq_subst (Model := core_model l) c c0 s s0 -> True) /\
                   (forall c0 s s0, eq_args (Model := core_model l) c c0 s s0 -> True))
      by (destruct Hind as [Hind' _]; exact (Hind' t1 t2 H)).
    apply (@cut_ind string _ _ _ l wfl c wfc Pinj
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)).
    - (* Hsort0: sort_eq_rule - impossible *)
      intros c' name t1' t2' s1 s2 Hin _ _.
      exfalso. exact (fo_no_sort_eq Hin).
    - (* Hsort1: sort congruence *)
      intros c_r name_r args_r s1 s2 Hin Heqa _.
      intros n s Heq.
      injection Heq. intros Hs Hn. subst n s.
      exists s2, c_r, args_r. eauto.
    - (* Hsort2: transitivity *)
      intros t1' t12 t2' _ IH1 _ IH2.
      intros n s Hts.
      destruct (IH1 n s Hts) as [s12 [c1 [a1 [Ht12 [Hin1 Ha1]]]]].
      destruct (IH2 n s12 Ht12) as [s2 [c2 [a2 [Ht2 [Hin2 Ha2]]]]].
      pose proof (proj2 (all_fresh_named_list_lookup_err_in fo_lang n
                           (sort_rule c1 a1) fo_all_fresh) Hin1) as Hl1.
      pose proof (proj2 (all_fresh_named_list_lookup_err_in fo_lang n
                           (sort_rule c2 a2) fo_all_fresh) Hin2) as Hl2.
      rewrite <- Hl1 in Hl2. injection Hl2. intros Ha_eq Hc_eq. subst c2 a2.
      assert (Hwf1 : wf_ctx (Model := core_model l) c1)
        by (eapply rule_in_ctx_wf; [exact fo_wf_lang | exact Hin1 | reflexivity]).
      exists s2, c1, a1. split; [exact Ht2|]. split; [exact Hin1|].
      eapply eq_args_trans;
        [exact (core_model_ok fo_wf_lang) | exact Hwf1 | exact Ha1 | exact Ha2].
    - (* Hsort3: symmetry - prove Pinj t2' t1' from Pinj t1' t2' *)
      intros t1' t2' _ IH.
      intros n s Hts.
      (* t1' is scon m args1 for some m, args1 (only constructor) *)
      destruct t1' as [m args1].
      (* Apply IH to t1' = scon m args1 to get t2' = scon m s12 *)
      destruct (IH m args1 eq_refl) as [s12 [c_r [a_r [Ht12 [Hin Ha12]]]]].
      (* Ht12 : t2' = scon m s12, Hts : t2' = scon n s *)
      rewrite Hts in Ht12.
      injection Ht12 as Heqn Heqs.
      (* Heqn : n = m, Heqs : s = s12; Ha12 : eq_args [] c_r args1 s12 *)
      subst m. (* replace m by n *) subst s12. (* replace s12 by s *)
      (* Hin : In (n, sort_rule c_r a_r) fo_lang, Ha12 : eq_args [] c_r args1 s *)
      assert (Hwf_r : wf_ctx (Model := core_model l) c_r)
        by (eapply rule_in_ctx_wf; [exact fo_wf_lang | exact Hin | reflexivity]).
      (* Goal: exists s2 c' a', scon n args1 = scon n s2 /\ In (n, ...) /\ eq_args [] c' s s2 *)
      exists args1, c_r, a_r. split; [reflexivity|]. split; [exact Hin|].
      eapply eq_args_sym;
        [exact (core_model_ok fo_wf_lang) | exact Hwf_r | exact Ha12].
    - (* f: term_eq_rule -> True *) intros; exact I.
    - (* f0: term cong -> True *)   intros; exact I.
    - (* f01: term var -> True *)   intros; exact I.
    - (* f1: term trans -> True *)  intros; exact I.
    - (* f2: term sym -> True *)    intros; exact I.
    - (* f3: term conv -> True *)   intros; exact I.
    - (* f4: subst nil -> True *)   exact I.
    - (* f5: subst cons -> True *)  intros; exact I.
    - (* f6: args nil -> True *)    exact I.
    - (* f7: args cons -> True *)   intros; exact I.
  Qed.

End SortInj.

(* ===== Env ctx_len preservation (Lemma 2) ===== *)

Definition Penv (s : sort string) (e1 e2 : @term string) : Prop :=
  s = scon "env" [] -> ctx_len e1 = ctx_len e2.

(* For the ext rule, the rule context is uniquely determined: first var is G : env *)
(* We use all_fresh + vm_compute to determine the rule lookup value *)
Lemma fo_ext_rule_first_var_env (c' : @ctx string) args (t : sort string) :
    In ("ext", term_rule c' args t) fo_lang ->
    named_list_lookup_err c' "G" = Some (scon "env" []).
Proof.
  intro Hin.
  apply (proj2 (all_fresh_named_list_lookup_err_in fo_lang "ext"
                  (term_rule c' args t) fo_all_fresh)) in Hin.
  vm_compute in Hin.
  (* Hin is now a concrete equation. Inversion gives us c'. *)
  inversion Hin as [Hinner].
  (* subst c' to the computed value and reflect *)
  vm_compute. reflexivity.
Qed.

Section EnvCtxLen.
  Let l : lang string := fo_lang.
  Let wfl : wf_lang l := fo_wf_lang.
  Let c : @ctx string := [].
  Let wfc : wf_ctx (Model := core_model l) c := wf_ctx_nil.

  Lemma env_ctxlen_eq : forall a b,
      eq_term l c (scon "env" []) a b -> ctx_len a = ctx_len b.
  Proof.
    intros a b H.
    enough (Penv (scon "env" []) a b) by (apply H0; reflexivity).
    revert H.
    apply (@term_cut_ind string _ _ _ l wfl c wfc Penv).
    - (* f: term_eq_rule *)
      intros c' name t e1 e2 s1 s2 Hin _ _ Hs.
      destruct t as [nt at_]. cbn in Hs. injection Hs. intros _ Hnt. subst nt.
      exact (False_ind _ (fo_no_env_term_eq Hin eq_refl)).
    - (* f0: term congruence *)
      intros c' name t args s1 s2 Hin Heqa IHargs Hs.
      destruct t as [nt at_]. cbn in Hs. injection Hs. intros _ Hnt. subst nt.
      assert (Hnames : name = "emp" \/ name = "ext").
      {
        assert (Hb : forallb (fun p => match snd p with
                                       | term_rule _ _ (scon nm _) =>
                                           implb (String.eqb nm "env")
                                                 (orb (String.eqb (fst p) "emp")
                                                      (String.eqb (fst p) "ext"))
                                       | _ => true
                                       end) fo_lang = true) by (vm_compute; reflexivity).
        rewrite forallb_forall in Hb. apply Hb in Hin. cbn in Hin.
        (* After cbn, Hin : orb (eqb name "emp") (eqb name "ext") = true *)
        rewrite Bool.orb_true_iff in Hin.
        destruct Hin as [H1|H2].
        - left.  apply String.eqb_eq. exact H1.
        - right. apply String.eqb_eq. exact H2.
      }
      destruct Hnames as [Hemp|Hext].
      + subst name. reflexivity.
      + subst name.
        (* Determine c' for the ext rule via vm_compute on the lookup *)
        (* The ext rule is: term_rule [("A", ty["G","i"]); ("i", tyinfo); ("G", env)] ["A";"G"] env *)
        pose proof (proj2 (all_fresh_named_list_lookup_err_in fo_lang "ext"
                             (term_rule c' args (scon "env" at_)) fo_all_fresh) Hin) as Hlook.
        vm_compute in Hlook.
        (* Hlook : Some (term_rule c' args scon "env" at_) = Some (term_rule [exact...] ["A";"G"] scon "env" []) *)
        inversion Hlook as [Hconc]. subst c'. subst args. subst at_.
        (* Now c' = [("A", scon "ty" [con "G" []; con "i" []]); ("i", scon "tyinfo" []); ("G", scon "env" [])] *)
        (* P_args c' s1 s2 has structure: *)
        (*   P_args (("G",env)::rest') s1' s2' /\ Penv Aty[...] A1 A2         -- innermost from "A" *)
        (* Wait: P_args iterates from head to tail. For c' = [A, i, G]: *)
        (*   P_args [A,i,G] [a1;i1;g1] [a2;i2;g2] = P_args [i,G] [i1;g1] [i2;g2] /\ Penv Aty a1 a2 *)
        (*   = (P_args [G] [g1] [g2] /\ Penv ity i1 i2) /\ Penv Aty a1 a2      *)
        (*   = ((P_args [] [] [] /\ Penv env g1 g2) /\ Penv ity i1 i2) /\ Penv Aty a1 a2 *)
        (*   = ((True /\ Penv (scon "env" []) g1 g2) /\ ...) /\ ...             *)
        (* Use eq_args length lemmas to determine s1 and s2 have length 3 *)
        assert (Hlen1 : length s1 = 3).
        { pose proof (Model.eq_args_length_eq_l (Model := core_model fo_lang) Heqa).
          simpl in H. exact (eq_sym H). }
        assert (Hlen2 : length s2 = 3).
        { pose proof (Model.eq_args_length_eq_r (Model := core_model fo_lang) Heqa).
          simpl in H. exact (eq_sym H). }
        destruct s1 as [|A1 [|i1 [|G1 [|]]]]; simpl in Hlen1; try discriminate.
        destruct s2 as [|A2 [|i2 [|G2 [|]]]]; simpl in Hlen2; try discriminate.
        (* IHargs : ((True /\ Penv (scon "env" []) G1 G2) /\ Penv ity[...] i1 i2) /\ Penv Aty[...] A1 A2 *)
        destruct IHargs as [[[_ HG] _] _].
        cbn in HG. specialize (HG eq_refl).
        cbn. rewrite HG. reflexivity.
    - (* f01: variable - In (n, scon "env" []) [] is False *)
      intros n t Hin. exact (False_ind _ (List.in_nil Hin)).
    - (* f1: trans *)
      intros t e1 e12 e2 _ IH1 _ IH2 Hs.
      exact (eq_trans (IH1 Hs) (IH2 Hs)).
    - (* f2: sym *)
      intros t e1 e2 _ IH Hs. exact (eq_sym (IH Hs)).
    - (* f3: conv - Penv t' e1 e2 from Penv t e1 e2 and eq_sort t t' *)
      intros t t' Heqs e1 e2 _ IH Hs.
      (* Hs : t' = scon "env" [], IH : Penv t e1 e2 *)
      (* Apply IH: need t = scon "env" [] *)
      (* From eq_sort l [] t t' and t' = scon "env" [], get t ~ scon "env" [] *)
      subst t'.
      apply eq_sort_sym in Heqs.
      apply eq_sort_inj in Heqs.
      unfold Pinj in Heqs.
      destruct (Heqs "env" [] eq_refl) as [s2 [c'' [args'' [Ht [Hin_env Heqa2]]]]].
      (* s2 comes from eq_args [] c'' [] s2, and c'' = [] since env is sort_rule [] [] *)
      (* Derive c'' = [] and s2 = [] from Hin_env *)
      pose proof (proj2 (all_fresh_named_list_lookup_err_in fo_lang "env"
                           (sort_rule c'' args'') fo_all_fresh) Hin_env) as Hlook_env.
      vm_compute in Hlook_env. inversion Hlook_env as [Henv_conc]. subst c''. subst args''.
      (* Now eq_args [] [] [] s2, so s2 = [] *)
      inversion Heqa2. subst s2.
      (* Ht : t = scon "env" [] *)
      apply IH. exact Ht.
  Qed.

End EnvCtxLen.

(* ===== Sub codomain ctx_len (Lemma 3) ===== *)

Lemma sub_codomain_ctxlen : forall (a b c d : @term string),
    eq_sort fo_lang [] (scon "sub" [a;b]) (scon "sub" [c;d]) ->
    ctx_len a = ctx_len c.
Proof.
  intros a b c d H.
  apply eq_sort_inj in H.
  unfold Pinj in H.
  destruct (H "sub" [a;b] eq_refl) as [s2 [c' [args' [Hs2 [Hin Heqa]]]]].
  injection Hs2. intro Hs2eq. subst s2.
  (* eq_args (Model := core_model fo_lang) [] c' [a;b] [c;d] *)
  (* c' is the sub sort rule context: [G:env; G':env] *)
  (* Determine c' by vm_compute on the sub rule lookup *)
  pose proof (proj2 (all_fresh_named_list_lookup_err_in fo_lang "sub"
                       (sort_rule c' args') fo_all_fresh) Hin) as Hlook_sub.
  vm_compute in Hlook_sub.
  inversion Hlook_sub as [Hsub_conc]. subst c'. subst args'.
  (* c' = [("G'", env); ("G", env)], args' = ["G'"; "G"] *)
  (* eq_args [] [("G'",env);("G",env)] [a;b] [c;d] *)
  (* First arg: a corresponds to G' (env), c corresponds to G' (env) *)
  rewrite invert_eq_args_cons in Heqa.
  destruct Heqa as [_ Heqa_G].
  (* Heqa_G : eq_term [] (scon "env" []) [/with_names_from [("G'",env)] [d]/] a c *)
  cbn in Heqa_G.
  exact (env_ctxlen_eq Heqa_G).
Qed.

(* ===== Helper: nth_default is irrelevant when index is in range ===== *)
Lemma nth_default_irrel_sval (l : ssub) (k : nat) (d1 d2 : sval) :
    k < length l -> nth_default d1 l k = nth_default d2 l k.
Proof.
  intro Hlt.
  unfold nth_default.
  assert (He : nth_error l k <> None).
  { rewrite nth_error_Some. exact Hlt. }
  destruct (nth_error l k); [reflexivity | contradiction].
Qed.

(* ===== (B) map_apply_id_list ===== *)
Lemma map_apply_id_list : forall (sf : ssub) n,
    length sf = n -> map (apply_val sf) (id_list n) = sf.
Proof.
  intros sf n Hlen.
  unfold id_list.
  rewrite map_map.
  (* map (fun k => apply_val sf (vNe (nVar k))) (seq 0 n) = sf *)
  (* apply_val sf (vNe (nVar k)) = nth_default (vNe (nVar k)) sf k *)
  (* = nth k sf (vNe (nVar k))  by nth_default_eq *)
  (* = nth k sf (vNe (nVar 0))  for k < n = length sf (by nth_default_irrel) *)
  erewrite map_ext_in.
  2: {
    intros k Hk.
    cbn.
    apply (@nth_default_irrel_sval sf k (vNe (nVar k)) (vNe (nVar 0))).
    subst n. apply in_seq in Hk. Lia.lia.
  }
  (* map (fun k => nth_default (vNe (nVar 0)) sf k) (seq 0 n) = sf *)
  erewrite map_ext.
  2: { intro k. apply nth_default_eq. }
  subst n.
  apply map_seq_nth.
Qed.

(* ===== (B) map_apply_wkn_list ===== *)
Lemma map_apply_wkn_list : forall (sg : ssub) (vv : sval) n,
    length sg = n -> map (apply_val (vv :: sg)) (wkn_list n) = sg.
Proof.
  intros sg vv n Hlen.
  unfold wkn_list.
  rewrite map_map.
  (* map (fun k => apply_val (vv::sg) (vNe (nVar (S k)))) (seq 0 n) = sg *)
  erewrite map_ext_in.
  2: {
    intros k Hk.
    cbn.
    unfold nth_default. simpl (nth_error (vv :: sg) (S k)).
    change (match nth_error sg k with Some x => x | None => vNe (nVar (S k)) end)
    with (nth_default (vNe (nVar (S k))) sg k).
    apply (@nth_default_irrel_sval sg k (vNe (nVar (S k))) (vNe (nVar 0))).
    subst n. apply in_seq in Hk. Lia.lia.
  }
  (* map (fun k => nth_default (vNe (nVar 0)) sg k) (seq 0 n) = sg *)
  erewrite map_ext.
  2: { intro k. apply nth_default_eq. }
  subst n.
  apply map_seq_nth.
Qed.

(* ===== (A) eval_sub_len_wf ===== *)

(* Tactic to pin a rule from an In hypothesis using fo_all_fresh *)
Ltac pin_rule Hin :=
  apply (proj2 (all_fresh_named_list_lookup_err_in _ _ _ fo_all_fresh)) in Hin;
  vm_compute in Hin;
  injection Hin; clear Hin; intros; subst.

Lemma eval_sub_len : forall Gin Gout g sg,
    eval_sub Gin Gout g sg -> length sg = length Gin.
Proof.
  intros Gin Gout g sg H. induction H.
  - unfold id_list. rewrite length_map, length_seq. reflexivity.
  - unfold wkn_list. rewrite length_map, length_seq. reflexivity.
  - reflexivity.
  - rewrite length_map. assumption.
  - cbn [length]. rewrite length_map. f_equal. assumption.
Qed.
