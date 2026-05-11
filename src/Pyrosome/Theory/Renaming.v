Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core Theory.CutFreeInd.



#[local] Notation eq_subst l :=
  (eq_subst (Model:= core_model l)).
#[local] Notation eq_args l :=
  (eq_args (Model:= core_model l)).
#[local] Notation wf_subst l :=
  (wf_subst (Model:= core_model l)).
#[local] Notation wf_args l :=
  (wf_args (Model:= core_model l)).
#[local] Notation wf_ctx l :=
  (wf_ctx (Model:= core_model l)).


(*TODO: check if this is defined somewhere.
    If not, move it to Utils.v
 *)
Definition Injective {A B : Type} (f : A -> B) := forall a a', f a = f a' -> a = a'.

Definition Injective_on {A B : Type} (S : A -> Prop) (f : A -> B) :=
  forall a a', S a -> S a' -> f a = f a' -> a = a'.

Lemma Injective_to_Injective_on {A B} (S : A -> Prop) (f : A -> B)
  : Injective f -> Injective_on S f.
Proof. unfold Injective, Injective_on; eauto. Qed.

Lemma Injective_on_weaken {A B} (S S' : A -> Prop) (f : A -> B)
  : (forall a, S a -> S' a) -> Injective_on S' f -> Injective_on S f.
Proof. unfold Injective_on; eauto. Qed.

Section Injective.
  Context (A B : Type)
    {Eqb_A : Eqb A}
    {Eqb_B : Eqb B}
    {Eqb_ok_A : Eqb_ok Eqb_A}
    {Eqb_ok_B : Eqb_ok Eqb_B}
    (f : A -> B)
    (f_inj : Injective f).

  
  Lemma injective_in a l
    : In (f a) (map f l) ->
      In a l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
  Qed.

  #[local] Hint Resolve injective_in : utils.
  

  Fixpoint rename e :=
    match e with
    | var n => var (f n)
    | con n l => con (f n) (map rename l)
    end.

  
  Definition rename_subst : subst A -> _:=
    map (fun p => (f (fst p), rename (snd p))).
  
  Definition rename_sort t :=
    match t with
    | scon n l => scon (f n) (map rename l)
    end.

  Definition rename_ctx : ctx A -> _:=
    map (fun p => (f (fst p), rename_sort (snd p))).

  Definition rename_rule r :=
    match r with
    | sort_rule c args => sort_rule (rename_ctx c) (map f args)
    | term_rule c args t => term_rule (rename_ctx c) (map f args) (rename_sort t)
    | sort_eq_rule c t t' => sort_eq_rule (rename_ctx c) (rename_sort t) (rename_sort t')
    | term_eq_rule c e e' t =>
        term_eq_rule (rename_ctx c) (rename e) (rename e') (rename_sort t)
    end.
  
  Definition rename_lang : lang A -> _ :=
    map (fun p => (f (fst p), rename_rule (snd p))).

  Lemma rename_lookup s n
    : rename (subst_lookup s n) = subst_lookup (rename_subst s) (f n).
  Proof.
    induction s; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  (*TODO: make this export?*)
  #[local] Hint Rewrite rename_lookup : term.
  
  (*TODO: make this export & move to Utils?*)
  #[local] Hint Rewrite map_map : utils.
  
  Lemma rename_distr_subst e s
    : rename e[/s/] = (rename e) [/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; basic_term_crush.
    revert H.
    induction l; basic_goal_prep; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_distr_subst : term.

  
  Lemma rename_args_distr_subst e s
    : map rename e[/s/] = (map rename e) [/rename_subst s/].
  Proof.
    induction e; basic_goal_prep; fold_Substable; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_args_distr_subst : term.

  
  Lemma rename_sort_distr_subst e s
    : rename_sort e[/s/] = (rename_sort e) [/rename_subst s/].
  Proof.
    destruct e; basic_goal_prep; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_sort_distr_subst : term.

  
  Lemma rename_subst_distr_with_names_from c' s
    : rename_subst (with_names_from c' s)
      = with_names_from (rename_ctx c') (map rename s).
  Proof.
    revert s;
      induction c';
      destruct s;
      basic_goal_prep; fold_Substable; basic_term_crush.
  Qed.
  
  #[local] Hint Rewrite rename_subst_distr_with_names_from : term.
  

  Lemma rename_mono l
    : (forall c t1 t2,
          eq_sort l c t1 t2 ->
          eq_sort (rename_lang l) (rename_ctx c) (rename_sort t1) (rename_sort t2))
      /\ (forall c t e1 e2,
             eq_term l c t e1 e2 ->
             eq_term (rename_lang l) (rename_ctx c) (rename_sort t) (rename e1) (rename e2))
      /\ (forall c c' s1 s2,
             eq_subst l c c' s1 s2 ->
             eq_subst (rename_lang l) (rename_ctx c) (rename_ctx c')
               (rename_subst s1) (rename_subst s2))
      /\ (forall c t,
             wf_sort l c t ->
             wf_sort (rename_lang l) (rename_ctx c) (rename_sort t))
      /\ (forall c e t,
             wf_term l c e t ->
             wf_term (rename_lang l) (rename_ctx c) (rename e) (rename_sort t))
      /\ (forall c s c',
             wf_args l c s c' ->
             wf_args (rename_lang l) (rename_ctx c) (map rename s) (rename_ctx c'))
      /\ (forall c,
             wf_ctx l c ->
             wf_ctx (rename_lang l) (rename_ctx c)).
  Proof using f_inj Eqb_ok_A Eqb_ok_B.
    apply judge_ind; basic_goal_prep.
    all:
      let l := lazymatch goal with l : lang _ |- _ => l end in
      try lazymatch goal with
          H : In _ l |- _ => 
            eapply in_map in H
        end.
    {
      eapply eq_sort_by.
      exact H.
    }
    all: basic_core_crush.
    {
      eapply eq_sort_trans; eauto.
    }
    {
      eapply eq_sort_sym; eauto.
    }
    {
      eapply eq_term_by.
      exact H.
    }
    {
      eapply eq_term_trans; eauto.
    }
    {
      eapply eq_term_sym; eauto.
    }
    {
      eapply wf_sort_by; eauto.
      exact H.
    }
    {
      eapply wf_term_by; eauto.
      exact H.
    }
    {
      eapply wf_term_var; eauto.
      eapply in_map in H.
      exact H.
    }
    {
      intro.
      apply H.
      eapply injective_in.
      unfold rename_ctx in *.
      rewrite !map_map in *; simpl in *; auto.
    }
  Qed.

  (*TODO: move to Lists.v*)  
  Lemma combine_map_projections {C D} (n : list (C * D))
    : (combine (map fst n) (map snd n)) = n.
  Proof.
    induction n;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma sublist_map {C D} (g : C -> D) l1 l2
    : sublist l1 l2 ->
      sublist (map g l1) (map g l2).
  Proof.
    revert l1;
      induction l2;
      destruct l1;
      basic_goal_prep;
      basic_utils_crush.
    change ((g c :: map g l1)) with (map g (c::l1)).
    eauto.
  Qed.
  #[local] Hint Resolve sublist_map : utils.
  
  Lemma rename_rule_mono l r
    : wf_rule l r ->
      wf_rule (rename_lang l) (rename_rule r).
  Proof.
    destruct r;
      basic_goal_prep;
      basic_core_crush.
    all: try eapply rename_mono; auto.
    all: unfold rename_ctx;
      rewrite !map_map;
      simpl.
    all: rewrite <- map_map with (f:=fst).
    all: eauto with utils.
  Qed.

  Lemma rename_lang_mono l
    : wf_lang l -> wf_lang (rename_lang l).
  Proof.
    induction l; basic_goal_prep;
      basic_core_crush.
    2: eauto using rename_rule_mono.
    clear H1.
    unfold rename_lang.
    unfold fresh in *.
    intro H'; apply H0.
    basic_utils_crush.
    rewrite in_map_iff in H'; break.
    simpl in *.
    apply f_inj in H1; subst.
    eapply pair_fst_in; eauto.
  Qed.

  Lemma rename_lang_mono_ext l_pre l
    (* TODO: probably don't need 1st assumption*)
    : wf_lang l_pre -> wf_lang_ext l_pre l -> wf_lang_ext (rename_lang l_pre) (rename_lang l).
  Proof.
    intros.
    eapply wf_lang_concat_iff.
    unfold rename_lang; rewrite <- map_app.
    eapply rename_lang_mono.
    basic_core_crush.
  Qed.
    
End Injective.


Arguments rename_lang_mono {A B}%type_scope {Eqb_A Eqb_B Eqb_ok_A Eqb_ok_B}
  [f]%function_scope f_inj [l]%lang_scope _.
#[export] Hint Resolve rename_lang_mono : lang_core.


Section InjectiveOn.
  Context (A B : Type)
    {Eqb_A : Eqb A}
    {Eqb_B : Eqb B}
    {Eqb_ok_A : Eqb_ok Eqb_A}
    {Eqb_ok_B : Eqb_ok Eqb_B}
    {V_default : WithDefault A}
    {V_default_B : WithDefault B}
    (S : A -> Prop)
    (f : A -> B)
    (f_inj_S : Injective_on S f).

  Fixpoint term_in_S (e : @term A) : Prop :=
    match e with
    | var n => S n
    | con n l => S n /\ all term_in_S l
    end.

  Definition sort_in_S (t : @sort A) : Prop :=
    match t with scon n l => S n /\ all term_in_S l end.

  Definition subst_in_S (s : @subst A) : Prop :=
    all (fun p => S (fst p) /\ term_in_S (snd p)) s.

  Definition ctx_in_S (c : @ctx A) : Prop :=
    all (fun p => S (fst p) /\ sort_in_S (snd p)) c.

  Definition rule_in_S (r : @rule A) : Prop :=
    match r with
    | sort_rule c args => ctx_in_S c /\ all S args
    | term_rule c args t => ctx_in_S c /\ all S args /\ sort_in_S t
    | sort_eq_rule c t1 t2 => ctx_in_S c /\ sort_in_S t1 /\ sort_in_S t2
    | term_eq_rule c e1 e2 t =>
        ctx_in_S c /\ term_in_S e1 /\ term_in_S e2 /\ sort_in_S t
    end.

  Definition lang_in_S (l : @lang A) : Prop :=
    all (fun p => S (fst p) /\ rule_in_S (snd p)) l.

  Lemma lang_in_S_in n r l_ :
    lang_in_S l_ -> In (n, r) l_ -> S n /\ rule_in_S r.
  Proof. induction l_; basic_goal_prep; basic_utils_crush. Qed.

  Lemma ctx_in_S_in n t c :
    ctx_in_S c -> In (n, t) c -> S n /\ sort_in_S t.
  Proof. induction c; basic_goal_prep; basic_utils_crush. Qed.

  Lemma lang_in_S_app l1 l2 :
    lang_in_S l1 -> lang_in_S l2 -> lang_in_S (l1 ++ l2).
  Proof. unfold lang_in_S. intros. apply all_app. split; auto. Qed.

  Lemma injective_in_S a l_
    : S a -> all S l_ ->
      In (f a) (map f l_) -> In a l_.
  Proof.
    intros Ha Hl Hin.
    induction l_; cbn in *; [tauto|].
    destruct Hl as [Ha' Hl].
    destruct Hin as [Heq | Hin]; [|right; auto].
    left. symmetry; apply f_inj_S; auto.
  Qed.

  Lemma rename_lookup_S s n
    : S n -> subst_in_S s ->
      rename f (subst_lookup s n) = subst_lookup (rename_subst f s) (f n).
  Proof.
    intros Hn Hs.
    induction s as [|[m e] s' IH]; cbn in *; [reflexivity|].
    destruct Hs as [[Hm He] Hs'].
    pose proof (eqb_spec n m) as Heq_nm.
    pose proof (eqb_spec (f n) (f m)) as Heq_fnm.
    destruct (eqb n m); destruct (eqb (f n) (f m)).
    - reflexivity.
    - exfalso; apply Heq_fnm; subst; reflexivity.
    - exfalso; apply Heq_nm; apply f_inj_S; auto.
    - apply IH; auto.
  Qed.

  Lemma rename_distr_subst_S e s
    : term_in_S e -> subst_in_S s ->
      rename f e[/s/] = (rename f e) [/rename_subst f s/].
  Proof.
    intros He Hs.
    induction e; cbn in *.
    - apply rename_lookup_S; assumption.
    - f_equal.
      destruct He as [Hn Hl].
      revert H Hl.
      induction l; cbn; intros HH Hl; [reflexivity|].
      destruct HH; destruct Hl.
      f_equal; auto.
  Qed.

  Lemma rename_args_distr_subst_S es s
    : all term_in_S es -> subst_in_S s ->
      map (rename f) es[/s/] = (map (rename f) es) [/rename_subst f s/].
  Proof.
    intros Hes Hs.
    induction es; cbn in *; fold_Substable; [reflexivity|].
    destruct Hes.
    f_equal; auto using rename_distr_subst_S.
  Qed.

  Lemma rename_sort_distr_subst_S t s
    : sort_in_S t -> subst_in_S s ->
      rename_sort f t[/s/] = (rename_sort f t) [/rename_subst f s/].
  Proof.
    destruct t; cbn; intros [Hn Hes] Hs; f_equal.
    apply rename_args_distr_subst_S; auto.
  Qed.

  Lemma term_subst_in_S e s
    : term_in_S e -> subst_in_S s -> term_in_S e[/s/].
  Proof.
    revert s.
    induction e using term_ind; intros s He Hs; cbn in *.
    - induction s as [|[m a] s' IH]; cbn in *; [exact He|].
      destruct Hs as [[Hm Ha] Hs'].
      destruct (eqb n m); auto.
    - destruct He as [Hn Hes].
      split; auto.
      revert H Hes.
      induction l; cbn in *; auto.
      intros [HP HPs] [Ha Has].
      split; auto.
      apply HP; auto.
  Qed.

  Lemma args_subst_in_S es s
    : all term_in_S es -> subst_in_S s -> all term_in_S es[/s/].
  Proof.
    induction es; cbn in *; fold_Substable; intros Hes Hs; auto.
    destruct Hes; split; auto using term_subst_in_S.
  Qed.

  Lemma sort_subst_in_S t s
    : sort_in_S t -> subst_in_S s -> sort_in_S t[/s/].
  Proof.
    destruct t; cbn; intros [Hn Hes] Hs; split; auto using args_subst_in_S.
  Qed.

  Lemma with_names_from_subst_in_S (c : @ctx A) (es : list (@term A))
    : ctx_in_S c -> all term_in_S es -> subst_in_S (with_names_from c es).
  Proof.
    revert es.
    induction c as [|[n t] c IH]; intros [|e es] Hc Hes; cbn in *; auto.
    destruct Hc as [[Hn Ht] Hc].
    destruct Hes as [He Hes].
    split; [split; auto | apply IH; auto].
  Qed.

  Lemma rename_lang_in n r l_ :
    In (n, r) l_ -> In (f n, rename_rule f r) (rename_lang f l_).
  Proof.
    intros Hin.
    apply (in_map (fun p => (f (fst p), rename_rule f (snd p)))) in Hin.
    exact Hin.
  Qed.

  Lemma rename_ctx_in n t c :
    In (n, t) c -> In (f n, rename_sort f t) (rename_ctx f c).
  Proof.
    intros Hin.
    apply (in_map (fun p => (f (fst p), rename_sort f (snd p)))) in Hin.
    exact Hin.
  Qed.

  Lemma rename_subst_with_names_from c' s :
    rename_subst f (with_names_from c' s)
    = with_names_from (rename_ctx f c') (map (rename f) s).
  Proof.
    revert s.
    induction c' as [|[n t] c' IH]; intros [|e s]; cbn in *; auto.
    f_equal; auto.
  Qed.

  (* Extract wf_ctx of an intermediate context c' from In ... l
     and wf_lang. *)
  Lemma rename_ctx_wf_from_eq_rule (lr : @lang B) (name : B) (c' : @ctx A)
        (t1 t2 : @sort A) :
    wf_lang lr ->
    In (name, sort_eq_rule (rename_ctx f c') (rename_sort f t1) (rename_sort f t2)) lr ->
    wf_ctx lr (rename_ctx f c').
  Proof.
    intros Hwf Hin.
    pose proof (rule_in_wf _ _ Hwf Hin) as Hr.
    rewrite app_nil_r in Hr.
    inversion Hr; auto.
  Qed.

  Lemma rename_ctx_wf_from_term_eq_rule (lr : @lang B) (name : B) (c' : @ctx A)
        (e1 e2 : @term A) (t : @sort A) :
    wf_lang lr ->
    In (name, term_eq_rule (rename_ctx f c') (rename f e1) (rename f e2)
                            (rename_sort f t)) lr ->
    wf_ctx lr (rename_ctx f c').
  Proof.
    intros Hwf Hin.
    pose proof (rule_in_wf _ _ Hwf Hin) as Hr.
    rewrite app_nil_r in Hr.
    inversion Hr; auto.
  Qed.

  Lemma rename_ctx_wf_from_sort_rule (lr : @lang B) (name : B) (c' : @ctx A)
        (args : list A) :
    wf_lang lr ->
    In (name, sort_rule (rename_ctx f c') (map f args)) lr ->
    wf_ctx lr (rename_ctx f c').
  Proof.
    intros Hwf Hin.
    pose proof (rule_in_wf _ _ Hwf Hin) as Hr.
    rewrite app_nil_r in Hr.
    inversion Hr; auto.
  Qed.

  Lemma rename_ctx_wf_from_term_rule (lr : @lang B) (name : B) (c' : @ctx A)
        (args : list A) (t : @sort A) :
    wf_lang lr ->
    In (name, term_rule (rename_ctx f c') (map f args) (rename_sort f t)) lr ->
    wf_ctx lr (rename_ctx f c') /\ wf_sort lr (rename_ctx f c') (rename_sort f t).
  Proof.
    intros Hwf Hin.
    pose proof (rule_in_wf _ _ Hwf Hin) as Hr.
    rewrite app_nil_r in Hr.
    inversion Hr; auto.
  Qed.

  (** ** Main monotonicity proof (under boundedness hypotheses).

     Unlike [rename_mono], we cannot eliminate the [wf_ctx] side conditions
     of [eq_sort_subst]/[eq_term_subst] via induction here: building those
     constructors on the renamed lang requires [wf_ctx (rename_lang f l) c']
     for some intermediate [c'], which is the very statement we'd be trying
     to prove.  We resolve the cycle by taking [wf_lang (rename_lang f l)]
     and [wf_ctx (rename_lang f l) (rename_ctx f c)] as hypotheses; callers
     supply these from [rename_lang_mono_S] and [rename_mono_S_wf_ctx]
     (which is proven separately by induction on [wf_ctx]).
   *)

  Section Mono.
    Context (l : @lang A) (wfl : wf_lang l) (Hls : lang_in_S l)
            (wfl_ren : wf_lang (rename_lang f l)).

    Section MonoCtx.
      Context (c : @ctx A) (wfc : wf_ctx l c) (Hcs : ctx_in_S c)
              (wfc_ren_c : wf_ctx (rename_lang f l) (rename_ctx f c)).

      Definition P_sort_mono (t1 t2 : @sort A) : Prop :=
        sort_in_S t1 /\ sort_in_S t2 /\
        Core.eq_sort (rename_lang f l) (rename_ctx f c)
                     (rename_sort f t1) (rename_sort f t2).

      Definition P_term_mono (t : @sort A) (e1 e2 : @term A) : Prop :=
        sort_in_S t /\ term_in_S e1 /\ term_in_S e2 /\
        Core.eq_term (rename_lang f l) (rename_ctx f c)
                     (rename_sort f t) (rename f e1) (rename f e2).

      Definition P_subst_mono (c' : @ctx A) (s1 s2 : @subst A) : Prop :=
        ctx_in_S c' ->
        subst_in_S s1 /\ subst_in_S s2 /\
        eq_subst (rename_lang f l) (rename_ctx f c) (rename_ctx f c')
                 (rename_subst f s1) (rename_subst f s2).

      Definition P_args_mono (c' : @ctx A) (s1 s2 : list (@term A)) : Prop :=
        ctx_in_S c' ->
        all term_in_S s1 /\ all term_in_S s2 /\
        eq_args (rename_lang f l) (rename_ctx f c) (rename_ctx f c')
                (map (rename f) s1) (map (rename f) s2).

      Lemma rename_mono_S_eq_aux
        : (forall t1 t2, eq_sort l c t1 t2 -> P_sort_mono t1 t2)
          /\ (forall t e1 e2, eq_term l c t e1 e2 -> P_term_mono t e1 e2)
          /\ (forall c' s1 s2, eq_subst l c c' s1 s2 -> P_subst_mono c' s1 s2)
          /\ (forall c' s1 s2, eq_args l c c' s1 s2 -> P_args_mono c' s1 s2).
      Proof using wfl wfc Hls Hcs wfl_ren wfc_ren_c f_inj_S Eqb_ok_A Eqb_ok_B V_default.
        eapply (cut_ind A l wfl c wfc
                        P_sort_mono P_term_mono P_subst_mono P_args_mono);
          unfold P_sort_mono, P_term_mono, P_subst_mono, P_args_mono.
        - (* Hsort0: eq_sort_subst (sort_eq_rule) *)
          intros c' name t1 t2 s1 s2 Hin _ IHsubst.
          pose proof (lang_in_S_in _ _ _ Hls Hin) as [Hname Hrule].
          cbn in Hrule. destruct Hrule as (Hc' & Ht1 & Ht2).
          specialize (IHsubst Hc') as (Hs1 & Hs2 & Heqr).
          split; [|split].
          + apply sort_subst_in_S; auto.
          + apply sort_subst_in_S; auto.
          + rewrite (rename_sort_distr_subst_S _ _ Ht1 Hs1).
            rewrite (rename_sort_distr_subst_S _ _ Ht2 Hs2).
            eapply eq_sort_subst; eauto.
            * eapply eq_sort_by. apply (rename_lang_in _ _ _ Hin).
            * eapply rename_ctx_wf_from_eq_rule; eauto.
              apply (rename_lang_in _ _ _ Hin).
        - (* Hsort1: sort congruence *)
          intros c' name args s1 s2 Hin _ IHargs.
          pose proof (lang_in_S_in _ _ _ Hls Hin) as [Hname Hrule].
          cbn in Hrule. destruct Hrule as (Hc' & Hargs).
          specialize (IHargs Hc') as (Hs1 & Hs2 & Heqr).
          split; [|split].
          + split; auto.
          + split; auto.
          + cbn. eapply sort_con_congruence; eauto.
            apply (rename_lang_in _ _ _ Hin).
        - (* Hsort2: eq_sort_trans *)
          intros t1 t12 t2 _ IH1 _ IH2.
          destruct IH1 as (Ht1 & Ht12 & Heq1).
          destruct IH2 as (_ & Ht2 & Heq2).
          split; [|split]; auto.
          eapply eq_sort_trans; eauto.
        - (* Hsort3: eq_sort_sym *)
          intros t1 t2 _ IH.
          destruct IH as (Ht1 & Ht2 & Heq).
          split; [|split]; auto.
          eapply eq_sort_sym; eauto.
        - (* f: eq_term_subst (term_eq_rule) *)
          intros c' name t e1 e2 s1 s2 Hin _ IHsubst.
          pose proof (lang_in_S_in _ _ _ Hls Hin) as [Hname Hrule].
          cbn in Hrule. destruct Hrule as (Hc' & He1 & He2 & Ht).
          specialize (IHsubst Hc') as (Hs1 & Hs2 & Heqr).
          split; [|split; [|split]].
          + apply sort_subst_in_S; auto.
          + apply term_subst_in_S; auto.
          + apply term_subst_in_S; auto.
          + rewrite (rename_sort_distr_subst_S _ _ Ht Hs2).
            rewrite (rename_distr_subst_S _ _ He1 Hs1).
            rewrite (rename_distr_subst_S _ _ He2 Hs2).
            eapply eq_term_subst; eauto.
            * eapply eq_term_by. apply (rename_lang_in _ _ _ Hin).
            * eapply rename_ctx_wf_from_term_eq_rule; eauto.
              apply (rename_lang_in _ _ _ Hin).
        - (* f0: term congruence *)
          intros c' name t args s1 s2 Hin _ IHargs.
          pose proof (lang_in_S_in _ _ _ Hls Hin) as [Hname Hrule].
          cbn in Hrule. destruct Hrule as (Hc' & Hargs & Ht).
          specialize (IHargs Hc') as (Hs1 & Hs2 & Heqr).
          assert (Hws2 : subst_in_S (with_names_from c' s2))
            by (apply with_names_from_subst_in_S; auto).
          split; [|split; [|split]].
          + apply sort_subst_in_S; auto.
          + split; auto.
          + split; auto.
          + cbn.
            rewrite (rename_sort_distr_subst_S _ _ Ht Hws2).
            rewrite rename_subst_with_names_from.
            eapply term_con_congruence.
            * apply (rename_lang_in _ _ _ Hin).
            * right; reflexivity.
            * exact wfl_ren.
            * exact Heqr.
        - (* f01: eq_term_refl on var *)
          intros n t Hin.
          pose proof (ctx_in_S_in _ _ _ Hcs Hin) as [Hn Ht].
          split; [|split; [|split]]; auto.
          eapply eq_term_refl. eapply wf_term_var.
          apply (rename_ctx_in _ _ _ Hin).
        - (* f1: eq_term_trans *)
          intros t e1 e12 e2 _ IH1 _ IH2.
          destruct IH1 as (Ht & He1 & He12 & Heq1).
          destruct IH2 as (_ & _ & He2 & Heq2).
          split; [|split; [|split]]; auto.
          eapply eq_term_trans; eauto.
        - (* f2: eq_term_sym *)
          intros t e1 e2 _ IH.
          destruct IH as (Ht & He1 & He2 & Heq).
          split; [|split; [|split]]; auto.
          eapply eq_term_sym; eauto.
        - (* f3: eq_term_conv *)
          intros t t' _ IHs e1 e2 _ IHe.
          destruct IHs as (Ht & Ht' & Heqs).
          destruct IHe as (_ & He1 & He2 & Heqe).
          split; [|split; [|split]]; auto.
          eapply eq_term_conv; eauto.
        - (* f4: eq_subst_nil *)
          intros _.
          split; [|split]; cbn; auto.
          constructor.
        - (* f5: eq_subst_cons *)
          intros c' s1 s2 _ IHsubst name t e1 e2 _ IHterm.
          intros [[Hname Ht] Hc'].
          cbn in Hname, Ht.
          specialize (IHsubst Hc') as (Hs1 & Hs2 & Heqs).
          destruct IHterm as (_ & He1 & He2 & Heqe).
          split; [|split].
          + cbn; split; auto.
          + cbn; split; auto.
          + cbn.
            rewrite (rename_sort_distr_subst_S _ _ Ht Hs2) in Heqe.
            econstructor; eauto.
        - (* f6: eq_args_nil *)
          intros _.
          split; [|split]; cbn; auto.
          constructor.
        - (* f7: eq_args_cons *)
          intros c' s1 s2 _ IHargs name t e1 e2 _ IHterm.
          intros [[Hname Ht] Hc'].
          cbn in Hname, Ht.
          specialize (IHargs Hc') as (Hs1 & Hs2 & Heqs).
          assert (Hws2 : subst_in_S (with_names_from c' s2))
            by (apply with_names_from_subst_in_S; auto).
          destruct IHterm as (_ & He1 & He2 & Heqe).
          split; [|split].
          + cbn; split; auto.
          + cbn; split; auto.
          + cbn.
            rewrite (rename_sort_distr_subst_S _ _ Ht Hws2) in Heqe.
            rewrite rename_subst_with_names_from in Heqe.
            econstructor; eauto.
      Qed.

    End MonoCtx.

    Lemma rename_mono_S_eq c (wfc : wf_ctx l c) (Hcs : ctx_in_S c)
          (wfc_ren_c : wf_ctx (rename_lang f l) (rename_ctx f c))
      : (forall t1 t2, eq_sort l c t1 t2 ->
                       sort_in_S t1 -> sort_in_S t2 ->
                       Core.eq_sort (rename_lang f l) (rename_ctx f c)
                                    (rename_sort f t1) (rename_sort f t2))
        /\ (forall t e1 e2, eq_term l c t e1 e2 ->
                            sort_in_S t -> term_in_S e1 -> term_in_S e2 ->
                            Core.eq_term (rename_lang f l) (rename_ctx f c)
                                         (rename_sort f t) (rename f e1) (rename f e2))
        /\ (forall c' s1 s2, eq_subst l c c' s1 s2 ->
                             ctx_in_S c' -> subst_in_S s1 -> subst_in_S s2 ->
                             eq_subst (rename_lang f l) (rename_ctx f c) (rename_ctx f c')
                                      (rename_subst f s1) (rename_subst f s2))
        /\ (forall c' s1 s2, eq_args l c c' s1 s2 ->
                             ctx_in_S c' -> all term_in_S s1 -> all term_in_S s2 ->
                             eq_args (rename_lang f l) (rename_ctx f c) (rename_ctx f c')
                                     (map (rename f) s1) (map (rename f) s2)).
    Proof using wfl Hls wfl_ren f_inj_S Eqb_ok_A Eqb_ok_B V_default.
      pose proof (rename_mono_S_eq_aux wfc Hcs wfc_ren_c) as
        (Hs & Ht & Hsu & Ha).
      split; [|split; [|split]].
      - intros t1 t2 Heq _ _; apply (Hs _ _ Heq).
      - intros t e1 e2 Heq _ _ _; apply (Ht _ _ _ Heq).
      - intros c' s1 s2 Heq Hc' _ _; apply (Hsu _ _ _ Heq Hc').
      - intros c' s1 s2 Heq Hc' _ _; apply (Ha _ _ _ Heq Hc').
    Qed.

    (** ** wf_term / wf_sort: corollaries of the eq-half via reflexivity.

       Given [wf_term l c e t], we have [eq_term l c t e e] by reflexivity.
       Renaming the eq_term via [rename_mono_S_eq] and then projecting
       [wf_term] back via [eq_term_wf_l] (which requires [wf_lang] and
       [wf_ctx] of the renamed language).  This sidesteps the need to do
       induction on [wf_term] directly, which is awkward because the
       [wf_term_conv] case introduces an arbitrary intermediate sort that
       may not be in [S]. *)

    Lemma rename_mono_S_wf_term c (wfc : wf_ctx l c) (Hcs : ctx_in_S c)
          (wfc_ren_c : wf_ctx (rename_lang f l) (rename_ctx f c))
          e t (Hwf : wf_term l c e t) (He : term_in_S e) (Ht : sort_in_S t)
      : wf_term (rename_lang f l) (rename_ctx f c)
                (rename f e) (rename_sort f t).
    Proof using wfl Hls wfl_ren f_inj_S Eqb_ok_A Eqb_ok_B V_default V_default_B.
      eapply eq_term_wf_l; eauto.
      apply (proj1 (proj2 (rename_mono_S_eq wfc Hcs wfc_ren_c)));
        auto using eq_term_refl.
    Qed.

    Lemma rename_mono_S_wf_sort c (wfc : wf_ctx l c) (Hcs : ctx_in_S c)
          (wfc_ren_c : wf_ctx (rename_lang f l) (rename_ctx f c))
          t (Hwf : wf_sort l c t) (Ht : sort_in_S t)
      : wf_sort (rename_lang f l) (rename_ctx f c) (rename_sort f t).
    Proof using wfl Hls wfl_ren f_inj_S Eqb_ok_A Eqb_ok_B V_default V_default_B.
      eapply eq_sort_wf_l; eauto.
      apply (proj1 (rename_mono_S_eq wfc Hcs wfc_ren_c));
        auto using eq_sort_refl.
    Qed.

    (** ** wf_ctx preservation.

       By induction on [wf_ctx l c].  At each cons step we use
       [rename_mono_S_wf_sort] with the tail's freshly-built renamed
       wf_ctx, plus [injective_in_S] to lift freshness through the
       (partial) renaming. *)
    Lemma rename_mono_S_wf_ctx c (wfc : wf_ctx l c) (Hcs : ctx_in_S c)
      : wf_ctx (rename_lang f l) (rename_ctx f c).
    Proof using wfl Hls wfl_ren f_inj_S Eqb_ok_A Eqb_ok_B V_default V_default_B.
      induction wfc as [|name c0 v Hfresh wfc IH Hwfs]; cbn.
      - constructor.
      - destruct Hcs as [[Hname Hv] Hc0].
        cbn in Hname, Hv.
        specialize (IH Hc0).
        constructor; auto.
        + (* fresh (f name) (rename_ctx f c0) *)
          intro Hin.
          unfold rename_ctx in Hin; rewrite map_map in Hin; cbn in Hin.
          (* normalize map (fun x => f (fst x)) to map f (map fst) *)
          rewrite <- map_map with (f := fst) (g := f) in Hin.
          assert (Hall_S : all S (map fst c0)).
          { clear -Hc0. induction c0 as [|[n t] c0 IH]; cbn in *; auto.
            destruct Hc0 as [[Hn Ht] Hc0]; split; auto. }
          unfold fresh in Hfresh.
          apply Hfresh.
          apply (injective_in_S (a := name) (map fst c0) Hname Hall_S Hin).
        + (* wf_sort renamed *)
          apply (rename_mono_S_wf_sort wfc Hc0 IH); auto.
    Qed.

    (** ** wf_rule preservation. *)
    Lemma rename_rule_mono_S r (wfr : wf_rule l r) (Hrs : rule_in_S r)
      : wf_rule (rename_lang f l) (rename_rule f r).
    Proof using wfl Hls wfl_ren f_inj_S Eqb_ok_A Eqb_ok_B V_default V_default_B.
      destruct r as [rc rargs | rc rargs rt | rc rt1 rt2 | rc re1 re2 rt];
        cbn in Hrs |- *;
        inversion wfr; subst.
      - (* sort_rule rc rargs *)
        destruct Hrs as [Hc Hargs].
        constructor.
        + apply rename_mono_S_wf_ctx; auto.
        + unfold rename_ctx.
          rewrite map_map; cbn.
          rewrite <- map_map with (f := fst) (g := f).
          eauto using sublist_map.
      - (* term_rule rc rargs rt *)
        destruct Hrs as (Hc & Hargs & Ht).
        match goal with H : wf_ctx _ rc |- _ => rename H into Hwfc end.
        match goal with H : wf_sort _ rc rt |- _ => rename H into Hwfs end.
        assert (Hctxr : wf_ctx (rename_lang f l) (rename_ctx f rc))
          by (apply rename_mono_S_wf_ctx; auto).
        constructor.
        + exact Hctxr.
        + apply (rename_mono_S_wf_sort Hwfc Hc Hctxr); auto.
        + unfold rename_ctx.
          rewrite map_map; cbn.
          rewrite <- map_map with (f := fst) (g := f).
          eauto using sublist_map.
      - (* sort_eq_rule rc rt1 rt2 *)
        destruct Hrs as (Hc & Ht1 & Ht2).
        match goal with H : wf_ctx _ rc |- _ => rename H into Hwfc end.
        match goal with H : wf_sort _ rc rt1 |- _ => rename H into Hwfs1 end.
        match goal with H : wf_sort _ rc rt2 |- _ => rename H into Hwfs2 end.
        assert (Hctxr : wf_ctx (rename_lang f l) (rename_ctx f rc))
          by (apply rename_mono_S_wf_ctx; auto).
        constructor; auto.
        + apply (rename_mono_S_wf_sort Hwfc Hc Hctxr); auto.
        + apply (rename_mono_S_wf_sort Hwfc Hc Hctxr); auto.
      - (* term_eq_rule rc re1 re2 rt *)
        destruct Hrs as (Hc & He1 & He2 & Ht).
        match goal with H : wf_ctx _ rc |- _ => rename H into Hwfc end.
        match goal with H : wf_sort _ rc rt |- _ => rename H into Hwfs end.
        match goal with H : wf_term _ rc re1 rt |- _ => rename H into Hwfe1 end.
        match goal with H : wf_term _ rc re2 rt |- _ => rename H into Hwfe2 end.
        assert (Hctxr : wf_ctx (rename_lang f l) (rename_ctx f rc))
          by (apply rename_mono_S_wf_ctx; auto).
        constructor; auto.
        + apply (rename_mono_S_wf_sort Hwfc Hc Hctxr); auto.
        + apply (rename_mono_S_wf_term Hwfc Hc Hctxr); auto.
        + apply (rename_mono_S_wf_term Hwfc Hc Hctxr); auto.
    Qed.

  End Mono.

  (** ** wf_lang preservation: bootstrap [wfl_ren] from [wf_lang l] by
     induction on the language list. *)
  Lemma rename_lang_mono_S l (Hls : lang_in_S l)
    : wf_lang l -> wf_lang (rename_lang f l).
  Proof.
    induction l as [|[n r] l IH]; cbn in Hls |- *.
    - intros _. constructor.
    - intros Hwfl.
      destruct Hls as [[Hn Hr] Hl].
      cbn in Hn, Hr.
      inversion Hwfl; subst.
      match goal with H : wf_lang_ext [] l |- _ => rename H into Hwfl_tail end.
      match goal with H : wf_rule (l ++ []) r |- _ => rename H into Hwfr end.
      rewrite app_nil_r in Hwfr.
      specialize (IH Hl Hwfl_tail).
      constructor.
      + (* fresh (f n) (rename_lang f l ++ []) *)
        rewrite app_nil_r.
        intro Hin.
        unfold rename_lang in Hin; rewrite map_map in Hin; cbn in Hin.
        rewrite <- map_map with (f := fst) (g := f) in Hin.
        assert (Hall : all S (map fst l)).
        { clear -Hl. induction l as [|[n0 r0] l IH]; cbn in *; auto.
          destruct Hl as [[Hn0 Hr0] Hl]; split; auto. }
        match goal with H : fresh n (l ++ []) |- _ =>
          unfold fresh in H; rewrite app_nil_r in H; apply H end.
        apply (injective_in_S (a := n) (map fst l) Hn Hall Hin).
      + exact IH.
      + rewrite app_nil_r.
        apply (rename_rule_mono_S Hwfl_tail Hl IH Hwfr Hr).
  Qed.

End InjectiveOn.

Arguments rename_lang_mono_S {A B}%_type_scope {Eqb_A Eqb_B Eqb_ok_A Eqb_ok_B
  V_default V_default_B}
  [S]%_function_scope [f]%_function_scope f_inj_S [l]%_lang_scope _ _.
#[export] Hint Resolve rename_lang_mono_S : lang_core.


Section Inverse.
  
  Context (A B : Type)
    `{Eqb A}
    `{Eqb B}
    (f : A -> B)
    (g : B -> A)
    (f_g_inverse : forall a, g (f a) = a).

  #[local] Lemma f_inj : Injective f.
  Proof.      
    intros a a' Heq.
    congruence.
  Qed.

  Lemma rename_inverse e
    : rename g (rename f e) = e.
  Proof.
    induction e; basic_goal_prep; repeat case_match; basic_term_crush.
    revert H.
    induction l; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  #[local] Hint Rewrite rename_inverse : term.
  
  Lemma rename_inverse_args s
    : map (rename g) (map (rename f) s) = s.
  Proof.
    induction s; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  #[local] Hint Rewrite rename_inverse_args : term.
  
  Lemma rename_inverse_sort e
    : rename_sort g (rename_sort f e) = e.
  Proof.
    induction e; basic_goal_prep; repeat case_match; basic_term_crush.
  Qed.

  #[local] Hint Rewrite rename_inverse_sort : term.

End Inverse.
  

(*TODO: rules about renaming inverses*)

