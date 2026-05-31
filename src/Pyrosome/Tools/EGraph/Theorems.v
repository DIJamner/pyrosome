From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsParents SemanticsAreUnified SemanticsSaturate SemanticsUnionSem SemanticsLSurvive.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
From Pyrosome.Theory Require WfCutElim.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.


#[local] Hint Resolve Properties.map.extends_refl : utils.

(*TODO: move to Monad.v
      TODO: generalize monad equiv?   
 *)
Lemma list_Mmap_ext A B M `{Monad M} (f g : A -> M B) lst
  : (forall x, In x lst -> f x = g x) ->
    list_Mmap f lst = list_Mmap g lst.
Proof using.
  intro Hfg.
  enough (forall l', incl l' lst ->  list_Mmap f l' = list_Mmap g l')
    by eauto using incl_refl.
  induction l';
    basic_goal_prep;
    basic_utils_crush.
  rewrite Hfg; eauto.
  rewrite H0.
  reflexivity.
Qed.

(*TODO: move to utils*)
Lemma named_list_lookup_prefix {S A} `{Eqb S} (s s' : NamedList.named_list S A) x v
  : named_list_lookup_err s x = Some v ->
    named_list_lookup_err (s++s') x = Some v.
Proof.
  induction s; basic_goal_prep; [congruence|].
  case_match;
    basic_goal_prep;
    basic_utils_crush.
Qed.


(*TODO: move somewhere*)
Lemma NoDup_fresh A B (s : named_list A B)
  : NoDup (map fst s) <-> all_fresh s.
Proof.
  induction s;
    basic_goal_prep.
  { split; auto; try constructor. }
  rewrite <- IHs; clear IHs.
  intuition try constructor; auto;
    inversion H; subst; eauto.
Qed.
  


Lemma Mmap_lookup_self  {S A} `{Eqb_ok S} (x : NamedList.named_list S A)
  : all_fresh x -> Some (map snd x) = list_Mmap (named_list_lookup_err x) (map fst x).
Proof.
  induction x; basic_goal_prep; basic_utils_crush.
  rewrite list_Mmap_ext with (g:=(named_list_lookup_err x)).
  {
    rewrite <- H1.
    reflexivity.
  }
  {
    basic_goal_prep.
    eqb_case x0 s;
      basic_utils_crush.
  }
Qed.

(*TODO: move to Utils *)
Lemma combine_map_fst_snd S A (s : NamedList.named_list S A)
  : combine (map fst s) (map snd s) = s.
Proof.
  induction s;
    basic_goal_prep;
    basic_utils_crush.
Qed.
#[local] Hint Rewrite combine_map_fst_snd : utils.


  (*TODO: duplicated*)    
  Ltac iss_case :=
    lazymatch goal with
    | H : ?ma <$> _ |- _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn in H;[| tauto]
    | |- ?ma <?> _ =>
        let Hma := fresh "Hma" in
        destruct ma eqn:Hma; cbn;[| tauto]
    end.
  

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  
  Context 
    (V_map : forall A, map.map V A)
      (V_map_plus : ExtraMaps.map_plus V_map)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A)
      (V_trie_ok : forall A, map.ok (V_trie A)).

  Notation instance := (instance V V V_map V_map V_trie).

  Notation atom := (atom V V).

  
  Context (succ : V -> V).
  
  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).
  
  Context (lt : V -> V -> Prop).
  
  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).

  Section WithLang.
    Context (l : lang). (* {X} (i : instance X).*)

    Context (sort_of_fresh : fresh sort_of l).

    Definition eq_sum {A B} (eqA : A -> A -> Prop) eqB (x y : A + B) :=
      match x, y with
      | inl x, inl y => eqA x y
      | inr x, inr y => eqB x y
      | _, _ => False
      end.

    (* Note: can prove via lemma (should exist somewhere) that if
       a term is wf under some sort, it has this sort *)
    Definition interp_sort_of (args : list (term + sort))
        : option (term + sort) :=
        @!let [inl e] <?- Some args in
          let (con f s) <?- Some e in
          let (term_rule c args t) <?- named_list_lookup_err l f in
          let (scon tf ts) := t in
          ret (inr (scon tf ts[/with_names_from c s/])).

    (*TODO: write?
    Context (is_sort is_term : V -> bool).
     *)

    (* since sorts and terms are all jumbled in the domain,
       construct a subsuming judgment.
     *)
    Inductive lang_model_eq : term + sort -> term + sort -> Prop :=
    | lm_eq_terms e1 e2 t : eq_term l [] t e1 e2 -> lang_model_eq (inl e1) (inl e2)
    | lm_eq_sorts t1 t2 : eq_sort l [] t1 t2 -> lang_model_eq (inr t1) (inr t2).
    Hint Constructors lang_model_eq : lang_core.


    Lemma invert_lang_model_eq_inl e1 e2
      : lang_model_eq (inl e1) (inl e2) <-> exists t, eq_term l [] t e1 e2.
    Proof.
      intuition break; eauto with lang_core.
      inversion H; try eexists; subst;eauto.
    Qed.
    #[local] Hint Rewrite invert_lang_model_eq_inl : lang_core.

    
    Lemma invert_lang_model_eq_inr e1 e2
      : lang_model_eq (inr e1) (inr e2) <-> eq_sort l [] e1 e2.
    Proof. prove_inversion_lemma. Qed.
    #[local] Hint Rewrite invert_lang_model_eq_inr : lang_core.

    
    Lemma invert_lang_model_eq_inl_inr e1 e2
      : lang_model_eq (inl e1) (inr e2) <-> False.
    Proof. prove_inversion_lemma. Qed.
    #[local] Hint Rewrite invert_lang_model_eq_inl_inr : lang_core.
    
    Lemma invert_lang_model_eq_inr_inl e1 e2
      : lang_model_eq (inr e1) (inl e2) <-> False.
    Proof. prove_inversion_lemma. Qed.
    #[local] Hint Rewrite invert_lang_model_eq_inr_inl : lang_core.

    (* The reflexive case of _eq *)
    Inductive lang_model_wf : term + sort -> Prop :=
    | lm_wf_term e t : wf_term l [] e t -> lang_model_wf (inl e)
    | lm_wf_sort t : wf_sort l [] t -> lang_model_wf (inr t).
    Hint Constructors lang_model_wf : lang_core.
    
    Lemma invert_lang_model_wf_inl e
      : lang_model_wf (inl e) <-> exists t, wf_term l [] e t.
    Proof.
      intuition break; eauto with lang_core.
      inversion H; try eexists; subst;eauto.
    Qed.
    #[local] Hint Rewrite invert_lang_model_wf_inl : lang_core.

    
    Lemma invert_lang_model_wf_inr t
      : lang_model_wf (inr t) <-> wf_sort l [] t.
    Proof. prove_inversion_lemma. Qed.
    #[local] Hint Rewrite invert_lang_model_wf_inr : lang_core.

    Context (wfl : wf_lang l).

    (* TODO: this is sufficient to t/c, but want to relate e and t.
       Worth proving separately or no?
     *)
    Lemma interp_sort_of_wf e t
      : lang_model_wf e ->
        interp_sort_of [e] = Some t -> lang_model_wf t.
    Proof.
      cbn.
      cbv[default option_default].
      repeat (case_match; cbn; try congruence).
      subst.
      symmetry in case_match_eqn.
      apply named_list_lookup_err_in in case_match_eqn.
      basic_goal_prep;
        autorewrite with lang_core in *;
        inversions.
      autorewrite with lang_core in *;
        inversions.
      apply WfCutElim.invert_wf_term_con in H;
        break.
      clear H1 x.
      eapply in_all_fresh_same in H; try apply case_match_eqn; eauto with lang_core.
      autorewrite with term in *; break; subst.
      use_rule_in_wf.
      autorewrite with term lang_core utils in *; break; subst.
      change (scon v0 l2 [/with_names_from x0 l0 /])
        with (scon v0 l2) [/with_names_from x0 l0 /].
      eapply wf_sort_subst_monotonicity; eauto.
      apply wf_subst_from_wf_args; eauto.
    Qed.

    (*TODO: move to utils*)
    Definition get_left {A B} (x : A + B) : option A :=
      match x with inl x' => Some x' | _ => None end.

    (*TODO: move to Rule.v*)
    Definition is_sort x :=
      match named_list_lookup_err l x with
      | Some (sort_rule _ _) => true
      | _ => false
      end.

    Variant lang_model_interprets_to
      : V -> list (term + sort) -> term + sort -> Prop :=
      | interprets_to_sort_of e t
        : wf_term l [] e t -> lang_model_interprets_to sort_of [inl e] (inr t)
      | interprets_to_sort f args t
        : eq_sort l [] (scon f args) t ->
          lang_model_interprets_to f (map inl args) (inr t)
      | interprets_to_term f args e t
        : eq_term l [] t (con f args) e ->
          lang_model_interprets_to f (map inl args) (inl e).
    
    
    Definition lang_model : model V :=
      {|
        domain := term + sort;
        domain_eq := lang_model_eq;
        interprets_to := lang_model_interprets_to;
      |}.

    
    Lemma all2_model_eq_eq_args args args0 c'
      : wf_args l [] args c' ->
        wf_ctx l c' ->
        all2 lang_model_eq (map inl args) (map inl args0) ->
        eq_args l []  c' args args0.
    Proof.
      intro H; revert args0.
      induction H;
        destruct args0;
        basic_goal_prep;
        basic_utils_crush;
        constructor;
        safe_invert H1; eauto.
      safe_invert H3.
      eapply eq_term_conv; eauto.
      eapply eq_sort_trans.
      {
        eapply term_sorts_eq; eauto; try constructor.
        eauto with lang_core.
      }
      {
        eapply eq_sort_subst; eauto; try constructor.
        1: exact H9.
        apply eq_args_implies_eq_subst; eauto.
      }
    Qed.

    
    Lemma all2_lang_model_eq_inl args args2
      : all2 lang_model_eq (map inl args) args2
        -> exists args2', args2 = map inl args2'.
    Proof.
      revert args2;
        induction args;
        destruct args2;
        basic_goal_prep;
        basic_utils_crush.
      { exists []; eauto. }
      {
        eapply IHargs in H1; break; subst.
        safe_invert H0.
        exists (e2::x); eauto.
      }
    Qed.
    
    Lemma all2_lang_model_eq_inl' args args2
      : all2 lang_model_eq args2 (map inl args)
        -> exists args2', args2 = map inl args2'.
    Proof.
      revert args2;
        induction args;
        destruct args2;
        basic_goal_prep;
        basic_utils_crush.
      { exists []; eauto. }
      {
        eapply IHargs in H1; break; subst.
        safe_invert H0.
        exists (e1::x); eauto.
      }
    Qed.

    Instance lang_model_eq_PER : PER lang_model_eq.
    Proof.
      constructor; repeat intro.
      { inversion H; subst; econstructor; eauto using eq_term_sym, eq_sort_sym. }
      {
        inversion H; subst; inversion H0; subst;
          econstructor; eauto using eq_sort_trans.
        eapply eq_term_trans; eauto.
        eapply eq_term_conv; eauto.
        eapply eq_term_wf_r in H1;eauto; [|constructor].
        eapply eq_term_wf_l in H3;eauto; [|constructor].
        eapply term_sorts_eq; eauto; constructor.
      }
    Qed.


  Ltac transitive_extension :=
    repeat first [apply Properties.map.extends_refl
                 | eapply map_extends_trans;[ eassumption |] ].

  (*TODO: tactic changed due to missing Mmap_extends. May be broken*)
  Ltac extension_congruence Hext H H' :=
    apply eq_of_eq_Some;
    (eapply Hext in H' (*outdated|| (eapply Mmap_extends in H'; [| eauto | eauto | apply Hext])*));
    rewrite <- H, <- H'; reflexivity.
  
  Ltac get_ext_cong :=
    repeat lazymatch goal with
      | H : map.get ?i1 ?a = Some ?l1,
          H' : map.get ?i2 ?a = Some ?l2 |- _ =>
          let Hext := fresh "Hext" in
          (assert (map.extends i1 i2) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H H'; subst; clear H)
          || 
          (assert (map.extends i2 i1) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H' H; subst; clear H')
      | H : list_Mmap (map.get ?i1) ?a = Some ?l1,
          H' : list_Mmap (map.get ?i2) ?a = Some ?l2 |- _ =>
          let Hext := fresh "Hext" in
          (assert (map.extends i1 i2) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H H'; subst; clear H)
          || 
          (assert (map.extends i2 i1) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H' H; subst; clear H')
          
      end.

  Ltac lang_model_simp :=
    get_ext_cong;
    repeat lazymatch goal with
      | H : lang_model_eq _ (inr _) |- _ =>
          safe_invert H
      | H : lang_model_eq (inr _) _ |- _ =>
          safe_invert H
      | |- lang_model_eq (inr _) (inr _) =>
          constructor
      | H : lang_model_interprets_to _ _ (inl _) |- _ =>
          safe_invert H
      | Hwf : wf_lang ?l,
          H1 : In (?name, _) ?l,
            H2 : In (?name, _) ?l |- _ =>
          eapply in_all_fresh_same in H2; try apply H1; eauto with lang_core
      | H : term_rule _ _ _ = term_rule _ _ _ |- _=> safe_invert H
      end.


    Instance lang_model_ok : model_ok _ lang_model.
    Proof.
      unfold lang_model.
      constructor; cbn in *.
      { apply lang_model_eq_PER. }
      {
        basic_goal_prep.
        inversion H; subst; inversion H0; subst; clear H H0;
          repeat basic_goal_prep.
        {
          inversion H; subst; clear H.
          constructor.
          pose proof H6 as H7.
          eapply eq_term_wf_l in H6; eauto; try constructor.
          eapply eq_term_wf_r in H7; eauto; try constructor.
          eapply eq_sort_trans; eapply term_sorts_eq; eauto; try constructor.
        }
        {
          destruct args; basic_goal_prep; try tauto.
          destruct args; basic_goal_prep; try tauto.
          eapply eq_sort_wf_l in H3; eauto using wf_ctx_nil.
          safe_invert H3.
          exfalso; eapply fresh_notin; eauto.
        }
        {
          destruct args; basic_goal_prep; try tauto.
          destruct args; basic_goal_prep; try tauto.
          eapply eq_term_wf_l in H3; eauto using wf_ctx_nil.
          apply WfCutElim.invert_wf_term_con in H3;
            break.
          exfalso; eapply fresh_notin; eauto.
        }
        {
          destruct args; basic_goal_prep; try tauto.
          destruct args; basic_goal_prep; try tauto.
          eapply eq_sort_wf_l in H2; eauto using wf_ctx_nil.
          safe_invert H2.
          exfalso; eapply fresh_notin; eauto.
        }
        {
          constructor.
          eapply eq_sort_trans; eauto.
          eapply eq_sort_wf_l in H3; eauto using wf_ctx_nil.
          safe_invert H3.
          eapply eq_sort_sym.
          eapply eq_sort_trans; eauto.
          eapply eq_sort_sym.
          eapply sort_con_congruence; eauto.
          eapply eq_sort_wf_l in H2; eauto using wf_ctx_nil.
          safe_invert H2.
          eapply in_all_fresh_same in H4; try apply H5; eauto with lang_core.
          safe_invert H4.
          apply all2_model_eq_eq_args; eauto.
          use_rule_in_wf.
          basic_core_crush.          
        }
        {
          exfalso.
          eapply eq_term_wf_l in H3; eauto using wf_ctx_nil.
          eapply eq_sort_wf_l in H2; eauto using wf_ctx_nil.
          repeat lazymatch goal with
                 | H : wf_sort _ _ (scon _ _) |- _ => safe_invert H
                 | H : wf_term _ _ (con _ _) _ |- _ =>
                     apply WfCutElim.invert_wf_term_con in H;
                     break
                 end.
          eapply in_all_fresh_same in H; try apply H5; eauto with lang_core;
            congruence.
        }
        {
          destruct args; basic_goal_prep; try tauto.
          destruct args; basic_goal_prep; try tauto.
          eapply eq_term_wf_l in H2; eauto using wf_ctx_nil.
          repeat lazymatch goal with
                 | H : wf_sort _ _ (scon _ _) |- _ => safe_invert H
                 | H : wf_term _ _ (con _ _) _ |- _ =>
                     apply WfCutElim.invert_wf_term_con in H;
                     break
                 end.
          exfalso; eapply fresh_notin; eauto.
        }
        {
          exfalso.
          eapply eq_term_wf_l in H2; eauto using wf_ctx_nil.
          eapply eq_sort_wf_l in H3; eauto using wf_ctx_nil.
          repeat lazymatch goal with
                 | H : wf_sort _ _ (scon _ _) |- _ => safe_invert H
                 | H : wf_term _ _ (con _ _) _ |- _ =>
                     apply WfCutElim.invert_wf_term_con in H;
                     break
                 end.
          eapply in_all_fresh_same in H; try apply H5; eauto with lang_core;
            congruence.
        }
        {
          pose proof H2 as Hwf.
          eapply eq_term_wf_l in Hwf; eauto using wf_ctx_nil.
          pose proof H3 as Hwf'.
          eapply eq_term_wf_l in Hwf'; eauto using wf_ctx_nil.
          repeat lazymatch goal with
                 | H : wf_sort _ _ (scon _ _) |- _ => safe_invert H
                 | H : wf_term _ _ (con _ _) _ |- _ =>
                     apply WfCutElim.invert_wf_term_con in H;
                     break
                 end.
          eapply in_all_fresh_same in H; try apply H5; eauto with lang_core.
          safe_invert H.
          use_rule_in_wf.
          autorewrite with lang_core utils in H; break.
          etransitivity; [symmetry |];
            try now (econstructor; eauto).
          etransitivity; [symmetry |];
            try now (econstructor; eauto).
          symmetry.
          econstructor.
          eapply term_con_congruence; eauto.
          eapply all2_model_eq_eq_args; eauto.
        }
      }
      {        
        basic_goal_prep.
        inversion H; subst; clear H; basic_goal_prep;
          repeat case_match; try tauto; break;        
          repeat lazymatch goal with
                 | H : lang_model_eq _ (inl _) |- _ => safe_invert H
                 | H : lang_model_eq (inl _) _ |- _ => safe_invert H
                 | H : lang_model_eq _ (inr _) |- _ => safe_invert H
                 | H : lang_model_eq (inr _) _ |- _ => safe_invert H
                 end.
        {
          econstructor.
          eapply wf_term_conv; eauto with lang_core.
          eapply eq_term_wf_l in H4;eauto; [|constructor].
          eapply term_sorts_eq in H2; eauto; constructor.
          eapply eq_sort_sym; eapply eq_sort_trans; eauto.
        }
        {
          pose proof H0.
          apply all2_lang_model_eq_inl in H0; break; subst.
          pose proof H2.
          eapply eq_sort_wf_l in H2; eauto using wf_ctx_nil.
          safe_invert H2.
          eapply interprets_to_sort.
          eapply eq_sort_trans; eauto.
          clear H3.
          eapply eq_sort_trans; eauto.
          eapply eq_sort_sym.
          eapply sort_con_congruence; eauto.
          eapply all2_model_eq_eq_args; eauto.
          use_rule_in_wf; basic_core_crush.
        }
        {
          pose proof H0.
          apply all2_lang_model_eq_inl in H0; break; subst.
          pose proof H2.
          eapply eq_term_wf_l in H2; eauto using wf_ctx_nil.
          repeat lazymatch goal with
                 | H : wf_sort _ _ (scon _ _) |- _ => safe_invert H
                 | H : wf_term _ _ (con _ _) _ |- _ =>
                     apply WfCutElim.invert_wf_term_con in H;
                     break
                 end.
          econstructor.
          eapply eq_term_trans; eauto.
          eapply eq_term_conv.
          1: eapply eq_term_trans; try apply H0.
          2:{
            eapply eq_term_wf_l in H3; eauto using wf_ctx_nil.
            eapply eq_term_wf_r in H0; eauto using wf_ctx_nil.
            eapply term_sorts_eq; eauto using wf_ctx_nil.
          }
          eapply term_con_congruence; eauto.
          { intuition eauto using eq_sort_sym. }
          {
            eapply eq_args_sym; try typeclasses eauto;
              eauto using core_model_ok with lang_core.        
            eapply eq_term_wf_l in H0; eauto using wf_ctx_nil. 
            repeat lazymatch goal with
                   | H : wf_sort _ _ (scon _ _) |- _ => safe_invert H
                   | H : wf_term _ _ (con _ _) _ |- _ =>
                       apply WfCutElim.invert_wf_term_con in H;
                       break
                   end.
            lang_model_simp.
            eapply all2_model_eq_eq_args; eauto.
            use_rule_in_wf; basic_core_crush.
          }          
        }
      }
      {
        destruct 1; basic_goal_prep; intuition eauto with lang_core.
        {
          eapply eq_sort_wf_l in H; eauto with lang_core; safe_invert H.
          apply all_map; cbn.
          clear H3.
          induction H4; basic_goal_prep;
            basic_core_crush.
        }
        {
          eapply eq_term_wf_l in H; eauto with lang_core.
          apply WfCutElim.invert_wf_term_con in H; break.
          clear H H1.
          apply all_map; cbn.
          induction H0; basic_goal_prep;
            basic_core_crush.
        }
      }
      {
        destruct 1; econstructor; basic_core_crush.
        eapply eq_sort_refl.
        eapply eq_term_wf_sort; eauto with lang_core.
        eapply eq_term_refl; eauto.
      }
    Qed.

    (* lang_model instance of eq_sound_to_domain_eq: if two ids are equal
       under interpretation [i] and denote the closed terms [e1], [e2],
       then [e1] and [e2] are provably equal in [l].  The model-level
       endpoint of the saturation->eq_term bridge; compose with the term
       denotations from add_open_term_sound and are_unified_eq_sound. *)
    Lemma eq_sound_to_eq_term (i : V_map (term + sort)%type) (x1 x2 : V) (e1 e2 : term) :
      eq_sound_for_model V V V_map lang_model i x1 x2 ->
      option_relation lang_model_eq (map.get i x1) (Some (inl e1)) ->
      option_relation lang_model_eq (map.get i x2) (Some (inl e2)) ->
      exists t, eq_term l [] t e1 e2.
    Proof.
      intros Hes Hd1 Hd2.
      apply invert_lang_model_eq_inl.
      exact (@eq_sound_to_domain_eq V V V_map lang_model lang_model_ok
               i x1 x2 (inl e1) (inl e2) Hes Hd1 Hd2).
    Qed.

(*
    Definition sort_of_term e :=
      match e with
      | con f s => scon f s
      | _ => (*shouldn't happen*) default
      end.
    
    Lemma lang_model_sort_of_sound e t
      : wf_term l [] e t ->
        forall t',
        interp_sort_of [inl e] = Some (inr t') ->
        wf_term l [] e t'.
    Proof using V_Eqb V_Eqb_ok V_default wfl.
      clear succ.
      induction 1;
          basic_goal_prep;
          basic_core_crush.
      unfold interp_sort_of in *; cbn in *.
      pose proof H as Hin.
      eapply all_fresh_named_list_lookup_err_in in H; eauto;
        [|basic_core_crush].
      rewrite <- H in H1.
      destruct t.
      basic_utils_crush.
      unfold sort_of_term; cbn.
      change (scon v l0 [/with_names_from c' s /])
        with (scon v l0) [/with_names_from c' s /].
      safe_invert H1.
      change (scon v l0 [/with_names_from c' s /])
        with (scon v l0) [/with_names_from c' s /].
      eapply wf_term_by; eauto.
    Qed.
*)
      
    (*
    Context (le_V : V -> V -> Prop)
      (le_V_refl : forall x, le_V x x)
      (le_V_sym : forall x y z, le_V x y -> le_V y z -> le_V x z)
      (* TODO: to work w/ int63, have to weaken this *)
      (succ_le : forall x, le_V x (succ x))
      (succ_neq : forall x, x <> succ x)
      (supremum_le : forall l x, In x l -> le_V x (supremum l)).

    Local Hint Resolve le_V_refl : utils.

    Definition lt_V x y := le_V (succ x) y.
     *)

    (*
    (*TODO: why isn't this hint working: pair_equal_spec:
    *)
    Lemma term_pat_to_clauses_var next_var e l1 x next_var'
      :  term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
         le_V next_var next_var'.
    Proof.
      revert next_var l1 x next_var'.
      induction e.
      {
        basic_goal_prep;
          basic_utils_crush.
        cbv in H.
        rewrite !pair_equal_spec in H.
        basic_goal_prep;
          basic_utils_crush.
      }
      {
        revert H; induction l0;   
        basic_goal_prep;
          unfold Basics.compose in *;
        basic_goal_prep.
        {
          cbv in H0;
            rewrite !pair_equal_spec in H0.
          basic_goal_prep; subst; eauto.
        }
        {
          destruct (term_pat_to_clauses succ a next_var) eqn:Hpat.
          unfold uncurry in *.
          basic_goal_prep.
          destruct (list_Mmap (term_pat_to_clauses succ) l0 v0) eqn:Hlist.
          basic_goal_prep.
          cbv [writer] in H0;
            rewrite !pair_equal_spec in H0.
          basic_goal_prep.
          subst.
          eapply H in Hpat.
          eapply IHl0 with (next_var:=v0) in H1.
          all: cbn; eauto.
          rewrite Hlist.
          cbn; eauto.
        }
      }
    Qed.
*)

    (*TODO
    Lemma term_pat_to_clauses_sound next_var
      :  next_var > fvs e ->
         term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
         matches assignment l1 ->
         let s := (combine (fvs e) (map (lookup assignment) (fvs e))) in
         lookup assignment x = Some e [/s/].
     *)

    
   

    (*TODO: move to core*)
    Lemma wf_subst_fresh c s c'
      : all_fresh c' -> wf_subst l c s c' -> all_fresh s.
    Proof.
      intros H H'; revert H;
        induction H';
        basic_goal_prep;
        basic_utils_crush.
      unfold fresh.
      erewrite wf_subst_dom_eq; eauto.
    Qed.
    Hint Resolve wf_subst_fresh : lang_core.

    (*TODO: move to core *)
    Lemma wf_args_from_wf_subst c s c'
      : wf_subst l c s c' -> wf_args l c (map snd s) c'.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_core_crush.
      rewrite <- combine_map_fst_is_with_names_from.
      erewrite <- wf_subst_dom_eq; eauto.
      unfold fresh.
      basic_utils_crush.
    Qed.
    Hint Resolve wf_args_from_wf_subst : lang_core.

    (*TODO: move to Utils *)
    Lemma named_list_lookup_suffix S A `{Eqb_ok S} (l1 l2 : NamedList.named_list S A) x
      : fresh x l1 ->
        named_list_lookup_err l2 x
        = named_list_lookup_err (l1++l2) x.
    Proof.
      induction l1; basic_goal_prep; try tauto.
      autorewrite with utils in *; break.
      eqb_case x s; auto; try tauto.
    Qed.

    
    Lemma wf_con_rule_in c e t
      : wf_term l c e t ->
        forall n s, e = con n s ->
        exists c' args t', In (n, term_rule c' args t') l.
    Proof.
      induction 1; basic_goal_prep;
        basic_core_crush.
    Qed.
    
    Lemma wf_scon_rule_in c t
      : wf_sort l c t ->
        forall n s, t = scon n s ->
        exists c' args, In (n, sort_rule c' args) l.
    Proof.
      induction 1; basic_goal_prep;
        basic_core_crush.
    Qed.
    
    (*
    Context (supremum : list V -> V).
    Context (V_to_nat : V -> nat)
      (VtN_inj : FinFun.Injective V_to_nat)
    (VtN_succ : forall x, V_to_nat (succ x) = Nat.succ (V_to_nat x)).

    Definition le_V a b := V_to_nat a <= V_to_nat b.
    Definition lt_V a b := V_to_nat a < V_to_nat b.

    Context (supremum_le : forall l x, In x l -> le_V x (supremum l)).
     *)


    Lemma wf_var_in
      : (forall c s,
            wf_sort l c s ->
            forall x, In x (fv_sort s) -> In x (map fst c))
        /\ (forall c e t,
               wf_term l c e t ->
               forall x, In x (fv e) -> In x (map fst c))
        /\ (forall c l0 c0,
               wf_args l c l0 c0 ->
               forall x, In x (fv_args l0) -> In x (map fst c)).
    Proof.
      clear succ lt_succ.
      eapply wf_judge_ind;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    (*
    Lemma lang_model_no_vars v
      : lang_model_eq {{e v}} {{e v}} <-> False.
    Proof.
      clear succ.
      intuition auto.
      inversion H; clear H; subst;
        basic_goal_prep;
        basic_core_crush.
      eapply eq_term_wf_r in H0; eauto with lang_core.
      eapply wf_var_in in H0;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite lang_model_no_vars : lang_core.
*)

    
    Lemma wf_term_con_inv' c e t
      : wf_term l c e t ->
        forall f args, e = (con f args) ->
        exists c' args' t', In (f,term_rule c' args' t') l
                            /\ wf_args l c args c'.
    Proof using.
      clear succ lt_succ V_default lt lt_asymmetric lt_trans.
      induction 1;
        basic_goal_prep;
        basic_core_crush.
    Qed.
    
    Lemma wf_term_con_inv c f args t
      : wf_term l c (con f args) t ->
        exists c' args' t', In (f,term_rule c' args' t') l
                            /\ wf_args l c args c'.
    Proof. eauto using wf_term_con_inv'. Qed.

    (*TODO: move*)    
    Arguments interprets_to {symbol}%_type_scope m f args%_list_scope d.
    
    Definition args_in_instance (args : list _)
      (i : V_map lang_model.(domain _)) (r : list V) : Prop :=
      list_Mmap (map.get i) r <$> (fun dl => all2 lang_model.(domain_eq _) dl (map inl args)).
                                   (*
      all2 (fun pr ps => fst pr = fst ps
                         /\ option_relation lang_model.(domain_eq _)
                               (map.get i (snd pr)) (Some (inl (snd ps))))
        r s.
*)

    (*
    Definition subst_of_rename_interp r (i : V_map lang_model.(domain _)) : subst :=
      named_map (fun x => match map.get i x with
                          | Some (inl e) => e
                          | _ => default
                          end)
        r.
     *)

  (*
  Lemma Mmap_subst_in_inst i a s (c' : ctx)
    : option_relation (all2 lang_model.(domain_eq _))
        (list_Mmap (map.get i) a)
        (Some (map inl s)) ->
      args_in_instance s i a.
  Proof.
    unfold assign_subst_in_instance.
    revert c' s;
      induction a;
      destruct s;
      destruct c';
      basic_goal_prep;
      repeat (inversions; try case_match;cbn in * );
      safe_invert H;
      intuition eauto.
    econstructor; eauto.
  Qed.
*)

  Lemma interpret_sort_of a o
    : lang_model_interprets_to sort_of [a] o <->
        exists e t, a = inl e /\ o = inr t /\  wf_term l {{c }} e t.
  Proof.
    split.
    2:{ basic_goal_prep; subst; econstructor; eauto. }
    inversion 1; subst.
    { eexists; eexists; intuition eauto. }
    all: exfalso.
    {
      eapply eq_sort_wf_l in H2; eauto with lang_core.
      safe_invert H2.
      eapply fresh_notin in H5; eauto using sort_of_fresh; tauto.
    }
    {
      eapply eq_term_wf_l in H2; eauto with lang_core.
      apply WfCutElim.invert_wf_term_con in H2; break.
      eapply fresh_notin in H1; eauto using sort_of_fresh; tauto.
    }
  Qed.    
  

  
  
  Lemma map_injective A B (f : A -> B)
    : (forall x y, f x = f y -> x = y) ->
      forall l1 l2, map f l1 = map f l2 -> l1 = l2.
  Proof.
    induction l1; destruct l2;
      basic_goal_prep;
      repeat case_match; basic_utils_crush.
  Qed.
  
    Lemma interprets_to_term_rule name c' args t s s1
      : In (name, term_rule c' args t) l ->
        lang_model_interprets_to name s s1 ->
        exists e x, s = map inl x
                    /\ s1 = inl e
                  /\ eq_term l {{c }} t[/with_names_from c' x/] (con name x) e.
    Proof.
      inversion 2; subst.
      { exfalso; eapply fresh_notin; eauto. }
      {
        eapply eq_sort_wf_l in H1; eauto with lang_core.
        safe_invert H1.
        eapply in_all_fresh_same in H5; try apply H; eauto with lang_core.
        congruence.
      }
      {
        eexists;eexists; intuition eauto.
        pose proof H1.
        eapply eq_term_wf_l in H1; eauto with lang_core.
        eapply WfCutElim.invert_wf_term_con in H1; break.
        lang_model_simp.
        apply map_injective in H5; [ subst | intros; congruence].
        intuition subst; eauto.
        eapply eq_term_conv; eauto.
        eapply eq_sort_sym; eapply eq_sort_trans; try eassumption.
        eapply term_sorts_eq; eauto with lang_core.
        all: eapply eq_term_wf_r; eauto with lang_core.
      }
    Qed.
    
  
    Lemma interprets_to_sort_rule name c' args x s1
      : In (name, sort_rule c' args) l ->
        lang_model_interprets_to name (map inl x) s1 ->
        exists t, s1 = inr t
                  /\ eq_sort l {{c }} (scon name x) t.
    Proof.
      inversion 2; subst.
      { exfalso; eapply fresh_notin; eauto. }
      2:{
        eapply eq_term_wf_l in H3; eauto with lang_core.
        eapply WfCutElim.invert_wf_term_con in H3; break.
        eapply in_all_fresh_same in H2; try apply H; eauto with lang_core.
        congruence.
      }
      {
        apply map_injective in H1; subst.
        2: intros; congruence.
        eexists; intuition eauto.
      }
    Qed.     

  End WithLang.

  
  Ltac transitive_extension :=
    repeat first [apply Properties.map.extends_refl
                 | eapply map_extends_trans;[ eassumption |] ].
  
  (*TODO: tactic changed due to missing Mmap_extends. May be broken*)
  Ltac extension_congruence Hext H H' :=
    apply eq_of_eq_Some;
    (eapply Hext in H' (*outdated|| (eapply Mmap_extends in H'; [| eauto | eauto | apply Hext])*));
    rewrite <- H, <- H'; reflexivity.
  
  Ltac get_ext_cong :=
    repeat lazymatch goal with
      | H : map.get ?i1 ?a = Some ?l1,
          H' : map.get ?i2 ?a = Some ?l2 |- _ =>
          let Hext := fresh "Hext" in
          (assert (map.extends i1 i2) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H H'; subst; clear H)
          || 
          (assert (map.extends i2 i1) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H' H; subst; clear H')
      | H : list_Mmap (map.get ?i1) ?a = Some ?l1,
          H' : list_Mmap (map.get ?i2) ?a = Some ?l2 |- _ =>
          let Hext := fresh "Hext" in
          (assert (map.extends i1 i2) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H H'; subst; clear H)
          || 
          (assert (map.extends i2 i1) as Hext
              by transitive_extension;
           assert (l1 = l2) by extension_congruence Hext H' H; subst; clear H')
          
      end.

  Ltac lang_model_simp :=
    get_ext_cong;
    repeat lazymatch goal with
      | H : lang_model_eq _ (inr _) |- _ =>
          safe_invert H
      | H : lang_model_eq (inr _) _ |- _ =>
          safe_invert H
      | |- lang_model_eq (inr _) (inr _) =>
          constructor
      | H : lang_model_interprets_to _ _ (inl _) |- _ =>
          safe_invert H
      | Hwf : wf_lang ?l,
          H1 : In (?name, _) ?l,
            H2 : In (?name, _) ?l |- _ =>
          eapply in_all_fresh_same in H2; try apply H1; eauto with lang_core
      | H : term_rule _ _ _ = term_rule _ _ _ |- _=> safe_invert H
      end.

  
  Lemma args_in_instance_length l s0 i' a
    : args_in_instance l s0 i' a ->
      length a = length s0.
  Proof.
    unfold args_in_instance; basic_goal_prep.
    iss_case.
    apply PosListMap.all2_len in H.
    apply TrieMap.list_Mmap_length in Hma.
    basic_utils_crush.
    congruence.
  Qed.

  
  Lemma args_in_instance_in l s i c n e x r
    : args_in_instance l s i (map snd r) ->
      wf_args l {{c }} s c ->
      map fst c = map fst r ->
      all_fresh c ->
      In (n,e) (with_names_from c s) ->
      In (n,x) r ->
      exists d, map.get i x = Some d
                /\ lang_model_eq l d (inl e).
  Proof.
    unfold args_in_instance.
    intros H Hi.
    iss_case.
    generalize dependent l0.
    revert r.
    induction Hi;
      basic_goal_prep;
      try tauto.
    destruct l0; basic_goal_prep; try tauto.
    destruct r; basic_goal_prep; repeat (case_match; try congruence; try tauto);try tauto.
    inversions.
    assert (fresh v r).
    {
      unfold fresh in *.
      congruence.
    }
    eqb_case v n; intuition subst; eauto.
    {
      exfalso.
      rewrite <- combine_map_fst_is_with_names_from in *.
      apply in_combine_l in H8.
      eauto.
    }
    {
      exfalso.
      rewrite <- combine_map_fst_is_with_names_from in *.
      apply pair_fst_in in H8.
      eauto.
    }
  Qed.
  
  Lemma args_in_instance_cons l (es : list term) i aa (e : term) a
    : args_in_instance l es i aa ->
      map.get i a <$> (fun d => domain_eq V (lang_model l) d (inl e)) ->
      args_in_instance l (e::es) i (a::aa).
  Proof.
    unfold args_in_instance;
      intros; repeat iss_case.
    cbn in *.
    rewrite Hma.
    rewrite Hma0.
    cbn.
    intuition auto.
  Qed.

  Lemma list_Mmap_get_extends {A} (i i' : V_map A) a ds
    : map.extends i' i ->
      list_Mmap (map.get i) a = Some ds ->
      list_Mmap (map.get i') a = Some ds.
  Proof.
    intros Hext. revert ds.
    induction a as [|x xs IH]; cbn; intros ds Hmi.
    - exact Hmi.
    - destruct (map.get i x) as [vx|] eqn:Hgix.
      2:{ cbn in Hmi. discriminate. }
      cbn in Hmi.
      destruct (list_Mmap (map.get i) xs) as [ls|] eqn:Hmxs.
      2:{ cbn in Hmi. discriminate. }
      cbn in Hmi.
      apply Hext in Hgix. rewrite Hgix.
      specialize (IH ls eq_refl). rewrite IH. cbn. exact Hmi.
  Qed.

  Lemma args_in_instance_monotone l s i i' a
    : map.extends i' i ->
      args_in_instance l s i a ->
      args_in_instance l s i' a.
  Proof.
    unfold args_in_instance.
    intros Hext Hin.
    destruct (list_Mmap (map.get i) a) as [ds|] eqn:Hmi; cbn in Hin; [|tauto].
    erewrite list_Mmap_get_extends; cbn; eauto.
  Qed.

  Lemma map_get_monotone {A} (i i' : V_map A) (x : V) (d : A)
    : map.extends i' i ->
      map.get i x = Some d ->
      map.get i' x = Some d.
  Proof. intros Hext Hgd. apply Hext. exact Hgd. Qed.

  (* Splitter: from `In (n, r) l` and `wf_lang l`, extract a smaller
     well-formed prefix `l_post` (the part strictly before `(n, r)`
     in cons-order) where `r` is wf.  Used to satisfy the strict-
     decreasing-language precondition of add_open_sort_inner_sound. *)
  Lemma wf_lang_ext_split (l : lang) (n : V) (r : rule)
    : wf_lang l -> In (n, r) l ->
      exists l_post,
        wf_lang l_post /\ wf_rule l_post r /\ incl l_post l
        /\ length l_post < length l.
  Proof.
    induction l as [|[n0 r0] l_rest IH]; intros Hwf Hin; cbn in Hin.
    - contradiction.
    - destruct Hin as [Heq | Hin'].
      + inversion Heq; subst.
        exists l_rest. cbn.
        pose proof Hwf as Hwf'.
        apply invert_wf_lang_cons in Hwf'.
        destruct Hwf' as [_ Hwfr]. destruct Hwfr as [Hwfl Hwfrule].
        rewrite List.app_nil_r in Hwfrule.
        repeat split.
        * exact Hwfl.
        * exact Hwfrule.
        * intros x Hx. right. exact Hx.
        * Lia.lia.
      + pose proof Hwf as Hwf'.
        apply invert_wf_lang_cons in Hwf'.
        destruct Hwf' as [_ Hwfr]. destruct Hwfr as [Hwfl _].
        specialize (IH Hwfl Hin').
        destruct IH as [l_post H_lp].
        destruct H_lp as [Hwfl_post H_lp1].
        destruct H_lp1 as [Hwfr_post H_lp2].
        destruct H_lp2 as [Hincl_post Hlen_post].
        exists l_post. repeat split; auto.
        * intros x Hx. right. apply Hincl_post. exact Hx.
        * cbn. Lia.lia.
  Qed.

  (* =============================================================== *)
  (* Re-proof of add_open_term_sound / add_open_sort_sound /          *)
  (* add_ctx_sound against the current `vc` + `egraph_ok` style       *)
  (* (see src/Utils/EGraph/Semantics.v).  The old statements lived    *)
  (* in this file as a giant comment block phrased against the        *)
  (* now-removed `state_sound_for_model` predicate and the missing    *)
  (* primitive helpers `hash_entry_sound`, `alloc_opaque_sound`,      *)
  (* `update_entry_sound`.                                            *)
  (*                                                                  *)
  (* The new statements use `vc` directly (Utils/VC.v) and admit at   *)
  (* "Layer A" the three primitive sound lemmas added next to         *)
  (* `union_sound` in Semantics.v.  See                               *)
  (* /root/.claude/plans/                                             *)
  (* a-number-of-theorems-functional-trinket.md                       *)
  (* for the design.                                                  *)
  (* =============================================================== *)
  Section AddOpenSound.
    Context (X : Type) `{analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).
    Context (with_sorts : bool).

    Local Notation lang_model := (lang_model l).
    Local Notation interp := (V_map lang_model.(domain _)).
    (* Section-explicit-args from Semantics.v need to be partially
       applied here. *)
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie X).
    Local Notation egraph_sound_for_interpretation :=
      (egraph_sound_for_interpretation V V V_map V_map V_trie X).

    (* ----------- Post-condition predicates ----------- *)

    (* The "extending sound" postcondition: the output egraph stays
       well-formed, the interpretation is extended (so prior facts
       still hold under the new interpretation), and any id that was
       a union-find key remains one.  Standard envelope we propagate
       through the proof. *)
    Definition extending_sound
       (i_in : interp) (e_in : instance X) (i_out : interp) (e_out : instance X) : Prop :=
      egraph_ok e_out
      /\ map.extends i_out i_in
      /\ egraph_sound_for_interpretation lang_model i_out e_out
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv e_out))).

    Definition open_term_post (c : ctx) (s : list term) (e : term)
       (r : named_list V) (i_in : interp) (e_in : instance X)
       (res : V * instance X) : Prop :=
      egraph_ok e_in ->
      egraph_sound_for_interpretation lang_model i_in e_in ->
      args_in_instance l s i_in (map snd r) ->
      exists i_out,
        extending_sound i_in e_in i_out (snd res)
        /\ option_relation lang_model.(domain_eq _)
             (map.get i_out (fst res)) (Some (inl e[/with_names_from c s/])).

    Definition open_sort_post (c : ctx) (s : list term) (t : sort)
       (r : named_list V) (i_in : interp) (e_in : instance X)
       (res : V * instance X) : Prop :=
      egraph_ok e_in ->
      egraph_sound_for_interpretation lang_model i_in e_in ->
      args_in_instance l s i_in (map snd r) ->
      exists i_out,
        extending_sound i_in e_in i_out (snd res)
        /\ option_relation lang_model.(domain_eq _)
             (map.get i_out (fst res)) (Some (inr t[/with_names_from c s/])).

    Definition open_args_post (c : ctx) (s : list term) (args : list term)
       (r : named_list V) (i_in : interp) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      egraph_ok e_in ->
      egraph_sound_for_interpretation lang_model i_in e_in ->
      args_in_instance l s i_in (map snd r) ->
      exists i_out,
        extending_sound i_in e_in i_out (snd res)
        /\ args_in_instance l args[/with_names_from c s/] i_out (fst res).

    Definition ctx_post (s : subst) (c : ctx)
       (i_in : interp) (e_in : instance X)
       (res : named_list V * instance X) : Prop :=
      egraph_ok e_in ->
      egraph_sound_for_interpretation lang_model i_in e_in ->
      exists i_out,
        extending_sound i_in e_in i_out (snd res)
        /\ map fst (fst res) = map fst c
        /\ args_in_instance l (map snd s) i_out (map snd (fst res)).

    (* ----------- Helpers for chaining extending_sound ----------- *)

    Lemma extending_sound_refl i e
      : egraph_ok e ->
        egraph_sound_for_interpretation lang_model i e ->
        extending_sound i e i e.
    Proof.
      unfold extending_sound; intuition auto using Properties.map.extends_refl.
    Qed.

    Lemma extending_sound_trans i1 i2 i3 e1 e2 e3
      : extending_sound i1 e1 i2 e2 ->
        extending_sound i2 e2 i3 e3 ->
        extending_sound i1 e1 i3 e3.
    Proof.
      unfold extending_sound.
      intros (Hok2 & Hext12 & Hsnd2 & Hk12) (Hok3 & Hext23 & Hsnd3 & Hk23).
      split; [exact Hok3|]. split.
      { intros k v Hgv. apply Hext23. apply Hext12. exact Hgv. }
      split; [exact Hsnd3|].
      intros k Hk. apply Hk23. apply Hk12. exact Hk.
    Qed.

    (* From a sound interpretation in which a list of ids is jointly
       resolvable, each individual id has a key. *)
    Lemma list_Mmap_get_has_some {A} (i : V_map A) a (dl : list A) x
      : list_Mmap (map.get i) a = Some dl ->
        In x a ->
        Is_Some (map.get i x).
    Proof.
      revert dl. induction a as [|y ys IH]; cbn; intros dl Hma Hin; [tauto|].
      destruct (map.get i y) as [vy|] eqn:Hgy; cbn in Hma; [|discriminate].
      destruct (list_Mmap (map.get i) ys) as [vs|] eqn:Hgs; cbn in Hma;
        [|discriminate].
      destruct Hin as [Hxy|Hin']; [subst y; rewrite Hgy; exact I|].
      eapply IH; eauto.
    Qed.

    Lemma args_in_instance_has_keys s i e a
      : egraph_sound_for_interpretation lang_model i e ->
        args_in_instance l s i a ->
        forall x, In x a -> Sep.has_key x (parent (Defs.equiv e)).
    Proof.
      intros [_ Hexact _ _] Hai x Hin.
      apply Hexact.
      unfold args_in_instance in Hai.
      destruct (list_Mmap (map.get i) a) as [dl|] eqn:Hma; cbn in Hai; [|tauto].
      eapply list_Mmap_get_has_some; eauto.
    Qed.

    (* Lift an [option_relation _ (map.get i _) (Some _)] across an
       interpretation extension. *)
    Lemma option_relation_get_extends {B} (R : domain V lang_model -> B -> Prop)
                                      (i i' : interp) x d
      : map.extends i' i ->
        option_relation R (map.get i x) (Some d) ->
        option_relation R (map.get i' x) (Some d).
    Proof.
      intros Hext Hor.
      destruct (map.get i x) as [v|] eqn:Hg; cbn in Hor; [|discriminate].
      apply Hext in Hg. rewrite Hg. cbn. exact Hor.
    Qed.

    (* ----------- Theorem statements & proofs ----------- *)

    (* Mutually recursive workhorse: simultaneous induction on
       [wf_term l1 c e t] and [wf_args l1 c args c'] via
       [WfCutElim.wf_cut_ind].  Generalized over the inner
       [add_open_sort] argument so the recursion on sorts can be
       discharged separately via a strictly-decreasing language-length
       measure: [length l2 < length l1]. *)
    Lemma add_open_sound (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (add_open_sort_inner_sound :
        forall l2 c' t s r' i,
          wf_lang l2 ->
          length l2 < length l1 ->
          incl l2 l1 ->
          wf_args l [] s c' ->
          wf_ctx l2 c' ->
          wf_sort l2 c' t ->
          map fst c' = map fst r' ->
          vc (add_open_sort_inner r' t)
             (open_sort_post c' s t r' i))
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      s c (Hsubst : wf_args l [] s c) (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t ->
                     forall r i,
                       map fst c = map fst r ->
                       vc (add_open_term' succ sort_of l with_sorts false
                                          add_open_sort_inner r e)
                          (open_term_post c s e r i))
        /\ (forall args c', wf_args l1 c args c' ->
                     forall r i,
                       map fst c = map fst r ->
                       vc (list_Mmap (add_open_term' succ sort_of l with_sorts false
                                                      add_open_sort_inner r) args)
                          (open_args_post c s args r i)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r i, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l with_sorts false
                                     add_open_sort_inner r e)
                     (open_term_post c s e r i))
               (fun args c' => forall r i, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l with_sorts false
                                                add_open_sort_inner r) args)
                     (open_args_post c s args r i))).
      - (* con case: e = con name s', wf_term l1 c (con name s') t [/.../].
           Computation: list_Mmap of add_open_term' for args, then hash_entry
           on the constructor. with_sorts=true also adds a sort_of annotation
           via add_open_sort_inner + update_entry. *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r i Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r i Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        (* Now we have hash_entry n a_out followed by conditionals.
           Apply vc_bind for hash_entry next, but it's wrapped in a
           goal of shape `forall e, P (a_out, e) -> Q ...`.  Step through
           hash_entry_sound directly via vc unfolding. *)
        unfold vc; intros e_inner Hpost_args.
        unfold open_term_post.
        intros Hok Hsound Hai.
        unfold open_args_post in Hpost_args.
        specialize (Hpost_args Hok Hsound Hai).
        destruct Hpost_args as [i_out Hpa]. destruct Hpa as [Hext_out Hai_out].
        pose proof Hext_out as Hext_out_save.
        destruct Hext_out as (Hok_out & Hexti_out & Hsnd_out & Hkeys_out).
        cbn [fst snd] in *.
        unfold args_in_instance in Hai_out.
        iss_case.
        rename Hma into Hdl. rename l0 into dl.
        pose proof Hai_out as Hai_out'.
        apply all2_lang_model_eq_inl' in Hai_out'.
        destruct Hai_out' as [dl' Hdl_eq]; subst dl.
        pose proof (@hash_entry_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                       V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X _ lang_model
                       (lang_model_ok l Hsof Hwf) lt_asymmetric lt_succ lt_trans
                       i_out name a_out
                       (inl (con name s'[/with_names_from c s/]))) as Hhe.
        unfold vc in Hhe. specialize (Hhe e_inner).
        assert (Hkeys_args : forall x, In x a_out ->
                              Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. eapply args_in_instance_has_keys; eauto.
          unfold args_in_instance. rewrite Hdl. cbn. exact Hai_out. }
        assert (Hwfc'_rule : wf_ctx l c'_rule).
        { use_rule_in_wf. inversion H0; subst.
          rewrite List.app_nil_r in H4. exact H4. }
        assert (Hwfargs_subst : wf_args l {{c }} s'[/with_names_from c s /] c'_rule).
        { eapply wf_args_subst_monotonicity.
          1: exact V_Eqb_ok.
          1: exact Hwf.
          1:{ eapply wf_args_lang_monotonicity. 1: exact Hl1. exact Hwf_args_inner. }
          1:{ eapply wf_ctx_lang_monotonicity. 1: exact Hl1. exact Hctx. }
          1: exact Hwfc'_rule.
          apply wf_subst_from_wf_args; exact Hsubst. }
        assert (Heqt : eq_term l {{c }}
                          (t_rule[/with_names_from c'_rule (s'[/with_names_from c s/])/])
                          (con name dl') (con name s'[/with_names_from c s/])).
        { eapply term_con_congruence.
          1: exact Hrule_in.
          1: right; reflexivity.
          1: exact Hwf.
          eapply eq_args_sym.
          1: apply (core_model_ok Hwf).
          1: exact Hwfc'_rule.
          eapply all2_model_eq_eq_args.
          1: exact Hwf.
          1: exact Hwfargs_subst.
          1: exact Hwfc'_rule.
          pose proof (lang_model_eq_PER l Hwf : PER (lang_model_eq l)) as Hper.
          destruct Hper as [Hsym_per _].
          apply (@all2_Symmetric _ _ Hsym_per).
          exact Hai_out. }
        assert (Hint_wit :
                  exists arg_doms,
                    list_Mmap (map.get i_out) a_out = Some arg_doms
                    /\ interprets_to V lang_model name arg_doms
                         (inl (con name s'[/with_names_from c s/]))).
        { exists (map inl dl').
          split. 1: exact Hdl.
          cbn [lang_model domain interprets_to].
          eapply interprets_to_term. exact Heqt. }
        specialize (Hhe Hok_out Hsnd_out Hkeys_args Hint_wit).
        destruct Hhe as [Hok_he Hex_he].
        destruct Hex_he as [i' Hi'].
        destruct Hi' as (Hexti' & Hsnd' & Hkeys' & Hkey_res & Hdom_eq).
        (* Now we're past hash_entry; need to handle the with_sorts conditional
           and the Mret tt for with_ctx_sorts=false.  Both ifs reduce to literals. *)
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in *.
        assert (Hext_he : extending_sound i e_pre i' e_he)
          by (eapply extending_sound_trans; [exact Hext_out_save|];
              unfold extending_sound; eauto 10).
        (* The remaining program is:
           Mret tt >>= fun _ => if with_sorts then add_open_sort_inner ... else Mret x_res *)
        cbn [Mbind StateMonad.state_monad Mret].
        destruct with_sorts eqn:Hws.
        1:{ (* with_sorts = true: add_open_sort_inner on t_rule, then
               update_entry on sort_of(x_res). *)
            pose proof (wf_lang_ext_split _ _ _ Hwf1 Hrule_in_l1) as Hsplit.
            destruct Hsplit as [l2 Hsplit2].
            destruct Hsplit2 as [Hwfl2 Hsplit3].
            destruct Hsplit3 as [Hwfr_l2 Hsplit4].
            destruct Hsplit4 as [Hincl_l2 Hlen_l2].
            apply invert_wf_term_rule in Hwfr_l2.
            destruct Hwfr_l2 as [Hwfc_l2 Hwfrest].
            destruct Hwfrest as [_ Hwfsort_l2].
            assert (Hlen_aout : length a_out = length c'_rule) by
              (pose proof (wf_args_length_eq Hwfargs_subst) as Hlen_eq;
               apply TrieMap.list_Mmap_length in Hdl; rewrite Hdl, length_map;
               destruct (PeanoNat.Nat.eq_dec
                           (length (map inl dl' : list (term + sort)))
                           (length (map inl s'[/with_names_from c s/]
                                    : list (term + sort)))) as [Heq|Hne];
               [rewrite !length_map in Heq; congruence
               | exfalso;
                 apply (all2_len_False (lang_model_eq l) _ _ Hne Hai_out)]).
            assert (Hmaps_rule : map fst c'_rule
                                 = map fst (combine (map fst c'_rule) a_out)) by
              (rewrite combine_map_fst_is_with_names_from;
               symmetry; apply map_fst_with_names_from; congruence).
            pose proof (add_open_sort_inner_sound l2 c'_rule t_rule
                          (s'[/with_names_from c s/])
                          (combine (map fst c'_rule) a_out) i'
                          Hwfl2 Hlen_l2 Hincl_l2 Hwfargs_subst
                          Hwfc_l2 Hwfsort_l2 Hmaps_rule)
              as Hsort_snd.
            unfold vc in Hsort_snd. specialize (Hsort_snd e_he).
            unfold open_sort_post in Hsort_snd.
            assert (Hai_at_he :
                      args_in_instance l (s'[/with_names_from c s/]) i'
                        (map snd (combine (map fst c'_rule) a_out))).
            { rewrite combine_map_fst_is_with_names_from.
              replace (map snd (with_names_from c'_rule a_out)) with a_out;
                [|clear -Hlen_aout; revert a_out Hlen_aout;
                  induction c'_rule as [|[? ?] ? IH]; intros [|? ?]; cbn;
                  intros; try discriminate; try reflexivity;
                  f_equal; auto].
              eapply args_in_instance_monotone; [exact Hexti'|].
              unfold args_in_instance. rewrite Hdl. cbn. exact Hai_out. }
            specialize (Hsort_snd Hok_he Hsnd' Hai_at_he).
            destruct (add_open_sort_inner (combine (map fst c'_rule) a_out)
                        t_rule e_he) as [t_v e_sort] eqn:Heq_sort.
            cbn [fst snd] in Hsort_snd.
            destruct Hsort_snd as [i_sort Hi_sort].
            destruct Hi_sort as [Hext_sort Hdom_sort].
            pose proof Hext_sort as Hext_sort_save.
            destruct Hext_sort as
                (Hok_sort & Hexti_sort & Hsnd_sort & Hkeys_sort).
            cbn [fst snd] in *.
            assert (Hdom_eq_lifted :
                      option_relation (domain_eq V lang_model)
                        (map.get i_sort x_res)
                        (Some (inl (con name s'[/with_names_from c s/])
                               : domain V lang_model))).
            { destruct (map.get i' x_res) as [d|] eqn:Hg; cbn in Hdom_eq.
              - apply Hexti_sort in Hg. rewrite Hg. cbn. exact Hdom_eq.
              - discriminate Hdom_eq. }
            destruct (map.get i_sort x_res) as [d_x|] eqn:Hgx_sort;
              cbn in Hdom_eq_lifted; [|discriminate Hdom_eq_lifted].
            destruct (map.get i_sort t_v) as [d_t|] eqn:Hgtv;
              cbn in Hdom_sort; [|discriminate Hdom_sort].
            inversion Hdom_eq_lifted as
                [e_x e_y t_x Heqterm_x Hdxeq Hineq | ]; subst d_x.
            inversion Hdom_sort as
                [| t_t1 t_t2 Heqsort_t Hdteq Hineq2]; subst d_t.
            assert (Hwfex_tx : wf_term l [] e_x t_x) by
              (eapply eq_term_wf_l; eauto using wf_ctx_nil).
            assert (Hwfcon_tx :
                      wf_term l [] (con name s'[/with_names_from c s/]) t_x) by
              (eapply eq_term_wf_r; eauto using wf_ctx_nil).
            assert (Hwfcon_tr :
                      wf_term l [] (con name s'[/with_names_from c s/])
                        (t_rule[/with_names_from c'_rule
                                 (s'[/with_names_from c s/])/])) by
              (eapply wf_term_by; eauto).
            assert (Heq_tx_tr :
                      eq_sort l [] t_x
                        (t_rule[/with_names_from c'_rule
                                 (s'[/with_names_from c s/])/])) by
              (eapply term_sorts_eq; eauto using wf_ctx_nil).
            assert (Heq_tx_t1 : eq_sort l [] t_x t_t1) by
              (eapply eq_sort_trans; [exact Heq_tx_tr|];
               eapply eq_sort_sym; eauto).
            assert (Hwfex_t1 : wf_term l [] e_x t_t1) by
              (eapply wf_term_conv; eauto).
            assert (Hkey_tv : Sep.has_key t_v (parent (equiv e_sort))).
            { destruct Hsnd_sort as [_ Hi_exact _ _].
              apply Hi_exact. rewrite Hgtv. exact I. }
            assert (Hkey_xres_sort :
                      Sep.has_key x_res (parent (equiv e_sort))) by
              (apply Hkeys_sort; exact Hkey_res).
            assert (Hatom_snd :
                      atom_sound_for_model V V V_map lang_model i_sort
                        (Build_atom sort_of [x_res] t_v)).
            { unfold atom_sound_for_model. cbn.
              destruct (map.get i_sort x_res) eqn:Hgx_sort2; [|congruence].
              inversion Hgx_sort2; subst. rewrite H1.
              destruct (map.get i_sort t_v) eqn:Hgtv2; [|congruence].
              inversion Hgtv2; subst. rewrite H2. cbn.
              inversion Hgx_sort; inversion Hgtv; subst.
              econstructor. exact Hwfex_t1. }
            pose proof (@update_entry_sound V V_Eqb V_Eqb_ok lt succ V_default
                          V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok
                          V_trie V_trie_ok X _ lang_model
                          (lang_model_ok l Hsof Hwf)
                          i_sort (Build_atom sort_of [x_res] t_v)) as Hue.
            unfold vc in Hue. specialize (Hue e_sort).
            specialize (Hue Hok_sort Hsnd_sort).
            assert (Hargs_keys :
                      forall x, In x [x_res] ->
                                Sep.has_key x (parent (equiv e_sort))) by
              (intros x Hx; cbn in Hx; destruct Hx as [Hxx|Hxx];
               [subst x; exact Hkey_xres_sort | contradiction]).
            specialize (Hue Hargs_keys Hkey_tv Hatom_snd).
            destruct (update_entry (Build_atom sort_of [x_res] t_v) e_sort)
              as [unit_r e_update] eqn:Heq_update.
            cbn [fst snd] in Hue.
            destruct Hue as (Hok_update & Hsnd_update & Hkeys_update).
            exists i_sort. cbn [fst snd]. split.
            { eapply extending_sound_trans; [exact Hext_he|].
              eapply extending_sound_trans; [exact Hext_sort_save|].
              unfold extending_sound.
              split; [exact Hok_update|].
              split; [apply Properties.map.extends_refl|].
              split; [exact Hsnd_update | exact Hkeys_update]. }
            { rewrite Hgx_sort. cbn.
              apply lm_eq_terms with (t := t_x). exact Heqterm_x. } }
        (* with_sorts = false: just return x_res *)
        cbn [Mret StateMonad.state_monad fst snd].
        exists i'. split; [exact Hext_he|exact Hdom_eq].
      - (* var case: e = var n, wf_term l1 c (var n) t (with In (n, t) c). *)
        intros n t_var Hin_var r i Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_term_post.
        intros Hok Hsound Hai.
        exists i. split; [apply extending_sound_refl; auto|].
        (* result id is named_list_lookup default r n; extract interpretation
             via args_in_instance_in *)
          assert (Hafc : all_fresh c) by basic_core_crush.
          assert (Hafr : all_fresh r).
          { apply NoDup_fresh. rewrite <- Hmaps. apply NoDup_fresh; exact Hafc. }
          assert (Hlen_cs : length c = length s) by (eapply wf_args_length_eq; eauto).
          assert (Hafws : all_fresh (with_names_from c s)).
          { apply NoDup_fresh. rewrite map_fst_with_names_from by auto.
            apply NoDup_fresh; exact Hafc. }
          assert (Hex_x : exists x_n, In (n, x_n) r).
          { apply pair_fst_in_exists. rewrite <- Hmaps. eapply pair_fst_in; exact Hin_var. }
          destruct Hex_x as [x_n Hin_xn].
          assert (Hex_e : exists e_n, In (n, e_n) (with_names_from c s)).
          { apply pair_fst_in_exists. rewrite map_fst_with_names_from by auto.
            eapply pair_fst_in; exact Hin_var. }
          destruct Hex_e as [e_n Hin_en].
          pose proof (args_in_instance_in l s i c n e_n x_n r Hai Hsubst Hmaps Hafc Hin_en Hin_xn)
            as Hin_d.
          destruct Hin_d as [d Hd_conj]. destruct Hd_conj as [Hgd Hled].
          assert (Hlk : named_list_lookup default r n = x_n).
          { clear -V_Eqb_ok Hafr Hin_xn.
            induction r as [|[m v_m] r' IH]; cbn in *; [tauto|].
            destruct Hafr as [Hfr Hafr'].
            destruct Hin_xn as [Heq|Hin_xn'].
            - inversion Heq; subst.
              eqb_case n n; congruence.
            - eqb_case n m.
              + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_xn'.
              + apply IH; auto. }
          cbn [fst].
          rewrite Hlk, Hgd. cbn.
          unfold term_subst_lookup.
          assert (named_list_lookup (var n) (with_names_from c s) n = e_n) as Hsl.
          { clear -V_Eqb_ok Hafws Hin_en.
            induction (with_names_from c s) as [|[m v_m] r' IH]; cbn in *; [tauto|].
            destruct Hafws as [Hfr Hafr'].
            destruct Hin_en as [Heq|Hin_en'].
            - inversion Heq; subst.
              eqb_case n n; congruence.
            - eqb_case n m.
              + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_en'.
              + apply IH; auto. }
          rewrite Hsl.
          exact Hled.
      - (* eq_sort conversion: postcondition doesn't depend on the sort, so IH applies. *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r i Hmaps.
        apply IH_term; assumption.
      - (* nil args: list_Mmap on []. Trivial: open_args_post holds with i_in. *)
        intros r i Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_args_post. intros e_pre Hok Hsound Hai.
        exists i. split; [apply extending_sound_refl; auto|].
        cbn. unfold args_in_instance. cbn. constructor.
      - (* cons args: chain via vc_bind on the head and IH_args on the tail,
           then args_in_instance_cons. *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r i Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_args_post.
        intros Hok Hsound Hai.
        (* Apply IH_term to e_in *)
        specialize (IH_term r i Hmaps).
        unfold vc, open_term_post in IH_term.
        specialize (IH_term e_in Hok Hsound Hai).
        destruct (add_open_term' succ sort_of l with_sorts false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        cbn [fst snd] in IH_term.
        destruct IH_term as [i_head Hih].
        destruct Hih as [Hext_head Hgvhead].
        pose proof Hext_head as Hh.
        destruct Hh as (Hok_head & Hexti_head & Hsound_head & _).
        (* Now apply IH_args with i_head *)
        specialize (IH_args r i_head Hmaps).
        unfold vc, open_args_post in IH_args.
        specialize (IH_args e_after_head Hok_head Hsound_head
                            (args_in_instance_monotone _ _ _ _ _ Hexti_head Hai)).
        destruct (list_Mmap
                    (add_open_term' succ sort_of l with_sorts false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd] in IH_args.
        destruct IH_args as [i_final Hif].
        destruct Hif as [Hext_final Hai_tail].
        exists i_final. split.
        { eapply extending_sound_trans; eauto. }
        { apply args_in_instance_cons; [exact Hai_tail|].
          destruct Hext_final as (_ & Hexti_final & _).
          destruct (map.get i_head v_head) as [d|] eqn:Hgh; cbn in Hgvhead;
            [|discriminate].
          apply Hexti_final in Hgh. rewrite Hgh. cbn. exact Hgvhead. }
    Qed.

    (* Induction on the fuel parameter, using [add_open_sound] in the
       step case to discharge the [list_Mmap (add_open_term' ...)]
       sub-call.  Generalized over the sub-language [l1] for the
       well-founded recursion. *)
    Lemma add_open_sort'_sound l1 c r s t fuel
      : wf_lang l1 ->
        length l1 < fuel ->
        incl l1 l ->
        wf_args l [] s c ->
        wf_ctx l1 c ->
        wf_sort l1 c t ->
        map fst c = map fst r ->
        forall i,
        vc (add_open_sort' succ sort_of l with_sorts false fuel r t)
           (open_sort_post c s t r i).
    Proof.
      revert l1 c r s t.
      induction fuel; intros l1 c r s t Hwfl1 Hflen Hincl Hsubst Hctx Hsort Hmaps i.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { (* args: apply add_open_sound proj2 with IHfuel as inner soundness *)
          apply (proj2 (add_open_sound l1
                          (add_open_sort' succ sort_of l with_sorts false fuel)
                          (fun l2 c'2 t2 s2 r2 i2 Hwfl2 Hflen2 Hincl2
                               Hsubst2 Hctx2 Hsort2 Hmaps2 =>
                             IHfuel l2 c'2 r2 s2 t2 Hwfl2
                               ltac:(Lia.lia)
                               (incl_tran Hincl2 Hincl)
                               Hsubst2 Hctx2 Hsort2 Hmaps2 i2)
                          Hwfl1 Hincl s c Hsubst Hctx)
                _ _ Hwfargs r i Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_sort_post.
        intros Hok Hsound Hai.
        unfold open_args_post in Hpost_args.
        specialize (Hpost_args Hok Hsound Hai).
        destruct Hpost_args as [i_out Hpa]. destruct Hpa as [Hext_out Hai_out].
        pose proof Hext_out as Hext_out_save.
        destruct Hext_out as (Hok_out & Hexti_out & Hsnd_out & Hkeys_out).
        cbn [fst snd] in *.
        unfold args_in_instance in Hai_out.
        iss_case.
        rename Hma into Hdl. rename l0 into dl.
        pose proof Hai_out as Hai_out'.
        apply all2_lang_model_eq_inl' in Hai_out'.
        destruct Hai_out' as [dl' Hdl_eq]; subst dl.
        pose proof (@hash_entry_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                       V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X _ lang_model
                       (lang_model_ok l Hsof Hwf) lt_asymmetric lt_succ lt_trans
                       i_out n a_out (inr (scon n s_t[/with_names_from c s/]))) as Hhe.
        unfold vc in Hhe. specialize (Hhe e_inner).
        assert (Hkeys_args : forall x, In x a_out ->
                              Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. eapply args_in_instance_has_keys; eauto.
          unfold args_in_instance. rewrite Hdl. cbn. exact Hai_out. }
        assert (Hwfc' : wf_ctx l c').
        { use_rule_in_wf. inversion H0; subst.
          rewrite List.app_nil_r in H3. exact H3. }
        assert (Hwfargs_subst : wf_args l {{c }} s_t [/with_names_from c s /] c').
        { eapply wf_args_subst_monotonicity.
          1: exact V_Eqb_ok.
          1: exact Hwf.
          1:{ eapply wf_args_lang_monotonicity. 1: exact Hincl. exact Hwfargs. }
          1:{ eapply wf_ctx_lang_monotonicity. 1: exact Hincl. exact Hctx. }
          1: exact Hwfc'.
          apply wf_subst_from_wf_args; exact Hsubst. }
        assert (Heqs : eq_sort l {{c }} (scon n dl') (scon n s_t [/with_names_from c s /])).
        { eapply sort_con_congruence.
          1: exact V_Eqb_ok.
          1: exact Hrule.
          1: exact Hwf.
          eapply eq_args_sym.
          1: apply (core_model_ok Hwf).
          1: exact Hwfc'.
          eapply all2_model_eq_eq_args.
          1: exact Hwf.
          1: exact Hwfargs_subst.
          1: exact Hwfc'.
          pose proof (lang_model_eq_PER l Hwf : PER (lang_model_eq l)) as Hper.
          destruct Hper as [Hsym_per _].
          apply (@all2_Symmetric _ _ Hsym_per).
          exact Hai_out. }
        assert (Hint_wit :
                  exists arg_doms,
                    list_Mmap (map.get i_out) a_out = Some arg_doms
                    /\ interprets_to V lang_model n arg_doms
                         (inr (scon n s_t[/with_names_from c s/]))).
        { exists (map inl dl').
          split. 1: exact Hdl.
          cbn [lang_model domain interprets_to].
          eapply interprets_to_sort. exact Heqs. }
        specialize (Hhe Hok_out Hsnd_out Hkeys_args Hint_wit).
        destruct Hhe as [Hok_he Hex_he].
        destruct Hex_he as [i' Hi'].
        destruct Hi' as (Hexti' & Hsnd' & Hkeys' & Hkey_res & Hdom_eq).
        exists i'.
        split; [|exact Hdom_eq].
        eapply extending_sound_trans; [exact Hext_out_save|].
        unfold extending_sound; eauto 10.
    Qed.

    Lemma add_open_sort_sound c r s t
      : wf_args l [] s c ->
        wf_ctx l c ->
        wf_sort l c t ->
        map fst c = map fst r ->
        forall i,
        vc (add_open_sort succ sort_of l with_sorts false r t)
           (open_sort_post c s t r i).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_sound; try eassumption; eauto with utils.
    Qed.

    Lemma add_open_term_sound c r s e t
      : wf_args l [] s c ->
        wf_term l c e t ->
        wf_ctx l c ->
        map fst c = map fst r ->
        forall i,
        vc (add_open_term succ sort_of l with_sorts false r e)
           (open_term_post c s e r i).
    Proof.
      intros Hsubst Hwft Hctx Hmaps i.
      unfold add_open_term.
      pose proof (add_open_sound l (add_open_sort succ sort_of l with_sorts false))
        as Hsnd.
      specialize (Hsnd ltac:(intros; eapply add_open_sort_sound; try eassumption;
                             [eapply wf_ctx_lang_monotonicity; eauto
                             |eapply wf_sort_lang_monotonicity; eauto])).
      specialize (Hsnd Hwf (incl_refl _) s c Hsubst Hctx).
      destruct Hsnd as [Hsndt _].
      eapply Hsndt; eauto.
    Qed.

    (* Induction on [wf_subst l [] s c] (which gives [wf_ctx l c] via
       its inversion); per step the body is a vc_bind chain over
       [add_open_sort_sound], [alloc_opaque_sound],
       [hash_entry_sound] (for [(sort_of, [x'])]), and
       [union_sound] (to identify [sort_of(x')] with the sort id). *)
    Lemma add_ctx_sound s c
      : wf_subst l [] s c ->
        wf_ctx l c ->
        forall i,
        vc (add_ctx succ sort_of l with_sorts false c)
           (ctx_post s c i).
    Proof.
      intros Hsubst Hctx i.
      unfold add_ctx.
      induction Hsubst.
      - (* nil case: list_Mfoldr ... [] [] reduces to ret []; ctx_post holds
           with i_out := i_in (identity extension). *)
        cbn [list_Mfoldr].
        unfold vc, Mret. cbn.
        unfold ctx_post. intros e_in Hok Hsound.
        exists i. split; [apply extending_sound_refl; auto|].
        split; [reflexivity|].
        cbn. unfold args_in_instance. cbn. constructor.
      - (* cons case: chain vc_bind over
           add_open_sort_sound -> alloc_opaque_sound -> hash_entry_sound -> union_sound,
           then construct the extended ctx_post. *)
        cbn [list_Mfoldr].
        eapply vc_bind.
        { apply IHHsubst. inversion Hctx; assumption. }
        intros e_pre base'.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_tail.
        unfold ctx_post. intros Hok Hsound.
        unfold ctx_post in Hpost_tail.
        specialize (Hpost_tail Hok Hsound).
        destruct Hpost_tail as [i_tail Hpa]. destruct Hpa as [Hext_tail Hpa'].
        destruct Hpa' as [Hfst_tail Hai_tail].
        pose proof Hext_tail as Hext_tail_save.
        destruct Hext_tail as (Hok_tail & Hexti_tail & Hsnd_tail & Hkeys_tail).
        cbn [fst snd] in *.
        (* Step 1: add_open_sort_sound on t *)
        pose proof (add_open_sort_sound c' base' (map snd s) t
                      (wf_args_from_wf_subst _ _ _ _ Hsubst)) as Hsort_snd.
        assert (Hwfc' : wf_ctx l c') by (inversion Hctx; assumption).
        assert (Hwfst : wf_sort l c' t) by (inversion Hctx; assumption).
        specialize (Hsort_snd Hwfc' Hwfst).
        assert (Hmaps_t : map fst c' = map fst base') by (symmetry; exact Hfst_tail).
        specialize (Hsort_snd Hmaps_t i_tail).
        unfold vc in Hsort_snd. specialize (Hsort_snd e_inner).
        unfold open_sort_post in Hsort_snd.
        specialize (Hsort_snd Hok_tail Hsnd_tail Hai_tail).
        destruct (add_open_sort succ sort_of l with_sorts false base' t e_inner)
          as [t_v e_sort] eqn:Heq_sort.
        cbn [fst snd] in Hsort_snd.
        destruct Hsort_snd as [i_sort Hi_sort]. destruct Hi_sort as [Hext_sort Hdom_sort].
        pose proof Hext_sort as Hext_sort_save.
        destruct Hext_sort as (Hok_sort & Hexti_sort & Hsnd_sort & Hkeys_sort).
        cbn [fst snd] in *.
        (* Step 2: alloc_opaque_sound with d := inl e *)
        pose proof (@alloc_opaque_sound V V_Eqb V_Eqb_ok lt succ V_default V
                       V_map V_map V_map_ok V_trie X _ lang_model
                       lt_asymmetric lt_succ lt_trans
                       i_sort (inl e : domain V lang_model)) as Halloc_snd.
        assert (Hwfd : domain_wf V lang_model (inl e)).
        { unfold domain_wf. cbn. econstructor.
          eapply eq_term_refl; eauto with lang_core. }
        specialize (Halloc_snd Hwfd Hwfd).
        unfold vc in Halloc_snd. specialize (Halloc_snd e_sort).
        specialize (Halloc_snd Hok_sort Hsnd_sort).
        destruct (alloc_opaque V succ V V_map V_map V_trie X e_sort) as [x' e_alloc] eqn:Heq_alloc.
        cbn [fst snd] in Halloc_snd.
        destruct Halloc_snd as (Hok_alloc & Hsnd_alloc & Hinone_x' & Hx'_fresh
                                & Hx'_key & Hkeys_alloc & Hdb_alloc & Hpar_alloc
                                & Hwl_alloc).
        cbn [fst snd] in *.
        (* Step 3: hash_entry_sound on sort_of [x'] *)
        pose proof (@hash_entry_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                      V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X _ lang_model
                      (lang_model_ok l Hsof Hwf) lt_asymmetric lt_succ lt_trans
                      (map.put i_sort x' (inl e : domain V lang_model))
                      sort_of [x'] (inr (t[/s/]) : domain V lang_model)) as Hhe.
        unfold vc in Hhe. specialize (Hhe e_alloc).
        assert (Hkeys_args : forall y, In y [x'] -> Sep.has_key y (parent (equiv e_alloc))).
        { intros y Hy. cbn in Hy. destruct Hy as [Hy|]; [|contradiction]. subst y. exact Hx'_key. }
        assert (Hint_wit : exists arg_doms,
                  list_Mmap (map.get (map.put i_sort x' (inl e : domain V lang_model))) [x']
                  = Some arg_doms
                  /\ interprets_to V lang_model sort_of arg_doms
                       (inr (t[/s/]) : domain V lang_model)).
        { exists [inl e]. split.
          - cbn. rewrite map.get_put_same. reflexivity.
          - cbn. eapply interprets_to_sort_of. exact H0. }
        specialize (Hhe Hok_alloc Hsnd_alloc Hkeys_args Hint_wit).
        destruct Hhe as [Hok_he Hex_he].
        destruct Hex_he as [i_he Hi_he].
        destruct Hi_he as (Hexti_he & Hsnd_he & Hkeys_he & Hkey_he_res & Hdom_he).
        destruct (hash_entry succ sort_of [x'] e_alloc) as [tx' e_he] eqn:Heq_he.
        cbn [fst snd] in *.
        (* Step 4: union_sound on (t_v, tx') *)
        assert (Hkey_tv_he : Sep.has_key t_v (parent (equiv e_he))).
        { apply Hkeys_he. apply Hkeys_alloc.
          pose proof Hsnd_sort as Hsnd_sort_copy.
          destruct Hsnd_sort_copy as [_ Hsnd_exact _ _].
          apply Hsnd_exact.
          destruct (map.get i_sort t_v) as [d|]; cbn in Hdom_sort;
            [constructor|discriminate]. }
        pose proof (@union_sound V V_Eqb V_Eqb_ok lt succ V_default V
                      V_map V_map V_map_ok V_trie X _ t_v tx') as Hu.
        unfold vc in Hu. specialize (Hu e_he).
        pose proof Hok_he as Hok_he_save.
        destruct Hok_he as [Heqok_he Hwlok_he Hparok_he Hdbkok_he].
        destruct Heqok_he as [roots_he Hroots_he].
        specialize (Hu (ex_intro _ roots_he Hroots_he)).
        specialize (Hu Hkey_tv_he Hkey_he_res).
        destruct (union t_v tx' e_he) as [v_u e_u] eqn:Heq_union.
        cbn [fst snd] in Hu.
        destruct Hu as (Hdb_u & [roots_u Hroots_u] & Hper_u & Hpar_u
                       & Hwl_rel_u & Hper_tv_u).
        cbn [fst snd] in *.
        (* Now build the post for e_u: i_out := i_he *)
        (* Derive eq_sound i_he t_v tx' via both interpreting to inr t[/s/]. *)
        assert (Heq_subst : with_names_from c' (map snd s) = s).
        { pose proof (wf_subst_dom_eq Hsubst) as Hdom.
          revert Hdom. clear -s c'. revert s.
          induction c' as [|[n0 t0] c_rest IH]; destruct s as [|[n1 e1] s_rest];
            cbn; intros Hdom; auto; try discriminate.
          inversion Hdom; subst. f_equal. apply IH. exact H1. }
        rewrite Heq_subst in Hdom_sort.
        (* Lift Hdom_sort through extensions: i_sort -> map.put i_sort x' _ -> i_he *)
        assert (Hext_put : map.extends (map.put i_sort x' (inl e : domain V lang_model)) i_sort).
        { intros k v Hgk.
          eqb_case k x'.
          - rewrite Hgk in Hinone_x'. discriminate.
          - rewrite map.get_put_diff by congruence. exact Hgk. }
        assert (Hext_he_sort : map.extends i_he i_sort).
        { intros k v Hgk. apply Hexti_he. apply Hext_put. exact Hgk. }
        assert (Hdom_sort_he : option_relation (domain_eq V lang_model)
                                  (map.get i_he t_v) (Some (inr t[/s/]))).
        { destruct (map.get i_sort t_v) as [d|] eqn:Hgts; cbn in Hdom_sort;
            [|discriminate].
          apply Hext_he_sort in Hgts. rewrite Hgts. cbn. exact Hdom_sort. }
        assert (Heqs_tv_tx : eq_sound_for_model V V V_map lang_model i_he t_v tx').
        { unfold eq_sound_for_model.
          destruct (map.get i_he t_v) as [d_tv|] eqn:Hgtv; cbn in Hdom_sort_he;
            [|discriminate].
          destruct (map.get i_he tx') as [d_tx|] eqn:Hgtx; cbn in Hdom_he;
            [|discriminate].
          cbn.
          (* domain_eq d_tv (inr t[/s/]) AND domain_eq d_tx (inr t[/s/]) -> domain_eq d_tv d_tx *)
          pose proof (lang_model_ok l Hsof Hwf) as Hmok.
          assert (Hsym : Symmetric (domain_eq V lang_model))
            by (apply Hmok).
          assert (Htrans : Transitive (domain_eq V lang_model))
            by (apply Hmok).
          eapply Htrans; [exact Hdom_sort_he|].
          apply Hsym. exact Hdom_he. }
        (* Lift e_he hypotheses across union *)
        assert (Hkey_pres_he_u : forall x, Sep.has_key x (parent (equiv e_he)) ->
                                            Sep.has_key x (parent (equiv e_u))).
        { intros x Hx. unfold Sep.has_key in *.
          destruct (map.get (parent (equiv e_u)) x) eqn:Hgx; [constructor|].
          exfalso.
          destruct (map.get (parent (equiv e_he)) x) eqn:Hgx_he; [|tauto].
          assert (Hxx : uf_rel_PER V (V_map V) (V_map nat) (equiv e_he) x x).
          { unfold uf_rel_PER.
            eapply PER_clo_trans;
              [apply PER_clo_base; exact Hgx_he
              |apply PER_clo_sym; apply PER_clo_base; exact Hgx_he]. }
          assert (Hxx' : uf_rel_PER V (V_map V) (V_map nat) (equiv e_u) x x).
          { apply Hper_u. unfold Relations.union_closure_PER.
            apply PER_clo_base. left. exact Hxx. }
          edestruct (@uf_rel_PER_has_key V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok
                       (equiv e_u) roots_u x x Hroots_u Hxx') as [Hkx _].
          unfold Sep.has_key in Hkx. rewrite Hgx in Hkx. tauto. }
        assert (Hper_lift : forall i1 i2,
                            uf_rel_PER V (V_map V) (V_map nat) (equiv e_he) i1 i2 ->
                            uf_rel_PER V (V_map V) (V_map nat) (equiv e_u) i1 i2).
        { intros i1 i2 Hi12. apply Hper_u.
          unfold Relations.union_closure_PER. apply PER_clo_base. left. exact Hi12. }
        assert (Hrel_new : forall i1 i2,
                            uf_rel_PER V (V_map V) (V_map nat) (equiv e_u) i1 i2 ->
                            eq_sound_for_model V V V_map lang_model i_he i1 i2).
        { intros i1 i2 Hi12. apply Hper_u in Hi12.
          induction Hi12 as [a b H1 | a b c2 IHab Hab IHbc Hbc | a b IHab Hab].
          - destruct H1 as [Hold | Hnew];
              [destruct Hsnd_he as [_ _ _ Hi_rel]; apply Hi_rel; exact Hold
              |destruct Hnew as [Hpa Hpb]; subst; exact Heqs_tv_tx].
          - pose proof (lang_model_ok l Hsof Hwf) as Hmok_t.
            eapply (eq_sound_for_model_trans V V V_map lang_model);
              [exact Hab|exact Hbc].
          - pose proof (lang_model_ok l Hsof Hwf) as Hmok_s.
            eapply (eq_sound_for_model_Symmetric V V V_map lang_model); exact Hab. }
        (* Construct egraph_ok e_u *)
        assert (Hok_u : egraph_ok e_u).
        { constructor.
          1:{ exists roots_u. exact Hroots_u. }
          1:{ destruct Hwl_rel_u as [Hwl_same | Hwl_new].
              { rewrite Hwl_same. eapply all_wkn; [|exact Hwlok_he].
                intros ent _ Hp. destruct ent as [old new improved | x_a];
                  cbn in *; [apply Hper_lift; exact Hp | exact I]. }
              { destruct Hwl_new as [v_old Hwln1]. destruct Hwln1 as [v_new Hwln2].
                destruct Hwln2 as [improved Hwln3]. destruct Hwln3 as [Hwl_eq Hwln4].
                destruct Hwln4 as [Hper_old Hper_new].
                rewrite Hwl_eq. cbn. split.
                1:{ assert (Hr_ar : uf_rel_PER V (V_map V) (V_map nat) (equiv e_u) t_v tx').
                    { apply Hper_u. apply PER_clo_base. right. unfold Relations.singleton_rel.
                      split; reflexivity. }
                    unfold uf_rel_PER in *.
                    eapply PER_clo_trans; [exact Hper_old|].
                    eapply PER_clo_trans; [exact Hr_ar|].
                    apply PER_clo_sym. exact Hper_new. }
                eapply all_wkn; [|exact Hwlok_he].
                intros ent2 _ Hp2. destruct ent2 as [old2 new2 improved2 | x_a2];
                  cbn in *; [apply Hper_lift; exact Hp2 | exact I]. } }
          1:{ rewrite <- Hpar_u. intros x_p s_p Hgs.
              specialize (Hparok_he _ _ Hgs).
              eapply all_wkn; [|exact Hparok_he].
              intros b _ Hbup.
              destruct Hbup as [bb Hbb]. destruct Hbb as [Hca Hbain].
              destruct Hca as [Hfn Hargs_ret]. destruct Hargs_ret as [Hargs Hret].
              exists bb. split.
              1:{ unfold atom_canonical_equiv. split; [exact Hfn|]. split.
                  1:{ clear -Hargs Hper_lift.
                      revert Hargs. generalize (atom_args b), (atom_args bb).
                      intros l1 l2. revert l2.
                      induction l1 as [|y ys IH']; destruct l2 as [|z zs];
                        cbn; auto; try tauto.
                      intros [Hy Hys]. split.
                      { apply Hper_lift. exact Hy. }
                      { apply IH'. exact Hys. } }
                  apply Hper_lift. exact Hret. }
              unfold atom_in_egraph. rewrite <- Hdb_u. exact Hbain. }
          rewrite <- Hdb_u. intros b Hb. specialize (Hdbkok_he _ Hb).
          destruct Hdbkok_he as [Hka Hkr]. split.
          1:{ eapply all_wkn; [|exact Hka].
              intros j _ Hj. apply Hkey_pres_he_u. exact Hj. }
          apply Hkey_pres_he_u. exact Hkr. }
        (* Construct egraph_sound_for_interpretation lang_model i_he e_u *)
        assert (Hsnd_u : egraph_sound_for_interpretation lang_model i_he e_u).
        { constructor.
          1:{ destruct Hsnd_he as [Hi_wf _ _ _]. exact Hi_wf. }
          1:{ intros y Hy. destruct Hsnd_he as [_ Hi_exact _ _].
              apply Hkey_pres_he_u. apply Hi_exact. exact Hy. }
          1:{ destruct Hsnd_he as [_ _ Hi_atom _].
              unfold atom_in_egraph. rewrite <- Hdb_u. exact Hi_atom. }
          exact Hrel_new. }
        (* Now assemble the result *)
        exists i_he.
        split.
        1:{ unfold extending_sound.
            split. 1: exact Hok_u.
            split.
            1:{ intros k v Hgv. apply Hext_he_sort. apply Hexti_sort.
                apply Hexti_tail. exact Hgv. }
            split. 1: exact Hsnd_u.
            intros k Hk. apply Hkey_pres_he_u. apply Hkeys_he.
            apply Hkeys_alloc. apply Hkeys_sort. apply Hkeys_tail. exact Hk. }
        split.
        1:{ cbn. f_equal. exact Hfst_tail. }
        (* args_in_instance via cons *)
        cbn [map snd].
        apply args_in_instance_cons.
        + (* args_in_instance for the tail: lift Hai_tail through extensions *)
          eapply args_in_instance_monotone; [|exact Hai_tail].
          intros k v Hgv. apply Hext_he_sort. apply Hexti_sort. exact Hgv.
        + (* map.get i_he x' returns Some d ≈ inl e *)
          assert (Hgx'_put : map.get (map.put i_sort x' (inl e : domain V lang_model)) x'
                            = Some (inl e)) by (rewrite map.get_put_same; reflexivity).
          apply Hexti_he in Hgx'_put.
          rewrite Hgx'_put. cbn.
          econstructor. eapply eq_term_refl; eauto with lang_core.
    Qed.

    (* =============================================================== *)
    (* Model-faithful representation (the (I)-side workhorse for the    *)
    (* source-rule soundness adapter).  See [[project-source-rule-      *)
    (* adapter]].                                                       *)
    (* =============================================================== *)

    (* [represents a eF sg e xe]: the egraph id [xe] denotes [e[/sg/]]
       under the adversary interpretation [a], witnessed by node atoms
       present in the (post-rebuild) assumption egraph [eF].  This is
       PURE / syntax-directed — the egraph appears only through
       [atom_in_egraph ... eF] — which decouples the faithful induction
       below from egraph-building and the rebuild equiv-shift.  It is
       established for [add_open]'s outputs by [add_ctx_all_roots] +
       [L_survive_canonical] (the deferred F1c kernel); here we only
       CONSUME it. *)
    Inductive represents (a : interp) (eF : instance X) (sg : subst)
      : term -> V -> Prop :=
    | rep_var x xv :
        map.get a xv = Some (inl (named_list_lookup default sg x)) ->
        represents a eF sg (var x) xv
    | rep_con n s sids xe :
        Forall2 (represents a eF sg) s sids ->
        atom_in_egraph (Build_atom n sids xe) eF ->
        represents a eF sg (con n s) xe.

    (* The faithful induction: if [a] is sound on every atom of [eF] and
       [sg] is a wf substitution of [c], then any id representing a wf
       term [e] is interpreted by [a] as a term [eq_term]-equal to
       [e[/sg/]].  Engine = the [interprets_to] inversions on
       [lang_model] (NOT the forward construction).  PROVABLE NOW (no
       deferral): the only deferred dependency is establishing
       [represents] for the real add_open outputs. *)
    (* Per-element list lookup from a successful [list_Mmap].  Stated over a
       generic sum-codomain map so the [inl] constructor is syntactic. *)
    Lemma list_Mmap_get_nth_inl (A B : Type) (a : V_map (A + B))
      (sids : list V) (ats : list A)
      : list_Mmap (map.get a) sids = Some (map inl ats) ->
        Forall2 (fun i e => map.get a i = Some (inl e)) sids ats.
    Proof.
      revert ats; induction sids as [|i sids' IH];
        intros ats Hm; cbn [list_Mmap] in Hm.
      - unfold Mret in Hm; cbn in Hm.
        safe_invert Hm.
        destruct ats; cbn in *; [constructor | discriminate].
      - unfold Mbind in Hm.
        destruct (map.get a i) as [d|] eqn:Hgi; cbn in Hm; [|discriminate].
        destruct (list_Mmap (map.get a) sids') as [ds|] eqn:Hgs; cbn in Hm;
          [|discriminate].
        destruct ats as [|e ats']; cbn in Hm; [discriminate|].
        safe_invert Hm.
        constructor; eauto.
    Qed.

    (* Sort-alignment: the wf_args sort, substituted by [sg], lands in the
       shape [eq_args] wants. *)
    Lemma faithful_sort_align (sg : subst) (c' : ctx) (s : list term) (t : sort)
      : ws_sort (map fst c') t ->
        length c' = length s ->
        t[/with_names_from c' s/][/sg/]
        = t[/with_names_from c' s[/sg/]/].
    Proof.
      intros Hws Hlen.
      rewrite with_names_from_args_subst.
      erewrite subst_assoc; eauto.
      - typeclasses eauto.
      - rewrite map_fst_with_names_from; eauto.
    Qed.

    (* The [eq_args] assembly: from the per-argument IH, the
       [represents]-witnesses, and the resolved argument domains, build
       the [eq_args] feeding [term_con_congruence]. *)
    Lemma faithful_args_eq
      (a : interp) (eF : instance X) (sg : subst) (c0 : ctx)
      (Hsound : forall al, atom_in_egraph al eF ->
                  atom_sound_for_model V V V_map lang_model a al)
      (s : list term) (c' : ctx)
      (Hwfa : wf_args l c0 s c')
      (Hwfc' : wf_ctx l c')
      (IHs : all (fun e => forall t, wf_term l c0 e t ->
                   forall xe, represents a eF sg e xe ->
                   exists e', map.get a xe = Some (inl e')
                            /\ eq_term l [] t[/sg/] e' (e[/sg/])) s)
      : forall sids, Forall2 (represents a eF sg) s sids ->
        forall ats, Forall2 (fun i e => map.get a i = Some (inl e)) sids ats ->
        eq_args l [] c' ats s[/sg/].
    Proof.
      revert Hwfc' IHs; induction Hwfa;
        intros Hwfc' IHs sids Hrep ats Hm.
      { (* nil *)
        safe_invert Hrep; safe_invert Hm.
        cbn; constructor. }
      { (* cons: s = e::s0, c' = (name,t)::c'0 *)
        safe_invert Hrep.
        rename y into i.
        match goal with
          He : represents _ _ _ e _ |- _ => rename He into Hrep_e end.
        safe_invert Hm.
        cbn in Hwfc'.
        destruct IHs as [IHe IHs0].
        safe_invert Hwfc'.
        cbn [args_subst map apply_subst].
        constructor.
        2:{ (* head eq_term *)
          specialize (IHe _ ltac:(eassumption) i Hrep_e).
          destruct IHe as (e0 & Hge0 & Heq0).
          match goal with Hgi : map.get a i = Some (inl _) |- _ =>
            rewrite Hge0 in Hgi; safe_invert Hgi end.
          (* Heq0 : eq_term l [] (t[/with_names_from c'0 s0/])[/sg/] e'0 (e[/sg/]) *)
          rewrite faithful_sort_align in Heq0;
            [ exact Heq0
            | eapply wf_sort_implies_ws; eauto with lang_core
            | eapply wf_args_length_eq; eauto ]. }
        (* the tail: recursive IH of the wf_args induction *)
        match goal with
          IH : wf_ctx l _ -> _ |- _ =>
            eapply IH; eauto end. }
    Qed.

    Lemma add_open_faithful_rep
      (a : interp) (eF : instance X) (sg : subst) (c : ctx)
      (Hctx : wf_ctx l c)
      (Hsound : forall al, atom_in_egraph al eF ->
                  atom_sound_for_model V V V_map lang_model a al)
      (Hsg : wf_subst l [] sg c)
      : forall e t, wf_term l c e t ->
          forall xe, represents a eF sg e xe ->
          exists e', map.get a xe = Some (inl e')
                   /\ eq_term l [] t[/sg/] e' (e[/sg/]).
    Proof.
      intro e; revert c Hctx Hsg.
      induction e as [x | n s IHs] using term_ind;
        intros c Hctx Hsg t Hwt xe Hrep.
      { (* var case *)
        safe_invert Hrep.
        (* the var must be in dom c (hence dom sg) for wf_term (var x) t *)
        assert (In x (map fst c)) as Hxc.
        { change (In x (map fst c)) with (ws_term (map fst c) (var x)).
          eapply wf_term_implies_ws; eauto with lang_core. }
        assert (In x (map fst sg)) as Hxin.
        { erewrite wf_subst_dom_eq by eauto. exact Hxc. }
        (* the existential witness *)
        eexists; split; [eassumption|].
        (* the looked-up element equals (var x)[/sg/] = subst_lookup sg x *)
        assert (named_list_lookup default sg x = subst_lookup sg x) as Hlk.
        { unfold subst_lookup.
          clear -Hxin V_Eqb_ok.
          induction sg as [|[y v] sg' IH]; cbn in *; [tauto|].
          eqb_case x y; eauto.
          apply IH. destruct Hxin as [Hxy|]; [congruence|auto]. }
        rewrite Hlk.
        change ((var x)[/sg/]) with (subst_lookup sg x).
        eapply eq_term_refl.
        change (subst_lookup sg x) with ((var x)[/sg/]).
        eapply wf_term_subst_monotonicity; eauto. }
      { (* con case *)
        safe_invert Hrep.
        match goal with
          Hr : Forall2 (represents _ _ _) s _ |- _ => rename Hr into Hrepargs end.
        match goal with
          Ha : atom_in_egraph _ eF |- _ => rename Ha into Hatom end.
        (* invert wf_term *)
        apply WfCutElim.invert_wf_term_con in Hwt.
        destruct Hwt as (c' & args & t' & Hin & Hwfa & Hsort).
        (* node atom sound *)
        pose proof (Hsound _ Hatom) as Hsnd.
        unfold atom_sound_for_model, Is_Some_satisfying in Hsnd.
        cbn [atom_args atom_ret atom_fn Defs.atom_args Defs.atom_ret Defs.atom_fn]
          in Hsnd.
        destruct (list_Mmap (map.get a) sids) as [arg_doms|] eqn:Hargs;
          cbn beta iota in Hsnd; [|contradiction].
        destruct (map.get a xe) as [out|] eqn:Hgxe;
          cbn beta iota in Hsnd; [|contradiction].
        change (domain V lang_model) with (term + sort)%type in Hsnd.
        cbn [interprets_to lang_model] in Hsnd.
        (* invert interprets_to (3 cases) *)
        inversion Hsnd as
          [ es ts Hwt_es Hsoeq Hargdom Houtdom
          | f0 args0 t0 Heqs Hf0 Hargdom Houtdom
          | f0 args_terms e_out t0 Heqe Hf0 Hargdom Houtdom ]; subst.
        { (* interprets_to_sort_of : n = sort_of, contradiction with Hsof *)
          exfalso.
          apply Hsof.
          eapply pair_fst_in; eauto. }
        { (* interprets_to_sort : out = inr t0, but n is a term_rule *)
          exfalso.
          apply eq_sort_wf_l in Heqs; eauto with lang_core.
          safe_invert Heqs.
          match goal with
            Hsr : In (n, sort_rule _ _) l |- _ =>
              pose proof (in_all_fresh_same _ _ _ _
                            ltac:(eauto with lang_core) Hin Hsr) as Hbad end.
          discriminate Hbad. }
        { (* interprets_to_term : out = inl e0, the real case *)
          exists e_out; split; [solve [reflexivity | exact Hgxe]|].
          (* goal: eq_term l [] t[/sg/] e_out ((con n s)[/sg/]) *)
          change ((con n s)[/sg/]) with (con n s[/sg/]).
          (* eq_args from helper *)
          assert (wf_ctx l c') as Hwfc'.
          { eapply rule_in_ctx_wf with (r:=term_rule c' args t');
              eauto; reflexivity. }
          assert (Forall2 (fun i e => map.get a i = Some (inl e)) sids args_terms)
            as Hlk.
          { eapply (list_Mmap_get_nth_inl term sort).
            change (domain V lang_model) with (term + sort)%type in Hargs.
            exact Hargs. }
          (* specialize the (c-general) term IH to the current c *)
          assert (all (fun e => forall t, wf_term l c e t ->
                        forall xe, represents a eF sg e xe ->
                        exists e', map.get a xe = Some (inl e')
                                 /\ eq_term l [] t[/sg/] e' (e[/sg/])) s) as IHs'.
          { eapply all_wkn; [| exact IHs].
            intros e' _ He'. apply He'; assumption. }
          assert (eq_args l [] c' args_terms s[/sg/]) as Heqargs.
          { exact (faithful_args_eq a eF sg c Hsound s c' Hwfa Hwfc' IHs'
                     sids Hrepargs args_terms Hlk). }
          (* congruence: con n args_terms = con n s[/sg/] at the rule's sort *)
          assert (eq_term l [] (t'[/with_names_from c' s[/sg/]/])
                    (con n args_terms) (con n s[/sg/])) as Hcong.
          { eapply term_con_congruence; eauto. }
          (* both sorts t0 and t'[/wnf.../] type (con n args_terms): they agree *)
          assert (wf_term l [] (con n args_terms) t0) as Hwf2.
          { eapply (eq_term_wf_l Hwf ltac:(constructor) Heqe). }
          assert (wf_term l [] (con n args_terms)
                    (t'[/with_names_from c' s[/sg/]/])) as Hwf1.
          { eapply (eq_term_wf_l Hwf ltac:(constructor) Hcong). }
          assert (eq_sort l [] t0 (t'[/with_names_from c' s[/sg/]/])) as Hsorteq.
          { eapply term_sorts_eq; eauto; constructor. }
          (* convert Heqe's sort to the rule sort, then chain *)
          assert (eq_term l [] (t'[/with_names_from c' s[/sg/]/])
                    e_out (con n s[/sg/])) as Hchain.
          { eapply eq_term_trans;
              [ eapply eq_term_sym;
                eapply eq_term_conv; [ exact Heqe | exact Hsorteq ]
              | exact Hcong ]. }
          (* establish t'[/with_names_from c' s/] is well-scoped sort *)
          assert (ws_sort (map fst c') t') as Hwst'.
          { eapply wf_sort_implies_ws; eauto with lang_core.
            eapply term_rule_in_sort_wf; eauto. }
          (* fix the sort to t[/sg/] *)
          eapply eq_term_conv; [exact Hchain|].
          (* goal: eq_sort l [] (t'[/with_names_from c' s[/sg/]/]) (t[/sg/]) *)
          rewrite <- faithful_sort_align by
            (first [ assumption | eapply wf_args_length_eq; eauto ]).
          (* goal: eq_sort l [] (t'[/with_names_from c' s/])[/sg/] (t[/sg/]) *)
          assert (eq_sort l c (t'[/with_names_from c' s/]) t) as Hsort'.
          { destruct Hsort as [Hsort|Hsort]; [exact Hsort|].
            subst t.
            eapply eq_sort_refl.
            eapply wf_sort_subst_monotonicity; eauto.
            - eapply term_rule_in_sort_wf; eauto.
            - eapply wf_subst_from_wf_args; eauto. }
          change (t[/sg/]) with (apply_subst sg t).
          change ((t'[/with_names_from c' s/])[/sg/])
            with (apply_subst sg (t'[/with_names_from c' s/])).
          eapply eq_sort_subst with (c':=c) (s1:=sg) (s2:=sg).
          - exact Hsort'.
          - eapply eq_subst_refl; exact Hsg.
          - exact Hctx. } }
    Qed.

    (* The sort analogue of [represents].  A sort [scon n s] is built by
       [add_open_sort] = [hash_entry n s'] with [s'] the recursive
       [add_open_term] outputs over the (term) args [s]; so a sort id [xs]
       carries one node atom [(n, sids, xs)] whose args are TERMS, each
       witnessed by the term-level [represents].  No recursion in
       [represents_sort] itself (sorts do not nest). *)
    Definition represents_sort (a : interp) (eF : instance X) (sg : subst)
      (ts : sort) (xs : V) : Prop :=
      match ts with
      | scon n s =>
          exists sids, Forall2 (represents a eF sg) s sids
                    /\ atom_in_egraph (Build_atom n sids xs) eF
      end.

    (* Sort faithful-rep — the TOP-LEVEL (I) consumer (the ctx-var sort
       slots [tx'_j] are [add_open_sort] outputs).  Mirrors
       [add_open_faithful_rep]; the real [interprets_to] case is the SORT
       one, the term case is ruled out by rule-name uniqueness; reuses
       [faithful_args_eq] / [list_Mmap_get_nth_inl] + [sort_con_congruence]. *)
    Lemma add_open_faithful_rep_sort
      (a : interp) (eF : instance X) (sg : subst) (c : ctx)
      (Hctx : wf_ctx l c)
      (Hsound : forall al, atom_in_egraph al eF ->
                  atom_sound_for_model V V V_map lang_model a al)
      (Hsg : wf_subst l [] sg c)
      : forall ts, wf_sort l c ts ->
          forall xs, represents_sort a eF sg ts xs ->
          exists t', map.get a xs = Some (inr t')
                   /\ eq_sort l [] t' (ts[/sg/]).
    Proof.
      intros ts Hws xs Hrep.
      destruct ts as [n s].
      destruct Hrep as (sids & Hrepargs & Hatom).
      (* invert wf_sort: only ctor is wf_sort_by *)
      safe_invert Hws.
      match goal with
        Hin : In (n, sort_rule ?c'0 ?args0) l |- _ =>
          rename c'0 into c'; rename args0 into args; rename Hin into Hin end.
      match goal with
        Hwa : Model.wf_args _ s c' |- _ => rename Hwa into Hwfa end.
      (* node atom sound *)
      pose proof (Hsound _ Hatom) as Hsnd.
      unfold atom_sound_for_model, Is_Some_satisfying in Hsnd.
      cbn [atom_args atom_ret atom_fn Defs.atom_args Defs.atom_ret Defs.atom_fn]
        in Hsnd.
      destruct (list_Mmap (map.get a) sids) as [arg_doms|] eqn:Hargs;
        cbn beta iota in Hsnd; [|contradiction].
      destruct (map.get a xs) as [out|] eqn:Hgxs;
        cbn beta iota in Hsnd; [|contradiction].
      change (domain V lang_model) with (term + sort)%type in Hsnd.
      cbn [interprets_to lang_model] in Hsnd.
      (* invert interprets_to (3 cases) *)
      inversion Hsnd as
        [ es t_es Hwt_es Hargdom Houtdom
        | f0 args_terms t0 Heqs Hargdom Houtdom
        | f0 args0 e_out t0 Heqe Hargdom Houtdom ]; subst.
      { (* interprets_to_sort_of : n = sort_of, contradiction with Hsof *)
        exfalso.
        apply Hsof.
        eapply pair_fst_in; eauto. }
      2:{ (* interprets_to_term : out = inl e_out, but n is a sort_rule *)
        exfalso.
        apply eq_term_wf_l in Heqe; eauto with lang_core.
        apply WfCutElim.invert_wf_term_con in Heqe.
        destruct Heqe as (c'' & args' & t'' & Hin' & _ & _).
        match goal with
          Hsr : In (_, sort_rule _ _) l |- _ =>
            pose proof (in_all_fresh_same _ _ _ _
                          ltac:(eauto with lang_core) Hsr Hin') as Hbad end.
        discriminate Hbad. }
      { (* interprets_to_sort : out = inr t0, the real case *)
        exists t0; split; [solve [reflexivity | exact Hgxs]|].
        (* goal: eq_sort l [] t0 ((scon n s)[/sg/]) *)
        change ((scon n s)[/sg/]) with (scon n s[/sg/]).
        assert (wf_ctx l c') as Hwfc'.
        { eapply rule_in_ctx_wf with (r:=sort_rule c' args);
            eauto; reflexivity. }
        assert (Forall2 (fun i e => map.get a i = Some (inl e)) sids args_terms)
          as Hlk.
        { eapply (list_Mmap_get_nth_inl term sort).
          change (domain V lang_model) with (term + sort)%type in Hargs.
          exact Hargs. }
        (* term-level faithful rep over the args *)
        assert (HP : forall e t, wf_term l c e t ->
                      forall xe, represents a eF sg e xe ->
                      exists e', map.get a xe = Some (inl e')
                               /\ eq_term l [] t[/sg/] e' (e[/sg/])).
        { intros e0 t0' Hwt0 xe0 Hrep0.
          eapply add_open_faithful_rep with (c:=c); eauto. }
        assert (all (fun e => forall t, wf_term l c e t ->
                      forall xe, represents a eF sg e xe ->
                      exists e', map.get a xe = Some (inl e')
                               /\ eq_term l [] t[/sg/] e' (e[/sg/])) s) as IHs'.
        { clear -HP. induction s as [|e0 s0 IH]; cbn; [exact I|].
          split; [ exact (HP e0) | exact IH ]. }
        assert (eq_args l [] c' args_terms s[/sg/]) as Heqargs.
        { exact (faithful_args_eq a eF sg c Hsound s c' Hwfa Hwfc' IHs'
                   sids Hrepargs args_terms Hlk). }
        (* congruence: scon n args_terms = scon n s[/sg/] *)
        assert (eq_sort l [] (scon n args_terms) (scon n s[/sg/])) as Hcong.
        { eapply sort_con_congruence; eauto. }
        (* Heqs : eq_sort l [] (scon n args_terms) t0 *)
        eapply eq_sort_trans; [ eapply eq_sort_sym; exact Heqs | exact Hcong ]. }
    Qed.

    (* =============================================================== *)
    (* Model-free skeleton of [represents] (the (P2a) connection layer).*)
    (* See [[project-source-rule-adapter]].                             *)
    (* =============================================================== *)

    (* [atom_tree eF sub e xe]: the syntax-directed, PURELY STRUCTURAL
       witness that, in egraph [eF], id [xe] is [add_open]'s output for
       term [e] under the leaf map [sub] (var x |-> [named_list_lookup
       default sub x]).  It records exactly which node atoms [add_open]
       inserts -- the egraph appears only through [atom_in_egraph].  No
       model / adversary [a] is involved.  [add_open_node_atoms]
       establishes it for real [add_open] outputs; [atom_tree_to_represents]
       upgrades it to [represents] given leaf faithfulness of [a]. *)
    Inductive atom_tree (eF : instance X) (sub : named_list V)
      : term -> V -> Prop :=
    | at_var x :
        atom_tree eF sub (var x) (named_list_lookup default sub x)
    | at_con n s sids xe :
        Forall2 (atom_tree eF sub) s sids ->
        atom_in_egraph (Build_atom n sids xe) eF ->
        atom_tree eF sub (con n s) xe.

    (* Sort skeleton: sorts do not nest, so this is a plain definition whose
       arguments are terms witnessed by the term-level [atom_tree] (mirrors
       [represents_sort]'s shape). *)
    Definition atom_tree_sort (eF : instance X) (sub : named_list V)
       (ts : sort) (xs : V) : Prop :=
      match ts with
      | scon n s =>
          exists sids, Forall2 (atom_tree eF sub) s sids
                       /\ atom_in_egraph (Build_atom n sids xs) eF
      end.

    Lemma atom_tree_db_incl (eF eF' : instance X) (sub : named_list V)
      : (forall b, atom_in_egraph b eF -> atom_in_egraph b eF') ->
        forall e xe, atom_tree eF sub e xe -> atom_tree eF' sub e xe.
    Proof.
      intros Hincl e; induction e as [x | n s IHs] using term_ind; intros xe Htree.
      - safe_invert Htree. constructor.
      - safe_invert Htree.
        match goal with
        | Htrees : Forall2 (atom_tree eF sub) s ?sids,
          Hatom : atom_in_egraph (Build_atom n ?sids xe) eF |- _ =>
            eapply at_con; [| eapply Hincl; exact Hatom];
            clear Hatom;
            revert sids Htrees IHs; induction s as [|t0 s0 IHsl]; intros sids Htrees IHs;
            [ safe_invert Htrees; constructor
            | safe_invert Htrees; destruct IHs as [IHt0 IHs0];
              constructor; [ apply IHt0; assumption | apply IHsl; assumption ] ]
        end.
    Qed.

    (* =============================================================== *)
    (* Bridge: atom_tree -> represents, given faithful leaves.          *)
    (* =============================================================== *)

    Lemma atom_tree_args_to_represents
      (a : interp) (eF : instance X) (sub : named_list V) (sg : subst) (c c' : ctx)
      (Hleaf : forall x, In x (map fst sub) ->
                 map.get a (named_list_lookup default sub x) = Some (inl (named_list_lookup default sg x)))
      (s : list term)
      (Hwfa : wf_args l c s c')
      (IHs : all (fun e => forall t, wf_term l c e t ->
                   forall xe, atom_tree eF sub e xe -> represents a eF sg e xe) s)
      : forall sids, Forall2 (atom_tree eF sub) s sids -> Forall2 (represents a eF sg) s sids.
    Proof.
      revert IHs; induction Hwfa; intros IHs sids Htrees.
      - safe_invert Htrees. constructor.
      - safe_invert Htrees.
        destruct IHs as [IHe IHs0].
        constructor.
        + eapply IHe; eauto.
        + eapply IHHwfa; eauto.
    Qed.

    Lemma atom_tree_to_represents
      (a : interp) (eF : instance X) (sub : named_list V) (sg : subst) (c : ctx)
      (Hleaf : forall x, In x (map fst sub) ->
                 map.get a (named_list_lookup default sub x) = Some (inl (named_list_lookup default sg x)))
      (Hdom : map fst c = map fst sub)
      : forall e t, wf_term l c e t -> forall xe, atom_tree eF sub e xe -> represents a eF sg e xe.
    Proof.
      intro e; induction e as [x | n s IHs] using term_ind; intros t Hwt xe Htree.
      - safe_invert Htree.
        assert (In x (map fst c)) as Hxc.
        { change (In x (map fst c)) with (ws_term (map fst c) (var x)).
          eapply wf_term_implies_ws; eauto with lang_core. }
        rewrite Hdom in Hxc.
        constructor. apply Hleaf; exact Hxc.
      - safe_invert Htree.
        apply WfCutElim.invert_wf_term_con in Hwt.
        destruct Hwt as (c'0 & args0 & t' & Hin & Hwfa & _).
        eapply rep_con; [| match goal with H : atom_in_egraph _ eF |- _ => exact H end].
        assert (IHsall : all (fun e => forall t, wf_term l c e t ->
                                forall xe, atom_tree eF sub e xe -> represents a eF sg e xe) s).
        { clear -IHs Hleaf Hdom.
          induction s as [|e0 s0 IH]; cbn; [exact I|].
          destruct IHs as [IHe0 IHs0].
          split.
          - intros t0 Hwt0 xe0 Htree0.
            eapply IHe0; eauto.
          - apply IH; exact IHs0. }
        match goal with
          Htrees : Forall2 (atom_tree eF sub) s ?sids |- _ =>
            eapply atom_tree_args_to_represents with (c:=c) (c':=c'0); eauto
        end.
    Qed.

    Lemma atom_tree_sort_to_represents_sort
      (a : interp) (eF : instance X) (sub : named_list V) (sg : subst) (c : ctx)
      (Hleaf : forall x, In x (map fst sub) ->
                 map.get a (named_list_lookup default sub x) = Some (inl (named_list_lookup default sg x)))
      (Hdom : map fst c = map fst sub)
      : forall ts, wf_sort l c ts -> forall xs, atom_tree_sort eF sub ts xs -> represents_sort a eF sg ts xs.
    Proof.
      intros [n s] Hws xs Htree.
      unfold atom_tree_sort in Htree.
      destruct Htree as (sids & Htrees & Hatom).
      unfold represents_sort.
      exists sids; split; [| exact Hatom].
      safe_invert Hws.
      match goal with
        Hin : In (n, sort_rule ?c'0 ?args0) l,
        Hwfa : Model.wf_args _ s ?c'0 |- _ =>
          eapply atom_tree_args_to_represents with (c:=c) (c':=c'0); try eassumption
      end.
      assert (HP : forall e t, wf_term l c e t ->
                    forall xe, atom_tree eF sub e xe -> represents a eF sg e xe).
      { intros; eapply atom_tree_to_represents with (c:=c); eauto. }
      clear -HP s.
      induction s as [|e0 s0 IH]; cbn; [exact I|].
      split; [exact (HP e0) | exact IH].
    Qed.

  End AddOpenSound.

  Section AddOpenRoots.
    Context (X : Type) `{analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).
    Context (with_sorts : bool).

    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie X).
    Local Notation db_inv := (db_inv V V V_map V_map V_trie X).
    Local Notation atom_in_db := (atom_in_db V V V_map V_trie X).

    (* The db invariant actually preserved through add_ctx: every atom has root
       args; only non-[sort_of] (constructor) atoms keep root rets.  The
       [sort_of]-ctx atoms' rets are the demoted [tx'] ids. *)
    Definition db_ctx_inv (e : instance X) : Prop :=
      db_inv (fun s => s <> sort_of) e.

    (* "x is a root in e's union-find" -- the inline predicate used by the
       F1c bricks (e.g. repair_each_canonicalizes). *)
    Definition is_root (e : instance X) (x : V) : Prop :=
      map.get (parent (Defs.equiv e)) x = Some x.

    (* db monotonicity: every db atom of e_in survives to e_out. *)
    Definition db_incl (e_in e_out : instance X) : Prop :=
      forall a, atom_in_db a (Defs.db e_in) -> atom_in_db a (Defs.db e_out).

    (* root-set monotonicity. *)
    Definition roots_mono (e_in e_out : instance X) : Prop :=
      forall z, is_root e_in z -> is_root e_out z.

    (* The structural envelope, parallel to extending_sound but model-free. *)
    Definition roots_env (e_in e_out : instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_out) roots)
      /\ db_ctx_inv e_out
      /\ db_incl e_in e_out
      /\ roots_mono e_in e_out.

    Lemma roots_env_refl (e : instance X)
      : (exists roots, union_find_ok lt (Defs.equiv e) roots) ->
        db_ctx_inv e ->
        roots_env e e.
    Proof.
      intros Huf Hdb. unfold roots_env, db_incl, roots_mono.
      split; [exact Huf|]. split; [exact Hdb|]. split; auto.
    Qed.

    Lemma roots_env_trans (e1 e2 e3 : instance X)
      : roots_env e1 e2 -> roots_env e2 e3 -> roots_env e1 e3.
    Proof.
      unfold roots_env, db_incl, roots_mono.
      intros (Huf2 & Hdb2 & Hin2 & Hr2) (Huf3 & Hdb3 & Hin3 & Hr3).
      split; [exact Huf3|]. split; [exact Hdb3|].
      split; auto.
    Qed.

    Lemma is_root_has_key (e : instance X) x
      : is_root e x -> Sep.has_key x (parent (Defs.equiv e)).
    Proof.
      unfold is_root, Sep.has_key. intro Hr. rewrite Hr. exact I.
    Qed.

    Definition open_roots_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      roots_env e_in (snd res)
      /\ is_root (snd res) (fst res).

    Definition open_roots_args_post (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      roots_env e_in (snd res)
      /\ all (is_root (snd res)) (fst res).

    Definition open_roots_sort_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      roots_env e_in (snd res)
      /\ is_root (snd res) (fst res).

    (* Mutual term/args structural induction, mirroring add_open_sound
       but specialized to with_sorts=with_ctx_sorts=false (so add_open_term'
       is pure list_Mmap + hash_entry, never calls the inner sort fn nor
       update_entry -> no inner hyp needed). *)
    Lemma add_open_all_roots (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      c (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t ->
                     forall r, map fst c = map fst r ->
                       vc (add_open_term' succ sort_of l false false
                                          add_open_sort_inner r e)
                          (open_roots_post r))
        /\ (forall args c', wf_args l1 c args c' ->
                     forall r, map fst c = map fst r ->
                       vc (list_Mmap (add_open_term' succ sort_of l false false
                                                      add_open_sort_inner r) args)
                          (open_roots_args_post r)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l false false
                                     add_open_sort_inner r e)
                     (open_roots_post r))
               (fun args c' => forall r, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l false false
                                                add_open_sort_inner r) args)
                     (open_roots_args_post r))).
      - (* con case *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_roots_post.
        intros Huf Hdbr Hsub.
        unfold open_roots_args_post in Hpost_args.
        specialize (Hpost_args Huf Hdbr Hsub).
        destruct Hpost_args as [Henv_args Hroots_aout].
        pose proof Henv_args as Henv_args_save.
        destruct Henv_args as (Huf_inner & Hdbr_inner & Hincl_inner & Hmono_inner).
        assert (Hkeys : forall x, In x a_out ->
                          Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. apply is_root_has_key.
          exact (in_all _ _ _ Hroots_aout Hx). }
        assert (Hname_sof : name <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hrule_in. }
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhe.
        unfold vc in Hhe.
        specialize (Hhe e_inner Huf_inner Hdbr_inner Hkeys).
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe.
        destruct Hhe as (Huf_f & Hdbr_f & Hincl_f & Hmono_f & Hres_f).
        cbn [Mret StateMonad.state_monad fst snd].
        split.
        + eapply roots_env_trans; [exact Henv_args_save|].
          unfold roots_env, db_incl, roots_mono.
          split; [exact Huf_f|]. split; [exact Hdbr_f|]. split; auto.
        + apply Hres_f. exact Hname_sof.
      - (* var case *)
        intros n t_var Hin_var r Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_roots_post.
        intros Huf Hdbr Hsub.
        split; [apply roots_env_refl; auto|].
        assert (Hafc : all_fresh c) by basic_core_crush.
        assert (Hafr : all_fresh r).
        { apply NoDup_fresh. rewrite <- Hmaps. apply NoDup_fresh; exact Hafc. }
        assert (Hex_x : exists x_n, In (n, x_n) r).
        { apply pair_fst_in_exists. rewrite <- Hmaps. eapply pair_fst_in; exact Hin_var. }
        destruct Hex_x as [x_n Hin_xn].
        assert (Hlk : named_list_lookup default r n = x_n).
        { clear -V_Eqb_ok Hafr Hin_xn.
          induction r as [|[m v_m] r' IH]; cbn in *; [tauto|].
          destruct Hafr as [Hfr Hafr'].
          destruct Hin_xn as [Heq|Hin_xn'].
          - inversion Heq; subst.
            eqb_case n n; congruence.
          - eqb_case n m.
            + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_xn'.
            + apply IH; auto. }
        cbn [fst]. rewrite Hlk.
        exact (in_all _ _ _ Hsub Hin_xn).
      - (* eq_sort conversion *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r Hmaps.
        apply IH_term; assumption.
      - (* nil args *)
        intros r Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_roots_args_post. intros Huf Hdbr Hsub.
        split; [apply roots_env_refl; auto | cbn; exact I].
      - (* cons args *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_roots_args_post.
        intros Huf Hdbr Hsub.
        specialize (IH_term r Hmaps).
        unfold vc, open_roots_post in IH_term.
        specialize (IH_term e_in Huf Hdbr Hsub).
        destruct (add_open_term' succ sort_of l false false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        cbn [fst snd] in IH_term.
        destruct IH_term as [Henv_head Hroot_head].
        pose proof Henv_head as Henv_head_save.
        destruct Henv_head as (Huf_head & Hdbr_head & Hincl_head & Hmono_head).
        specialize (IH_args r Hmaps).
        unfold vc, open_roots_args_post in IH_args.
        assert (Hsub_head : all (fun p => is_root e_after_head (snd p)) r).
        { eapply all_wkn; [|exact Hsub].
          intros x Hx Hr. apply Hmono_head. exact Hr. }
        specialize (IH_args e_after_head Huf_head Hdbr_head Hsub_head).
        destruct (list_Mmap
                    (add_open_term' succ sort_of l false false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd] in IH_args.
        destruct IH_args as [Henv_tail Hroots_tail].
        pose proof Henv_tail as Henv_tail_save.
        destruct Henv_tail as (Huf_tail & Hdbr_tail & Hincl_tail & Hmono_tail).
        split.
        + eapply roots_env_trans; eauto.
        + cbn [all]. split.
          * apply Hmono_tail. exact Hroot_head.
          * exact Hroots_tail.
    Qed.

    Lemma add_open_sort'_all_roots l1 c r t fuel
      : wf_lang l1 ->
        length l1 < fuel ->
        incl l1 l ->
        wf_ctx l1 c ->
        wf_sort l1 c t ->
        map fst c = map fst r ->
        vc (add_open_sort' succ sort_of l false false fuel r t)
           (open_roots_sort_post r).
    Proof.
      revert l1 c r t.
      induction fuel; intros l1 c r t Hwfl1 Hflen Hincl Hctx Hsort Hmaps.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { apply (proj2 (add_open_all_roots l1
                          (add_open_sort' succ sort_of l false false fuel)
                          Hwfl1 Hincl c Hctx)
                  _ _ Hwfargs r Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_roots_sort_post.
        intros Huf Hdbr Hsub.
        unfold open_roots_args_post in Hpost_args.
        specialize (Hpost_args Huf Hdbr Hsub).
        destruct Hpost_args as [Henv_args Hroots_aout].
        pose proof Henv_args as Henv_args_save.
        destruct Henv_args as (Huf_inner & Hdbr_inner & Hincl_inner & Hmono_inner).
        assert (Hkeys : forall x, In x a_out ->
                          Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. apply is_root_has_key.
          exact (in_all _ _ _ Hroots_aout Hx). }
        assert (Hname_sof : n <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hrule. }
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhe.
        unfold vc in Hhe.
        specialize (Hhe e_inner Huf_inner Hdbr_inner Hkeys).
        destruct (hash_entry succ n a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe.
        destruct Hhe as (Huf_f & Hdbr_f & Hincl_f & Hmono_f & Hres_f).
        cbn [Mret StateMonad.state_monad fst snd].
        split.
        + eapply roots_env_trans; [exact Henv_args_save|].
          unfold roots_env, db_incl, roots_mono.
          split; [exact Huf_f|]. split; [exact Hdbr_f|]. split; auto.
        + apply Hres_f. exact Hname_sof.
    Qed.

    Lemma add_open_sort_all_roots c r t
      : wf_ctx l c ->
        wf_sort l c t ->
        map fst c = map fst r ->
        vc (add_open_sort succ sort_of l false false r t)
           (open_roots_sort_post r).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_all_roots; try eassumption; eauto with utils.
    Qed.

    (* ----- egraph_ok / has_key family (simpler post, decoupled from roots) ----- *)

    Definition open_egraph_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      egraph_ok e_in ->
      all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) sub ->
      egraph_ok (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ Sep.has_key (fst res) (parent (Defs.equiv (snd res))).

    Definition open_egraph_args_post (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      egraph_ok e_in ->
      all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) sub ->
      egraph_ok (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ all (fun x => Sep.has_key x (parent (Defs.equiv (snd res)))) (fst res).

    Definition open_egraph_sort_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop := open_egraph_post sub e_in res.

    (* ------------------------------------------------------------------ *)
    (* Worklist-frame family: add_open does not push to worklist and       *)
    (* preserves+extends analyses_cover.                                   *)
    (* ------------------------------------------------------------------ *)

    (* analyses_cover: every node that is a key in the parent map has an
       analysis entry. *)
    Definition analyses_cover (e : instance X) : Prop :=
      forall z, Sep.has_key z (parent (Defs.equiv e)) ->
                exists a, map.get (Defs.analyses e) z = Some a.

    Definition open_wlframe_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      egraph_ok e_in ->
      analyses_cover e_in ->
      all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) sub ->
        Defs.worklist (snd res) = Defs.worklist e_in
      /\ egraph_ok (snd res)
      /\ analyses_cover (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ Sep.has_key (fst res) (parent (Defs.equiv (snd res))).

    Definition open_wlframe_args_post (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      egraph_ok e_in ->
      analyses_cover e_in ->
      all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) sub ->
        Defs.worklist (snd res) = Defs.worklist e_in
      /\ egraph_ok (snd res)
      /\ analyses_cover (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ all (fun x => Sep.has_key x (parent (Defs.equiv (snd res)))) (fst res).

    Definition open_wlframe_sort_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop := open_wlframe_post sub e_in res.

    Lemma add_open_egraph_ok (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      c (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t ->
                     forall r, map fst c = map fst r ->
                       vc (add_open_term' succ sort_of l false false
                                          add_open_sort_inner r e)
                          (open_egraph_post r))
        /\ (forall args c', wf_args l1 c args c' ->
                     forall r, map fst c = map fst r ->
                       vc (list_Mmap (add_open_term' succ sort_of l false false
                                                      add_open_sort_inner r) args)
                          (open_egraph_args_post r)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l false false
                                     add_open_sort_inner r e)
                     (open_egraph_post r))
               (fun args c' => forall r, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l false false
                                                add_open_sort_inner r) args)
                     (open_egraph_args_post r))).
      - (* con case *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_egraph_post.
        intros Hok Hsub.
        unfold open_egraph_args_post in Hpost_args.
        specialize (Hpost_args Hok Hsub).
        destruct Hpost_args as (Hok_args & Hmono_args & Hkeys_aout).
        assert (Hkeys : forall x, In x a_out ->
                          Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. exact (in_all _ _ _ Hkeys_aout Hx). }
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhe.
        unfold vc in Hhe.
        specialize (Hhe e_inner Hok_args Hkeys).
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe.
        destruct Hhe as (Hok_f & Hmono_f & Hres_f).
        cbn [Mret StateMonad.state_monad fst snd].
        split; [exact Hok_f|]. split; [|exact Hres_f].
        intros x Hx. apply Hmono_f. apply Hmono_args. exact Hx.
      - (* var case *)
        intros n t_var Hin_var r Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_egraph_post.
        intros Hok Hsub.
        split; [exact Hok|]. split; [auto|].
        assert (Hafc : all_fresh c) by basic_core_crush.
        assert (Hafr : all_fresh r).
        { apply NoDup_fresh. rewrite <- Hmaps. apply NoDup_fresh; exact Hafc. }
        assert (Hex_x : exists x_n, In (n, x_n) r).
        { apply pair_fst_in_exists. rewrite <- Hmaps. eapply pair_fst_in; exact Hin_var. }
        destruct Hex_x as [x_n Hin_xn].
        assert (Hlk : named_list_lookup default r n = x_n).
        { clear -V_Eqb_ok Hafr Hin_xn.
          induction r as [|[m v_m] r' IH]; cbn in *; [tauto|].
          destruct Hafr as [Hfr Hafr'].
          destruct Hin_xn as [Heq|Hin_xn'].
          - inversion Heq; subst.
            eqb_case n n; congruence.
          - eqb_case n m.
            + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_xn'.
            + apply IH; auto. }
        cbn [fst]. rewrite Hlk.
        exact (in_all _ _ _ Hsub Hin_xn).
      - (* eq_sort conversion *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r Hmaps.
        apply IH_term; assumption.
      - (* nil args *)
        intros r Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_egraph_args_post. intros e_in Hok Hsub.
        split; [exact Hok|]. split; [auto | cbn; exact I].
      - (* cons args *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_egraph_args_post.
        intros Hok Hsub.
        specialize (IH_term r Hmaps).
        unfold vc, open_egraph_post in IH_term.
        specialize (IH_term e_in Hok Hsub).
        destruct (add_open_term' succ sort_of l false false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        cbn [fst snd] in IH_term.
        destruct IH_term as (Hok_head & Hmono_head & Hkey_head).
        specialize (IH_args r Hmaps).
        unfold vc, open_egraph_args_post in IH_args.
        assert (Hsub_head : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_after_head))) r).
        { eapply all_wkn; [|exact Hsub].
          intros x Hx Hk. apply Hmono_head. exact Hk. }
        specialize (IH_args e_after_head Hok_head Hsub_head).
        destruct (list_Mmap
                    (add_open_term' succ sort_of l false false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd] in IH_args.
        destruct IH_args as (Hok_tail & Hmono_tail & Hkeys_tail).
        split; [exact Hok_tail|]. split.
        + intros x Hx. apply Hmono_tail. apply Hmono_head. exact Hx.
        + cbn [all]. split.
          * apply Hmono_tail. exact Hkey_head.
          * exact Hkeys_tail.
    Qed.

    Lemma add_open_sort'_egraph_ok l1 c r t fuel
      : wf_lang l1 ->
        length l1 < fuel ->
        incl l1 l ->
        wf_ctx l1 c ->
        wf_sort l1 c t ->
        map fst c = map fst r ->
        vc (add_open_sort' succ sort_of l false false fuel r t)
           (open_egraph_sort_post r).
    Proof.
      revert l1 c r t.
      induction fuel; intros l1 c r t Hwfl1 Hflen Hincl Hctx Hsort Hmaps.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { apply (proj2 (add_open_egraph_ok l1
                          (add_open_sort' succ sort_of l false false fuel)
                          Hwfl1 Hincl c Hctx)
                  _ _ Hwfargs r Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_egraph_sort_post, open_egraph_post.
        intros Hok Hsub.
        unfold open_egraph_args_post in Hpost_args.
        specialize (Hpost_args Hok Hsub).
        destruct Hpost_args as (Hok_args & Hmono_args & Hkeys_aout).
        assert (Hkeys : forall x, In x a_out ->
                          Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. exact (in_all _ _ _ Hkeys_aout Hx). }
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhe.
        unfold vc in Hhe.
        specialize (Hhe e_inner Hok_args Hkeys).
        destruct (hash_entry succ n a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe.
        destruct Hhe as (Hok_f & Hmono_f & Hres_f).
        cbn [Mret StateMonad.state_monad fst snd].
        split; [exact Hok_f|]. split; [|exact Hres_f].
        intros x Hx. apply Hmono_f. apply Hmono_args. exact Hx.
    Qed.

    Lemma add_open_sort_egraph_ok c r t
      : wf_ctx l c ->
        wf_sort l c t ->
        map fst c = map fst r ->
        vc (add_open_sort succ sort_of l false false r t)
           (open_egraph_sort_post r).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_egraph_ok; try eassumption; eauto with utils.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* parents-frame family: add_open preserves parents at any key that   *)
    (* was already a key in the input and is NOT a root in the output.     *)
    (* ------------------------------------------------------------------ *)

    (* Rich combined postcondition: egraph_ok + roots_env + has_key_mono +
       all_keys_aout + parents_frame.  The IH carries all of these so that
       in the con/sort' cases the vc_bind second goal has enough to work
       with (paralleling how open_egraph_args_post carries egraph_ok). *)
    Definition open_parents_frame_args_post (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      egraph_ok e_in ->
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      egraph_ok (snd res)
      /\ (exists roots, union_find_ok lt (Defs.equiv (snd res)) roots)
      /\ db_ctx_inv (snd res)
      /\ roots_mono e_in (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ all (is_root (snd res)) (fst res)
      /\ (forall y, Sep.has_key y (parent (Defs.equiv e_in)) ->
                    ~ is_root (snd res) y ->
                    map.get (Defs.parents (snd res)) y = map.get (Defs.parents e_in) y).

    (* External postcondition for terms: just the parents_frame part. *)
    Definition open_parents_frame_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      egraph_ok e_in ->
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      forall y, Sep.has_key y (parent (Defs.equiv e_in)) ->
                ~ is_root (snd res) y ->
        map.get (Defs.parents (snd res)) y = map.get (Defs.parents e_in) y.

    Definition open_parents_frame_sort_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop := open_parents_frame_post sub e_in res.

    (* Internal rich args post with all facts — used in Layer 1. *)
    Definition open_parents_frame_args_post_rich (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop := open_parents_frame_args_post sub e_in res.

    (* Layer 1: mutual induction. The args branch returns the rich post;
       the term branch returns only the parents_frame (sufficient for Layer 2). *)
    Lemma add_open_parents_frame (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      c (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t -> forall r, map fst c = map fst r ->
           vc (add_open_term' succ sort_of l false false add_open_sort_inner r e)
              (open_parents_frame_post r))
        /\ (forall args c', wf_args l1 c args c' -> forall r, map fst c = map fst r ->
           vc (list_Mmap (add_open_term' succ sort_of l false false add_open_sort_inner r) args)
              (open_parents_frame_args_post r)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l false false
                                     add_open_sort_inner r e)
                     (open_parents_frame_post r))
               (fun args c' => forall r, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l false false
                                                add_open_sort_inner r) args)
                     (open_parents_frame_args_post r))).
      - (* con case *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_parents_frame_post.
        intros Hok Huf Hdbi Hsub y Hy_key Hy_nonroot.
        (* Unpack the rich args post *)
        unfold open_parents_frame_args_post in Hpost_args.
        specialize (Hpost_args Hok Huf Hdbi Hsub).
        destruct Hpost_args as
          (Hok_inner & Huf_inner & Hdbi_inner & Hmono_roots & Hmono_kf
           & Hroots_aout & Hpf_inner).
        assert (Hkeys_aout : forall x, In x a_out -> Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. apply is_root_has_key. exact (in_all _ _ _ Hroots_aout Hx). }
        assert (Hname_sof : name <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hrule_in. }
        (* hash_entry_all_roots for roots_mono e_inner e_he *)
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhe_roots.
        unfold vc in Hhe_roots.
        specialize (Hhe_roots e_inner).
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe_roots, Hy_nonroot |- *.
        specialize (Hhe_roots Huf_inner Hdbi_inner Hkeys_aout).
        destruct Hhe_roots as (_ & _ & _ & Hmono_roots_he & _).
        (* hash_entry_parents_frame: parents e_he y = parents e_inner y *)
        pose proof (@hash_entry_parents_frame V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map V_map_ok V_trie X _
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhpf.
        unfold vc in Hhpf.
        specialize (Hhpf e_inner).
        rewrite Heqhe in Hhpf. cbn [fst snd] in Hhpf.
        assert (Hy_key_inner : Sep.has_key y (parent (Defs.equiv e_inner))).
        { apply Hmono_kf. exact Hy_key. }
        assert (Hy_nonroot_inner : ~ is_root e_inner y).
        { intro Hroot. apply Hy_nonroot.
          unfold is_root in *. apply Hmono_roots_he. exact Hroot. }
        assert (Hpar_he_inner : map.get (Defs.parents e_he) y = map.get (Defs.parents e_inner) y).
        { apply Hhpf.
          - exact Huf_inner.
          - exact Hkeys_aout.
          - exact Hy_key_inner.
          - unfold is_root in Hy_nonroot. exact Hy_nonroot. }
        (* parents_frame from e_inner to e_pre *)
        specialize (Hpf_inner y Hy_key Hy_nonroot_inner).
        cbn [snd] in Hpf_inner.
        rewrite Hpar_he_inner. exact Hpf_inner.
      - (* var case *)
        intros n t_var Hin_var r Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_parents_frame_post.
        intros Hok Huf Hdbi Hsub y Hy_key Hy_nonroot.
        reflexivity.
      - (* eq_sort conversion *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r Hmaps.
        apply IH_term; assumption.
      - (* nil args *)
        intros r Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_parents_frame_args_post.
        intros e_in Hok Huf Hdbi Hsub.
        cbn [fst snd].
        split; [exact Hok|].
        split; [exact Huf|].
        split; [exact Hdbi|].
        split; [unfold roots_mono; intros z Hz; exact Hz|].
        split; [auto|].
        split; [cbn; exact I|].
        intros y Hy_key Hy_nonroot. reflexivity.
      - (* cons args *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_parents_frame_args_post.
        intros Hok Huf Hdbi Hsub.
        specialize (IH_term r Hmaps).
        specialize (IH_args r Hmaps).
        destruct (add_open_term' succ sort_of l false false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        destruct (list_Mmap
                    (add_open_term' succ sort_of l false false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd].
        (* Get structural facts for the head step from the proven lemmas *)
        assert (Hhead_roots : open_roots_post r e_in (v_head, e_after_head)).
        { pose proof (proj1 (add_open_all_roots l1 add_open_sort_inner
                              Hwf1 Hl1 c Hctx) _ _ Hwft r Hmaps) as Hvc.
          unfold vc in Hvc. specialize (Hvc e_in). rewrite Heq1 in Hvc. exact Hvc. }
        unfold open_roots_post in Hhead_roots.
        specialize (Hhead_roots Huf Hdbi Hsub).
        destruct Hhead_roots as (Henv_head & Hroot_head).
        destruct Henv_head as (Huf_head & Hdbi_head & _ & Hmono_roots_head).
        assert (Hhead_ok : open_egraph_post r e_in (v_head, e_after_head)).
        { pose proof (proj1 (add_open_egraph_ok l1 add_open_sort_inner
                              Hwf1 Hl1 c Hctx) _ _ Hwft r Hmaps) as Hvc.
          unfold vc in Hvc. specialize (Hvc e_in). rewrite Heq1 in Hvc. exact Hvc. }
        unfold open_egraph_post in Hhead_ok.
        assert (Hsub_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) r).
        { eapply all_wkn; [|exact Hsub].
          intros x Hx Hr. apply is_root_has_key. exact Hr. }
        specialize (Hhead_ok Hok Hsub_keys).
        destruct Hhead_ok as (Hok_head & Hmono_kf_head & Hkey_vhead).
        (* Lift sub to e_after_head *)
        assert (Hsub_head : all (fun p => is_root e_after_head (snd p)) r).
        { eapply all_wkn; [|exact Hsub].
          intros x Hx Hr. apply Hmono_roots_head. exact Hr. }
        (* Get structural facts for the tail step *)
        assert (Htail_roots : open_roots_args_post r e_after_head (v_tail, e_final)).
        { pose proof (proj2 (add_open_all_roots l1 add_open_sort_inner
                              Hwf1 Hl1 c Hctx) _ _ Hwf_args r Hmaps) as Hvc.
          unfold vc in Hvc. specialize (Hvc e_after_head). rewrite Heq2 in Hvc. exact Hvc. }
        unfold open_roots_args_post in Htail_roots.
        specialize (Htail_roots Huf_head Hdbi_head Hsub_head).
        destruct Htail_roots as (Henv_tail & Hroots_tail).
        destruct Henv_tail as (Huf_tail & Hdbi_tail & _ & Hmono_roots_tail).
        assert (Htail_ok : open_egraph_args_post r e_after_head (v_tail, e_final)).
        { pose proof (proj2 (add_open_egraph_ok l1 add_open_sort_inner
                              Hwf1 Hl1 c Hctx) _ _ Hwf_args r Hmaps) as Hvc.
          unfold vc in Hvc. specialize (Hvc e_after_head). rewrite Heq2 in Hvc. exact Hvc. }
        unfold open_egraph_args_post in Htail_ok.
        assert (Hsub_keys_head : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_after_head))) r).
        { eapply all_wkn; [|exact Hsub_head].
          intros x Hx Hr. apply is_root_has_key. exact Hr. }
        specialize (Htail_ok Hok_head Hsub_keys_head).
        destruct Htail_ok as (Hok_tail & Hmono_kf_tail & Hkeys_tail).
        (* Get head parents-frame IH *)
        assert (Hhead_pf : open_parents_frame_post r e_in (v_head, e_after_head)).
        { unfold vc in IH_term. specialize (IH_term e_in). rewrite Heq1 in IH_term. exact IH_term. }
        unfold open_parents_frame_post in Hhead_pf.
        (* Get tail parents-frame IH (rich) *)
        assert (Htail_pf : open_parents_frame_args_post r e_after_head (v_tail, e_final)).
        { unfold vc in IH_args. specialize (IH_args e_after_head). rewrite Heq2 in IH_args. exact IH_args. }
        unfold open_parents_frame_args_post in Htail_pf.
        specialize (Htail_pf Hok_head Huf_head Hdbi_head Hsub_head).
        destruct Htail_pf as
          (Hok_final & Huf_final & Hdbi_final & Hmono_roots_final
           & Hmono_kf_final & Hroots_final & Hpf_tail).
        (* Reduce snd/fst in all relevant hyps and the goal *)
        cbn [fst snd] in Hok_final, Huf_final, Hdbi_final, Hmono_roots_final,
          Hmono_kf_final, Hroots_final, Hpf_tail, Hhead_pf |- *.
        (* Now assemble the output: 7 conjuncts *)
        split; [exact Hok_final|].
        split; [exact Huf_final|].
        split; [exact Hdbi_final|].
        split.
        { unfold roots_mono. intros z Hz.
          apply Hmono_roots_final. apply Hmono_roots_head. exact Hz. }
        split.
        { intros x Hx. apply Hmono_kf_final. apply Hmono_kf_head. exact Hx. }
        split.
        { cbn [all]. split.
          - apply Hmono_roots_final. exact Hroot_head.
          - exact Hroots_final. }
        { intros y Hy_key Hy_nonroot.
          (* y non-root in e_final, need: parents e_final y = parents e_in y *)
          (* Chain: parents e_final y = parents e_after_head y = parents e_in y *)
          assert (Hy_key_head : Sep.has_key y (parent (Defs.equiv e_after_head))).
          { apply Hmono_kf_head. exact Hy_key. }
          assert (Hy_nonroot_head : ~ is_root e_after_head y).
          { intro Hroot. apply Hy_nonroot.
            unfold is_root in *. apply Hmono_roots_final. exact Hroot. }
          specialize (Hpf_tail y Hy_key_head Hy_nonroot).
          specialize (Hhead_pf Hok Huf Hdbi Hsub y Hy_key Hy_nonroot_head).
          rewrite Hpf_tail. exact Hhead_pf. }
    Qed.

    Lemma add_open_sort'_parents_frame l1 c r t fuel
      : wf_lang l1 -> length l1 < fuel -> incl l1 l -> wf_ctx l1 c -> wf_sort l1 c t ->
        map fst c = map fst r ->
        vc (add_open_sort' succ sort_of l false false fuel r t)
           (open_parents_frame_sort_post r).
    Proof.
      revert l1 c r t.
      induction fuel; intros l1 c r t Hwfl1 Hflen Hincl Hctx Hsort Hmaps.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { apply (proj2 (add_open_parents_frame l1
                          (add_open_sort' succ sort_of l false false fuel)
                          Hwfl1 Hincl c Hctx)
                  _ _ Hwfargs r Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_parents_frame_sort_post, open_parents_frame_post.
        intros Hok Huf Hdbi Hsub y Hy_key Hy_nonroot.
        (* Unpack the rich args post *)
        unfold open_parents_frame_args_post in Hpost_args.
        specialize (Hpost_args Hok Huf Hdbi Hsub).
        destruct Hpost_args as
          (Hok_inner & Huf_inner & Hdbi_inner & Hmono_roots & Hmono_kf
           & Hroots_aout & Hpf_inner).
        assert (Hkeys_aout : forall x, In x a_out -> Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. apply is_root_has_key. exact (in_all _ _ _ Hroots_aout Hx). }
        assert (Hname_sof : n <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hrule. }
        (* hash_entry_all_roots for roots_mono e_inner e_he *)
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhe_roots.
        unfold vc in Hhe_roots.
        specialize (Hhe_roots e_inner).
        destruct (hash_entry succ n a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe_roots, Hy_nonroot |- *.
        specialize (Hhe_roots Huf_inner Hdbi_inner Hkeys_aout).
        destruct Hhe_roots as (_ & _ & _ & Hmono_roots_he & _).
        (* hash_entry_parents_frame: parents e_he y = parents e_inner y *)
        pose proof (@hash_entry_parents_frame V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map V_map_ok V_trie X _
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhpf.
        unfold vc in Hhpf.
        specialize (Hhpf e_inner).
        rewrite Heqhe in Hhpf. cbn [fst snd] in Hhpf.
        assert (Hy_key_inner : Sep.has_key y (parent (Defs.equiv e_inner))).
        { apply Hmono_kf. exact Hy_key. }
        assert (Hy_nonroot_inner : ~ is_root e_inner y).
        { intro Hroot. apply Hy_nonroot.
          unfold is_root in *. apply Hmono_roots_he. exact Hroot. }
        assert (Hpar_he_inner : map.get (Defs.parents e_he) y = map.get (Defs.parents e_inner) y).
        { apply Hhpf.
          - exact Huf_inner.
          - exact Hkeys_aout.
          - exact Hy_key_inner.
          - unfold is_root in Hy_nonroot. exact Hy_nonroot. }
        specialize (Hpf_inner y Hy_key Hy_nonroot_inner).
        cbn [snd] in Hpf_inner.
        rewrite Hpar_he_inner. exact Hpf_inner.
    Qed.

    Lemma add_open_sort_parents_frame c r t
      : wf_ctx l c -> wf_sort l c t -> map fst c = map fst r ->
        vc (add_open_sort succ sort_of l false false r t)
           (open_parents_frame_sort_post r).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_parents_frame; try eassumption; eauto with utils.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* Worklist-frame lemmas                                               *)
    (* ------------------------------------------------------------------ *)

    (* Helper: get_analyses is a pure read when every arg in the list has an analysis. *)
    Lemma get_analyses_stable_per_arg args (e : instance X) :
      (forall x, In x args -> exists a, map.get (Defs.analyses e) x = Some a) ->
      exists anas, get_analyses V V V_map V_map V_trie X args e = (anas, e).
    Proof.
      unfold get_analyses.
      induction args as [|x xs IH]; intros Hana.
      - cbn [list_Mmap Mret StateMonad.state_monad fst snd]. exists []. reflexivity.
      - assert (Hkx : exists a, map.get (Defs.analyses e) x = Some a).
        { apply Hana. left. reflexivity. }
        assert (Hana' : forall y, In y xs -> exists a, map.get (Defs.analyses e) y = Some a).
        { intros y Hy. apply Hana. right. exact Hy. }
        destruct Hkx as [ax Hax].
        destruct (IH Hana') as [anas IHe].
        (* Unfold get_analysis x e → (ax, e) *)
        assert (Hga_x : get_analysis V V V_map V_map V_trie X x e = (ax, e)).
        { unfold get_analysis. rewrite Hax. reflexivity. }
        (* Unfold list_Mmap and use get_analysis result + IHe *)
        cbn [list_Mmap Mbind StateMonad.state_monad].
        rewrite Hga_x.
        cbn [fst snd].
        rewrite IHe.
        cbn [fst snd].
        exists (ax :: anas). reflexivity.
    Qed.

    (* Helper: alloc parent equality. After alloc e_find = (r_new, e_alloc),
       parent e_alloc.equiv = map.put (parent e_find.equiv) r_new r_new. *)
    Lemma alloc_parent_eq_put (e_find : instance X) r_new e_alloc :
      Defs.alloc V succ V V_map V_map V_trie X e_find = (r_new, e_alloc) ->
      forall z, z <> r_new ->
      map.get (parent (Defs.equiv e_alloc)) z = map.get (parent (Defs.equiv e_find)) z.
    Proof.
      intros Halloc_eq z Hne.
      unfold Defs.alloc in Halloc_eq.
      destruct (UnionFind.alloc V _ _ succ (Defs.equiv e_find)) as [uf' x_f] eqn:Huf_a.
      injection Halloc_eq as <- <-.
      cbn [Defs.equiv].
      unfold UnionFind.alloc in Huf_a.
      destruct (Defs.equiv e_find) as [ra pa mr l'] eqn:Heq_find.
      cbn [UnionFind.parent] in *.
      injection Huf_a as <- <-.
      cbn [UnionFind.parent].
      rewrite map.get_put_diff by exact Hne. reflexivity.
    Qed.

    (* hash_entry worklist frame: worklist and analyses_cover both preserved/extended. *)
    Lemma hash_entry_wl_frame f args (e : instance X) :
      egraph_ok e ->
      analyses_cover e ->
      (forall x, In x args -> Sep.has_key x (parent (Defs.equiv e))) ->
      let '(_, e') := hash_entry succ f args e in
      Defs.worklist e' = Defs.worklist e /\ analyses_cover e'.
    Proof.
      intros Hok Hcov Hkeys.
      unfold hash_entry.
      cbn [Mbind StateMonad.state_monad].
      (* Step 1: list_Mmap find args e → (args', e_find) *)
      assert (Huf_ex : exists l0, union_find_ok lt (Defs.equiv e) l0).
      { destruct Hok as [Huf_ok _ _ _]. exact Huf_ok. }
      assert (Hkeys_all : all (fun i => Sep.has_key i (parent (Defs.equiv e))) args).
      { clear -Hkeys.
        induction args as [|x xs IH]; cbn; [exact I|].
        split; [apply Hkeys; left; reflexivity
               | apply IH; intros y Hy; apply Hkeys; right; exact Hy]. }
      pose proof (@list_Mmap_find_preserves_fields_strong V V_Eqb V_Eqb_ok lt succ V_default
                    V V_map V_map V_map_ok V_trie X args) as Hfp_vc.
      unfold vc in Hfp_vc. specialize (Hfp_vc e).
      destruct (list_Mmap find args e)
        as [args' e_find] eqn:Hfind_eq.
      cbn [fst snd] in Hfp_vc.
      specialize (Hfp_vc Huf_ex Hkeys_all).
      destruct Hfp_vc as (Huf_find & Hfp_find & Ha_out'_rel).
      destruct Hfp_find as (Hdb_find & _ & _ & Hwl_find & Hana_find & Hkey_iff_find & _).
      (* analyses_cover e_find (from Hcov + fields_preserved) *)
      assert (Hcov_find : analyses_cover e_find).
      { unfold analyses_cover. intros z Hz'.
        assert (Hz : Sep.has_key z (parent (Defs.equiv e))).
        { apply Hkey_iff_find. exact Hz'. }
        destruct (Hcov z Hz) as [a Ha].
        exists a. rewrite Hana_find. exact Ha. }
      (* args' are all has_key in e_find, using uf_rel_PER_has_key *)
      assert (Hkeys_args' : forall x', In x' args' -> Sep.has_key x' (parent (Defs.equiv e_find))).
      { destruct Huf_find as [roots_find Huf_find_ok].
        (* From all2 (uf_rel_PER e_find.equiv) args' args:
           each pair (x', x) satisfies uf_rel_PER, x has_key e_find (via iff), hence x' too *)
        (* Use all2-based induction without reverting the fixed args' variable *)
        assert (Hstep : forall l1 l2,
          all2 (uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_find)) l1 l2 ->
          all (fun x => Sep.has_key x (parent (Defs.equiv e))) l2 ->
          forall z, In z l1 -> Sep.has_key z (parent (Defs.equiv e_find))).
        { induction l1 as [|y1 l1' IH1]; intros l2 Hall2 Hkl2 z Hz.
          - inversion Hz.
          - destruct l2 as [|y2 l2'].
            + cbn [all2] in Hall2. exact (False_ind _ Hall2).
            + cbn [all2] in Hall2. destruct Hall2 as [Hrel1 Hrest1].
              cbn [all] in Hkl2. destruct Hkl2 as [Hky2 Hkl2'].
              cbn [In] in Hz. destruct Hz as [Heq | Hz'].
              * subst z.
                apply (proj1 (@uf_rel_PER_has_key V V_Eqb V_Eqb_ok lt V_default
                                V_map V_map_ok (Defs.equiv e_find) roots_find y1 y2
                                Huf_find_ok Hrel1)).
              * exact (IH1 l2' Hrest1 Hkl2' z Hz'). }
        intros x' Hx'. apply (Hstep args' args Ha_out'_rel Hkeys_all x' Hx'). }
      (* Step 2: db_lookup *)
      pose proof (@db_lookup_pure V V V_map V_map V_trie X f args') as Hlk_pure.
      unfold vc in Hlk_pure. specialize (Hlk_pure e_find).
      destruct (db_lookup V V V_map V_map V_trie X f args' e_find) as [mout e_lk] eqn:Hlkeq.
      cbn [fst snd] in Hlk_pure.
      destruct Hlk_pure as [He_lk_eq _]. subst e_lk.
      destruct mout as [r_hit |]; cbn [Mbind StateMonad.state_monad fst snd].
      - (* Hit: Mret r_hit, state unchanged *)
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        split.
        + rewrite <- Hwl_find. reflexivity.
        + exact Hcov_find.
      - (* Miss: alloc + db_set *)
        cbn [Mbind StateMonad.state_monad].
        (* alloc *)
        pose proof (@alloc_struct V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X
                      lt_asymmetric lt_succ lt_trans) as Halloc_s.
        unfold vc in Halloc_s. specialize (Halloc_s e_find).
        destruct (Defs.alloc V succ V V_map V_map V_trie X e_find) as [r_new e_alloc] eqn:Halloc_eq.
        cbn [fst snd] in Halloc_s.
        destruct Huf_find as [roots_find Huf_find_ok].
        specialize (Halloc_s roots_find Huf_find_ok).
        destruct Halloc_s as (_ & Hr_fresh & Hr_new_key & Hmono_alloc & _ & _ & Hwl_alloc).
        (* analyses e_alloc = analyses e_find (alloc def) *)
        assert (Hana_alloc : Defs.analyses e_alloc = Defs.analyses e_find).
        { unfold Defs.alloc in Halloc_eq.
          destruct (UnionFind.alloc V _ _ succ (Defs.equiv e_find)) as [uf' x_f] eqn:Huf_alloc.
          injection Halloc_eq as <- <-. reflexivity. }
        (* Each arg in args' has an analysis in e_alloc (they are old keys, not r_new) *)
        assert (Hana_args' : forall x, In x args' ->
                               exists a, map.get (Defs.analyses e_alloc) x = Some a).
        { intros x Hx.
          (* x has_key in e_find *)
          assert (Hkx_find : Sep.has_key x (parent (Defs.equiv e_find))).
          { apply Hkeys_args'. exact Hx. }
          (* x ≠ r_new: r_new is NOT in e_find but x is *)
          assert (Hxne : x <> r_new).
          { intro Heq. subst x. exact (Hr_fresh Hkx_find). }
          (* analyses e_alloc = analyses e_find, so x has analysis there *)
          destruct (Hcov_find x Hkx_find) as [a Ha].
          exists a. rewrite Hana_alloc. exact Ha. }
        (* get_analyses args' e_alloc is a pure read *)
        destruct (get_analyses_stable_per_arg args' e_alloc Hana_args') as [arg_as Hga_stable].
        (* db_set (Build_atom f args' r_new) *)
        unfold db_set.
        cbn [atom_fn atom_args atom_ret].
        cbn [Mbind StateMonad.state_monad fst snd].
        rewrite Hga_stable.
        cbn [fst snd].
        (* update_analyses r_new out_a: worklist unchanged, analyses gains r_new *)
        set (out_a := analyze V V X (Build_atom f args' r_new) arg_as).
        destruct (update_analyses V V V_map V_map V_trie X r_new out_a e_alloc) as [_u e_ua] eqn:Hue.
        assert (Hwl_ua : Defs.worklist e_ua = Defs.worklist e_alloc).
        { unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; reflexivity. }
        assert (Hana_ua_r : exists a, map.get (Defs.analyses e_ua) r_new = Some a).
        { unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; cbn.
          rewrite map.get_put_same. eexists. reflexivity. }
        assert (Hana_ua_old : forall z, z <> r_new ->
                               map.get (Defs.analyses e_ua) z = map.get (Defs.analyses e_alloc) z).
        { intros z Hne.
          unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; cbn.
          rewrite map.get_put_diff by exact Hne. reflexivity. }
        assert (Hequiv_ua : Defs.equiv e_ua = Defs.equiv e_alloc).
        { unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; reflexivity. }
        (* db_set' (Build_atom f args' r_new) out_a e_ua: worklist and analyses unchanged *)
        destruct (db_set' V V_Eqb V V_map V_map V_trie X (Build_atom f args' r_new) out_a e_ua)
          as [_v e_db] eqn:Hde.
        assert (Hwl_db : Defs.worklist e_db = Defs.worklist e_ua).
        { unfold db_set' in Hde; injection Hde as _ Hde'; subst e_db; reflexivity. }
        assert (Hana_db : Defs.analyses e_db = Defs.analyses e_ua).
        { unfold db_set' in Hde; injection Hde as _ Hde'; subst e_db; reflexivity. }
        assert (Hequiv_db : Defs.equiv e_db = Defs.equiv e_ua).
        { unfold db_set' in Hde; injection Hde as _ Hde'; subst e_db; reflexivity. }
        cbn [Mret StateMonad.state_monad fst snd].
        split.
        + (* Worklist: e_db.wl = e_ua.wl = e_alloc.wl = e_find.wl = e.wl *)
          rewrite Hwl_db, Hwl_ua, <- Hwl_alloc, <- Hwl_find. reflexivity.
        + (* analyses_cover e_db *)
          unfold analyses_cover. intros z Hz'.
          (* parent e_db.equiv = parent e_ua.equiv = parent e_alloc.equiv *)
          rewrite Hequiv_db, Hequiv_ua in Hz'.
          (* parent e_alloc.equiv: either r_new or was in e_find *)
          pose proof (eqb_spec z r_new) as Hzrn_spec.
          destruct (eqb z r_new) eqn:Hzrn.
          * (* z = r_new *)
            subst z.
            destruct Hana_ua_r as [a Ha].
            exists a. rewrite Hana_db. exact Ha.
          * (* z ≠ r_new: z was in e_find.parent (from alloc_parent_eq_put) *)
            assert (Hne : z <> r_new). { exact Hzrn_spec. }
            assert (Hz_find : Sep.has_key z (parent (Defs.equiv e_find))).
            { unfold Sep.has_key.
              rewrite <- (alloc_parent_eq_put e_find r_new e_alloc Halloc_eq z Hne).
              exact Hz'. }
            destruct (Hcov_find z Hz_find) as [a Ha].
            exists a.
            rewrite Hana_db, Hana_ua_old by exact Hne.
            rewrite Hana_alloc. exact Ha.
    Qed.

    Lemma add_open_worklist_frame (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      c (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t -> forall r, map fst c = map fst r ->
           vc (add_open_term' succ sort_of l false false add_open_sort_inner r e)
              (open_wlframe_post r))
        /\ (forall args c', wf_args l1 c args c' -> forall r, map fst c = map fst r ->
           vc (list_Mmap (add_open_term' succ sort_of l false false add_open_sort_inner r) args)
              (open_wlframe_args_post r)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l false false
                                     add_open_sort_inner r e)
                     (open_wlframe_post r))
               (fun args c' => forall r, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l false false
                                                add_open_sort_inner r) args)
                     (open_wlframe_args_post r))).
      - (* con case *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_wlframe_post.
        intros Hok Hcov Hsub.
        unfold open_wlframe_args_post in Hpost_args.
        specialize (Hpost_args Hok Hcov Hsub).
        destruct Hpost_args as (Hwl_inner & Hok_inner & Hcov_inner & Hmono_inner & Hkeys_aout).
        assert (Hkeys_aout_in : forall x, In x a_out ->
                                  Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. exact (in_all _ _ _ Hkeys_aout Hx). }
        (* Use hash_entry_egraph_ok for has_key-mono and has_key x_res *)
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhe_ok.
        unfold vc in Hhe_ok.
        specialize (Hhe_ok e_inner Hok_inner Hkeys_aout_in).
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe_ok |- *.
        destruct Hhe_ok as (Hok_he & Hmono_he & Hres_he).
        (* Use hash_entry_wl_frame for worklist and analyses_cover *)
        pose proof (hash_entry_wl_frame name a_out e_inner Hok_inner Hcov_inner Hkeys_aout_in) as Hwlf.
        rewrite Heqhe in Hwlf.
        cbn [fst snd] in Hwlf.
        destruct Hwlf as (Hwl_he & Hcov_he).
        cbn [Mret StateMonad.state_monad fst snd].
        split; [rewrite Hwl_he; exact Hwl_inner|].
        split; [exact Hok_he|].
        split; [exact Hcov_he|].
        split; [intros x Hx; apply Hmono_he; apply Hmono_inner; exact Hx|].
        exact Hres_he.
      - (* var case *)
        intros n t_var Hin_var r Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_wlframe_post.
        intros Hok Hcov Hsub.
        split; [reflexivity|].
        split; [exact Hok|].
        split; [exact Hcov|].
        split; [auto|].
        assert (Hafc : all_fresh c) by basic_core_crush.
        assert (Hafr : all_fresh r).
        { apply NoDup_fresh. rewrite <- Hmaps. apply NoDup_fresh; exact Hafc. }
        assert (Hex_x : exists x_n, In (n, x_n) r).
        { apply pair_fst_in_exists. rewrite <- Hmaps. eapply pair_fst_in; exact Hin_var. }
        destruct Hex_x as [x_n Hin_xn].
        assert (Hlk : named_list_lookup default r n = x_n).
        { clear -V_Eqb_ok Hafr Hin_xn.
          induction r as [|[m v_m] r' IH]; cbn in *; [tauto|].
          destruct Hafr as [Hfr Hafr'].
          destruct Hin_xn as [Heq|Hin_xn'].
          - inversion Heq; subst.
            eqb_case n n; congruence.
          - eqb_case n m.
            + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_xn'.
            + apply IH; auto. }
        cbn [fst]. rewrite Hlk.
        exact (in_all _ _ _ Hsub Hin_xn).
      - (* eq_sort conversion *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r Hmaps.
        apply IH_term; assumption.
      - (* nil args *)
        intros r Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_wlframe_args_post. intros e_in Hok Hcov Hsub.
        split; [reflexivity|].
        split; [exact Hok|].
        split; [exact Hcov|].
        split; [auto | cbn; exact I].
      - (* cons args *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_wlframe_args_post.
        intros Hok Hcov Hsub.
        specialize (IH_term r Hmaps).
        specialize (IH_args r Hmaps).
        unfold vc, open_wlframe_post in IH_term.
        specialize (IH_term e_in Hok Hcov Hsub).
        destruct (add_open_term' succ sort_of l false false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        cbn [fst snd] in IH_term.
        destruct IH_term as (Hwl_head & Hok_head & Hcov_head & Hmono_head & Hkey_vhead).
        assert (Hsub_head : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_after_head))) r).
        { eapply all_wkn; [|exact Hsub].
          intros x _ Hk. apply Hmono_head. exact Hk. }
        unfold vc, open_wlframe_args_post in IH_args.
        specialize (IH_args e_after_head Hok_head Hcov_head Hsub_head).
        destruct (list_Mmap
                    (add_open_term' succ sort_of l false false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd] in IH_args |- *.
        destruct IH_args as (Hwl_tail & Hok_tail & Hcov_tail & Hmono_tail & Hkeys_tail).
        split; [rewrite Hwl_tail; exact Hwl_head|].
        split; [exact Hok_tail|].
        split; [exact Hcov_tail|].
        split.
        + intros x Hx. apply Hmono_tail. apply Hmono_head. exact Hx.
        + cbn [all]. split.
          * apply Hmono_tail. exact Hkey_vhead.
          * exact Hkeys_tail.
    Qed.

    Lemma add_open_sort'_worklist_frame l1 c r t fuel
      : wf_lang l1 -> length l1 < fuel -> incl l1 l -> wf_ctx l1 c -> wf_sort l1 c t ->
        map fst c = map fst r ->
        vc (add_open_sort' succ sort_of l false false fuel r t)
           (open_wlframe_sort_post r).
    Proof.
      revert l1 c r t.
      induction fuel; intros l1 c r t Hwfl1 Hflen Hincl Hctx Hsort Hmaps.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { apply (proj2 (add_open_worklist_frame l1
                          (add_open_sort' succ sort_of l false false fuel)
                          Hwfl1 Hincl c Hctx)
                  _ _ Hwfargs r Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_wlframe_sort_post, open_wlframe_post.
        intros Hok Hcov Hsub.
        unfold open_wlframe_args_post in Hpost_args.
        specialize (Hpost_args Hok Hcov Hsub).
        destruct Hpost_args as (Hwl_inner & Hok_inner & Hcov_inner & Hmono_inner & Hkeys_aout).
        assert (Hkeys_aout_in : forall x, In x a_out ->
                                  Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. exact (in_all _ _ _ Hkeys_aout Hx). }
        (* Use hash_entry_egraph_ok and hash_entry_wl_frame *)
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhe_ok.
        unfold vc in Hhe_ok.
        specialize (Hhe_ok e_inner Hok_inner Hkeys_aout_in).
        destruct (hash_entry succ n a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe_ok |- *.
        destruct Hhe_ok as (Hok_he & Hmono_he & Hres_he).
        pose proof (hash_entry_wl_frame n a_out e_inner Hok_inner Hcov_inner Hkeys_aout_in) as Hwlf.
        rewrite Heqhe in Hwlf.
        cbn [fst snd] in Hwlf.
        destruct Hwlf as (Hwl_he & Hcov_he).
        cbn [Mret StateMonad.state_monad fst snd].
        split; [rewrite Hwl_he; exact Hwl_inner|].
        split; [exact Hok_he|].
        split; [exact Hcov_he|].
        split; [intros x Hx; apply Hmono_he; apply Hmono_inner; exact Hx|].
        exact Hres_he.
    Qed.

    Lemma add_open_sort_worklist_frame c r t
      : wf_ctx l c -> wf_sort l c t -> map fst c = map fst r ->
        vc (add_open_sort succ sort_of l false false r t)
           (open_wlframe_sort_post r).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_worklist_frame; try eassumption; eauto with utils.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* PKE (parents-keys-in-equiv) family: add_open preserves              *)
    (* parents_keys_in_equiv along with egraph_ok.                         *)
    (* ------------------------------------------------------------------ *)

    (* Shorthand for parents_keys_in_equiv at our section types. *)
    Local Notation pke_inst :=
      (SemanticsParents.parents_keys_in_equiv V V V_map V_map V_trie X).

    Definition open_pke_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      egraph_ok e_in ->
      pke_inst e_in ->
      all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) sub ->
        egraph_ok (snd res)
      /\ pke_inst (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ Sep.has_key (fst res) (parent (Defs.equiv (snd res))).

    Definition open_pke_args_post (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      egraph_ok e_in ->
      pke_inst e_in ->
      all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_in))) sub ->
        egraph_ok (snd res)
      /\ pke_inst (snd res)
      /\ (forall x, Sep.has_key x (parent (Defs.equiv e_in)) ->
                    Sep.has_key x (parent (Defs.equiv (snd res))))
      /\ all (fun x => Sep.has_key x (parent (Defs.equiv (snd res)))) (fst res).

    Definition open_pke_sort_post (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop := open_pke_post sub e_in res.

    Lemma add_open_pke (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      c (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t -> forall r, map fst c = map fst r ->
           vc (add_open_term' succ sort_of l false false add_open_sort_inner r e)
              (open_pke_post r))
        /\ (forall args c', wf_args l1 c args c' -> forall r, map fst c = map fst r ->
           vc (list_Mmap (add_open_term' succ sort_of l false false add_open_sort_inner r) args)
              (open_pke_args_post r)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l false false
                                     add_open_sort_inner r e)
                     (open_pke_post r))
               (fun args c' => forall r, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l false false
                                                add_open_sort_inner r) args)
                     (open_pke_args_post r))).
      - (* con case *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_pke_post.
        intros Hok Hpke Hsub.
        unfold open_pke_args_post in Hpost_args.
        specialize (Hpost_args Hok Hpke Hsub).
        destruct Hpost_args as (Hok_inner & Hpke_inner & Hmono_inner & Hkeys_aout).
        cbn [fst snd] in Hok_inner, Hpke_inner, Hmono_inner, Hkeys_aout.
        assert (Hkeys_aout_in : forall x, In x a_out ->
                                  Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. exact (in_all _ _ _ Hkeys_aout Hx). }
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhe_ok.
        unfold vc in Hhe_ok.
        specialize (Hhe_ok e_inner Hok_inner Hkeys_aout_in).
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe_ok |- *.
        destruct Hhe_ok as (Hok_he & Hmono_he & Hres_he).
        pose proof (@SemanticsParents.hash_entry_parents_keys_in_equiv V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map V_map_ok V_trie X _
                      lt_asymmetric lt_succ lt_trans name a_out) as Hpke_he.
        unfold vc in Hpke_he.
        specialize (Hpke_he e_inner).
        rewrite Heqhe in Hpke_he. cbn [fst snd] in Hpke_he.
        destruct Hok_inner as [Huf_inner Hdb_inner].
        specialize (Hpke_he Huf_inner Hkeys_aout Hpke_inner).
        cbn [Mret StateMonad.state_monad fst snd].
        split; [exact Hok_he|].
        split; [exact Hpke_he|].
        split; [intros x Hx; apply Hmono_he; apply Hmono_inner; exact Hx|].
        exact Hres_he.
      - (* var case *)
        intros n t_var Hin_var r Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_pke_post.
        intros Hok Hpke Hsub.
        split; [exact Hok|].
        split; [exact Hpke|].
        split; [auto|].
        assert (Hafc : all_fresh c) by basic_core_crush.
        assert (Hafr : all_fresh r).
        { apply NoDup_fresh. rewrite <- Hmaps. apply NoDup_fresh; exact Hafc. }
        assert (Hex_x : exists x_n, In (n, x_n) r).
        { apply pair_fst_in_exists. rewrite <- Hmaps. eapply pair_fst_in; exact Hin_var. }
        destruct Hex_x as [x_n Hin_xn].
        assert (Hlk : named_list_lookup default r n = x_n).
        { clear -V_Eqb_ok Hafr Hin_xn.
          induction r as [|[m v_m] r' IH]; cbn in *; [tauto|].
          destruct Hafr as [Hfr Hafr'].
          destruct Hin_xn as [Heq|Hin_xn'].
          - inversion Heq; subst.
            eqb_case n n; congruence.
          - eqb_case n m.
            + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_xn'.
            + apply IH; auto. }
        cbn [fst]. rewrite Hlk.
        exact (in_all _ _ _ Hsub Hin_xn).
      - (* eq_sort conversion *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r Hmaps.
        apply IH_term; assumption.
      - (* nil args *)
        intros r Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_pke_args_post. intros e_in Hok Hpke Hsub.
        split; [exact Hok|].
        split; [exact Hpke|].
        split; [auto | cbn; exact I].
      - (* cons args *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_pke_args_post.
        intros Hok Hpke Hsub.
        specialize (IH_term r Hmaps).
        specialize (IH_args r Hmaps).
        unfold vc, open_pke_post in IH_term.
        specialize (IH_term e_in Hok Hpke Hsub).
        destruct (add_open_term' succ sort_of l false false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        cbn [fst snd] in IH_term.
        destruct IH_term as (Hok_head & Hpke_head & Hmono_head & Hkey_vhead).
        assert (Hsub_head : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_after_head))) r).
        { eapply all_wkn; [|exact Hsub].
          intros x _ Hk. apply Hmono_head. exact Hk. }
        unfold vc, open_pke_args_post in IH_args.
        specialize (IH_args e_after_head Hok_head Hpke_head Hsub_head).
        destruct (list_Mmap
                    (add_open_term' succ sort_of l false false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd] in IH_args |- *.
        destruct IH_args as (Hok_tail & Hpke_tail & Hmono_tail & Hkeys_tail).
        split; [exact Hok_tail|].
        split; [exact Hpke_tail|].
        split.
        + intros x Hx. apply Hmono_tail. apply Hmono_head. exact Hx.
        + cbn [all]. split.
          * apply Hmono_tail. exact Hkey_vhead.
          * exact Hkeys_tail.
    Qed.

    Lemma add_open_sort'_pke l1 c r t fuel
      : wf_lang l1 -> length l1 < fuel -> incl l1 l -> wf_ctx l1 c -> wf_sort l1 c t ->
        map fst c = map fst r ->
        vc (add_open_sort' succ sort_of l false false fuel r t)
           (open_pke_sort_post r).
    Proof.
      revert l1 c r t.
      induction fuel; intros l1 c r t Hwfl1 Hflen Hincl Hctx Hsort Hmaps.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { apply (proj2 (add_open_pke l1
                          (add_open_sort' succ sort_of l false false fuel)
                          Hwfl1 Hincl c Hctx)
                  _ _ Hwfargs r Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_pke_sort_post, open_pke_post.
        intros Hok Hpke Hsub.
        unfold open_pke_args_post in Hpost_args.
        specialize (Hpost_args Hok Hpke Hsub).
        destruct Hpost_args as (Hok_inner & Hpke_inner & Hmono_inner & Hkeys_aout).
        assert (Hkeys_aout_in : forall x, In x a_out ->
                                  Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. exact (in_all _ _ _ Hkeys_aout Hx). }
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhe_ok.
        unfold vc in Hhe_ok.
        specialize (Hhe_ok e_inner Hok_inner Hkeys_aout_in).
        destruct (hash_entry succ n a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe_ok |- *.
        destruct Hhe_ok as (Hok_he & Hmono_he & Hres_he).
        pose proof (@SemanticsParents.hash_entry_parents_keys_in_equiv V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map V_map_ok V_trie X _
                      lt_asymmetric lt_succ lt_trans n a_out) as Hpke_he.
        unfold vc in Hpke_he.
        specialize (Hpke_he e_inner).
        rewrite Heqhe in Hpke_he. cbn [fst snd] in Hpke_he.
        destruct Hok_inner as [Huf_inner Hdb_inner].
        specialize (Hpke_he Huf_inner Hkeys_aout Hpke_inner).
        cbn [Mret StateMonad.state_monad fst snd].
        split; [exact Hok_he|].
        split; [exact Hpke_he|].
        split; [intros x Hx; apply Hmono_he; apply Hmono_inner; exact Hx|].
        exact Hres_he.
    Qed.

    Lemma add_open_sort_parents_keys_in_equiv c r t
      : wf_ctx l c -> wf_sort l c t -> map fst c = map fst r ->
        vc (add_open_sort succ sort_of l false false r t)
           (open_pke_sort_post r).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_pke; try eassumption; eauto with utils.
    Qed.

    Lemma add_open_term_all_roots c r e t
      : wf_term l c e t ->
        wf_ctx l c ->
        map fst c = map fst r ->
        vc (add_open_term succ sort_of l false false r e)
           (open_roots_post r).
    Proof.
      intros Hwft Hctx Hmaps.
      unfold add_open_term.
      eapply (proj1 (add_open_all_roots l (add_open_sort succ sort_of l false false)
                      Hwf (incl_refl _) c Hctx)); eauto.
    Qed.

    Definition ctx_roots_post (c0 : ctx) (e_in : instance X)
        (res : named_list V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      (exists roots, union_find_ok lt (Defs.equiv (snd res)) roots)
      /\ db_ctx_inv (snd res)
      /\ all (fun p => is_root (snd res) (snd p)) (fst res)
      /\ map fst (fst res) = map fst c0.

    Lemma add_ctx_all_roots c
      : wf_ctx l c ->
        vc (add_ctx succ sort_of l false false c) (ctx_roots_post c).
    Proof.
      intros Hctx.
      unfold add_ctx.
      induction c as [|[name t] c' IH].
      - (* nil case *)
        cbn [list_Mfoldr].
        unfold vc, Mret. cbn [StateMonad.state_monad].
        unfold ctx_roots_post.
        intros e_in Hok Hdb.
        cbn [fst snd].
        split; [exact Hok|].
        split; [exact Hdb|].
        split; [cbn; exact I|].
        cbn. reflexivity.
      - (* cons case *)
        cbn [list_Mfoldr].
        eapply vc_bind.
        { apply IH. inversion Hctx; assumption. }
        intros e_pre base'.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Htail.
        unfold ctx_roots_post.
        intros Hok Hdb.
        unfold ctx_roots_post in Htail.
        assert (Hwfc' : wf_ctx l c') by (inversion Hctx; assumption).
        assert (Hwfst : wf_sort l c' t) by (inversion Hctx; assumption).
        specialize (Htail Hok Hdb).
        destruct Htail as (Huf_tail & Hdb_tail & Hall_tail & Hfst_tail).
        (* Step 1: add_open_sort_all_roots *)
        pose proof (add_open_sort_all_roots c' base' t Hwfc' Hwfst) as Hsort_roots.
        assert (Hmaps : map fst c' = map fst base') by (symmetry; exact Hfst_tail).
        specialize (Hsort_roots Hmaps).
        unfold vc in Hsort_roots. specialize (Hsort_roots e_inner).
        unfold open_roots_sort_post in Hsort_roots.
        specialize (Hsort_roots Huf_tail Hdb_tail Hall_tail).
        destruct (add_open_sort succ sort_of l false false base' t e_inner)
          as [t_v e_sort] eqn:Heq_sort.
        cbn [fst snd] in Hsort_roots.
        destruct Hsort_roots as [Henv_sort Htv_root].
        destruct Henv_sort as (Huf_sort & Hdb_sort & Hincl_sort & Hmono_sort).
        (* Step 2: alloc_opaque_rank_zero *)
        pose proof (@alloc_opaque_rank_zero V V_Eqb V_Eqb_ok lt succ
                      V V_map V_map V_map_ok V_trie X H
                      lt_asymmetric lt_succ lt_trans)
          as Halloc.
        unfold vc in Halloc. specialize (Halloc e_sort).
        destruct (alloc_opaque V succ V V_map V_map V_trie X e_sort) as [x' e_alloc] eqn:Heq_alloc.
        cbn [fst snd] in Halloc.
        destruct Huf_sort as [roots_s Hroots_s].
        specialize (Halloc roots_s Hroots_s).
        destruct Halloc as (Hok_alloc & Hfresh_x' & Hx'_root & Hx'_rank0
                           & Hkeys_alloc & Hmono_alloc & Hdb_alloc_eq
                           & Hpar_alloc & Hwl_alloc).
        cbn [fst snd] in *.
        (* Derive db_ctx_inv e_alloc from db_ctx_inv e_sort + db unchanged *)
        assert (Hdb_alloc : db_ctx_inv e_alloc).
        { unfold db_ctx_inv, db_inv in *.
          intros a Ha.
          rewrite <- Hdb_alloc_eq in Ha.
          specialize (Hdb_sort a Ha).
          destruct Hdb_sort as [Hargs_roots Hret_root].
          split.
          - eapply all_wkn; [|exact Hargs_roots].
            intros z _ Hz. exact (Hmono_alloc z Hz).
          - intro HPfn. exact (Hmono_alloc _ (Hret_root HPfn)). }
        (* Steps 3a and 3b: hash_entry_all_roots + hash_entry_fresh_rank_zero *)
        (* Prove x' is a key in e_alloc (it's a root) *)
        assert (Hx'_key : Sep.has_key x' (parent (Defs.equiv e_alloc))).
        { apply is_root_has_key. unfold is_root. exact Hx'_root. }
        (* Prove no (sort_of,[x'],r) atom in e_alloc.db *)
        assert (Hno_sortof : forall r, ~ atom_in_db (Build_atom sort_of [x'] r) e_alloc.(Defs.db)).
        { intros r Hin.
          (* e_alloc.db = e_sort.db *)
          rewrite <- Hdb_alloc_eq in Hin.
          (* by db_ctx_inv e_sort, x' is a root in e_sort *)
          unfold db_ctx_inv, db_inv in Hdb_sort.
          specialize (Hdb_sort (Build_atom sort_of [x'] r) Hin).
          destruct Hdb_sort as [Hargs_s _].
          cbn [atom_args] in Hargs_s.
          destruct Hargs_s as [Hx'_s _].
          (* x' is a root in e_sort => has_key x' e_sort *)
          assert (Hx'_ks : Sep.has_key x' (parent (Defs.equiv e_sort))).
          { apply is_root_has_key. unfold is_root. exact Hx'_s. }
          (* but alloc_opaque says x' is fresh in e_sort *)
          exact (Hfresh_x' Hx'_ks). }
        (* Apply hash_entry_all_roots *)
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_roots.
        (* Apply hash_entry_fresh_rank_zero *)
        pose proof (@hash_entry_fresh_rank_zero V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X H
                      lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_fresh.
        unfold vc in Hhe_roots, Hhe_fresh.
        specialize (Hhe_roots e_alloc).
        specialize (Hhe_fresh e_alloc).
        destruct (hash_entry succ sort_of [x'] e_alloc) as [tx' e_he] eqn:Heq_he.
        cbn [fst snd] in Hhe_roots, Hhe_fresh.
        (* Supply hypotheses to hash_entry_all_roots *)
        assert (Hkeys_he_args : forall y, In y [x'] -> Sep.has_key y (parent (Defs.equiv e_alloc))).
        { intros y Hy. cbn in Hy. destruct Hy as [Hy|]; [|contradiction].
          subst y. exact Hx'_key. }
        specialize (Hhe_roots (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        destruct Hhe_roots as (Huf_he & Hdb_he & Hincl_he & Hmono_he & _).
        (* Apply hash_entry_args_old_keys to get structural info about e_he.db *)
        pose proof (@hash_entry_args_old_keys V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X H lt_asymmetric lt_succ lt_trans
                      (fun s => s <> sort_of) sort_of [x']) as Hhe_old.
        unfold vc in Hhe_old. specialize (Hhe_old e_alloc).
        rewrite Heq_he in Hhe_old. cbn [fst snd] in Hhe_old.
        specialize (Hhe_old (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        (* Hhe_old : forall b in e_he.db,
             all (fun y => Sep.has_key y (parent e_alloc)) b.args
             /\ (b.fn <> sort_of -> atom_in_db b e_alloc.db) *)
        (* Supply hypotheses to hash_entry_fresh_rank_zero *)
        assert (Hx'_root_list : all (fun y => map.get (parent (Defs.equiv e_alloc)) y = Some y) [x']).
        { cbn. split; [exact Hx'_root | exact I]. }
        specialize (Hhe_fresh (ex_intro _ _ Hok_alloc) Hx'_root_list Hno_sortof).
        destruct Hhe_fresh as (Htx'_rank0 & Htx'_root & Htx'_fresh & Htx'_atom).
        (* Step 4: union_roots_demote_second *)
        (* t_v is a root in e_he (via Hmono_he from Htv_root in e_sort via Hmono_alloc) *)
        assert (Htv_root_alloc : is_root e_alloc t_v).
        { unfold is_root. exact (Hmono_alloc t_v Htv_root). }
        assert (Htv_root_he : is_root e_he t_v).
        { unfold is_root. exact (Hmono_he t_v (Htv_root_alloc)). }
        (* tx' is a root in e_he *)
        assert (Htx'_root_he : is_root e_he tx').
        { unfold is_root. exact Htx'_root. }
        (* t_v <> tx': t_v has_key in e_alloc, tx' is fresh in e_alloc *)
        assert (Htv_ne_tx' : t_v <> tx').
        { intro Heq. subst t_v.
          apply Htx'_fresh.
          apply is_root_has_key. exact Htv_root_alloc. }
        (* rank tx' = Some 0 in e_he *)
        assert (Hrank_tx' : map.get (@rank _ _ _ (Defs.equiv e_he)) tx' = Some 0).
        { exact Htx'_rank0. }
        pose proof (@union_roots_demote_second V V_Eqb V_Eqb_ok lt V_default
                      V V_map V_map V_map_ok V_trie X H t_v tx') as Hunion.
        unfold vc in Hunion. specialize (Hunion e_he).
        destruct (Defs.union t_v tx' e_he) as [v_u e_u] eqn:Heq_union.
        cbn [fst snd] in Hunion.
        destruct Huf_he as [roots_he Hroots_he].
        specialize (Hunion roots_he Hroots_he Htv_root_he Htx'_root_he Htv_ne_tx' Hrank_tx').
        destruct Hunion as (Hvu_tv & Htv_root_u & Htx'_demoted_u & Hothers_u
                           & Hdb_u & Hpar_u & [improved Hwl_u] & [roots_u Hroots_u]).
        cbn [fst snd] in *.
        (* Now prove tx' is not an arg of any e_he.db atom (needed for crux) *)
        assert (Htx'_not_arg : forall b, atom_in_db b (Defs.db e_he) -> ~ In tx' (atom_args b)).
        { intros b Hb Hin_tx'.
          (* From hash_entry_args_old_keys: all args of b were has_key in e_alloc *)
          destruct (Hhe_old b Hb) as [Hb_args_old _].
          assert (Htx'_hk : Sep.has_key tx' (parent (Defs.equiv e_alloc))).
          { exact (in_all _ _ _ Hb_args_old Hin_tx'). }
          (* But tx' is fresh in e_alloc — contradiction *)
          exact (Htx'_fresh Htx'_hk). }
        (* Build db_ctx_inv e_u *)
        assert (Hdb_u_inv : db_ctx_inv e_u).
        { unfold db_ctx_inv, db_inv in *.
          intros a Ha.
          rewrite <- Hdb_u in Ha.
          specialize (Hdb_he a Ha).
          destruct Hdb_he as [Hargs_he Hret_he].
          split.
          - (* args: each arg y is root in e_he; y != tx' (Htx'_not_arg); so others_u gives root in e_u *)
            eapply all_wkn; [|exact Hargs_he].
            intros y Hyin Hy_root.
            unfold is_root in Hy_root.
            apply Hothers_u.
            + intro Heq. subst y.
              exact (Htx'_not_arg a Ha Hyin).
            + exact Hy_root.
          - (* ret: a.fn != sort_of -> ret root in e_he -> ret != tx' -> root in e_u *)
            intro HPfn.
            assert (Hret_root : map.get (parent (Defs.equiv e_he)) (atom_ret a) = Some (atom_ret a)).
            { exact (Hret_he HPfn). }
            apply Hothers_u.
            + (* ret != tx': a.fn != sort_of, so by hash_entry_args_old_keys,
                 a is in e_alloc.db; by db_ctx_inv e_alloc, a.ret has_key in e_alloc;
                 tx' is fresh in e_alloc, so a.ret != tx'. *)
              intro Heq. subst.
              destruct (Hhe_old a Ha) as [_ Ha_old].
              assert (Ha_alloc : atom_in_db a (Defs.db e_alloc)) by (apply Ha_old; exact HPfn).
              unfold db_ctx_inv, db_inv in Hdb_alloc.
              specialize (Hdb_alloc a Ha_alloc).
              destruct Hdb_alloc as [_ Hret_alloc].
              assert (Htx'_hk : Sep.has_key (atom_ret a) (parent (Defs.equiv e_alloc))).
              { unfold Sep.has_key. rewrite (Hret_alloc HPfn). exact I. }
              exact (Htx'_fresh Htx'_hk).
            + exact Hret_root. }
        (* Assemble the 4 conjuncts *)
        split.
        { exact (ex_intro _ roots_u Hroots_u). }
        split.
        { exact Hdb_u_inv. }
        split.
        { (* all-roots ((name,x')::base') in e_u *)
          cbn [all].
          split.
          - (* x' is root in e_u *)
            unfold is_root.
            (* x' root in e_alloc -> root in e_he (Hmono_he) -> others_u (x' != tx') -> root in e_u *)
            apply Hothers_u.
            + (* x' != tx' *)
              intro Heq. apply Htx'_fresh.
              rewrite <- Heq. exact Hx'_key.
            + exact (Hmono_he x' Hx'_root).
          - (* all roots in base' (Hall_tail) lifted to e_u *)
            eapply all_wkn; [|exact Hall_tail].
            intros [xn yn] Hyin Hyn_root.
            cbn [snd] in *.
            unfold is_root in *.
            (* yn root in e_inner -> root in e_sort (Hmono_sort) -> root in e_alloc (Hmono_alloc)
               -> root in e_he (Hmono_he) -> others_u (yn != tx') -> root in e_u *)
            apply Hothers_u.
            + (* yn != tx': yn has_key in e_alloc, tx' doesn't *)
              intro Heq. subst yn.
              apply Htx'_fresh.
              apply is_root_has_key.
              unfold is_root.
              exact (Hmono_alloc _ (Hmono_sort _ Hyn_root)).
            + exact (Hmono_he _ (Hmono_alloc _ (Hmono_sort _ Hyn_root))). }
        { (* map fst ((name,x')::base') = map fst ((name,t)::c') *)
          cbn [map fst]. f_equal. exact Hfst_tail. }
    Qed.

    (* ============================================================== *)
    (* add_ctx_egraph_ok: add_ctx_all_roots augmented with a 5th      *)
    (* conjunct tracking egraph_ok through the four per-var ops.      *)
    (* ============================================================== *)

    Definition ctx_egraph_post (c0 : ctx) (e_in : instance X)
        (res : named_list V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      egraph_ok e_in ->
      (exists roots, union_find_ok lt (Defs.equiv (snd res)) roots)
      /\ db_ctx_inv (snd res)
      /\ all (fun p => is_root (snd res) (snd p)) (fst res)
      /\ map fst (fst res) = map fst c0
      /\ egraph_ok (snd res).

    Lemma add_ctx_egraph_ok c
      : wf_ctx l c ->
        vc (add_ctx succ sort_of l false false c) (ctx_egraph_post c).
    Proof.
      intros Hctx.
      unfold add_ctx.
      induction c as [|[name t] c' IH].
      - (* nil case *)
        cbn [list_Mfoldr].
        unfold vc, Mret. cbn [StateMonad.state_monad].
        unfold ctx_egraph_post.
        intros e_in Hok Hdb Hok_eg.
        cbn [fst snd].
        split; [exact Hok|].
        split; [exact Hdb|].
        split; [cbn; exact I|].
        split; [cbn; reflexivity|].
        exact Hok_eg.
      - (* cons case *)
        cbn [list_Mfoldr].
        eapply vc_bind.
        { apply IH. inversion Hctx; assumption. }
        intros e_pre base'.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Htail.
        unfold ctx_egraph_post.
        intros Hok Hdb Hok_eg.
        unfold ctx_egraph_post in Htail.
        assert (Hwfc' : wf_ctx l c') by (inversion Hctx; assumption).
        assert (Hwfst : wf_sort l c' t) by (inversion Hctx; assumption).
        specialize (Htail Hok Hdb Hok_eg).
        destruct Htail as (Huf_tail & Hdb_tail & Hall_tail & Hfst_tail & Hok_eg_tail).
        (* Step 1: add_open_sort_all_roots *)
        pose proof (add_open_sort_all_roots c' base' t Hwfc' Hwfst) as Hsort_roots.
        assert (Hmaps : map fst c' = map fst base') by (symmetry; exact Hfst_tail).
        specialize (Hsort_roots Hmaps).
        unfold vc in Hsort_roots. specialize (Hsort_roots e_inner).
        unfold open_roots_sort_post in Hsort_roots.
        specialize (Hsort_roots Huf_tail Hdb_tail Hall_tail).
        (* Step 1': add_open_sort_egraph_ok (same e_sort) *)
        pose proof (add_open_sort_egraph_ok c' base' t Hwfc' Hwfst Hmaps) as Hsort_eg.
        unfold vc in Hsort_eg. specialize (Hsort_eg e_inner).
        unfold open_egraph_sort_post, open_egraph_post in Hsort_eg.
        assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_inner))) base').
        { eapply all_wkn; [|exact Hall_tail].
          intros p _ Hp_root. apply is_root_has_key. exact Hp_root. }
        specialize (Hsort_eg Hok_eg_tail Hbase_keys).
        destruct (add_open_sort succ sort_of l false false base' t e_inner)
          as [t_v e_sort] eqn:Heq_sort.
        cbn [fst snd] in Hsort_roots, Hsort_eg.
        destruct Hsort_roots as [Henv_sort Htv_root].
        destruct Henv_sort as (Huf_sort & Hdb_sort & Hincl_sort & Hmono_sort).
        destruct Hsort_eg as (Hok_eg_sort & Hmono_eg_sort & Htv_key_sort).
        (* Step 2: alloc_opaque_rank_zero *)
        pose proof (@alloc_opaque_rank_zero V V_Eqb V_Eqb_ok lt succ
                      V V_map V_map V_map_ok V_trie X H
                      lt_asymmetric lt_succ lt_trans)
          as Halloc.
        unfold vc in Halloc. specialize (Halloc e_sort).
        (* Step 2': alloc_opaque_egraph_ok (same e_alloc) *)
        pose proof (@alloc_opaque_egraph_ok V V_Eqb V_Eqb_ok lt succ
                      V V_map V_map V_map_ok V_trie X H
                      lt_asymmetric lt_succ lt_trans)
          as Halloc_eg.
        unfold vc in Halloc_eg. specialize (Halloc_eg e_sort).
        destruct (alloc_opaque V succ V V_map V_map V_trie X e_sort) as [x' e_alloc] eqn:Heq_alloc.
        cbn [fst snd] in Halloc, Halloc_eg.
        destruct Huf_sort as [roots_s Hroots_s].
        specialize (Halloc roots_s Hroots_s).
        destruct Halloc as (Hok_alloc & Hfresh_x' & Hx'_root & Hx'_rank0
                           & Hkeys_alloc & Hmono_alloc & Hdb_alloc_eq
                           & Hpar_alloc & Hwl_alloc).
        specialize (Halloc_eg Hok_eg_sort).
        destruct Halloc_eg as (Hok_eg_alloc & _ & Hx'_key_alloc & Hmono_eg_alloc & _ & _ & _).
        cbn [fst snd] in *.
        (* Derive db_ctx_inv e_alloc from db_ctx_inv e_sort + db unchanged *)
        assert (Hdb_alloc : db_ctx_inv e_alloc).
        { unfold db_ctx_inv, db_inv in *.
          intros a Ha.
          rewrite <- Hdb_alloc_eq in Ha.
          specialize (Hdb_sort a Ha).
          destruct Hdb_sort as [Hargs_roots Hret_root].
          split.
          - eapply all_wkn; [|exact Hargs_roots].
            intros z _ Hz. exact (Hmono_alloc z Hz).
          - intro HPfn. exact (Hmono_alloc _ (Hret_root HPfn)). }
        (* Steps 3a and 3b: hash_entry_all_roots + hash_entry_fresh_rank_zero *)
        (* Prove x' is a key in e_alloc (it's a root) *)
        assert (Hx'_key : Sep.has_key x' (parent (Defs.equiv e_alloc))).
        { apply is_root_has_key. unfold is_root. exact Hx'_root. }
        (* Prove no (sort_of,[x'],r) atom in e_alloc.db *)
        assert (Hno_sortof : forall r, ~ atom_in_db (Build_atom sort_of [x'] r) e_alloc.(Defs.db)).
        { intros r Hin.
          (* e_alloc.db = e_sort.db *)
          rewrite <- Hdb_alloc_eq in Hin.
          (* by db_ctx_inv e_sort, x' is a root in e_sort *)
          unfold db_ctx_inv, db_inv in Hdb_sort.
          specialize (Hdb_sort (Build_atom sort_of [x'] r) Hin).
          destruct Hdb_sort as [Hargs_s _].
          cbn [atom_args] in Hargs_s.
          destruct Hargs_s as [Hx'_s _].
          (* x' is a root in e_sort => has_key x' e_sort *)
          assert (Hx'_ks : Sep.has_key x' (parent (Defs.equiv e_sort))).
          { apply is_root_has_key. unfold is_root. exact Hx'_s. }
          (* but alloc_opaque says x' is fresh in e_sort *)
          exact (Hfresh_x' Hx'_ks). }
        (* Apply hash_entry_all_roots *)
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_roots.
        (* Apply hash_entry_fresh_rank_zero *)
        pose proof (@hash_entry_fresh_rank_zero V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X H
                      lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_fresh.
        (* Apply hash_entry_egraph_ok *)
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X H lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_eg.
        unfold vc in Hhe_roots, Hhe_fresh, Hhe_eg.
        specialize (Hhe_roots e_alloc).
        specialize (Hhe_fresh e_alloc).
        specialize (Hhe_eg e_alloc).
        destruct (hash_entry succ sort_of [x'] e_alloc) as [tx' e_he] eqn:Heq_he.
        cbn [fst snd] in Hhe_roots, Hhe_fresh, Hhe_eg.
        (* Supply hypotheses to hash_entry_all_roots *)
        assert (Hkeys_he_args : forall y, In y [x'] -> Sep.has_key y (parent (Defs.equiv e_alloc))).
        { intros y Hy. cbn in Hy. destruct Hy as [Hy|]; [|contradiction].
          subst y. exact Hx'_key. }
        specialize (Hhe_roots (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        destruct Hhe_roots as (Huf_he & Hdb_he & Hincl_he & Hmono_he & _).
        (* Supply hypotheses to hash_entry_egraph_ok *)
        specialize (Hhe_eg Hok_eg_alloc Hkeys_he_args).
        destruct Hhe_eg as (Hok_eg_he & Hmono_eg_he & Htx'_key_he).
        (* Apply hash_entry_args_old_keys to get structural info about e_he.db *)
        pose proof (@hash_entry_args_old_keys V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X H lt_asymmetric lt_succ lt_trans
                      (fun s => s <> sort_of) sort_of [x']) as Hhe_old.
        unfold vc in Hhe_old. specialize (Hhe_old e_alloc).
        rewrite Heq_he in Hhe_old. cbn [fst snd] in Hhe_old.
        specialize (Hhe_old (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        (* Supply hypotheses to hash_entry_fresh_rank_zero *)
        assert (Hx'_root_list : all (fun y => map.get (parent (Defs.equiv e_alloc)) y = Some y) [x']).
        { cbn. split; [exact Hx'_root | exact I]. }
        specialize (Hhe_fresh (ex_intro _ _ Hok_alloc) Hx'_root_list Hno_sortof).
        destruct Hhe_fresh as (Htx'_rank0 & Htx'_root & Htx'_fresh & Htx'_atom).
        (* Step 4: union_roots_demote_second *)
        (* t_v is a root in e_he (via Hmono_he from Htv_root in e_sort via Hmono_alloc) *)
        assert (Htv_root_alloc : is_root e_alloc t_v).
        { unfold is_root. exact (Hmono_alloc t_v Htv_root). }
        assert (Htv_root_he : is_root e_he t_v).
        { unfold is_root. exact (Hmono_he t_v (Htv_root_alloc)). }
        (* tx' is a root in e_he *)
        assert (Htx'_root_he : is_root e_he tx').
        { unfold is_root. exact Htx'_root. }
        (* t_v <> tx': t_v has_key in e_alloc, tx' is fresh in e_alloc *)
        assert (Htv_ne_tx' : t_v <> tx').
        { intro Heq. subst t_v.
          apply Htx'_fresh.
          apply is_root_has_key. exact Htv_root_alloc. }
        (* rank tx' = Some 0 in e_he *)
        assert (Hrank_tx' : map.get (@rank _ _ _ (Defs.equiv e_he)) tx' = Some 0).
        { exact Htx'_rank0. }
        (* has_key t_v in e_he (for union_preserves_egraph_ok_sem) *)
        assert (Htv_key_he : Sep.has_key t_v (parent (Defs.equiv e_he))).
        { apply is_root_has_key. exact Htv_root_he. }
        pose proof (@union_roots_demote_second V V_Eqb V_Eqb_ok lt V_default
                      V V_map V_map V_map_ok V_trie X H t_v tx') as Hunion.
        unfold vc in Hunion. specialize (Hunion e_he).
        (* Step 4': union_preserves_egraph_ok_sem on e_he *)
        pose proof (@union_preserves_egraph_ok_sem V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map V_map_ok V_trie X H t_v tx' e_he
                      Hok_eg_he Htv_key_he Htx'_key_he) as Hok_eg_u.
        destruct (Defs.union t_v tx' e_he) as [v_u e_u] eqn:Heq_union.
        cbn [fst snd] in Hunion, Hok_eg_u.
        destruct Huf_he as [roots_he Hroots_he].
        specialize (Hunion roots_he Hroots_he Htv_root_he Htx'_root_he Htv_ne_tx' Hrank_tx').
        destruct Hunion as (Hvu_tv & Htv_root_u & Htx'_demoted_u & Hothers_u
                           & Hdb_u & Hpar_u & [improved Hwl_u] & [roots_u Hroots_u]).
        cbn [fst snd] in *.
        (* Now prove tx' is not an arg of any e_he.db atom (needed for crux) *)
        assert (Htx'_not_arg : forall b, atom_in_db b (Defs.db e_he) -> ~ In tx' (atom_args b)).
        { intros b Hb Hin_tx'.
          (* From hash_entry_args_old_keys: all args of b were has_key in e_alloc *)
          destruct (Hhe_old b Hb) as [Hb_args_old _].
          assert (Htx'_hk : Sep.has_key tx' (parent (Defs.equiv e_alloc))).
          { exact (in_all _ _ _ Hb_args_old Hin_tx'). }
          (* But tx' is fresh in e_alloc — contradiction *)
          exact (Htx'_fresh Htx'_hk). }
        (* Build db_ctx_inv e_u *)
        assert (Hdb_u_inv : db_ctx_inv e_u).
        { unfold db_ctx_inv, db_inv in *.
          intros a Ha.
          rewrite <- Hdb_u in Ha.
          specialize (Hdb_he a Ha).
          destruct Hdb_he as [Hargs_he Hret_he].
          split.
          - (* args: each arg y is root in e_he; y != tx' (Htx'_not_arg); so others_u gives root in e_u *)
            eapply all_wkn; [|exact Hargs_he].
            intros y Hyin Hy_root.
            unfold is_root in Hy_root.
            apply Hothers_u.
            + intro Heq. subst y.
              exact (Htx'_not_arg a Ha Hyin).
            + exact Hy_root.
          - (* ret: a.fn != sort_of -> ret root in e_he -> ret != tx' -> root in e_u *)
            intro HPfn.
            assert (Hret_root : map.get (parent (Defs.equiv e_he)) (atom_ret a) = Some (atom_ret a)).
            { exact (Hret_he HPfn). }
            apply Hothers_u.
            + (* ret != tx' *)
              intro Heq. subst.
              destruct (Hhe_old a Ha) as [_ Ha_old].
              assert (Ha_alloc : atom_in_db a (Defs.db e_alloc)) by (apply Ha_old; exact HPfn).
              unfold db_ctx_inv, db_inv in Hdb_alloc.
              specialize (Hdb_alloc a Ha_alloc).
              destruct Hdb_alloc as [_ Hret_alloc].
              assert (Htx'_hk : Sep.has_key (atom_ret a) (parent (Defs.equiv e_alloc))).
              { unfold Sep.has_key. rewrite (Hret_alloc HPfn). exact I. }
              exact (Htx'_fresh Htx'_hk).
            + exact Hret_root. }
        (* Assemble the 5 conjuncts *)
        split.
        { exact (ex_intro _ roots_u Hroots_u). }
        split.
        { exact Hdb_u_inv. }
        split.
        { (* all-roots ((name,x')::base') in e_u *)
          cbn [all].
          split.
          - (* x' is root in e_u *)
            unfold is_root.
            apply Hothers_u.
            + (* x' != tx' *)
              intro Heq. apply Htx'_fresh.
              rewrite <- Heq. exact Hx'_key.
            + exact (Hmono_he x' Hx'_root).
          - (* all roots in base' (Hall_tail) lifted to e_u *)
            eapply all_wkn; [|exact Hall_tail].
            intros [xn yn] Hyin Hyn_root.
            cbn [snd] in *.
            unfold is_root in *.
            apply Hothers_u.
            + (* yn != tx' *)
              intro Heq. subst yn.
              apply Htx'_fresh.
              apply is_root_has_key.
              unfold is_root.
              exact (Hmono_alloc _ (Hmono_sort _ Hyn_root)).
            + exact (Hmono_he _ (Hmono_alloc _ (Hmono_sort _ Hyn_root))). }
        split.
        { (* map fst ((name,x')::base') = map fst ((name,t)::c') *)
          cbn [map fst]. f_equal. exact Hfst_tail. }
        { (* egraph_ok e_u *)
          exact Hok_eg_u. }
    Qed.

    (* ============================================================== *)
    (* add_open_node_atoms: structural augmentation of add_open_all_  *)
    (* roots that additionally establishes atom_tree.                 *)
    (* ============================================================== *)

    Local Notation equiv_extends_inst e1 e2 :=
      (@equiv_extends V V V_map V_map V_trie X e1 e2).

    (* Explicit parent equation for Defs.alloc: the result's equiv.parent
       is exactly map.put of the input's parent with the fresh node. *)
    Lemma alloc_parent_eq (e_in : instance X) :
      let r_pair := Defs.alloc V succ V V_map V_map V_trie X e_in in
      parent (Defs.equiv (snd r_pair)) =
      map.put (parent (Defs.equiv e_in)) (fst r_pair) (fst r_pair).
    Proof.
      unfold Defs.alloc.
      destruct (UnionFind.alloc V _ _ succ (Defs.equiv e_in)) as [uf' r'] eqn:Halloc.
      cbn [fst snd Defs.equiv].
      unfold UnionFind.alloc in Halloc.
      destruct (Defs.equiv e_in) as [rk pa mr nx] eqn:Heq.
      cbn [parent UnionFind.next] in *.
      injection Halloc as H1 H2. subst.
      cbn [parent]. reflexivity.
    Qed.

    (* Same for alloc_opaque: only analyses differs from alloc, equiv.parent
       is the same map.put computation. *)
    Lemma alloc_opaque_parent_eq (e_in : instance X) :
      let r_pair := Defs.alloc_opaque V succ V V_map V_map V_trie X e_in in
      parent (Defs.equiv (snd r_pair)) =
      map.put (parent (Defs.equiv e_in)) (fst r_pair) (fst r_pair).
    Proof.
      unfold Defs.alloc_opaque.
      destruct (UnionFind.alloc V _ _ succ (Defs.equiv e_in)) as [uf' r'] eqn:Halloc.
      cbn [fst snd Defs.equiv].
      unfold UnionFind.alloc in Halloc.
      destruct (Defs.equiv e_in) as [rk pa mr nx] eqn:Heq.
      cbn [parent UnionFind.next] in *.
      injection Halloc as H1 H2. subst.
      cbn [parent]. reflexivity.
    Qed.

    (* hash_entry preserves all existing uf_rel_PER pairs (equiv_extends).
       Proof: list_Mmap find (fields_preserved -> equiv iff2) + alloc (fresh
       node -> uf_rel_PER_alloc_monotone via alloc_parent_eq) + db_set
       (equiv unchanged). *)
    Lemma hash_entry_equiv_extends f args
      : vc (hash_entry succ f args)
          (fun (e_in : instance X) res =>
             (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
             (forall x, In x args -> Sep.has_key x (parent (Defs.equiv e_in))) ->
             equiv_extends_inst e_in (snd res)).
    Proof.
      unfold hash_entry, vc. intros e_in.
      cbn [Mbind StateMonad.state_monad].
      pose proof (@list_Mmap_find_preserves_fields_strong V V_Eqb V_Eqb_ok lt succ V_default
                    V V_map V_map V_map_ok V_trie X args) as Hfp_vc.
      unfold vc in Hfp_vc. specialize (Hfp_vc e_in).
      intros Huf_ex Hkeys.
      destruct Huf_ex as [roots Huf].
      assert (Hkeys_all : all (fun i => Sep.has_key i (parent (Defs.equiv e_in))) args).
      { clear -Hkeys. induction args as [|x xs IH]; cbn; auto.
        split; [apply Hkeys; left; reflexivity
               | apply IH; intros y Hy; apply Hkeys; right; exact Hy]. }
      specialize (Hfp_vc (ex_intro _ roots Huf) Hkeys_all).
      destruct (list_Mmap find args e_in) as [args' e_post_find] eqn:Hmap.
      cbn [fst snd] in Hfp_vc |- *.
      destruct Hfp_vc as (Huf_post & Hfp & _).
      assert (Hext1 : equiv_extends_inst e_in e_post_find).
      { exact (@fields_preserved_equiv_extends V V V_map V_map V_trie X e_in e_post_find Hfp). }
      pose proof (@db_lookup_pure V V V_map V_map V_trie X f args') as Hlk_pure.
      unfold vc in Hlk_pure. specialize (Hlk_pure e_post_find).
      destruct (db_lookup V V V_map V_map V_trie X f args' e_post_find) as [mout e_lk] eqn:Hlk.
      cbn [fst snd] in Hlk_pure. destruct Hlk_pure as [He_eq _]. subst e_lk.
      destruct mout as [r|]; cbn beta iota; cbn [fst snd].
      - (* hit: no state change *)
        unfold Mret. cbn [fst snd StateMonad.state_monad]. exact Hext1.
      - (* miss: alloc + db_set *)
        cbn [Mbind StateMonad.state_monad].
        pose proof (alloc_parent_eq e_post_find) as Hpar.
        cbn [fst snd] in Hpar.
        destruct (Defs.alloc V succ V V_map V_map V_trie X e_post_find) as [r_new e_alloc] eqn:Halloc.
        cbn [fst snd] in Hpar |- *.
        pose proof (@alloc_struct V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X
                      lt_asymmetric lt_succ lt_trans) as Halloc_s.
        unfold vc in Halloc_s. specialize (Halloc_s e_post_find).
        rewrite Halloc in Halloc_s. cbn [fst snd] in Halloc_s.
        destruct Huf_post as [roots_post Huf_post_ok].
        specialize (Halloc_s roots_post Huf_post_ok).
        destruct Halloc_s as (_ & Hr_fresh & _ & _ & _ & _ & _).
        assert (Hnone_r : map.get (parent (Defs.equiv e_post_find)) r_new = None).
        { unfold Sep.has_key in Hr_fresh.
          destruct (map.get (parent (Defs.equiv e_post_find)) r_new); tauto. }
        assert (Hext2 : equiv_extends_inst e_post_find e_alloc).
        { unfold equiv_extends, uf_rel_PER. intros i j Hpre.
          rewrite Hpar. eapply uf_rel_PER_alloc_monotone;
            [exact V_map_ok | exact Hnone_r | unfold uf_rel_PER; exact Hpre]. }
        cbn [Mbind StateMonad.state_monad fst snd].
        unfold db_set. cbn [atom_fn atom_args atom_ret].
        cbn [Mbind StateMonad.state_monad fst snd].
        pose proof (@get_analyses_preserves_fields V lt succ V_default V V_map V_map V_trie X H
                      args' e_alloc) as Hga.
        cbn [fst snd] in Hga.
        destruct (get_analyses V V V_map V_map V_trie X args' e_alloc) as [arg_as e_ga] eqn:Hge.
        cbn [fst snd] in Hga. destruct Hga as (Hdb_ga & Heq_ga & _).
        destruct (update_analyses V V V_map V_map V_trie X r_new
                    (analyze V V X (Build_atom f args' r_new) arg_as) e_ga)
          as [_u e_ua] eqn:Hue.
        assert (Heq_ua : Defs.equiv e_ua = Defs.equiv e_ga).
        { unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; reflexivity. }
        destruct (db_set' V V_Eqb V V_map V_map V_trie X (Build_atom f args' r_new)
                    (analyze V V X (Build_atom f args' r_new) arg_as) e_ua) as [_v e_db] eqn:Hde.
        assert (Heq_db : Defs.equiv e_db = Defs.equiv e_alloc).
        { assert (Hdb_eq : Defs.equiv e_db = Defs.equiv e_ua)
            by (unfold db_set' in Hde; injection Hde as _ Hde'; subst e_db; reflexivity).
          rewrite Hdb_eq, Heq_ua. exact Heq_ga. }
        cbn [Mret StateMonad.state_monad fst snd].
        eapply (@equiv_extends_trans V V V_map V_map V_trie X); [exact Hext1 |].
        eapply (@equiv_extends_trans V V V_map V_map V_trie X); [exact Hext2 |].
        unfold equiv_extends, uf_rel_PER. intros i j Hpre.
        rewrite Heq_db. exact Hpre.
    Qed.

    Definition open_atomtree_post (e0 : term) (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) -> db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      roots_env e_in (snd res) /\ is_root (snd res) (fst res)
      /\ atom_tree X (snd res) sub e0 (fst res)
      /\ equiv_extends_inst e_in (snd res).

    Definition open_atomtree_args_post (es : list term) (sub : named_list V) (e_in : instance X)
       (res : list V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) -> db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      roots_env e_in (snd res) /\ all (is_root (snd res)) (fst res)
      /\ Forall2 (atom_tree X (snd res) sub) es (fst res)
      /\ equiv_extends_inst e_in (snd res).

    Lemma add_open_node_atoms (l1 : lang)
      (add_open_sort_inner : named_list V -> Term.sort V -> state (instance X) V)
      (Hwf1 : wf_lang l1) (Hl1 : incl l1 l)
      c (Hctx : wf_ctx l1 c)
      : (forall e t, wf_term l1 c e t -> forall r, map fst c = map fst r ->
           vc (add_open_term' succ sort_of l false false add_open_sort_inner r e)
              (open_atomtree_post e r))
        /\ (forall args c', wf_args l1 c args c' -> forall r, map fst c = map fst r ->
           vc (list_Mmap (add_open_term' succ sort_of l false false add_open_sort_inner r) args)
              (open_atomtree_args_post args r)).
    Proof.
      apply (WfCutElim.wf_cut_ind V l1 c
               (fun e t => forall r, map fst c = map fst r ->
                  vc (add_open_term' succ sort_of l false false
                                     add_open_sort_inner r e)
                     (open_atomtree_post e r))
               (fun args c' => forall r, map fst c = map fst r ->
                  vc (list_Mmap (add_open_term' succ sort_of l false false
                                                add_open_sort_inner r) args)
                     (open_atomtree_args_post args r))).
      - (* con case *)
        intros name c'_rule args t_rule s' Hrule_in_l1 Hwf_args_inner IH r Hmaps.
        cbn [add_open_term'].
        pose proof (Hl1 _ Hrule_in_l1) as Hrule_in.
        assert (Hlk : named_list_lookup_err l name = Some (term_rule c'_rule args t_rule)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad Mret].
        eapply vc_bind.
        { specialize (IH r Hmaps). apply IH. }
        intros e_pre a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_atomtree_post.
        intros Huf Hdbr Hsub.
        unfold open_atomtree_args_post in Hpost_args.
        specialize (Hpost_args Huf Hdbr Hsub).
        destruct Hpost_args as (Henv_args & Hroots_aout & Htrees_aout & Hext_args).
        pose proof Henv_args as Henv_args_save.
        destruct Henv_args as (Huf_inner & Hdbr_inner & Hincl_inner & Hmono_inner).
        assert (Hkeys : forall x, In x a_out ->
                          Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. apply is_root_has_key.
          exact (in_all _ _ _ Hroots_aout Hx). }
        assert (Hname_sof : name <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hrule_in. }
        (* hash_entry_all_roots: roots + db_inv survive *)
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans name a_out) as Hhe.
        unfold vc in Hhe.
        specialize (Hhe e_inner Huf_inner Hdbr_inner Hkeys).
        (* hash_entry_equiv_extends: equiv_extends e_inner e_he *)
        pose proof (hash_entry_equiv_extends name a_out) as Hhe_ext.
        unfold vc in Hhe_ext.
        specialize (Hhe_ext e_inner Huf_inner Hkeys).
        destruct (hash_entry succ name a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe, Hhe_ext.
        destruct Hhe as (Huf_f & Hdbr_f & Hincl_f & Hmono_f & Hres_f).
        (* hash_entry_output_atom: the node atom (name, a_out, x_res) is in e_he.db *)
        pose proof (@hash_entry_output_atom V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans name a_out) as Hout.
        unfold vc in Hout.
        specialize (Hout e_inner).
        rewrite Heqhe in Hout.
        cbn [fst snd] in Hout.
        specialize (Hout Huf_inner).
        assert (Hroots_all : all (fun x => map.get (parent (Defs.equiv e_inner)) x = Some x) a_out).
        { eapply all_wkn; [|exact Hroots_aout].
          intros x _ Hx. unfold is_root in Hx. exact Hx. }
        specialize (Hout Hroots_all).
        (* Hout : atom_in_db (Build_atom name a_out x_res) e_he.(db) *)
        unfold atom_in_egraph in *.
        cbn [Mret StateMonad.state_monad fst snd].
        split.
        + eapply roots_env_trans; [exact Henv_args_save|].
          unfold roots_env, db_incl, roots_mono.
          split; [exact Huf_f|]. split; [exact Hdbr_f|]. split; auto.
        + split.
          * apply Hres_f. exact Hname_sof.
          * split.
            -- (* atom_tree e_he r (con name s') x_res *)
              assert (Htrees_he : Forall2 (atom_tree X e_he r) s' a_out).
              { clear -Htrees_aout Hincl_f.
                eapply Forall2_impl; [| exact Htrees_aout].
                intros a b Hab. eapply (atom_tree_db_incl X); [exact Hincl_f | exact Hab]. }
              refine (at_con X e_he r name s' a_out x_res Htrees_he Hout).
            -- (* equiv_extends e_pre e_he: compose Hext_args + Hhe_ext *)
              eapply (@equiv_extends_trans V V V_map V_map V_trie X);
                [exact Hext_args | exact Hhe_ext].
      - (* var case *)
        intros n t_var Hin_var r Hmaps.
        cbn [add_open_term'].
        unfold vc. intros e_pre.
        cbn [Mret StateMonad.state_monad fst snd].
        unfold open_atomtree_post.
        intros Huf Hdbr Hsub.
        split; [apply roots_env_refl; auto|].
        assert (Hafc : all_fresh c) by basic_core_crush.
        assert (Hafr : all_fresh r).
        { apply NoDup_fresh. rewrite <- Hmaps. apply NoDup_fresh; exact Hafc. }
        assert (Hex_x : exists x_n, In (n, x_n) r).
        { apply pair_fst_in_exists. rewrite <- Hmaps. eapply pair_fst_in; exact Hin_var. }
        destruct Hex_x as [x_n Hin_xn].
        assert (Hlk : named_list_lookup default r n = x_n).
        { clear -V_Eqb_ok Hafr Hin_xn.
          induction r as [|[m v_m] r' IH]; cbn in *; [tauto|].
          destruct Hafr as [Hfr Hafr'].
          destruct Hin_xn as [Heq|Hin_xn'].
          - inversion Heq; subst.
            eqb_case n n; congruence.
          - eqb_case n m.
            + exfalso. apply Hfr. eapply pair_fst_in; exact Hin_xn'.
            + apply IH; auto. }
        split.
        + cbn [fst snd]. rewrite Hlk. exact (in_all _ _ _ Hsub Hin_xn).
        + split.
          * cbn [fst snd]. apply (at_var X e_pre r n).
          * (* equiv_extends e_pre e_pre: reflexivity *)
            apply (@equiv_extends_refl V V V_map V_map V_trie X).
      - (* eq_sort conversion *)
        intros e_x t_x t_x' Hwft IH_term Heq_sort r Hmaps.
        apply IH_term; assumption.
      - (* nil args *)
        intros r Hmaps.
        cbn [list_Mmap].
        unfold vc, Mret. cbn.
        unfold open_atomtree_args_post. intros Huf Hdbr Hsub.
        split; [apply roots_env_refl; auto|].
        split; [cbn; exact I|]. split; [constructor|].
        apply (@equiv_extends_refl V V V_map V_map V_trie X).
      - (* cons args *)
        intros c'_arg es Hwf_args IH_args name_arg t_arg e_arg Hwft IH_term r Hmaps.
        unfold vc. intros e_in.
        cbn [list_Mmap].
        cbn [Mbind Mret StateMonad.state_monad].
        unfold open_atomtree_args_post.
        intros Huf Hdbr Hsub.
        specialize (IH_term r Hmaps).
        unfold vc, open_atomtree_post in IH_term.
        specialize (IH_term e_in Huf Hdbr Hsub).
        destruct (add_open_term' succ sort_of l false false
                    add_open_sort_inner r e_arg e_in)
          as [v_head e_after_head] eqn:Heq1.
        cbn [fst snd] in IH_term.
        destruct IH_term as (Henv_head & Hroot_head & Htree_head & Hext_head).
        pose proof Henv_head as Henv_head_save.
        destruct Henv_head as (Huf_head & Hdbr_head & Hincl_head & Hmono_head).
        specialize (IH_args r Hmaps).
        unfold vc, open_atomtree_args_post in IH_args.
        assert (Hsub_head : all (fun p => is_root e_after_head (snd p)) r).
        { eapply all_wkn; [|exact Hsub].
          intros x Hx Hr. apply Hmono_head. exact Hr. }
        specialize (IH_args e_after_head Huf_head Hdbr_head Hsub_head).
        destruct (list_Mmap
                    (add_open_term' succ sort_of l false false
                       add_open_sort_inner r) es e_after_head)
          as [v_tail e_final] eqn:Heq2.
        cbn [fst snd] in IH_args.
        destruct IH_args as (Henv_tail & Hroots_tail & Htrees_tail & Hext_tail).
        pose proof Henv_tail as Henv_tail_save.
        destruct Henv_tail as (Huf_tail & Hdbr_tail & Hincl_tail & Hmono_tail).
        split.
        + eapply roots_env_trans; eauto.
        + split.
          * cbn [all]. split.
            -- apply Hmono_tail. exact Hroot_head.
            -- exact Hroots_tail.
          * split.
            -- constructor.
               ++ (* lift head atom_tree through tail's db_incl *)
                  unfold db_incl in Hincl_tail.
                  eapply (atom_tree_db_incl X); [exact Hincl_tail | exact Htree_head].
               ++ exact Htrees_tail.
            -- (* equiv_extends: compose head + tail *)
               eapply (@equiv_extends_trans V V V_map V_map V_trie X);
                 [exact Hext_head | exact Hext_tail].
    Qed.

    Definition open_atomtree_sort_post (ts : sort) (sub : named_list V) (e_in : instance X)
       (res : V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) -> db_ctx_inv e_in ->
      all (fun p => is_root e_in (snd p)) sub ->
      roots_env e_in (snd res) /\ is_root (snd res) (fst res)
      /\ atom_tree_sort X (snd res) sub ts (fst res)
      /\ equiv_extends_inst e_in (snd res).

    Lemma add_open_sort'_node_atoms l1 c r t fuel
      : wf_lang l1 ->
        length l1 < fuel ->
        incl l1 l ->
        wf_ctx l1 c ->
        wf_sort l1 c t ->
        map fst c = map fst r ->
        vc (add_open_sort' succ sort_of l false false fuel r t)
           (open_atomtree_sort_post t r).
    Proof.
      revert l1 c r t.
      induction fuel; intros l1 c r t Hwfl1 Hflen Hincl Hctx Hsort Hmaps.
      - exfalso. Lia.lia.
      - cbn [add_open_sort'].
        destruct t as [n s_t].
        pose proof Hsort as Hsort'.
        inversion Hsort' as [? n_ s_t_ args c' Hrule Hwfargs]; subst.
        apply Hincl in Hrule.
        assert (Hlk : named_list_lookup_err l n = Some (sort_rule c' args)).
        { symmetry. apply all_fresh_named_list_lookup_err_in; auto.
          basic_core_crush. }
        rewrite Hlk.
        cbn [Mbind StateMonad.state_monad].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        eapply vc_bind.
        { apply (proj2 (add_open_node_atoms l1
                          (add_open_sort' succ sort_of l false false fuel)
                          Hwfl1 Hincl c Hctx)
                  _ _ Hwfargs r Hmaps). }
        intros e_post a_out.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Hpost_args.
        unfold open_atomtree_sort_post.
        intros Huf Hdbr Hsub.
        unfold open_atomtree_args_post in Hpost_args.
        specialize (Hpost_args Huf Hdbr Hsub).
        destruct Hpost_args as (Henv_args & Hroots_aout & Htrees_aout & Hext_args).
        pose proof Henv_args as Henv_args_save.
        destruct Henv_args as (Huf_inner & Hdbr_inner & Hincl_inner & Hmono_inner).
        assert (Hkeys : forall x, In x a_out ->
                          Sep.has_key x (parent (Defs.equiv e_inner))).
        { intros x Hx. apply is_root_has_key.
          exact (in_all _ _ _ Hroots_aout Hx). }
        assert (Hname_sof : n <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hrule. }
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans n a_out) as Hhe.
        unfold vc in Hhe.
        specialize (Hhe e_inner Huf_inner Hdbr_inner Hkeys).
        (* hash_entry_equiv_extends: equiv_extends e_inner e_he *)
        pose proof (hash_entry_equiv_extends n a_out) as Hhe_ext.
        unfold vc in Hhe_ext.
        specialize (Hhe_ext e_inner Huf_inner Hkeys).
        destruct (hash_entry succ n a_out e_inner) as [x_res e_he] eqn:Heqhe.
        cbn [fst snd] in Hhe, Hhe_ext.
        destruct Hhe as (Huf_f & Hdbr_f & Hincl_f & Hmono_f & Hres_f).
        (* hash_entry_output_atom: the node atom (n, a_out, x_res) is in e_he.db *)
        pose proof (@hash_entry_output_atom V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _
                      lt_asymmetric lt_succ lt_trans n a_out) as Hout.
        unfold vc in Hout.
        specialize (Hout e_inner).
        rewrite Heqhe in Hout.
        cbn [fst snd] in Hout.
        specialize (Hout Huf_inner).
        assert (Hroots_all : all (fun x => map.get (parent (Defs.equiv e_inner)) x = Some x) a_out).
        { eapply all_wkn; [|exact Hroots_aout].
          intros x _ Hx. unfold is_root in Hx. exact Hx. }
        specialize (Hout Hroots_all).
        unfold atom_in_egraph in *.
        cbn [Mret StateMonad.state_monad fst snd].
        split.
        + eapply roots_env_trans; [exact Henv_args_save|].
          unfold roots_env, db_incl, roots_mono.
          split; [exact Huf_f|]. split; [exact Hdbr_f|]. split; auto.
        + split.
          * apply Hres_f. exact Hname_sof.
          * split.
            -- (* atom_tree_sort X e_he r (scon n s_t) x_res *)
              assert (Htrees_he : Forall2 (atom_tree X e_he r) s_t a_out).
              { clear -Htrees_aout Hincl_f.
                eapply Forall2_impl; [| exact Htrees_aout].
                intros a b Hab. eapply (atom_tree_db_incl X); [exact Hincl_f | exact Hab]. }
              unfold atom_tree_sort.
              exists a_out. split; [exact Htrees_he | exact Hout].
            -- (* equiv_extends: compose Hext_args + Hhe_ext *)
              eapply (@equiv_extends_trans V V V_map V_map V_trie X);
                [exact Hext_args | exact Hhe_ext].
    Qed.

    Lemma add_open_sort_node_atoms c r t
      : wf_ctx l c ->
        wf_sort l c t ->
        map fst c = map fst r ->
        vc (add_open_sort succ sort_of l false false r t)
           (open_atomtree_sort_post t r).
    Proof.
      intros.
      unfold add_open_sort.
      eapply add_open_sort'_node_atoms; try eassumption; eauto with utils.
    Qed.

    (* ============================================================== *)
    (* atom_tree survives rebuild (the F1c-gated CONNECTION for P2).   *)
    (* ============================================================== *)
    (* The node atoms of an [atom_tree] built in the pre-rebuild       *)
    (* assumption egraph [e] are FULLY canonical DAG (constructor)     *)
    (* atoms: [db_ctx_inv e] makes their args roots, and their head    *)
    (* symbol [n <> sort_of] (every constructor name is in [l], and    *)
    (* [fresh sort_of l]) makes their ret a root too.  Such atoms       *)
    (* survive [rebuild] (the [L_survive_canonical] kernel — the one    *)
    (* intentional axiom).  We abstract the survival fact as the        *)
    (* hypothesis [Hsurv] (a guarded db-inclusion) so this lemma stays  *)
    (* model-free and 0-axiom; the P3 caller discharges [Hsurv] from    *)
    (* [L_survive_canonical] in a model-aware context.  This            *)
    (* generalises [atom_tree_db_incl] (whose inclusion is              *)
    (* unconditional) to a canonical-only inclusion.                    *)

    Local Notation ain a e := (@atom_in_egraph V V V_map V_map V_trie X a e).

    Lemma atom_tree_args_survives (e eF : instance X) (sub : named_list V)
      (c c' : ctx) (s : list term)
      (Hwfa : wf_args l c s c')
      (IHs : all (fun e0 => forall t, wf_term l c e0 t ->
                   forall xe, atom_tree X e sub e0 xe ->
                              atom_tree X eF sub e0 xe) s)
      : forall sids, Forall2 (atom_tree X e sub) s sids ->
                     Forall2 (atom_tree X eF sub) s sids.
    Proof.
      revert IHs; induction Hwfa; intros IHs sids Htrees.
      - safe_invert Htrees. constructor.
      - safe_invert Htrees.
        destruct IHs as [IHe IHs0].
        constructor.
        + eapply IHe; eauto.
        + eapply IHHwfa; eauto.
    Qed.

    Lemma atom_tree_survives (e eF : instance X) (sub : named_list V) (c : ctx)
      (Hdbi : db_ctx_inv e)
      (Hsurv : forall a, ain a e ->
                 all (is_root e) a.(atom_args) ->
                 is_root e a.(atom_ret) ->
                 ain a eF)
      : forall e0 t, wf_term l c e0 t ->
          forall xe, atom_tree X e sub e0 xe -> atom_tree X eF sub e0 xe.
    Proof.
      intro e0; induction e0 as [x | n s IHs] using term_ind; intros t Hwt xe Htree.
      - safe_invert Htree. constructor.
      - safe_invert Htree.
        apply WfCutElim.invert_wf_term_con in Hwt.
        destruct Hwt as (c'0 & args0 & t' & Hin & Hwfa & _).
        assert (Hn : n <> sort_of).
        { intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hin. }
        assert (IHsall : all (fun e0 => forall t, wf_term l c e0 t ->
                                forall xe, atom_tree X e sub e0 xe ->
                                           atom_tree X eF sub e0 xe) s).
        { clear -IHs. induction s as [|e1 s0 IH]; cbn; [exact I|].
          destruct IHs as [IHe1 IHs0]. split; [exact IHe1 | apply IH; exact IHs0]. }
        match goal with
          Htrees : Forall2 (atom_tree X e sub) s ?sids,
          Hatom : atom_in_egraph (Build_atom n ?sids xe) e |- _ =>
            pose proof (Hdbi _ Hatom) as Hroots;
            cbn [atom_args atom_ret atom_fn] in Hroots;
            destruct Hroots as [Hargs_r Hret_r];
            eapply at_con;
              [ eapply atom_tree_args_survives with (c:=c) (c':=c'0); eauto
              | eapply Hsurv;
                [ exact Hatom
                | cbn [atom_args]; exact Hargs_r
                | cbn [atom_ret]; apply Hret_r; exact Hn ] ]
        end.
    Qed.

    Lemma atom_tree_sort_survives (e eF : instance X) (sub : named_list V) (c : ctx)
      (Hdbi : db_ctx_inv e)
      (Hsurv : forall a, ain a e ->
                 all (is_root e) a.(atom_args) ->
                 is_root e a.(atom_ret) ->
                 ain a eF)
      : forall ts, wf_sort l c ts ->
          forall xs, atom_tree_sort X e sub ts xs -> atom_tree_sort X eF sub ts xs.
    Proof.
      intros [n s] Hws xs Htree.
      unfold atom_tree_sort in *.
      destruct Htree as (sids & Htrees & Hatom).
      safe_invert Hws.
      match goal with
        Hin : In (n, sort_rule ?c'0 ?args0) l,
        Hwfa : Model.wf_args _ s ?c'0 |- _ =>
          assert (Hn : n <> sort_of);
            [ intro Heq; apply Hsof; rewrite <- Heq; eapply pair_fst_in; exact Hin |];
          exists sids; split;
            [ eapply atom_tree_args_survives with (c:=c) (c':=c'0); try eassumption
            | ]
      end.
      2:{ pose proof (Hdbi _ Hatom) as Hroots.
          cbn [atom_args atom_ret atom_fn] in Hroots.
          destruct Hroots as [Hargs_r Hret_r].
          eapply Hsurv;
            [ exact Hatom
            | cbn [atom_args]; exact Hargs_r
            | cbn [atom_ret]; apply Hret_r; exact Hn ]. }
      (* IHsall for the args: each arg term survives *)
      assert (HP : forall e0 t, wf_term l c e0 t ->
                     forall xe, atom_tree X e sub e0 xe -> atom_tree X eF sub e0 xe).
      { intros; eapply atom_tree_survives with (c:=c); eauto. }
      clear -HP s.
      induction s as [|e1 s0 IH]; cbn; [exact I|].
      split; [exact (HP e1) | exact IH].
    Qed.

    (* ============================================================== *)
    (* add_ctx readback characterization (the P3 (I)-inversion gate). *)
    (* ============================================================== *)
    (* Pre-rebuild structural characterization of the [add_ctx] output. *)
    (* For each ctx var [(x,t)] with [add_ctx]'s allocated companion id  *)
    (* [x'] (so [(x,x') ∈ sub]), the pre-rebuild assumption egraph [e1]:  *)
    (*   - contains a [sort_of([x']) -> _] atom (the per-var sort slot),   *)
    (*   - has [atom_tree_sort e1 sub' t xs] for some root [xs] (the       *)
    (*     structural witness that the sort id [xs] denotes [t] under any  *)
    (*     leaf-faithful adversary), where [sub'] is the tail of [sub]     *)
    (*     (aligned with [c'], the prefix in which [t] is well-formed).    *)
    (* This is what P3 feeds to [atom_tree_sort_to_represents_sort] +      *)
    (* [add_open_faithful_rep_sort] to build [σ_a] and [wf_subst].  The    *)
    (* equiv connection [sort_of ret ~ xs] (the rebuild canonicalisation)  *)
    (* is the F1c-gated part and is recovered at the P3 assembly site, not *)
    (* here, so this lemma stays model-free and 0-axiom (lifting is pure   *)
    (* [db_incl]/[roots_mono] monotonicity). *)
    (* db-monotonicity for the sort skeleton (sort version of
       [atom_tree_db_incl]). *)
    Lemma atom_tree_sort_db_incl (e1 e2 : instance X) (sub : named_list V)
      : (forall a, ain a e1 -> ain a e2) ->
        forall ts xs, atom_tree_sort X e1 sub ts xs -> atom_tree_sort X e2 sub ts xs.
    Proof.
      intros Hincl [n s] xs Htree.
      unfold atom_tree_sort in *.
      destruct Htree as (sids & Htrees & Hatom).
      exists sids. split.
      - eapply Forall2_impl; [|exact Htrees].
        intros a b Hab. eapply (atom_tree_db_incl X); [exact Hincl | exact Hab].
      - apply Hincl. exact Hatom.
    Qed.

    Fixpoint ctx_readback (e1 : instance X) (sub : named_list V) (c0 : ctx)
      {struct c0} : Prop :=
      match c0 with
      | [] => True
      | (x,t)::c' =>
          match sub with
          | [] => False
          | (_, x')::sub' =>
              (exists xs, is_root e1 xs /\ atom_tree_sort X e1 sub' t xs
                       /\ exists tx', atom_in_db (Build_atom sort_of [x'] tx') (Defs.db e1)
                                   /\ uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e1) tx' xs)
              /\ ctx_readback e1 sub' c'
          end
      end.

    (* [ctx_readback] is monotone in the egraph: it survives [db_incl],
       [roots_mono], and [uf_rel_PER] monotonicity (equiv_extends). *)
    Lemma ctx_readback_mono (e1 e2 : instance X) (sub : named_list V) (c0 : ctx)
      : (forall a, atom_in_db a (Defs.db e1) -> atom_in_db a (Defs.db e2)) ->
        roots_mono e1 e2 ->
        (forall i j, uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e1) i j ->
                     uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e2) i j) ->
        ctx_readback e1 sub c0 -> ctx_readback e2 sub c0.
    Proof.
      revert sub; induction c0 as [|[x t] c' IH]; intros sub Hincl Hmono Hequiv Hrb.
      - exact I.
      - destruct sub as [|[x0 x'] sub']; [exact Hrb|].
        cbn in Hrb |- *.
        destruct Hrb as [ [xs Hxs] Hrb'].
        destruct Hxs as (Hxs_root & Htree & tx' & Hatom & Hper).
        split; [|eapply IH; eauto].
        exists xs. split.
        + exact (Hmono xs Hxs_root).
        + split.
          * eapply atom_tree_sort_db_incl; [exact Hincl | exact Htree].
          * exists tx'. split.
            -- exact (Hincl _ Hatom).
            -- exact (Hequiv _ _ Hper).
    Qed.

    (* Combined post: [ctx_roots_post]'s 4 conjuncts plus [ctx_readback]. *)
    Definition ctx_readback_post (c0 : ctx) (e_in : instance X)
        (res : named_list V * instance X) : Prop :=
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      db_ctx_inv e_in ->
      (exists roots, union_find_ok lt (Defs.equiv (snd res)) roots)
      /\ db_ctx_inv (snd res)
      /\ all (fun p => is_root (snd res) (snd p)) (fst res)
      /\ map fst (fst res) = map fst c0
      /\ ctx_readback (snd res) (fst res) c0.

    Lemma add_ctx_readback c
      : wf_ctx l c ->
        vc (add_ctx succ sort_of l false false c) (ctx_readback_post c).
    Proof.
      intros Hctx.
      unfold add_ctx.
      induction c as [|[name t] c' IH].
      - (* nil case *)
        cbn [list_Mfoldr].
        unfold vc, Mret. cbn [StateMonad.state_monad].
        unfold ctx_readback_post.
        intros e_in Hok Hdb.
        cbn [fst snd].
        split; [exact Hok|].
        split; [exact Hdb|].
        split; [cbn; exact I|].
        split; [cbn; reflexivity|].
        cbn. exact I.
      - (* cons case *)
        cbn [list_Mfoldr].
        eapply vc_bind.
        { apply IH. inversion Hctx; assumption. }
        intros e_pre base'.
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Htail.
        unfold ctx_readback_post.
        intros Hok Hdb.
        unfold ctx_readback_post in Htail.
        assert (Hwfc' : wf_ctx l c') by (inversion Hctx; assumption).
        assert (Hwfst : wf_sort l c' t) by (inversion Hctx; assumption).
        specialize (Htail Hok Hdb).
        destruct Htail as (Huf_tail & Hdb_tail & Hall_tail & Hfst_tail & Hrb_tail).
        (* Step 1: add_open_sort_node_atoms (gives roots_env + atom_tree + equiv_extends) *)
        assert (Hmaps : map fst c' = map fst base') by (symmetry; exact Hfst_tail).
        pose proof (add_open_sort_node_atoms c' base' t Hwfc' Hwfst Hmaps) as Hnode_sort.
        unfold vc in Hnode_sort. specialize (Hnode_sort e_inner).
        unfold open_atomtree_sort_post in Hnode_sort.
        destruct (add_open_sort succ sort_of l false false base' t e_inner)
          as [t_v e_sort] eqn:Heq_sort.
        cbn [fst snd] in Hnode_sort.
        specialize (Hnode_sort Huf_tail Hdb_tail Hall_tail).
        destruct Hnode_sort as (Henv_sort & Htv_root & Htree_sort & Hext_sort).
        destruct Henv_sort as (Huf_sort & Hdb_sort & Hincl_sort & Hmono_sort).
        (* Step 2: alloc_opaque_rank_zero *)
        pose proof (@alloc_opaque_rank_zero V V_Eqb V_Eqb_ok lt succ
                      V V_map V_map V_map_ok V_trie X H
                      lt_asymmetric lt_succ lt_trans)
          as Halloc.
        unfold vc in Halloc. specialize (Halloc e_sort).
        destruct (alloc_opaque V succ V V_map V_map V_trie X e_sort) as [x' e_alloc] eqn:Heq_alloc.
        cbn [fst snd] in Halloc.
        destruct Huf_sort as [roots_s Hroots_s].
        specialize (Halloc roots_s Hroots_s).
        destruct Halloc as (Hok_alloc & Hfresh_x' & Hx'_root & Hx'_rank0
                           & Hkeys_alloc & Hmono_alloc & Hdb_alloc_eq
                           & Hpar_alloc & Hwl_alloc).
        cbn [fst snd] in *.
        (* Derive db_ctx_inv e_alloc from db_ctx_inv e_sort + db unchanged *)
        assert (Hdb_alloc : db_ctx_inv e_alloc).
        { unfold db_ctx_inv, db_inv in *.
          intros a Ha.
          rewrite <- Hdb_alloc_eq in Ha.
          specialize (Hdb_sort a Ha).
          destruct Hdb_sort as [Hargs_roots Hret_root].
          split.
          - eapply all_wkn; [|exact Hargs_roots].
            intros z _ Hz. exact (Hmono_alloc z Hz).
          - intro HPfn. exact (Hmono_alloc _ (Hret_root HPfn)). }
        (* Steps 3a and 3b: hash_entry_all_roots + hash_entry_fresh_rank_zero *)
        (* Prove x' is a key in e_alloc (it's a root) *)
        assert (Hx'_key : Sep.has_key x' (parent (Defs.equiv e_alloc))).
        { apply is_root_has_key. unfold is_root. exact Hx'_root. }
        (* Prove no (sort_of,[x'],r) atom in e_alloc.db *)
        assert (Hno_sortof : forall r, ~ atom_in_db (Build_atom sort_of [x'] r) e_alloc.(Defs.db)).
        { intros r Hin.
          (* e_alloc.db = e_sort.db *)
          rewrite <- Hdb_alloc_eq in Hin.
          (* by db_ctx_inv e_sort, x' is a root in e_sort *)
          unfold db_ctx_inv, db_inv in Hdb_sort.
          specialize (Hdb_sort (Build_atom sort_of [x'] r) Hin).
          destruct Hdb_sort as [Hargs_s _].
          cbn [atom_args] in Hargs_s.
          destruct Hargs_s as [Hx'_s _].
          (* x' is a root in e_sort => has_key x' e_sort *)
          assert (Hx'_ks : Sep.has_key x' (parent (Defs.equiv e_sort))).
          { apply is_root_has_key. unfold is_root. exact Hx'_s. }
          (* but alloc_opaque says x' is fresh in e_sort *)
          exact (Hfresh_x' Hx'_ks). }
        (* Apply hash_entry_all_roots *)
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ (fun s => s <> sort_of)
                      lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_roots.
        (* Apply hash_entry_fresh_rank_zero *)
        pose proof (@hash_entry_fresh_rank_zero V V_Eqb V_Eqb_ok lt succ V_default
                      V V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X H
                      lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_fresh.
        unfold vc in Hhe_roots, Hhe_fresh.
        specialize (Hhe_roots e_alloc).
        specialize (Hhe_fresh e_alloc).
        destruct (hash_entry succ sort_of [x'] e_alloc) as [tx' e_he] eqn:Heq_he.
        cbn [fst snd] in Hhe_roots, Hhe_fresh.
        (* Supply hypotheses to hash_entry_all_roots *)
        assert (Hkeys_he_args : forall y, In y [x'] -> Sep.has_key y (parent (Defs.equiv e_alloc))).
        { intros y Hy. cbn in Hy. destruct Hy as [Hy|]; [|contradiction].
          subst y. exact Hx'_key. }
        specialize (Hhe_roots (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        destruct Hhe_roots as (Huf_he & Hdb_he & Hincl_he & Hmono_he & _).
        (* Apply hash_entry_args_old_keys to get structural info about e_he.db *)
        pose proof (@hash_entry_args_old_keys V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X H lt_asymmetric lt_succ lt_trans
                      (fun s => s <> sort_of) sort_of [x']) as Hhe_old.
        unfold vc in Hhe_old. specialize (Hhe_old e_alloc).
        rewrite Heq_he in Hhe_old. cbn [fst snd] in Hhe_old.
        specialize (Hhe_old (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        (* Hhe_old : forall b in e_he.db,
             all (fun y => Sep.has_key y (parent e_alloc)) b.args
             /\ (b.fn <> sort_of -> atom_in_db b e_alloc.db) *)
        (* Supply hypotheses to hash_entry_fresh_rank_zero *)
        assert (Hx'_root_list : all (fun y => map.get (parent (Defs.equiv e_alloc)) y = Some y) [x']).
        { cbn. split; [exact Hx'_root | exact I]. }
        specialize (Hhe_fresh (ex_intro _ _ Hok_alloc) Hx'_root_list Hno_sortof).
        destruct Hhe_fresh as (Htx'_rank0 & Htx'_root & Htx'_fresh & Htx'_atom).
        (* Step 4: union_roots_demote_second *)
        (* t_v is a root in e_he (via Hmono_he from Htv_root in e_sort via Hmono_alloc) *)
        assert (Htv_root_alloc : is_root e_alloc t_v).
        { unfold is_root. exact (Hmono_alloc t_v Htv_root). }
        assert (Htv_root_he : is_root e_he t_v).
        { unfold is_root. exact (Hmono_he t_v (Htv_root_alloc)). }
        (* tx' is a root in e_he *)
        assert (Htx'_root_he : is_root e_he tx').
        { unfold is_root. exact Htx'_root. }
        (* t_v <> tx': t_v has_key in e_alloc, tx' is fresh in e_alloc *)
        assert (Htv_ne_tx' : t_v <> tx').
        { intro Heq. subst t_v.
          apply Htx'_fresh.
          apply is_root_has_key. exact Htv_root_alloc. }
        (* rank tx' = Some 0 in e_he *)
        assert (Hrank_tx' : map.get (@rank _ _ _ (Defs.equiv e_he)) tx' = Some 0).
        { exact Htx'_rank0. }
        pose proof (@union_roots_demote_second V V_Eqb V_Eqb_ok lt V_default
                      V V_map V_map V_map_ok V_trie X H t_v tx') as Hunion.
        unfold vc in Hunion. specialize (Hunion e_he).
        destruct (Defs.union t_v tx' e_he) as [v_u e_u] eqn:Heq_union.
        cbn [fst snd] in Hunion.
        destruct Huf_he as [roots_he Hroots_he].
        specialize (Hunion roots_he Hroots_he Htv_root_he Htx'_root_he Htv_ne_tx' Hrank_tx').
        destruct Hunion as (Hvu_tv & Htv_root_u & Htx'_demoted_u & Hothers_u
                           & Hdb_u & Hpar_u & [improved Hwl_u] & [roots_u Hroots_u]).
        cbn [fst snd] in *.
        (* Now prove tx' is not an arg of any e_he.db atom (needed for crux) *)
        assert (Htx'_not_arg : forall b, atom_in_db b (Defs.db e_he) -> ~ In tx' (atom_args b)).
        { intros b Hb Hin_tx'.
          (* From hash_entry_args_old_keys: all args of b were has_key in e_alloc *)
          destruct (Hhe_old b Hb) as [Hb_args_old _].
          assert (Htx'_hk : Sep.has_key tx' (parent (Defs.equiv e_alloc))).
          { exact (in_all _ _ _ Hb_args_old Hin_tx'). }
          (* But tx' is fresh in e_alloc — contradiction *)
          exact (Htx'_fresh Htx'_hk). }
        (* Build db_ctx_inv e_u *)
        assert (Hdb_u_inv : db_ctx_inv e_u).
        { unfold db_ctx_inv, db_inv in *.
          intros a Ha.
          rewrite <- Hdb_u in Ha.
          specialize (Hdb_he a Ha).
          destruct Hdb_he as [Hargs_he Hret_he].
          split.
          - (* args: each arg y is root in e_he; y != tx' (Htx'_not_arg); so others_u gives root in e_u *)
            eapply all_wkn; [|exact Hargs_he].
            intros y Hyin Hy_root.
            unfold is_root in Hy_root.
            apply Hothers_u.
            + intro Heq. subst y.
              exact (Htx'_not_arg a Ha Hyin).
            + exact Hy_root.
          - (* ret: a.fn != sort_of -> ret root in e_he -> ret != tx' -> root in e_u *)
            intro HPfn.
            assert (Hret_root : map.get (parent (Defs.equiv e_he)) (atom_ret a) = Some (atom_ret a)).
            { exact (Hret_he HPfn). }
            apply Hothers_u.
            + (* ret != tx': a.fn != sort_of, so by hash_entry_args_old_keys,
                 a is in e_alloc.db; by db_ctx_inv e_alloc, a.ret has_key in e_alloc;
                 tx' is fresh in e_alloc, so a.ret != tx'. *)
              intro Heq. subst.
              destruct (Hhe_old a Ha) as [_ Ha_old].
              assert (Ha_alloc : atom_in_db a (Defs.db e_alloc)) by (apply Ha_old; exact HPfn).
              unfold db_ctx_inv, db_inv in Hdb_alloc.
              specialize (Hdb_alloc a Ha_alloc).
              destruct Hdb_alloc as [_ Hret_alloc].
              assert (Htx'_hk : Sep.has_key (atom_ret a) (parent (Defs.equiv e_alloc))).
              { unfold Sep.has_key. rewrite (Hret_alloc HPfn). exact I. }
              exact (Htx'_fresh Htx'_hk).
            + exact Hret_root. }
        (* Assemble the 5 conjuncts *)
        split.
        { exact (ex_intro _ roots_u Hroots_u). }
        split.
        { exact Hdb_u_inv. }
        split.
        { (* all-roots ((name,x')::base') in e_u *)
          cbn [all].
          split.
          - (* x' is root in e_u *)
            unfold is_root.
            (* x' root in e_alloc -> root in e_he (Hmono_he) -> others_u (x' != tx') -> root in e_u *)
            apply Hothers_u.
            + (* x' != tx' *)
              intro Heq. apply Htx'_fresh.
              rewrite <- Heq. exact Hx'_key.
            + exact (Hmono_he x' Hx'_root).
          - (* all roots in base' (Hall_tail) lifted to e_u *)
            eapply all_wkn; [|exact Hall_tail].
            intros [xn yn] Hyin Hyn_root.
            cbn [snd] in *.
            unfold is_root in *.
            (* yn root in e_inner -> root in e_sort (Hmono_sort) -> root in e_alloc (Hmono_alloc)
               -> root in e_he (Hmono_he) -> others_u (yn != tx') -> root in e_u *)
            apply Hothers_u.
            + (* yn != tx': yn has_key in e_alloc, tx' doesn't *)
              intro Heq. subst yn.
              apply Htx'_fresh.
              apply is_root_has_key.
              unfold is_root.
              exact (Hmono_alloc _ (Hmono_sort _ Hyn_root)).
            + exact (Hmono_he _ (Hmono_alloc _ (Hmono_sort _ Hyn_root))). }
        split.
        { (* map fst ((name,x')::base') = map fst ((name,t)::c') *)
          cbn [map fst]. f_equal. exact Hfst_tail. }
        (* 5th conjunct: ctx_readback e_u ((name,x')::base') ((name,t)::c') *)
        (* db inclusion facts *)
        assert (Hincl_su : forall a, atom_in_db a (Defs.db e_sort) -> atom_in_db a (Defs.db e_u)).
        { intros a Ha. rewrite Hdb_alloc_eq in Ha. apply Hincl_he in Ha.
          rewrite Hdb_u in Ha. exact Ha. }
        assert (Hincl_iu : forall a, atom_in_db a (Defs.db e_inner) -> atom_in_db a (Defs.db e_u)).
        { intros a Ha. apply Hincl_sort in Ha. apply Hincl_su. exact Ha. }
        assert (Hmono_iu : roots_mono e_inner e_u).
        { unfold roots_mono. intros z Hz. unfold is_root in *.
          apply Hothers_u.
          - intro Heq. subst z. apply Htx'_fresh. apply is_root_has_key.
            unfold is_root. exact (Hmono_alloc _ (Hmono_sort _ Hz)).
          - exact (Hmono_he _ (Hmono_alloc _ (Hmono_sort _ Hz))). }
        (* equiv_extends e_inner e_u:
           e_inner ->sort (Hext_sort) ->alloc (alloc_parent_eq+fresh)
           ->he (hash_entry_equiv_extends) ->u (union extends) *)
        assert (Hext_alloc : equiv_extends_inst e_sort e_alloc).
        { pose proof (alloc_opaque_parent_eq e_sort) as Hpar_sort.
          cbn [fst snd] in Hpar_sort.
          (* Hpar_sort : parent (equiv (snd (alloc_opaque ... e_sort))) = map.put ... *)
          rewrite Heq_alloc in Hpar_sort. cbn [fst snd] in Hpar_sort.
          (* Hpar_sort : parent (equiv e_alloc) = map.put (parent (equiv e_sort)) x' x' *)
          assert (Hnone_x' : map.get (parent (Defs.equiv e_sort)) x' = None).
          { unfold Sep.has_key in Hfresh_x'.
            destruct (map.get (parent (Defs.equiv e_sort)) x'); tauto. }
          unfold equiv_extends_inst, equiv_extends, uf_rel_PER. intros i j Hpre.
          rewrite Hpar_sort.
          eapply uf_rel_PER_alloc_monotone;
            [exact V_map_ok | exact Hnone_x' | unfold uf_rel_PER; exact Hpre]. }
        assert (Hext_he : equiv_extends_inst e_alloc e_he).
        { (* Derive via hash_entry_equiv_extends, specialized AFTER the destruct *)
          pose proof (hash_entry_equiv_extends sort_of [x']) as Hhe_ext_he.
          unfold vc in Hhe_ext_he.
          specialize (Hhe_ext_he e_alloc).
          rewrite Heq_he in Hhe_ext_he. cbn [fst snd] in Hhe_ext_he.
          exact (Hhe_ext_he (ex_intro _ _ Hok_alloc) Hkeys_he_args). }
        (* e_he -> e_u: use union_sound to get iff2 (union_closure_PER ...) (uf_rel_PER e_u),
           then derive equiv_extends e_he e_u via the left-injection into union_closure_PER. *)
        assert (Hext_u : equiv_extends_inst e_he e_u).
        { pose proof (@union_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok
                        V_trie X H t_v tx') as Hu.
          unfold vc in Hu. specialize (Hu e_he).
          rewrite Heq_union in Hu. cbn [fst snd] in Hu.
          specialize (Hu (ex_intro _ roots_he Hroots_he)
                        (is_root_has_key e_he t_v Htv_root_he)
                        (is_root_has_key e_he tx' Htx'_root_he)).
          destruct Hu as (_ & _ & Hper_iff & _).
          unfold equiv_extends_inst, equiv_extends, uf_rel_PER. intros i j Hpre.
          apply Hper_iff.
          unfold Relations.union_closure_PER.
          apply PER_clo_base. left. exact Hpre. }
        assert (Hequiv_iu : forall i j,
            uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_inner) i j ->
            uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_u) i j).
        { intros i j Hij.
          exact (Hext_u _ _ (Hext_he _ _ (Hext_alloc _ _ (Hext_sort _ _ Hij)))). }
        cbn [ctx_readback].
        split; [|].
        { (* exists xs, is_root e_u xs /\ atom_tree_sort X e_u base' t xs
                     /\ exists tx', atom_in_db (sort_of,[x'],tx') (db e_u)
                                 /\ uf_rel_PER (equiv e_u) tx' xs *)
          exists t_v. split.
          - exact Htv_root_u.
          - split.
            + eapply atom_tree_sort_db_incl; [exact Hincl_su | exact Htree_sort].
            + exists tx'. split.
              * rewrite <- Hdb_u. exact Htx'_atom.
              * (* uf_rel_PER e_u tx' t_v = uf_rel_PER e_u tx' (fst (v_u, e_u)) *)
                (* Htx'_demoted_u : map.get (parent (equiv e_u)) tx' = Some t_v *)
                apply PER_clo_base. exact Htx'_demoted_u. }
        { (* ctx_readback e_u base' c' *)
          eapply ctx_readback_mono;
            [exact Hincl_iu | exact Hmono_iu | exact Hequiv_iu | exact Hrb_tail]. }
    Qed.

    (* ================================================================ *)
    (* [E] establishment: hash_entry worklist + parents singleton facts *)
    (* ================================================================ *)

    (* Shorthand notation for Semantics.parents_keys_in_equiv instantiated
       at the AddOpenRoots section types. *)
    Local Notation parents_keys_in_equiv_inst :=
      (SemanticsParents.parents_keys_in_equiv V V V_map V_map V_trie X).

    (* After hash_entry sort_of [x'] on a state e_in where:
       (1) x' is a root, (2) no sort_of[x']→r atom exists,
       (3) analyses[x'] is pre-populated (Some _),
       (4) parents_keys_in_equiv holds for e_in,
       the result (tx', e_result) satisfies:
       (a) worklist unchanged: e_in.worklist = e_result.worklist
       (b) parents[tx'] = Some [Build_atom sort_of [x'] tx']. *)
    Lemma hash_entry_sortof_fresh_facts (x' : V)
      : vc (hash_entry succ sort_of [x'])
          (fun (e_in : instance X) res =>
             (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
             map.get (parent (Defs.equiv e_in)) x' = Some x' ->
             (forall r, ~ atom_in_db (Build_atom sort_of [x'] r) (Defs.db e_in)) ->
             (exists a_x', map.get (Defs.analyses e_in) x' = Some a_x') ->
             parents_keys_in_equiv_inst e_in ->
             (Defs.worklist e_in) = (Defs.worklist (snd res))
             /\ map.get (Defs.parents (snd res)) (fst res) =
                Some [Build_atom sort_of [x'] (fst res)]).
    Proof.
      unfold vc, hash_entry.
      intros e_in.
      cbn [Mbind StateMonad.state_monad].
      intros Hroots_ex Hx'_root Hmiss Hana_x' Hpkf.
      (* Step 1: list_Mmap find [x'] = ([x'], e_in) since x' is root *)
      assert (Hargs_roots : all (fun x => map.get (parent (Defs.equiv e_in)) x = Some x) [x']).
      { cbn. split; [exact Hx'_root | exact I]. }
      rewrite (@list_Mmap_find_roots_identity V V_Eqb V_Eqb_ok V V_map V_map V_trie X [x'] e_in
                 Hargs_roots).
      cbn [fst snd].
      (* Step 2: db_lookup sort_of [x'] = (None, e_in) by Hmiss *)
      pose proof (@db_lookup_pure V V V_map V_map V_trie X sort_of [x'] e_in) as Hlk.
      cbn beta in Hlk.
      destruct (db_lookup V V V_map V_map V_trie X sort_of [x'] e_in) as [mout e_lk] eqn:Hlkeq.
      cbn [fst snd] in Hlk |- *.
      destruct Hlk as [He_eq Hlk2]. subst e_lk.
      destruct mout as [r|]; cbn beta iota; cbn [fst snd].
      - exfalso. apply (Hmiss r). unfold atom_in_egraph in Hlk2. exact Hlk2.
      - cbn [Mbind StateMonad.state_monad].
        (* Step 3: alloc e_in gives (tx', e_alloc) *)
        pose proof (@alloc_struct V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X
                      lt_asymmetric lt_succ lt_trans) as Halloc_s.
        unfold vc in Halloc_s. specialize (Halloc_s e_in).
        destruct (Defs.alloc V succ V V_map V_map V_trie X e_in) as [tx' e_alloc] eqn:Halloc_eq.
        cbn [fst snd] in Halloc_s.
        destruct Hroots_ex as [roots Hroots].
        specialize (Halloc_s roots Hroots).
        destruct Halloc_s as (_ & Htx'_fresh_uf & _ & _ & _ & Hpar_alloc & Hwl_alloc).
        (* Derive: e_alloc.analyses = e_in.analyses (alloc doesn't change analyses) *)
        assert (Hana_alloc : Defs.analyses e_alloc = Defs.analyses e_in).
        { unfold Defs.alloc in Halloc_eq.
          destruct (UnionFind.alloc V _ _ succ (Defs.equiv e_in)) as [uf' x_f] eqn:Huf.
          injection Halloc_eq as <- <-. reflexivity. }
        (* Derive: e_alloc.parents = e_in.parents *)
        assert (Hpar_alloc_eq : Defs.parents e_alloc = Defs.parents e_in).
        { symmetry. exact Hpar_alloc. }
        (* Derive: parents[tx'] = None in e_alloc (via parents_keys_in_equiv e_in + freshness) *)
        assert (Htx'_none : map.get (Defs.parents e_alloc) tx' = None).
        { rewrite Hpar_alloc_eq.
          (* Now goal: map.get e_in.parents tx' = None *)
          (* By Hpkf + Htx'_fresh_uf: tx' not in e_in.equiv → tx' not in e_in.parents *)
          destruct (map.get (Defs.parents e_in) tx') as [par_list|] eqn:Hg.
          - exfalso. apply Htx'_fresh_uf.
            apply Hpkf. exists par_list. exact Hg.
          - reflexivity. }
        (* Step 4: db_set (Build_atom sort_of [x'] tx') *)
        unfold db_set. cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret].
        cbn [Mbind StateMonad.state_monad fst snd].
        (* get_analyses [x'] e_alloc: x' pre-populated → no state change *)
        unfold get_analyses, get_analysis.
        cbn [list_Mmap Mbind Mret StateMonad.state_monad fst snd].
        destruct Hana_x' as [ana_x' Hana_x'_get].
        rewrite Hana_alloc. rewrite Hana_x'_get.
        cbn [fst snd].
        (* update_analyses tx' out_a: preserves parents and worklist *)
        set (out_a := analyze V V X (Build_atom sort_of [x'] tx') [ana_x']).
        destruct (update_analyses V V V_map V_map V_trie X tx' out_a e_alloc) as [_u e_ua] eqn:Hue.
        assert (Hpa_ua : Defs.parents e_ua = Defs.parents e_alloc).
        { unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; reflexivity. }
        assert (Hwl_ua : Defs.worklist e_ua = Defs.worklist e_alloc).
        { unfold update_analyses in Hue; injection Hue as _ Hue'; subst e_ua; reflexivity. }
        (* db_set' (Build_atom sort_of [x'] tx') *)
        destruct (db_set' V V_Eqb V V_map V_map V_trie X (Build_atom sort_of [x'] tx') out_a e_ua)
          as [_v e_db] eqn:Hde.
        cbn [fst snd].
        unfold Mret. cbn [StateMonad.state_monad fst snd].
        (* Worklist: e_db.wl = e_ua.wl = e_alloc.wl = e_in.wl *)
        assert (Hwl_db : Defs.worklist e_db = Defs.worklist e_ua).
        { unfold db_set' in Hde; injection Hde as _ Hde'; subst e_db; reflexivity. }
        split.
        + rewrite Hwl_db, Hwl_ua, <- Hwl_alloc. reflexivity.
        + (* parents[tx'] = Some [Build_atom sort_of [x'] tx'] in e_db *)
          (* e_db.parents = fold_left (map_update (cons a)) (dedup eqb (tx'::[x'])) e_ua.parents *)
          (* where a = Build_atom sort_of [x'] tx' *)
          assert (Htx'_ne_x' : tx' <> x').
          { intro Heq. subst tx'.
            exact (Htx'_fresh_uf (is_root_has_key e_in x' Hx'_root)). }
          assert (Htx'_none_ua : map.get (Defs.parents e_ua) tx' = None).
          { rewrite Hpa_ua. exact Htx'_none. }
          unfold db_set' in Hde. injection Hde as _ Hde'. subst e_db.
          cbn [Defs.parents Defs.atom_fn Defs.atom_args Defs.atom_ret fst snd].
          (* a_new: shorthand for Build_atom sort_of [x'] tx' *)
          set (a_new := Build_atom sort_of [x'] tx').
          fold a_new.
          (* Compute dedup eqb (tx' :: [x']) = [tx', x'] (since tx' ≠ x') *)
          (* Goal: map.get (fold_left ... (dedup eqb (tx'::x'::[])) e_ua.parents) tx' = Some [a_new]
             We need to compute fold_left over [tx', x'] (since tx' ≠ x' so dedup preserves order)
             and then show get at tx' = Some [a_new] using get_update_same + get_update_diff. *)
          (* Compute dedup (tx'::x'::[]) = tx'::x'::[] (since tx' ≠ x') *)
          assert (Hne_sym : x' <> tx').
          { intro h. exact (Htx'_ne_x' (eq_sym h)). }
          assert (Hfind : List.find (eqb tx') (x' :: nil) = None).
          { cbn. eqb_case tx' x'; [contradiction | reflexivity]. }
          (* Use fold_left on [tx', x'] to directly compute *)
          (* fold_left over [tx', x']: step1: map_update pars tx' (cons a), step2: map_update ... x' (cons a) *)
          (* map.get step2 tx' = map.get step1 tx' (get_update_diff, x' ≠ tx') *)
          (* map.get step1 tx' = Some [a_new] (get_update_same + pars[tx'] = None) *)
          (* Get step1 directly: *)
          assert (Hstep1 : map.get (map_update (Defs.parents e_ua) tx' (cons a_new)) tx' = Some [a_new]).
          { rewrite (@get_update_same V (list (Defs.atom V V)) (V_map _) (V_map_ok _) _
                       (Defs.parents e_ua) tx' (cons a_new)).
            rewrite Htx'_none_ua. reflexivity. }
          (* Get step2 doesn't affect tx' *)
          assert (Hstep2 : map.get (map_update (map_update (Defs.parents e_ua) tx' (cons a_new))
                                               x' (cons a_new)) tx'
                         = map.get (map_update (Defs.parents e_ua) tx' (cons a_new)) tx').
          { apply get_update_diff.
            - exact (V_map_ok _).
            - exact Hne_sym. }
          (* Directly use Hstep1 and Hstep2 by asserting the intermediate fact *)
          (* The fold_left over [tx', x'] starting from e_ua.parents gives
             map_update (map_update e_ua.parents tx' (cons a_new)) x' (cons a_new).
             We prove this separately and use it to rewrite the goal. *)
          (* Reduce dedup and fold_left directly in the goal *)
          cbn [dedup List.find].
          eqb_case tx' x'. { contradiction. }
          cbn [dedup List.find fold_left].
          rewrite Hstep2, Hstep1. reflexivity.
    Qed.

  End AddOpenRoots.

  (* ============================================================== *)
  (* P3 (I)-inversion assembly: ctx_readback_eF + ctx_readback_wf_subst. *)
  (* ============================================================== *)
  (* From an adversary [a] sound on the rebuilt assumption egraph     *)
  (* [eF]'s atoms, plus the F1c-discharged per-var readback in [eF]    *)
  (* ([ctx_readback_eF]: an [atom_tree_sort] witness for each ctx      *)
  (* var's sort at a sort id [xs], and the CANONICALISED               *)
  (* [sort_of([x']) -> xs] atom), reconstruct a wf substitution [sg]   *)
  (* of the ctx [c] agreeing with [a] on the companion ids.  This is   *)
  (* the (I)-inversion core of the source-rule soundness adapter; the  *)
  (* F1c gate is isolated to [ctx_readback_eF] (discharged at P5 from  *)
  (* [add_ctx_readback] + [atom_tree_sort_survives] + the [sort_of]    *)
  (* ret-canonicalisation fact).  See [[project-source-rule-adapter]]. *)
  Section AddCtxInvert.
    Context (X : Type) `{analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).

    Local Notation lang_model := (lang_model l).
    Local Notation interp := (V_map (lang_model.(domain _))).
    Local Notation ain a e := (@Semantics.atom_in_egraph V V V_map V_map V_trie X a e).
    Local Notation asnd a al := (@Semantics.atom_sound_for_model V V V_map lang_model a al).

    (* The eF-side readback: the F1c-discharged form of [ctx_readback].
       Per ctx var [(x,t)] with companion [x'], the rebuilt egraph [eF]
       carries (a) a structural [atom_tree_sort] for [t] at some sort id
       [xs], and (b) the CANONICALISED [sort_of([x']) -> xs] atom (same
       [xs]).  The (b) ret=[xs] coupling is exactly the [tx' -> xs]
       canonicalisation the F1c discharge supplies; [ctx_readback]
       (model-free) only had an existential [tx'].  This is what (I)
       consumes. *)
    Fixpoint ctx_readback_eF (eF : instance X) (sub : named_list V) (c0 : ctx)
      {struct c0} : Prop :=
      match c0, sub with
      | [], _ => True
      | (x,t)::c', (_, x')::sub' =>
          (exists xs, atom_tree_sort X eF sub' t xs
                   /\ ain (Build_atom sort_of [x'] xs) eF)
          /\ ctx_readback_eF eF sub' c'
      | _, _ => False
      end.

    Lemma ctx_readback_wf_subst (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      : forall c sub, wf_ctx l c ->
          map fst c = map fst sub ->
          ctx_readback_eF eF sub c ->
          exists sg, wf_subst l [] sg c
                  /\ map fst sg = map fst c
                  /\ (forall x, In x (map fst sub) ->
                        map.get a (named_list_lookup default sub x)
                          = Some (inl (named_list_lookup default sg x))).
    Proof.
      induction c as [|[x t] c' IH]; intros sub Hwfc Hdom Hrb.
      - exists []. split; [|split].
        + constructor.
        + reflexivity.
        + destruct sub as [|[? ?] ?]; cbn in Hdom; [|discriminate].
          intros x [].
      - destruct sub as [|[x0 x'] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hx Hdom'. subst x0.
        apply invert_wf_ctx_cons in Hwfc.
        destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
        cbn [ctx_readback_eF] in Hrb.
        destruct Hrb as [ [xs [Htree Hatom_sof] ] Hrb' ].
        specialize (IH sub' Hwfc' Hdom' Hrb').
        destruct IH as [sg' [Hwfsub' [Hdomsg' Hleaf'] ] ].
        assert (Hrep : represents_sort X l a eF sg' t xs).
        { eapply atom_tree_sort_to_represents_sort; eauto. }
        assert (Hfr : exists t', map.get a xs = Some (inr t')
                              /\ eq_sort l [] t' (t[/sg'/])).
        { eapply add_open_faithful_rep_sort; eauto. }
        destruct Hfr as [t' Hfr2]. destruct Hfr2 as [Hgxs Heqs].
        pose proof (Hsound _ Hatom_sof) as Hsnd.
        unfold Semantics.atom_sound_for_model, Is_Some_satisfying in Hsnd.
        cbn [atom_args atom_ret atom_fn Defs.atom_args Defs.atom_ret Defs.atom_fn
             list_Mmap] in Hsnd.
        destruct (map.get a x') as [dx|] eqn:Hgx'; cbn beta iota in Hsnd; [|contradiction].
        rewrite Hgxs in Hsnd.
        cbn beta iota in Hsnd.
        change (domain V lang_model) with (term + sort)%type in Hsnd.
        cbn [interprets_to lang_model] in Hsnd.
        cbn in Hsnd.
        (* Hsnd : interprets_to sort_of [dx] (inr t'); the [interprets_to_term]
           constructor is auto-eliminated (inl vs inr). *)
        inversion Hsnd as
          [ es t_es Hwt_es Hargdom Houtdom
          | f0 args0 t0 Heqs0 Hargdom Houtdom
          | f0 args0 e0 t0 Heqe0 Hargdom Houtdom ].
        + (* interprets_to_sort_of: Houtdom : inl es = dx; Hwt_es : wf_term l [] es t' *)
          exists ((x, es) :: sg').
          split; [|split].
          * econstructor; [exact Hwfsub' | eapply wf_term_conv; [exact Hwt_es | exact Heqs] ].
          * cbn [map fst]. rewrite Hdomsg'. reflexivity.
          * intros y Hy. cbn [map fst] in Hy. cbn [named_list_lookup].
            pose proof (eqb_spec y x) as Hsp.
            destruct (eqb y x) eqn:Hyx;
              [ rewrite Houtdom; exact Hgx'
              | apply Hleaf'; destruct Hy as [Heqyx | Hy];
                  [ exfalso; apply Hsp; symmetry; exact Heqyx | exact Hy ] ].
        + (* interprets_to_sort: f0 = sort_of, eq_sort scon -> fresh contradiction *)
          exfalso.
          apply eq_sort_wf_l in Heqs0; eauto with lang_core.
          safe_invert Heqs0.
          match goal with Hin : In (sort_of, _) l |- _ =>
            apply Hsof; eapply pair_fst_in; exact Hin end.
    Qed.

    (* ============================================================== *)
    (* P5 bridge: ctx_readback (pre-rebuild, model-free) -> ctx_readback_eF
       (post-rebuild eF).  The canonicalizing survival is taken as the
       single hypothesis [Hsurv] (mirroring [atom_tree_sort_survives]'
       verbatim Hsurv, but in the UP-TO-EQUIV / canonicalizing form so it
       also moves the demoted [sort_of([x']) -> tx'] atom to its canonical
       [sort_of([x']) -> xs]).  The assembly site (task 6) discharges
       [Hsurv] from the generalised [L_survive_canonical] (with [m :=
       lang_model] etc.), isolating the F1c gate there.  Keeps this lemma
       model-free and 0-axiom. *)
    Lemma ctx_readback_to_eF (e1 eF : instance X)
      (Hdbi : db_ctx_inv X e1)
      (Hsurv : forall a : atom,
          atom_in_egraph_up_to_equiv V V V_map V_map V_trie X a e1 ->
          all (is_root X e1) (atom_args a) ->
          is_root X e1 (atom_ret a) ->
          ain a eF)
      : forall c sub, wf_ctx l c ->
          all (fun p => is_root X e1 (snd p)) sub ->
          ctx_readback X e1 sub c ->
          ctx_readback_eF eF sub c.
    Proof.
      (* reflexivity of uf_rel_PER on a list of roots *)
      assert (Hrefl : forall xl,
                 all (is_root X e1) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e1)) xl xl).
      { induction xl as [|z xl IHxl]; cbn; [trivial|].
        intros [Hz Hxl]. split; [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]. }
      induction c as [|[x t] c' IH]; intros sub Hwfc Hroots Hrb.
      - cbn. exact I.
      - destruct sub as [|[x0 x'] sub'].
        + cbn in Hrb. contradiction.
        + apply invert_wf_ctx_cons in Hwfc.
          destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
          cbn in Hrb. destruct Hrb as [Hhead Hrb'].
          destruct Hhead as [xs [Hxs_root [Htree [tx' [Hatom_db Hper] ] ] ] ].
          cbn in Hroots. destruct Hroots as [Hx'_root Hroots'].
          cbn [ctx_readback_eF]. split.
          * exists xs. split.
            -- (* atom_tree_sort eF sub' t xs via survival (verbatim case of Hsurv) *)
               eapply atom_tree_sort_survives with (e:=e1) (c:=c');
                 [ exact Hsof | exact Hdbi | | exact Hwst | exact Htree ].
               intros a Ha_in Ha_args Ha_ret.
               apply Hsurv; [ | exact Ha_args | exact Ha_ret ].
               exists a. split; [| exact Ha_in].
               unfold atom_canonical_equiv. split; [reflexivity|]. split.
               ++ apply Hrefl; exact Ha_args.
               ++ apply Relations.PER_clo_base; exact Ha_ret.
            -- (* canonical sort_of atom in eF via Hsurv (canonicalizing case) *)
               apply Hsurv.
               ++ exists (Build_atom sort_of [x'] tx'). split.
                  ** unfold atom_canonical_equiv.
                     cbn [atom_fn atom_args atom_ret Defs.atom_fn Defs.atom_args Defs.atom_ret].
                     split; [reflexivity|]. split.
                     --- cbn. split; [apply Relations.PER_clo_base; exact Hx'_root | exact I].
                     --- apply Relations.PER_clo_sym; exact Hper.
                  ** exact Hatom_db.
               ++ cbn [atom_args Defs.atom_args]. split; [exact Hx'_root | exact I].
               ++ cbn [atom_ret Defs.atom_ret]. exact Hxs_root.
          * apply IH; [exact Hwfc' | exact Hroots' | exact Hrb'].
    Qed.

  End AddCtxInvert.

  (* ============================================================== *)
  (* F1c discharge: the canonicalizing survival hypothesis Hsurv     *)
  (* that ctx_readback_to_eF (and atom_tree_sort_survives) consume,   *)
  (* obtained by applying the (admitted) L_survive_canonical with     *)
  (* m := lang_model.  This is the SINGLE site where the one          *)
  (* intentional F1c axiom is pulled in; both its side-conditions     *)
  (* (egraph_ok via add_ctx_sound, db_injective via db_inv_db_        *)
  (* injective + add_ctx_all_roots) are provable 0-axiom.  The extra  *)
  (* map_plus/spaced_list_intersect context is what L_survive_         *)
  (* canonical was generalised over in Semantics' WithMap; the final   *)
  (* positive instantiation supplies concrete instances.              *)
  Section F1cDischarge.
    Context (X : Type) `{analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).
    Context (V_map_plus_ok : ExtraMaps.map_plus_ok V_map).
    Context (V_trie_plus : ExtraMaps.map_plus V_trie).
    Context (sli : forall B, WithDefault B -> (B -> B -> B) ->
                   ne_list (V_trie B * list bool) -> V_trie B).

    Local Notation lang_model := (lang_model l).
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie X).
    Local Notation ain a e := (@Semantics.atom_in_egraph V V V_map V_map V_trie X a e).
    Local Notation interp := (V_map (lang_model.(domain _))).
    Local Notation asnd a al := (@Semantics.atom_sound_for_model V V V_map lang_model a al).

    Lemma rebuild_survives_canonical (e1 : instance X) (n : nat)
      (Hok : egraph_ok e1)
      (Hdbinj : Semantics.db_injective V V V_map V_map V_trie X e1)
      : forall a : atom,
          atom_in_egraph_up_to_equiv V V V_map V_map V_trie X a e1 ->
          all (is_root X e1) (atom_args a) ->
          is_root X e1 (atom_ret a) ->
          ain a (snd (rebuild n e1)).
    Proof.
      intros a Hup Hargs Hret.
      eapply (@L_survive_canonical V V_Eqb V_Eqb_ok lt succ V_default
                V V_Eqb V_Eqb_ok V_map V_map_plus V_map_plus_ok V_map_ok
                V_map V_map_plus V_map_ok V_trie V_trie_ok V_trie_plus X
                V_map_plus_ok sli _ lang_model (lang_model_ok l Hsof Hwf) n e1 a).
      - exact Hok.
      - exact Hdbinj.
      - exact Hup.
      - exact Hargs.
      - exact Hret.
    Qed.

    (* ============================================================ *)
    (* Assembly: from an adversary [a] sound on the rebuilt           *)
    (* assumption egraph's atoms, recover a wf substitution of [c].   *)
    (* Linearly chains add_ctx_egraph_ok + add_ctx_readback +         *)
    (* db_inv_db_injective + rebuild_survives_canonical +             *)
    (* ctx_readback_to_eF + ctx_readback_wf_subst.                    *)
    Lemma add_ctx_inversion (rf : nat) (a : interp) c
      : wf_ctx l c ->
        (forall al, ain al (snd (rebuild rf (snd (add_ctx succ sort_of l false false c
                                                   (empty_egraph V_default X)))))
                  -> asnd a al) ->
        exists sg, wf_subst l [] sg c
                /\ map fst sg = map fst c
                /\ (forall x, In x (map fst (fst (add_ctx succ sort_of l false false c
                                                  (empty_egraph V_default X)))) ->
                      map.get a (named_list_lookup default
                                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                        = Some (inl (named_list_lookup default sg x))).
    Proof.
      intros Hwfc Hsound.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e1 := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (eF := snd (rebuild rf e1)) in *.
      (* --- base facts at empty_egraph --- *)
      assert (Hok0 : egraph_ok e0).
      { exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                        V_map V_map_ok V_trie X lang_model)). }
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots).
      { exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)). }
      assert (Hdb0 : db_ctx_inv X e0).
      { intros aa Hin. exfalso.
        unfold Semantics.atom_in_db in Hin.
        unfold e0 in Hin. cbn [Defs.db empty_egraph] in Hin.
        rewrite map.get_empty in Hin.
        exact Hin. }
      (* --- add_ctx_egraph_ok: structural envelope --- *)
      pose proof (add_ctx_egraph_ok X l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e1 in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      (* --- add_ctx_readback: model-free per-var readback --- *)
      pose proof (add_ctx_readback X l Hwf Hsof c Hwfc) as HR.
      unfold vc in HR. specialize (HR e0).
      fold sub e1 in HR.
      specialize (HR Huf0 Hdb0).
      destruct HR as (_ & _ & _ & _ & Hrb).
      (* --- db_injective from db_ctx_inv + uf-ok --- *)
      assert (Hdbinj : Semantics.db_injective V V V_map V_map V_trie X e1).
      { exact (@db_inv_db_injective V V_Eqb V_Eqb_ok lt V_default V V_map V_map V_map_ok
                 V_trie X (fun s => s <> sort_of) e1 Huf1 Hdb1). }
      (* --- canonicalizing survival for eF --- *)
      pose proof (rebuild_survives_canonical e1 rf Hok1 Hdbinj) as Hsurv.
      (* --- ctx_readback (e1) -> ctx_readback_eF (eF) --- *)
      pose proof (ctx_readback_to_eF X l Hsof e1 eF Hdb1 Hsurv c sub Hwfc Hroots1 Hrb) as Hrbef.
      (* --- finish: build wf_subst from eF readback + a sound on eF --- *)
      pose proof (ctx_readback_wf_subst X l Hwf Hsof eF a Hsound c sub Hwfc
                    (eq_sym Hmapfst) Hrbef) as Hfin.
      exact Hfin.
    Qed.

  End F1cDischarge.

  (* ============================================================== *)
  (* Soundness of scheduled saturation                              *)
  (* ============================================================== *)
  (* Wraps Semantics' saturate_until_sound up through the Pyrosome   *)
  (* scheduled_saturate_until loop, against an arbitrary model m.    *)
  (* The Phase-4 caller instantiates m := lang_model.  The per-      *)
  (* rule_set side conditions [rs_saturation_hyps] are the real      *)
  (* content of schedule_sound, discharged in Phase 6.               *)
  Section SchedSat.
    Context (V_map_plus_ok : ExtraMaps.map_plus_ok V_map).
    Context (X : Type) `{analysis V V X}.
    Context (spaced_list_intersect
              : forall B, WithDefault B -> (B -> B -> B) ->
                          ne_list (V_trie B * list bool) -> V_trie B).
    Context (m : model V) (Hm : model_ok V m).

    Local Notation instance := (Utils.EGraph.Defs.instance V V V_map V_map V_trie X).
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie X).
    Local Notation sound := (egraph_sound_for_interpretation V V V_map V_map V_trie X m).

    (* The per-rule_set side conditions saturation needs: process_const_rules
       is sound (const-rule analogue of erule_sound; deferred Hconst), and every
       compiled rule satisfies run1iter's per-rule bundle against any snapshot. *)
    Definition rs_saturation_hyps (rs : rule_set V V V_map V_map) : Prop :=
      (forall e i, egraph_ok e -> sound i e ->
         egraph_ok (snd (process_const_rules V V_Eqb succ V_default V V_map V_map V_trie X rs e))
         /\ exists i', map.extends i' i /\ sound i' (snd (process_const_rules V V_Eqb succ V_default V V_map V_map V_trie X rs e)))
      /\ (forall e r, In r (compiled_rules V V V_map V_map rs) ->
            run1iter_rule_hyps V V_Eqb V_default V V_map V_map_plus V_map V_map_plus V_trie X spaced_list_intersect m rs e r).

    (* One pass of the schedule (list_Miter_breakable, stopping at the first
       entry whose termination check fires) is sound: each entry runs
       saturate_until on its rule_set, sound by saturate_until_sound, and the
       interpretations compose. *)
    Lemma list_Miter_breakable_sound (rfuel : nat) (p : state instance bool)
      (HP : forall e i, egraph_ok e -> sound i e -> egraph_ok (snd (p e)) /\ sound i (snd (p e))) :
      forall (sched : list (nat * rule_set V V V_map V_map)),
      (forall n rs, In (n, rs) sched -> rs_saturation_hyps rs) ->
      forall i e, egraph_ok e -> sound i e ->
      match list_Miter_breakable (fun entry => saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel (snd entry) p (fst entry)) sched e with
      | (_, e') => egraph_ok e' /\ exists i', map.extends i' i /\ sound i' e'
      end.
    Proof.
      induction sched as [|entry sched' IH]; intros Hsched i e Hok Hsnd.
      - cbn [list_Miter_breakable Mret StateMonad.state_monad].
        split; [exact Hok|]. exists i. split; [apply Properties.map.extends_refl | exact Hsnd].
      - cbn [list_Miter_breakable Mbind Mret StateMonad.state_monad].
        destruct entry as [fuel_i rs_i].
        cbn [fst snd].
        destruct (Hsched fuel_i rs_i (or_introl eq_refl)) as [Hconst_i Hrules_i].
        pose proof (@saturate_until_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                      V_map V_map_plus V_map_plus_ok V_map_ok V_map V_map_plus V_map_ok
                      V_trie V_trie_ok X V_map_plus_ok spaced_list_intersect _ m Hm
                      lt_asymmetric lt_succ lt_trans rfuel rs_i p HP Hconst_i Hrules_i fuel_i i e Hok Hsnd) as Hsat.
        destruct (saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel rs_i p fuel_i e) as [break e1] eqn:Hsu.
        destruct Hsat as (Hok1 & i1 & Hext1 & Hsnd1).
        destruct break.
        + split; [exact Hok1|]. exists i1. split; [exact Hext1 | exact Hsnd1].
        + assert (Hsched' : forall n rs, In (n, rs) sched' -> rs_saturation_hyps rs)
            by (intros n rs Hin; apply (Hsched n rs); right; exact Hin).
          pose proof (IH Hsched' i1 e1 Hok1 Hsnd1) as HIH.
          destruct (list_Miter_breakable (fun entry => saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel (snd entry) p (fst entry)) sched' e1) as [b e2] eqn:Hlmb.
          destruct HIH as (Hok2 & i2 & Hext2 & Hsnd2).
          split; [exact Hok2|]. exists i2.
          split; [eapply map_extends_trans; [exact Hext2 | exact Hext1] | exact Hsnd2].
    Qed.

    (* The scheduled saturation loop is sound: fuel induction, each round one
       schedule pass (list_Miter_breakable_sound); interpretations compose. *)
    Lemma scheduled_saturate_until_sound (rfuel : nat) (p : state instance bool)
      (HP : forall e i, egraph_ok e -> sound i e -> egraph_ok (snd (p e)) /\ sound i (snd (p e)))
      (schedule : list (nat * rule_set V V V_map V_map))
      (Hsched : forall n rs, In (n, rs) schedule -> rs_saturation_hyps rs)
      (fuel : nat) :
      forall i e, egraph_ok e -> sound i e ->
      match scheduled_saturate_until V_map_plus succ spaced_list_intersect rfuel schedule p fuel e with
      | (_, e') => egraph_ok e' /\ exists i', map.extends i' i /\ sound i' e'
      end.
    Proof.
      induction fuel as [|fuel IH]; intros i e Hok Hsnd.
      - cbn [scheduled_saturate_until Mret StateMonad.state_monad].
        split; [exact Hok|]. exists i. split; [apply Properties.map.extends_refl | exact Hsnd].
      - cbn [scheduled_saturate_until Mbind Mret StateMonad.state_monad].
        pose proof (list_Miter_breakable_sound rfuel p HP schedule Hsched i e Hok Hsnd) as Hlmb.
        destruct (list_Miter_breakable (fun entry => saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel (snd entry) p (fst entry)) schedule e) as [done e1] eqn:Hlmb_eq.
        destruct Hlmb as (Hok1 & i1 & Hext1 & Hsnd1).
        destruct done.
        + split; [exact Hok1|]. exists i1. split; [exact Hext1 | exact Hsnd1].
        + pose proof (IH i1 e1 Hok1 Hsnd1) as HIH.
          destruct (scheduled_saturate_until V_map_plus succ spaced_list_intersect rfuel schedule p fuel e1) as [b e2] eqn:Hss.
          destruct HIH as (Hok2 & i2 & Hext2 & Hsnd2).
          split; [exact Hok2|]. exists i2.
          split; [eapply map_extends_trans; [exact Hext2 | exact Hext1] | exact Hsnd2].
    Qed.

  End SchedSat.
End WithVar.

(* ============================================================== *)
(* NOTE: the post-WithVar sections ReducingStep / CongSubgoals /  *)
(* CongMain (Phases 4-5: reducing-step, congruence-subgoals, and  *)
(* egraph_reducing_cong_sound) were split out into                *)
(* Pyrosome.Tools.EGraph.ReducingCong to keep this file smaller.  *)
(* ============================================================== *)
