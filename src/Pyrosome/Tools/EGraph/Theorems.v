From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt.
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

  End AddOpenSound.

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
(* Soundness of one [egraph_reducing_equal_step] (Phase 4).        *)
(* ============================================================== *)
Section ReducingStep.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.
  Context (V_map : forall A, map.map V A)
    (V_map_plus : ExtraMaps.map_plus V_map)
    (V_map_ok : forall A, map.ok (V_map A))
    (V_map_plus_ok : ExtraMaps.map_plus_ok V_map)
    (V_trie : forall A, map.map (list V) A)
    (V_trie_ok : forall A, map.ok (V_trie A)).
  Context (succ : V -> V) (sort_of : V) (lt : V -> V -> Prop).
  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).
  Context (spaced_list_intersect
            : forall B, WithDefault B -> (B -> B -> B) ->
                        ne_list (V_trie B * list bool) -> V_trie B).
  Context (l : lang V) (wfl : wf_lang l) (sort_of_fresh : fresh sort_of l).

    Local Notation lang_model := (lang_model V sort_of l).
    Local Notation sound :=
      (egraph_sound_for_interpretation V V V_map V_map V_trie (option positive) lang_model).
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie (option positive)).

    (* ============================================================== *)
    (* Extraction soundness (Phase 5 keystone).                       *)
    (* [select_optimal_nodes] picks, per e-class, an optimal db node; *)
    (* a node it records for class [out] really is a db row for that  *)
    (* class -- i.e. [atom_in_db].  Pure nested-[map.fold] reasoning.  *)
    (* ============================================================== *)
    Lemma select_optimal_nodes_correct (X : Type) (le : X -> X -> bool)
      (analyses : V_map X) (db : Utils.EGraph.Defs.db_map V V V_map V_trie X)
      (out f : V) (args : list V) :
      map.get (@Pyrosome.Tools.EGraph.Defs.select_optimal_nodes V V_map V_trie X le analyses db) out = Some (f, args) ->
      exists tbl r,
        map.get db f = Some tbl
        /\ map.get tbl args = Some r
        /\ Utils.EGraph.Defs.entry_value V X r = out.
    Proof.
      unfold Pyrosome.Tools.EGraph.Defs.select_optimal_nodes.
      set (process_row := fun f0 (acc : V_map (V * list V)) args0 (row : Utils.EGraph.Defs.db_entry V X) =>
        let out0 := Utils.EGraph.Defs.entry_value _ _ row in
        let ra := Utils.EGraph.Defs.entry_analysis _ _ row in
        match map.get analyses out0 with
        | None => acc
        | Some a => if le ra a then map.put acc out0 (f0, args0) else acc
        end).
      set (process_table := fun (acc : V_map (V * list V)) f0 (tbl : V_trie (Utils.EGraph.Defs.db_entry V X)) =>
        map.fold (process_row f0) acc tbl).
      eapply (@map.fold_spec V (V_trie (Utils.EGraph.Defs.db_entry V X)) (V_map _) (V_map_ok _)
        (V_map (V * list V))
        (fun (db_partial : V_map (V_trie (Utils.EGraph.Defs.db_entry V X))) (acc : V_map (V * list V)) =>
                forall out' f' args',
                  map.get acc out' = Some (f', args') ->
                  exists tbl r,
                    map.get db_partial f' = Some tbl
                    /\ map.get tbl args' = Some r
                    /\ Utils.EGraph.Defs.entry_value _ _ r = out')
        process_table map.empty).
      - intros out' f' args' Hget.
        rewrite map.get_empty in Hget. discriminate.
      - intros f0 tbl0 db_partial acc Hnotf0 IH_outer.
        unfold process_table.
        eapply (@map.fold_spec (list V) (Utils.EGraph.Defs.db_entry V X) (V_trie _) (V_trie_ok _)
          (V_map (V * list V))
          (fun (tbl_partial : V_trie (Utils.EGraph.Defs.db_entry V X)) (acc' : V_map (V * list V)) =>
                  forall out' f' args',
                    map.get acc' out' = Some (f', args') ->
                    exists tbl r,
                      map.get (map.put db_partial f0 tbl_partial) f' = Some tbl
                      /\ map.get tbl args' = Some r
                      /\ Utils.EGraph.Defs.entry_value _ _ r = out')
          (process_row f0) acc).
        + intros out' f' args' Hget.
          destruct (IH_outer out' f' args' Hget) as (tbl & r & H1 & H2 & H3).
          exists tbl, r.
          refine (conj _ (conj H2 H3)).
          rewrite map.get_put_diff; [ exact H1 | intro Heq; subst; rewrite Hnotf0 in H1; discriminate ].
        + intros args0 row0 tbl_partial acc' Hnot_args0 IH_inner.
          assert (Htransport : forall (o2 f2 : V) (a2 : list V) tbl_src rr,
            map.get (map.put db_partial f0 tbl_partial) f2 = Some tbl_src ->
            map.get tbl_src a2 = Some rr ->
            Utils.EGraph.Defs.entry_value V X rr = o2 ->
            exists tbl r0,
              map.get (map.put db_partial f0 (map.put tbl_partial args0 row0)) f2 = Some tbl
              /\ map.get tbl a2 = Some r0 /\ Utils.EGraph.Defs.entry_value V X r0 = o2).
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
            destruct (map.get analyses (Utils.EGraph.Defs.entry_value V X row0)) as [a|] eqn:Hanalysis.
            -- destruct (le (Utils.EGraph.Defs.entry_analysis V X row0) a) eqn:Hle.
               ++ intros out' f' args' Hget'.
                  destruct (eqb out' (Utils.EGraph.Defs.entry_value V X row0)) eqn:Hbo;
                    pose proof (eqb_spec out' (Utils.EGraph.Defs.entry_value V X row0)) as Hso; rewrite Hbo in Hso.
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

    Lemma select_optimal_nodes_sound (X : Type) (le : X -> X -> bool)
      (analyses : V_map X) (db : Utils.EGraph.Defs.db_map V V V_map V_trie X)
      (out f : V) (args : list V) :
      map.get (@Pyrosome.Tools.EGraph.Defs.select_optimal_nodes V V_map V_trie X le analyses db) out = Some (f, args) ->
      atom_in_db V V V_map V_trie X (Build_atom f args out) db.
    Proof.
      intro H. apply select_optimal_nodes_correct in H.
      destruct H as (tbl & r & Htbl & Hr & Hev).
      unfold atom_in_db, Is_Some_satisfying; cbn.
      rewrite Htbl, Hr. exact Hev.
    Qed.

    (* ============================================================== *)
    (* Extraction soundness, part 2 (Phase 5 keystone).               *)
    (* [extract_weighted] reads a term out of an e-class that is      *)
    (* [eq_term]-equal to whatever that class denotes under [interp]. *)
    (* Fuel + memoization induction over the analysis extraction.     *)
    (* ============================================================== *)

    (* Clean reduction lemmas for the [stateT (V_map term) result] monad. *)
    Lemma stateT_result_bind {A B} (f : A -> stateT (V_map (term V)) Result.result B)
      (m : stateT (V_map (term V)) Result.result A) (s : V_map (term V)) :
      Mbind f m s = match m s with
                    | Success p => f (fst p) (snd p)
                    | Failure e => Failure e
                    end.
    Proof. cbn. unfold Basics.compose. destruct (m s) as [ [a s'] | e]; reflexivity. Qed.

    Lemma stateT_result_ret {A} (a : A) (s : V_map (term V)) :
      (Mret a : stateT (V_map (term V)) Result.result A) s = Success (a, s).
    Proof. reflexivity. Qed.

    Section ExtractFixed.
      Context (g : instance V V V_map V_map V_trie (option positive)).
      Context (interp : V_map (term V + sort V)).
      Context (Hsnd : sound interp g).

      Definition cache_sound (cache : V_map (term V)) : Prop :=
        forall k v, map.get cache k = Some v ->
          exists ek t, map.get interp k = Some (inl ek) /\ eq_term l [] t v ek.

      Lemma list_extract_sound
        (rec : V -> stateT (V_map (term V)) Result.result (term V))
        (Hrec : forall x cache e cache' e_x,
          cache_sound cache -> map.get interp x = Some (inl e_x) ->
          rec x cache = Result.Success (e, cache') ->
          cache_sound cache' /\ exists t, eq_term l [] t e e_x) :
        forall args args_terms cache children cache',
          list_Mmap (map.get interp) args = Some (map inl args_terms) ->
          cache_sound cache ->
          list_Mmap rec args cache = Result.Success (children, cache') ->
          cache_sound cache'
          /\ all2 (fun child e => exists t, eq_term l [] t child e) children args_terms.
      Proof.
        induction args as [|a args0 IHargs]; intros args_terms cache children cache' Hget Hcache Hmmap.
        - cbn in Hmmap. injection Hmmap; intros; subst children cache'.
          cbn in Hget. destruct args_terms as [|et args_terms0]; [ | cbn in Hget; discriminate ].
          split; [ exact Hcache | cbn; exact I ].
        - cbn [list_Mmap] in Hget, Hmmap.
          destruct (map.get interp a) as [d_a|] eqn:Hia; cbn [Mbind option_monad] in Hget; [ | discriminate ].
          destruct (list_Mmap (map.get interp) args0) as [ds|] eqn:Hds; cbn [Mbind Mret option_monad] in Hget; [ | discriminate ].
          injection Hget; intro Heq_dads.
          destruct args_terms as [|e_a args_terms0]; [ cbn in Heq_dads; discriminate | ].
          cbn [map] in Heq_dads. injection Heq_dads; intros Hds_eq Hda_eq.
          rewrite stateT_result_bind in Hmmap.
          destruct (rec a cache) as [ [c_a cache1] | err1 ] eqn:Hreca; [ cbn [fst snd] in Hmmap | discriminate ].
          rewrite stateT_result_bind in Hmmap.
          destruct (list_Mmap rec args0 cache1) as [ [cs cache2] | err2 ] eqn:Hlm; [ cbn [fst snd] in Hmmap | discriminate ].
          rewrite stateT_result_ret in Hmmap.
          injection Hmmap; intros Hcache'_eq Hchildren_eq; subst children cache'.
          assert (Hia' : map.get interp a = Some (inl e_a)) by (rewrite Hia, Hda_eq; reflexivity).
          destruct (Hrec a cache c_a cache1 e_a Hcache Hia' Hreca) as [Hcache1 Hhead].
          assert (Hds' : Some ds = Some (map inl args_terms0)) by (rewrite Hds_eq; reflexivity).
          destruct (IHargs args_terms0 cache1 cs cache2 Hds' Hcache1 Hlm) as [Hcache2 Htail].
          split; [ exact Hcache2 | ].
          cbn [all2]. split; [ exact Hhead | exact Htail ].
      Qed.

      Lemma extractF_sound
        (rec : V -> stateT (V_map (term V)) Result.result (term V))
        (Hrec : forall x cache e cache' e_x,
          cache_sound cache -> map.get interp x = Some (inl e_x) ->
          rec x cache = Result.Success (e, cache') ->
          cache_sound cache' /\ exists t, eq_term l [] t e e_x) :
        forall x cache e cache' e_x,
          cache_sound cache -> map.get interp x = Some (inl e_x) ->
          memoizeF (extract_weightedF g) rec x cache = Result.Success (e, cache') ->
          cache_sound cache' /\ exists t, eq_term l [] t e e_x.
      Proof.
        intros x cache e cache' e_x Hcache Hix Hmemo.
        unfold memoizeF in Hmemo.
        rewrite stateT_result_bind in Hmemo.
        unfold stateT_get in Hmemo.
        cbn [fst snd] in Hmemo.
        destruct (map.get cache x) as [v|] eqn:Hcx.
        - cbn [Mret result_monad fst snd] in Hmemo.
          rewrite Hcx in Hmemo.
          rewrite stateT_result_ret in Hmemo.
          injection Hmemo; intros Hc' He; subst e cache'.
          destruct (Hcache x v Hcx) as (ek & t & Hek & Heqv).
          rewrite Hix in Hek. injection Hek; intro Hekx; subst ek.
          split; [ exact Hcache | exists t; exact Heqv ].
        - cbn [Mret result_monad fst snd] in Hmemo.
          rewrite Hcx in Hmemo.
          rewrite stateT_result_bind in Hmemo.
          unfold extract_weightedF in Hmemo.
          destruct (map.get (select_optimal_nodes V_map V_trie oP_le (analyses g) (db g)) x) as [ [x_f x_args] | ] eqn:Hopt;
            cbn [result_of_option_else] in Hmemo; [ | cbn in Hmemo; discriminate ].
          rewrite stateT_result_bind in Hmemo.
          cbn [lift stateT_trans Mbind Mret result_monad fst snd] in Hmemo.
          rewrite stateT_result_bind in Hmemo.
          destruct (list_Mmap rec x_args cache) as [ [children0 cache_mid] | err ] eqn:Hlm;
            [ cbn [fst snd] in Hmemo | cbn [fst snd] in Hmemo; discriminate ].
          rewrite stateT_result_ret in Hmemo.
          cbn [fst snd] in Hmemo.
          rewrite stateT_result_bind in Hmemo.
          unfold stateT_put in Hmemo.
          cbn [Mret result_monad fst snd] in Hmemo.
          rewrite stateT_result_ret in Hmemo.
          injection Hmemo; intros Hcache'_eq He_eq; subst e cache'.
          pose proof (select_optimal_nodes_sound (option positive) oP_le (analyses g) (db g) x x_f x_args Hopt) as Hatomdb.
          destruct Hsnd as [Hwf_interp Hexact Hatom_interp Hrel].
          pose proof (Hatom_interp (Build_atom x_f x_args x) Hatomdb) as Hatomsnd.
          unfold atom_sound_for_model, Is_Some_satisfying in Hatomsnd.
          cbn [atom_args atom_ret atom_fn] in Hatomsnd.
          change (domain V lang_model) with (term V + sort V)%type in Hatomsnd.
          destruct (list_Mmap (map.get interp) x_args) as [arg_doms|] eqn:Hld;
            cbn beta iota in Hatomsnd; [ | contradiction ].
          rewrite Hix in Hatomsnd.
          change (interprets_to V lang_model) with (lang_model_interprets_to V sort_of l) in Hatomsnd.
          inversion Hatomsnd as [ | | f0 args0 e0 t0 Heqterm Hf0 Hargs0 He0 ]; subst.
          destruct (list_extract_sound rec Hrec x_args args0 cache children0 cache_mid Hld Hcache Hlm) as [Hcache_mid Hall].
          pose proof (eq_term_wf_l wfl ltac:(constructor) Heqterm) as Hwfcon.
          apply WfCutElim.invert_wf_term_con in Hwfcon.
          destruct Hwfcon as (c & rule_args & t_rule & Hin & Hwfargs0 & Ht0).
          assert (Hwfc : wf_ctx (Model:=core_model l) c) by eauto with lang_core.
          assert (Hall2 : all2 (lang_model_eq V l) (map inl args0) (map inl children0))
            by (clear -Hall; revert args0 Hall; induction children0 as [|c0 cs' IH];
                intros [|a0 args0'] Hall; cbn in Hall |- *; try contradiction; auto;
                destruct Hall as [ [t Ht] Hrest ]; split;
                [ econstructor; apply eq_term_sym; exact Ht | apply IH; exact Hrest ]).
          pose proof (all2_model_eq_eq_args V l wfl args0 children0 c Hwfargs0 Hwfc Hall2) as Heqargs.
          pose proof (term_con_congruence x_f rule_args t_rule Hin (or_intror eq_refl) wfl Heqargs) as Hcong.
          assert (Hwf1 : wf_term l [] (con x_f args0) (t_rule [/with_names_from c children0 /]))
            by (apply (eq_term_wf_l wfl ltac:(constructor) Hcong)).
          assert (Hwf2 : wf_term l [] (con x_f args0) t0)
            by (apply (eq_term_wf_l wfl ltac:(constructor) Heqterm)).
          assert (Hsorteq : eq_sort l [] (t_rule [/with_names_from c children0 /]) t0)
            by (apply (term_sorts_eq wfl ltac:(constructor) Hwf1 Hwf2)).
          assert (Hfinal : eq_term l [] t0 (con x_f children0) e_x)
            by (eapply eq_term_trans;
                [ exact (eq_term_conv (eq_term_sym Hcong) Hsorteq) | exact Heqterm ]).
          split.
          + intros k v Hk.
            destruct (eqb k x) eqn:Hkx; pose proof (eqb_spec k x) as Hkxs; rewrite Hkx in Hkxs.
            ++ subst k. rewrite map.get_put_same in Hk. injection Hk; intro Hv; subst v.
               exists e_x, t0. split; [ exact Hix | exact Hfinal ].
            ++ rewrite map.get_put_diff in Hk; [ | congruence ]. exact (Hcache k v Hk).
          + exists t0. exact Hfinal.
      Qed.

      Lemma extract_weighted'_sound :
        forall efuel x cache e cache' e_x,
          cache_sound cache -> map.get interp x = Some (inl e_x) ->
          extract_weighted' g efuel x cache = Result.Success (e, cache') ->
          cache_sound cache' /\ exists t, eq_term l [] t e e_x.
      Proof.
        induction efuel as [|n IHn]; intros x cache e cache' e_x Hcache Hix Hext.
        - cbn [extract_weighted' decr] in Hext.
          eapply (extractF_sound default); [ | exact Hcache | exact Hix | exact Hext ].
          intros x0 cache0 e0 cache0' e_x0 _ _ Hd. cbn in Hd. discriminate Hd.
        - cbn [extract_weighted' decr] in Hext.
          eapply (extractF_sound (extract_weighted' g n)); [ exact IHn | exact Hcache | exact Hix | exact Hext ].
      Qed.

      Lemma extract_weighted_sound (efuel : nat) (x : V) (e : term V) (e_x : term V) :
        map.get interp (snd (UnionFind.find (equiv g) x)) = Some (inl e_x) ->
        extract_weighted g efuel x = Result.Success e ->
        exists t, eq_term l [] t e e_x.
      Proof.
        intros Hix Hext.
        unfold extract_weighted in Hext.
        cbn [Mbind Mret] in Hext.
        destruct (extract_weighted' g efuel (snd (UnionFind.find (equiv g) x)) map.empty)
          as [ [e0 cache0] | err ] eqn:Hext'; cbn [Mbind Mret result_monad fst] in Hext;
          [ | discriminate ].
        injection Hext; intro He; subst e0.
        assert (Hcache0 : cache_sound map.empty)
          by (intros k v Hk; rewrite map.get_empty in Hk; discriminate).
        destruct (extract_weighted'_sound efuel _ map.empty e cache0 e_x Hcache0 Hix Hext')
          as [ _ Heq ].
        exact Heq.
      Qed.

    End ExtractFixed.

    (* The real [schedule_sound] content (Phase 3<->6 interface): every
       compiled rule_set in [schedule] satisfies the per-rule_set
       saturation hypotheses under [lang_model l].  This is exactly the
       [Hsched] hypothesis that [scheduled_saturate_until_sound] needs;
       it is discharged downstream from [build_rule_set] +
       [optimize_sequent_forward] + [pt_spaced_intersect_correct]. *)
    Definition schedule_sound_real
      (schedule : list (nat * rule_set V V V_map V_map)) : Prop :=
      forall n rs, In (n, rs) schedule ->
        @rs_saturation_hyps V V_Eqb V_default V_map V_map_plus V_trie succ lt
          (option positive) (depth V) spaced_list_intersect lang_model rs.

    (* Stronger form, exposing the resulting egraph's soundness and the input
       denotations regardless of [res]/[are_unified].  Chains: [empty] sound
       -> [add_open_term] x2 (places [a],[b]) -> [get_analysis] x2 (weight
       reads, preserve) -> [rebuild] (preserve) -> [scheduled_saturate_until]
       (extends interp, preserve; predicate HP via
       [get_analysis_preserves]/[are_unified_preserves]).  Used by
       [egraph_reducing_cong_sound]'s extract-and-recurse branch, which reads
       terms back from [g]. *)
    Lemma egraph_reducing_equal_step_sound_strong
      (schedule : list (nat * rule_set V V V_map V_map))
      (rfuel sat_fuel : nat)
      (a b : term V) (ta tb : sort V) :
      wf_term l [] a ta -> wf_term l [] b tb ->
      schedule_sound_real schedule ->
      let '(res, x1, x2, g) :=
        egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect
          l schedule rfuel sat_fuel a b in
      exists i,
        egraph_ok g /\ sound i g
        /\ option_relation (domain_eq V lang_model) (map.get i x1) (Some (inl a))
        /\ option_relation (domain_eq V lang_model) (map.get i x2) (Some (inl b)).
    Proof.
      intros Ha Hb Hsched.
      unfold egraph_reducing_equal_step.
      cbn [Mbind Mret StateMonad.state_monad fst snd].
      destruct (add_open_term succ sort_of l true false [] a (empty_egraph default (option positive))) as [x1 ea] eqn:Haa.
      destruct (add_open_term succ sort_of l true false [] b ea) as [x2 eb] eqn:Hab.
      destruct (get_analysis V V V_map V_map V_trie (option positive) x1 eb) as [w1 e1] eqn:Hga1.
      destruct (get_analysis V V V_map V_map V_trie (option positive) x2 e1) as [w2 e2] eqn:Hga2.
      destruct (rebuild rfuel e2) as [u e3] eqn:Hrb.
      match goal with
      | |- context [scheduled_saturate_until ?vmp ?sc ?sli ?rf ?sch ?p ?sf ?e] =>
          destruct (scheduled_saturate_until vmp sc sli rf sch p sf e) as [res g] eqn:Hsat
      end.
      cbn [fst snd].
      pose proof (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok V_map V_map_ok V_trie (option positive) lang_model) as Hempty.
      destruct Hempty as [Hok0 Hsnd0].
      assert (Hsub : forall (e:term V), e [/ with_names_from (@nil (V*sort V)) (@nil (term V)) /] = e) by (intro; cbn [with_names_from]; apply term_subst_nil).
      pose proof (@add_open_term_sound V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans (option positive) (depth V) l wfl sort_of_fresh true [] [] [] a ta) as Hpa.
      specialize (Hpa ltac:(constructor) Ha ltac:(constructor) (eq_refl) map.empty); unfold vc in Hpa.
      assert (Haa' : add_open_term succ sort_of l true false [] a (empty_egraph V_default (option positive)) = (x1, ea)) by (exact Haa).
      specialize (Hpa (empty_egraph V_default (option positive))).
      rewrite Haa' in Hpa.
      unfold open_term_post in Hpa.
      specialize (Hpa Hok0 Hsnd0 ltac:(cbn; trivial)).
      destruct Hpa as [i1 [ Hext1 Hrel1 ] ].
      cbn [fst snd] in Hext1, Hrel1.
      rewrite Hsub in Hrel1.
      destruct Hext1 as [ Hok_ea [ Hextmap1 [ Hsnd_ea Hkey1 ] ] ].
      pose proof (@add_open_term_sound V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans (option positive) (depth V) l wfl sort_of_fresh true [] [] [] b tb) as Hpb.
      specialize (Hpb ltac:(constructor) Hb ltac:(constructor) (eq_refl) i1); unfold vc in Hpb.
      specialize (Hpb ea).
      rewrite Hab in Hpb.
      unfold open_term_post in Hpb.
      specialize (Hpb Hok_ea Hsnd_ea ltac:(cbn; trivial)).
      destruct Hpb as [i2 [ Hext2 Hrel2 ] ].
      cbn [fst snd] in Hext2, Hrel2.
      rewrite Hsub in Hrel2.
      destruct Hext2 as [ Hok_eb [ Hextmap2 [ Hsnd_eb Hkey2 ] ] ].
      assert (Hlift : forall (ii ii' : V_map (domain V lang_model)) (xx:V) dd,
         map.extends ii' ii -> option_relation (domain_eq V lang_model) (map.get ii xx) (Some dd) ->
         option_relation (domain_eq V lang_model) (map.get ii' xx) (Some dd)).
      { intros ii ii' xx dd Hext Hor.
        unfold option_relation in *.
        destruct (map.get ii xx) as [v|] eqn:Hgv.
        - rewrite (Hext _ _ Hgv); exact Hor.
        - discriminate Hor. }
      pose proof (@lang_model_ok V V_Eqb V_Eqb_ok sort_of l sort_of_fresh wfl) as Hmok.
      pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x1 eb i2 Hok_eb Hsnd_eb) as Hg1.
      rewrite Hga1 in Hg1; cbn [snd] in Hg1; destruct Hg1 as [Hok_e1 Hsnd_e1].
      pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x2 e1 i2 Hok_e1 Hsnd_e1) as Hg2.
      rewrite Hga2 in Hg2; cbn [snd] in Hg2; destruct Hg2 as [Hok_e2 Hsnd_e2].
      pose proof (@rebuild_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok (option positive) (depth V) lang_model Hmok (fun _ => True) rfuel e2 Hok_e2) as Hrbs.
      rewrite Hrb in Hrbs; cbn [snd] in Hrbs; destruct Hrbs as [Hok_e3 Hiff3].
      assert (Hsnd_e3 : sound i2 e3) by (apply (Hiff3 i2); exact Hsnd_e2).
      match type of Hsat with
      | scheduled_saturate_until _ _ _ _ _ ?p _ _ = _ => set (pred := p) in *
      end.
      assert (HP : forall ee ii, egraph_ok ee -> sound ii ee -> egraph_ok (snd (pred ee)) /\ sound ii (snd (pred ee)))
        by (intros ee ii Hoke Hsnde; subst pred; unfold weight_less_than;
            cbn [Mbind Mret StateMonad.state_monad];
            pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x1 ee ii Hoke Hsnde) as Hp1;
            destruct (get_analysis V V V_map V_map V_trie (option positive) x1 ee) as [a1 e1'] eqn:He1';
            cbn [snd] in Hp1; destruct Hp1 as [ Hok1 Hsnd1 ]; cbn [fst snd];
            destruct (oP_lt a1 w1);
            [ cbn [snd]; split; assumption | ];
            cbn [fst snd];
            pose proof (@get_analysis_preserves_ok_sound V lt V V_map V_map V_trie (option positive) (depth V) lang_model x2 e1' ii Hok1 Hsnd1) as Hp2;
            destruct (get_analysis V V V_map V_map V_trie (option positive) x2 e1') as [a2 e2'] eqn:He2';
            cbn [snd] in Hp2; destruct Hp2 as [ Hok2 Hsnd2 ];
            destruct (oP_lt a2 w2);
            [ cbn [snd]; split; assumption | ];
            pose proof (@are_unified_preserves_ok_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie (option positive) lang_model x1 x2 e2' ii Hok2 Hsnd2) as Hau;
            destruct Hau as [ Hoku Hsndu ]; split; assumption).
      pose proof (@scheduled_saturate_until_sound V V_Eqb V_Eqb_ok V_default V_map V_map_plus V_map_ok V_trie V_trie_ok succ lt lt_asymmetric lt_succ lt_trans V_map_plus_ok (option positive) (depth V) spaced_list_intersect lang_model Hmok rfuel pred HP schedule Hsched sat_fuel i2 e3 Hok_e3 Hsnd_e3) as Hss.
      rewrite Hsat in Hss.
      destruct Hss as [ Hok_g [ i3 [ Hext3 Hsnd_g ] ] ].
      pose proof (Hlift i2 i3 x1 (inl a) Hext3 (Hlift i1 i2 x1 (inl a) Hextmap2 Hrel1)) as Hr1g.
      pose proof (Hlift i2 i3 x2 (inl b) Hext3 Hrel2) as Hr2g.
      exists i3.
      split; [ exact Hok_g | ].
      split; [ exact Hsnd_g | ].
      split; [ exact Hr1g | exact Hr2g ].
    Qed.

    (* The [res = true] / [are_unified] corollary used directly to decide
       equality: from the strong form's [g] soundness + denotations,
       [are_unified_eq_sound] -> [eq_sound_to_eq_term] -> conversion to the
       wanted sort ([term_sorts_eq]/[eq_term_conv]). *)
    Lemma egraph_reducing_equal_step_sound
      (schedule : list (nat * rule_set V V V_map V_map))
      (rfuel sat_fuel : nat)
      (a b : term V) (t : sort V) :
      wf_term l [] a t -> wf_term l [] b t ->
      schedule_sound_real schedule ->
      let '(res, x1, x2, g) :=
        egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect
          l schedule rfuel sat_fuel a b in
      res = true -> fst (Defs.are_unified x1 x2 g) = true -> eq_term l [] t a b.
    Proof.
      intros Ha Hb Hsched.
      pose proof (egraph_reducing_equal_step_sound_strong schedule rfuel sat_fuel a b t t Ha Hb Hsched) as Hstrong.
      revert Hstrong.
      destruct (egraph_reducing_equal_step V_map_plus V_trie succ sort_of spaced_list_intersect
                  l schedule rfuel sat_fuel a b) as [ [ [ res x1 ] x2 ] g ].
      intros [ i3 [ Hok_g [ Hsnd_g [ Hr1g Hr2g ] ] ] ] Hres Hunified.
      assert (Hisx1 : Is_Some (map.get i3 x1)) by (unfold option_relation in Hr1g; destruct (map.get i3 x1); [exact I | discriminate Hr1g]).
      assert (Hisx2 : Is_Some (map.get i3 x2)) by (unfold option_relation in Hr2g; destruct (map.get i3 x2); [exact I | discriminate Hr2g]).
      pose proof Hsnd_g as Hsnd_gc.
      destruct Hsnd_gc as [ _ Hexact _ _ ].
      assert (Hk1 : Sep.has_key x1 (UnionFind.parent (equiv g))) by (apply Hexact; exact Hisx1).
      assert (Hk2 : Sep.has_key x2 (UnionFind.parent (equiv g))) by (apply Hexact; exact Hisx2).
      pose proof (@are_unified_eq_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie (option positive) lang_model x1 x2 g i3 Hok_g Hsnd_g Hk1 Hk2 Hunified) as Hes.
      pose proof (@eq_sound_to_eq_term V V_Eqb V_Eqb_ok V_map sort_of l sort_of_fresh wfl i3 x1 x2 a b Hes Hr1g Hr2g) as Het.
      destruct Het as [ t' Heq ].
      eapply eq_term_conv; [ exact Heq | ].
      eapply term_sorts_eq with (e := a); eauto using eq_term_wf_l with lang_core.
    Qed.

End ReducingStep.

(* ============================================================== *)
(* Soundness of [cong_subgoals] (Phase 5, syntactic).             *)
(* If every pair produced by [cong_subgoals]/[select_inj_args] is  *)
(* [eq_term] (at some sort), the original goal is [eq_term] at its *)
(* sort -- by reconstructing [eq_args] (dependent arg-sort         *)
(* reconciliation, as in [all2_model_eq_eq_args]) + congruence.    *)
(* ============================================================== *)
Section CongSubgoals.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}.
  Context (l : lang V) (wfl : wf_lang l).

  Notation term := (@term V).
  Notation sort := (@sort V).
  Notation ctx := (@ctx V).

  Notation eq_args l := (eq_args (Model:= core_model l)).
  Notation wf_args l := (wf_args (Model:= core_model l)).
  Notation wf_ctx l := (wf_ctx (Model:= core_model l)).

  Lemma select_inj_args_sound (c' : ctx) inj_args (s1 s2 : list term) subgoals :
    @select_inj_args V V_Eqb c' inj_args s1 s2 = Some subgoals ->
    wf_ctx l c' ->
    wf_args l [] s1 c' ->
    wf_args l [] s2 c' ->
    all (fun p => let '(a,b) := p in exists s, eq_term l [] s a b) subgoals ->
    eq_args l [] c' s1 s2.
  Proof.
    intros Hsel Hwfc Hwfs1 Hwfs2 Hall.
    revert inj_args s2 subgoals Hsel Hwfs2 Hall.
    induction Hwfs1; intros inj_args s2 subgoals Hsel Hwfs2 Hall.
    - (* nil case: c' = [], s1 = [] *)
      destruct inj_args as [|x inj_t].
      + simpl in Hsel. inversion Hsel; subst. inversion Hwfs2; subst. constructor.
      + simpl in Hsel. discriminate.
    - (* cons case: c' = (name, t) :: c'_tail, s1 = e :: s *)
      rename c' into c'_tail.
      rename name into x'.
      rename t into ty.
      rename e into e1.
      rename s into s1_t.
      destruct s2 as [|e2 s2_t]. { inversion Hwfs2. }
      inversion Hwfs2 as [|xn' e2' t' Hwft2 Hwfs2_t xneq]; subst.
      rename H0 into Hwfs2_tail.
      destruct inj_args as [|x inj_t].
      { simpl in Hsel.
        case_match; try discriminate.
        inversion Hsel; subst.
        basic_utils_crush.
        assert (Hwfc_t : wf_ctx l c'_tail) by (inversion Hwfc; eauto).
        constructor.
        { eapply eq_args_refl; eauto. eapply core_model_ok; eauto. }
        { eapply eq_term_refl; eauto. }
      }
      simpl in Hsel.
      destruct (eqb x x') eqn:Hxx'.
      { destruct (select_inj_args c'_tail inj_t s1_t s2_t) as [rest|] eqn:Hrest.
        { simpl in Hsel. inversion Hsel; subst.
          simpl in Hall. destruct Hall as [ [se Hhead] Htail].
          assert (Hwfc_t : wf_ctx l c'_tail) by (inversion Hwfc; eauto).
          pose proof (IHHwfs1 Hwfc_t inj_t s2_t rest Hrest Hwfs2_tail Htail) as IH.
          constructor.
          { exact IH. }
          { eapply eq_term_conv; [ exact Hhead |].
            eapply term_sorts_eq; eauto using wf_ctx_nil.
            eapply eq_term_wf_r; eauto using wf_ctx_nil. }
        }
        { simpl in Hsel. discriminate. }
      }
      destruct (eqb e1 e2) eqn:He12.
      { basic_utils_crush.
        assert (Hwfc_t : wf_ctx l c'_tail) by (inversion Hwfc; eauto).
        pose proof (IHHwfs1 Hwfc_t (x :: inj_t) s2_t subgoals Hsel Hwfs2_tail Hall) as IH.
        constructor.
        { exact IH. }
        { eapply eq_term_refl; eauto. }
      }
      { discriminate. }
  Qed.

  Lemma cong_subgoals_sound inj_list (e1 e2 : term) (t : sort) :
    wf_term l [] e1 t -> wf_term l [] e2 t ->
    all (fun p => let '(a,b) := p in exists s, eq_term l [] s a b)
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)) ->
    eq_term l [] t e1 e2.
  Proof.
    intros Hwf1 Hwf2 Hall.
    unfold cong_subgoals in Hall.
    destruct e1 as [x1 | n1 s1], e2 as [x2 | n2 s2]; simpl in Hall.
    1-3: (destruct Hall as [ [se Heq] _];
          eapply eq_term_conv; [ exact Heq |];
          eapply term_sorts_eq; eauto using wf_ctx_nil;
          eapply eq_term_wf_r; eauto using wf_ctx_nil).
    (* con/con case *)
    destruct (eqb n1 n2) eqn:Hn12;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    pose proof (@eqb_spec _ _ V_Eqb_ok n1 n2) as Hn12eq.
    rewrite Hn12 in Hn12eq. subst n2.
    destruct (named_list_lookup_err inj_list n1) as [inj_args|] eqn:Hinj;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    destruct (named_list_lookup_err l n1) as [r|] eqn:Hl1;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    destruct r as [ | c args t_rule | |];
    try (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil).
    (* term_rule case *)
    destruct (select_inj_args c inj_args s1 s2) as [subs|] eqn:Hselect;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _];
         eapply eq_term_conv; [ exact Heq |];
         eapply term_sorts_eq; eauto using wf_ctx_nil;
         eapply eq_term_wf_r; eauto using wf_ctx_nil) ].
    assert (Hin1 : In (n1, term_rule c args t_rule) l) by
      (apply named_list_lookup_err_in; auto).
    apply WfCutElim.invert_wf_term_con in Hwf1.
    destruct Hwf1 as (c1 & args1 & t1 & Hinwf1 & Hwfargs1 & Ht1or1).
    apply WfCutElim.invert_wf_term_con in Hwf2.
    destruct Hwf2 as (c2 & args2 & t2 & Hinwf2 & Hwfargs2 & Ht2or2).
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf1 Hin1) as Heq1.
    inversion Heq1; subst c1 args1 t1; clear Heq1.
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf2 Hin1) as Heq2.
    inversion Heq2; subst c2 args2 t2; clear Heq2.
    assert (Hwfc : wf_ctx l c) by (eauto with lang_core).
    eapply select_inj_args_sound in Hselect; eauto.
    eapply eq_term_conv.
    { eapply term_con_congruence; eauto. }
    { destruct Ht2or2 as [Ht2 | Ht2].
      + exact Ht2.
      + subst. eapply eq_sort_refl.
        eapply wf_sort_subst_monotonicity; eauto.
        * eapply term_rule_in_sort_wf; eauto.
        * eapply wf_subst_from_wf_args; eauto. }
  Qed.

  (* Existential-sort variant: the two sides may be wf at *different* sorts
     (the dependent argument sorts that arise in the cong recursion).  We
     conclude [eq_term] at *some* sort; the final conversion to a specific
     target sort is done by the caller ([egraph_reducing_equal_sound]). *)
  Lemma cong_subgoals_sound_ex inj_list (e1 e2 : term) (ta tb : sort) :
    wf_term l [] e1 ta -> wf_term l [] e2 tb ->
    all (fun p => let '(a,b) := p in exists s, eq_term l [] s a b)
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)) ->
    exists s, eq_term l [] s e1 e2.
  Proof.
    intros Hwf1 Hwf2 Hall.
    unfold cong_subgoals in Hall.
    destruct e1 as [x1 | n1 s1], e2 as [x2 | n2 s2]; simpl in Hall.
    1-3: (destruct Hall as [ [se Heq] _]; exists se; exact Heq).
    (* con/con case *)
    destruct (eqb n1 n2) eqn:Hn12;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    pose proof (@eqb_spec _ _ V_Eqb_ok n1 n2) as Hn12eq.
    rewrite Hn12 in Hn12eq. subst n2.
    destruct (named_list_lookup_err inj_list n1) as [inj_args|] eqn:Hinj;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    destruct (named_list_lookup_err l n1) as [r|] eqn:Hl1;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    destruct r as [ | c args t_rule | |];
    try (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq).
    (* term_rule case *)
    destruct (select_inj_args c inj_args s1 s2) as [subs|] eqn:Hselect;
    [ | (simpl in Hall; destruct Hall as [ [se Heq] _]; exists se; exact Heq) ].
    assert (Hin1 : In (n1, term_rule c args t_rule) l) by
      (apply named_list_lookup_err_in; auto).
    apply WfCutElim.invert_wf_term_con in Hwf1.
    destruct Hwf1 as (c1 & args1 & t1 & Hinwf1 & Hwfargs1 & Ht1or1).
    apply WfCutElim.invert_wf_term_con in Hwf2.
    destruct Hwf2 as (c2 & args2 & t2 & Hinwf2 & Hwfargs2 & Ht2or2).
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf1 Hin1) as Heq1.
    inversion Heq1; subst c1 args1 t1; clear Heq1.
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf2 Hin1) as Heq2.
    inversion Heq2; subst c2 args2 t2; clear Heq2.
    assert (Hwfc : wf_ctx l c) by (eauto with lang_core).
    eapply select_inj_args_sound in Hselect; eauto.
    eexists. eapply term_con_congruence; [ exact Hin1 | right; reflexivity | exact wfl | exact Hselect ].
  Qed.

  (* Each pair produced by [select_inj_args] has both components well-formed
     (they are arguments of the well-formed input terms). *)
  Lemma select_inj_args_wf (c' : ctx) inj_args (s1 s2 : list term) subgoals :
    @select_inj_args V V_Eqb c' inj_args s1 s2 = Some subgoals ->
    wf_args l [] s1 c' ->
    wf_args l [] s2 c' ->
    all (fun p => (exists sa, wf_term l [] (fst p) sa)
                  /\ (exists sb, wf_term l [] (snd p) sb)) subgoals.
  Proof.
    intros Hsel Hwfs1 Hwfs2.
    revert inj_args s2 subgoals Hsel Hwfs2.
    induction Hwfs1 as [| s1tl ctl nm e1 tyhd Hwfe1 Hwftail IHwf]; intros inj_args s2 subgoals Hsel Hwfs2.
    - destruct inj_args as [|x inj_t]; simpl in Hsel; [ inversion Hsel; subst; cbn; exact I | discriminate ].
    - destruct s2 as [|e2 s2tl]; [ inversion Hwfs2 | ].
      inversion Hwfs2; subst.
      destruct inj_args as [|x inj_t].
      + simpl in Hsel. case_match; [ | discriminate ]. inversion Hsel; subst. cbn. exact I.
      + simpl in Hsel.
        destruct (eqb x nm) eqn:Hxx'.
        * destruct (select_inj_args ctl inj_t s1tl s2tl) as [rest|] eqn:Hrest; [ | discriminate ].
          simpl in Hsel. inversion Hsel; subst.
          cbn [all]. split.
          -- split; eexists; eassumption.
          -- exact (IHwf inj_t s2tl rest Hrest ltac:(eassumption)).
        * destruct (eqb e1 e2) eqn:He12; [ | discriminate ].
          exact (IHwf (x :: inj_t) s2tl subgoals Hsel ltac:(eassumption)).
  Qed.

  (* Every pair in [cong_subgoals] of a goal has well-formed components. *)
  Lemma cong_subgoals_preserves_wf inj_list (e1 e2 : term) (ta tb : sort) :
    wf_term l [] e1 ta -> wf_term l [] e2 tb ->
    all (fun p => (exists sa, wf_term l [] (fst p) sa)
                  /\ (exists sb, wf_term l [] (snd p) sb))
        (@cong_subgoals V V_Eqb l inj_list (e1,e2)).
  Proof.
    intros Hwf1 Hwf2.
    unfold cong_subgoals.
    destruct e1 as [x1 | n1 s1], e2 as [x2 | n2 s2];
      try (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]).
    destruct (eqb n1 n2) eqn:Hn12;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    pose proof (@eqb_spec _ _ V_Eqb_ok n1 n2) as Hn12eq. rewrite Hn12 in Hn12eq. subst n2.
    destruct (named_list_lookup_err inj_list n1) as [inj_args|] eqn:Hinj;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    destruct (named_list_lookup_err l n1) as [r|] eqn:Hl1;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    destruct r as [ | c args t_rule | | ];
      try (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]).
    destruct (select_inj_args c inj_args s1 s2) as [subs|] eqn:Hselect;
      [ | (cbn [all fst snd]; split; [ split; eexists; eassumption | exact I ]) ].
    assert (Hin1 : In (n1, term_rule c args t_rule) l) by (apply named_list_lookup_err_in; auto).
    apply WfCutElim.invert_wf_term_con in Hwf1.
    destruct Hwf1 as (c1 & args1 & t1 & Hinwf1 & Hwfargs1 & _).
    apply WfCutElim.invert_wf_term_con in Hwf2.
    destruct Hwf2 as (c2 & args2 & t2 & Hinwf2 & Hwfargs2 & _).
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf1 Hin1) as Heq1.
    inversion Heq1; subst c1 args1 t1; clear Heq1.
    pose proof (in_all_fresh_same _ _ l n1 (wf_lang_ext_all_fresh wfl) Hinwf2 Hin1) as Heq2.
    inversion Heq2; subst c2 args2 t2; clear Heq2.
    exact (select_inj_args_wf c inj_args s1 s2 subs Hselect Hwfargs1 Hwfargs2).
  Qed.

End CongSubgoals.
