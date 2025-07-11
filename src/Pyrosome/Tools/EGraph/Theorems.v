Require Import Lists.List Coq.Classes.RelationClasses.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps.
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

  Notation state_sound_for_model := (state_sound_for_model lt).
  
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
  Ltac extension_congruence Hext H H' :=
    apply eq_of_eq_Some;
    (eapply Hext in H' || (eapply Mmap_extends in H'; [| eauto | eauto | apply Hext]));
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
    Arguments interprets_to {symbol}%type_scope m f args%list_scope d.
    
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

    
  (*TODO: move to definition site*)
  Arguments monotone1 {idx}%type_scope {idx_map}%function_scope {A B}%type_scope P%function_scope.
  
  Lemma args_in_instance_monotone s
    : monotone1 (args_in_instance s).
  Proof.
    unfold args_in_instance.
    repeat intro.
    iss_case.
    eapply Mmap_extends in Hma; eauto.
    rewrite Hma.
    cbn.
    auto.
  Qed.

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
  Ltac extension_congruence Hext H H' :=
    apply eq_of_eq_Some;
    (eapply Hext in H' || (eapply Mmap_extends in H'; [| eauto | eauto | apply Hext]));
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
    
  Section __.
    Context (X : Type) `{analysis V V X} (with_sorts : bool) (l l1 : lang) (sort_of_fresh : fresh sort_of l).
    Context (add_open_sort : named_list V -> Term.sort V -> state (instance X) V).
    Context (add_open_sort_sound
              : forall l2 t s c' r' i,
                wf_lang l2 ->
                length l2 < length l1 ->
                incl l2 l1 ->
                wf_args l [] s c' ->
                wf_ctx l2 c' ->
                wf_sort l2 c' t ->
                map fst c' = map fst r' ->
                args_in_instance l s i (map snd r') ->
                state_sound_for_model (lang_model l) i
                  (add_open_sort r' t)
                  (fun i' x => option_relation (lang_model l).(domain_eq _)
                               (map.get i' x) (Some (inr t[/with_names_from c' s/])))).
    Context s c 
      (Hsubst : wf_args l [] s c)
      (Hctx : wf_ctx l1 c)
      (Hwf : wf_lang l)
      (Hwf' : wf_lang l1)
      (Hl_sub : incl l1 l).
    

    Lemma add_open_sound
      : (forall e t, wf_term l1 c e t ->
                     forall i r, args_in_instance l s i (map snd r) ->
                                 map fst c = map fst r ->
                                state_sound_for_model (lang_model l) i
                                  (add_open_term' succ sort_of l with_sorts add_open_sort r e)
                                  (fun i x => option_relation (lang_model l).(domain_eq _)
                                              (map.get i x) (Some (inl e[/with_names_from c s/]))))
        /\ (forall args c', wf_args l1 c args c' ->
                     forall i r, args_in_instance l s i (map snd r) ->
                                 map fst c = map fst r ->
                                       state_sound_for_model (lang_model l) i
                                         (list_Mmap (add_open_term' succ sort_of l
                                                       with_sorts add_open_sort r) args)
                                         (fun i arg_ids =>
                                            args_in_instance l args[/with_names_from c s/] i arg_ids)).
    Proof.      
      pose proof (lang_model_eq_PER _ Hwf) as HPER.
      apply WfCutElim.wf_cut_ind; intros;
        cbn [add_open_term' list_Mmap]; eauto.
      {
        pose proof H0.
        eapply Hl_sub in H0;
          eapply all_fresh_named_list_lookup_err_in in H0; eauto with lang_core.
        rewrite <- H0; clear H0.
        ssm_bind.
        ssm_bind.
        {
          pose proof H6 as Ha.
          unfold args_in_instance in Ha.
          iss_case.
          pose proof Ha; apply all2_lang_model_eq_inl' in Ha; break; subst.
          1:eapply hash_entry_sound; eauto using lang_model_ok;
          cbn beta in *.
          {
            eapply lang_model_ok; eauto.
            {
              cbn in *.
              refine (interprets_to_term _ _ _ _ _ _).
              apply eq_term_refl.
              econstructor; eauto.
              {
                eapply wf_args_subst_monotonicity; auto.
                { eapply wf_args_lang_monotonicity; eauto. }
                { eapply wf_ctx_lang_monotonicity; eauto. }
                {
                  use_rule_in_wf;
                    basic_core_crush.
                }
                {
                  eapply wf_subst_from_wf_args; eauto.
                }
              }
            }
            { eapply all2_Symmetric in H7; try apply lang_model_eq_PER; eauto. }
            {
              cbn.
              refine (lm_eq_terms _ _ _ _ _).
              eapply eq_term_refl.
              eapply wf_term_by.
              { apply Hl_sub; eauto. }             
              eapply wf_args_subst_monotonicity; auto.
              { eapply wf_args_lang_monotonicity; eauto. }
              { eapply wf_ctx_lang_monotonicity; eauto. }
              {
                use_rule_in_wf;
                    basic_core_crush.
              }
              {
                eapply wf_subst_from_wf_args; eauto.
              }
            }
          }
        }
        case_match.
        {
          use_rule_in_wf.
          autorewrite with lang_core utils in H9; break.
          pose proof H5; apply in_split in H5; break; subst.
          ssm_bind.
          {
            eapply add_open_sort_sound.
            8:{
              rewrite map_combine_snd.
              1: eapply args_in_instance_monotone; now eauto.
              apply args_in_instance_length in H6.
              rewrite H6.
              autorewrite with utils.
              erewrite wf_args_length_eq; try eassumption.
              unfold apply_subst; cbn; unfold args_subst; cbn.
              basic_utils_crush.
            }
            4:{       
              eapply wf_args_subst_monotonicity; auto.
              { eapply wf_args_lang_monotonicity; eauto. }
              { eapply wf_ctx_lang_monotonicity; eauto. }
              { eapply wf_ctx_lang_monotonicity; eauto. }
              {
                eapply wf_subst_from_wf_args; eauto.
              }
            }
            5:{
              eapply wf_lang_tail in Hwf'; safe_invert Hwf'.
              safe_invert H17.
              autorewrite with utils in *.
              exact H19.
            }
            {
              eapply wf_lang_tail in Hwf'; safe_invert Hwf'; eauto.
            }
            {
              autorewrite with utils list; cbn.
              Lia.lia.
            }
            {
              basic_utils_crush.
            }
            {
              eapply wf_lang_tail in Hwf'; safe_invert Hwf'.
              safe_invert H17.
              autorewrite with utils in *; auto.
            }
            {
              rewrite map_combine_fst; auto.
              autorewrite with utils list; cbn.
              apply args_in_instance_length in H6.
              rewrite H6.
              autorewrite with utils.
              erewrite wf_args_length_eq; try eassumption.
              unfold apply_subst; cbn; unfold args_subst; cbn.
              basic_utils_crush.
            }
          }
          unfold atom_sound_for_model in H8;
            repeat iss_case; cbn beta in *.
          eapply interprets_to_term_rule in H8; eauto; break; subst.
          ssm_bind.
          {
            eapply hash_entry_sound; eauto using lang_model_ok;
            cbn beta in *.
            { cbn in *. apply H5 in Hma0; rewrite Hma0; reflexivity. }
            {
              cbn in *.
              apply interpret_sort_of; eauto.
              repeat eexists; intuition eauto.
              eapply eq_term_wf_r; eauto with lang_core.
            }
          }
          ssm_bind.
          1:eapply union_sound; eauto.
          { apply lang_model_ok; eauto. }
          {
            (*pose proof (eq_sound_for_model_PER _ _ V_map (lang_model l) (H0:=lang_model_ok l sort_of_fresh Hwf)).*)
            cbn in *.
            unfold option_relation in *; cbn in *.
            case_match; try congruence.
            unfold eq_sound_for_model.
            cbn in *.
            eapply H8 in case_match_eqn; rewrite case_match_eqn.
            cbn.
            unfold atom_sound_for_model in H14.
            cbn in *.
            repeat iss_case.
            case_match; try congruence.
            inversions.
            cbn.
            apply interpret_sort_of in H14; break; subst; eauto.
            etransitivity; try eassumption.
            lang_model_simp.
            safe_invert H14.
            etransitivity.
            2:{
              constructor.
              eapply term_sorts_eq; auto with lang_core.
              2: eassumption.
              eapply eq_term_wf_r; eauto with lang_core.
            }
            constructor.
            eapply eq_sort_subst; eauto.
            {
              eapply eq_sort_refl.
              apply Hl_sub in H12; use_rule_in_wf;
                basic_core_crush.
            }
            2:{
              apply Hl_sub in H12; use_rule_in_wf;
                basic_core_crush.
            }
            {
              apply eq_args_implies_eq_subst; eauto.
              unfold args_in_instance in H6.
              iss_case.
              eapply Mmap_extends in Hma1; eauto.
              cbn in *.
              rewrite Hma in Hma1.
              inversions.
              eapply all2_Symmetric in H6; try typeclasses eauto.
              eapply all2_model_eq_eq_args in H6; eauto.
              2:{
                eapply Hl_sub in H12;
                  use_rule_in_wf.
                  autorewrite with lang_core utils in *; break; eauto.
              }
              {
                eapply wf_args_subst_monotonicity; eauto with lang_core.
                { eapply wf_args_lang_monotonicity; eauto. }
                { eapply wf_ctx_lang_monotonicity; eauto. }
                
                eapply wf_subst_from_wf_args; eauto.
              }
            }
          }
          apply ret_sound_for_model'.
          repeat basic_goal_prep; subst.
          unfold  option_relation.
          cbn.
          apply H5 in Hma0.
          apply H8 in Hma0.
          rewrite Hma0.
          change (map (term_var_map (term_subst_lookup (with_names_from c s))) s0)
            with s0[/(with_names_from c s)/].
          symmetry.
          etransitivity; [| econstructor; eauto].
          econstructor.
          eapply term_con_congruence; eauto.
          unfold args_in_instance in H6.
          iss_case.
          eapply Mmap_extends in Hma1; eauto.
          cbn in *.
          rewrite Hma in Hma1.
          inversions.
          eapply all2_Symmetric in H6; try typeclasses eauto.
          eapply all2_model_eq_eq_args in H6; eauto.
          2:{
            eapply Hl_sub in H12;
              use_rule_in_wf.
            autorewrite with lang_core utils in *; break; eauto.
          }
          {
            eapply wf_args_subst_monotonicity; eauto with lang_core.
            { eapply wf_args_lang_monotonicity; eauto. }
            { eapply wf_ctx_lang_monotonicity; eauto. }
            
            eapply wf_subst_from_wf_args; eauto.
          }
        }
        {
          apply ret_sound_for_model'.
          repeat basic_goal_prep; subst.
          unfold option_relation.
          cbn.
          unfold atom_sound_for_model in H8.
          repeat iss_case.
          cbn in *.
          eapply interprets_to_term_rule in H8; eauto.
          break; subst.
          change (map (term_var_map (term_subst_lookup (with_names_from c s))) s0)
            with s0[/(with_names_from c s)/].
          symmetry.
          etransitivity; [| econstructor; eauto].
          econstructor.
          eapply term_con_congruence; eauto.
          unfold args_in_instance in H6.
          iss_case.
          eapply Mmap_extends in Hma1; eauto.
          cbn in *.
          rewrite Hma in Hma1.
          inversions.
          eapply all2_Symmetric in H6; try typeclasses eauto.
          eapply all2_model_eq_eq_args in H6; eauto.
          2:{
            eapply Hl_sub in H5;
              use_rule_in_wf.
            autorewrite with lang_core utils in *; break; eauto.
          }
          {
            eapply wf_args_subst_monotonicity; eauto with lang_core.
            { eapply wf_args_lang_monotonicity; eauto. }
            { eapply wf_ctx_lang_monotonicity; eauto. }
            eapply wf_subst_from_wf_args; eauto.
          }
        }
      }
      {
        apply ret_sound_for_model'.
        unfold option_relation.
        assert (exists x, In (n,x) r).
        {
          eapply pair_fst_in_exists.
          rewrite <- H2.
          eapply pair_fst_in; eauto.
        }
        break.
        erewrite named_list_lookup_in; eauto.
        {
          assert (exists e,  In (n, e) (with_names_from c s)).
          {
            apply pair_fst_in_exists.
            rewrite map_fst_with_names_from;
              basic_core_crush.
          }
          break.
          eapply args_in_instance_in in H3; eauto with model.
          break.
          rewrite H3.
          cbn.
          etransitivity; try eassumption.
          econstructor.
          replace x0 with (term_subst_lookup (with_names_from c s) n).
          {
            eapply eq_term_refl.
            eapply wf_term_lookup; eauto.
            1:eapply wf_subst_from_wf_args; eauto.
            { eapply wf_ctx_lang_monotonicity; eauto. }
          }            
          apply named_list_lookup_in; eauto.
          rewrite map_fst_with_names_from.
          2:{ basic_core_crush. }
          { apply NoDup_fresh; eauto with model. }
        }            
        { rewrite <- H2; apply NoDup_fresh; eauto with model. }
      }
      {
        apply ret_sound_for_model'.
        cbn in *; auto.
      }
      {
        ssm_bind.
        ssm_bind.
        {
          eapply H1; eauto.
          eapply args_in_instance_monotone; eauto.
        }
        apply ret_sound_for_model'.
        cbn in *; auto.
        apply args_in_instance_cons; eauto.
        unfold option_relation in *.
        case_match; try congruence.
        apply H8 in case_match_eqn; cbn in *; rewrite case_match_eqn.
        cbn.
        apply H7.
      }        
    Qed.

  End __.

  (*
  Lemma assign_subst_subst l i r c s s' c'
    : args_in_instance l s i r ->
      wf_subst l c s' c' ->
      assign_subst_in_instance l s' [/s /] i r.
  Proof.
    unfold assign_subst_in_instance.
    (*    TODO: false! needs a different r! (of course*)
    Abort.
   *)

    Lemma add_open_sort'_sound l l' with_sorts r s c t fuel (sort_of_fresh : fresh sort_of l)
      : wf_lang l ->
        length l' < fuel ->
        incl l' l ->
        wf_lang l' ->
        wf_args l [] s c ->
        wf_ctx l' c ->
        wf_sort l' c t ->
        forall i,
        args_in_instance l s i (map snd r) ->
        map fst c = map fst r ->
        state_sound_for_model (lang_model l) i
          (add_open_sort' succ sort_of l with_sorts fuel r t)
          (fun i x => option_relation (lang_model l).(domain_eq _)
                      (map.get i x) (Some (inr t[/with_names_from c s/]))).
    Proof.
      revert l' r s c t.
      induction fuel;
        cbn [add_open_sort'].
      { intros; Lia.lia. }
      {
        intros.
        destruct t.
        safe_invert H5.
        apply in_split in H11; break; subst.
        ssm_bind.
        {
          pose proof H2 as Htail.
          eapply wf_lang_tail in Htail; safe_invert Htail; eauto.
          autorewrite with lang_core utils in *; break.
          eapply add_open_sound.
          1: auto.
          1:intros; eapply IHfuel; auto.
          11: now eauto.
          10:now eauto.
          5: now eauto.          
          all: eauto.
          {
            repeat rewrite length_app, length_cons in *.
            Lia.lia.
          }
          { eapply incl_tran; eassumption. }
        }
        cbn beta in *.
        pose proof H8 as Ha.
        unfold args_in_instance in Ha.
        iss_case.
        pose proof Ha; apply all2_lang_model_eq_inl' in Ha; break; subst.
        eapply state_sound_for_model_wkn.
        1:eapply hash_entry_sound; eauto using lang_model_ok;
        cbn beta in *.
        {
          cbn in *.
          refine (interprets_to_sort _ _ _ _ _).
          apply eq_sort_refl.
          econstructor; eauto.
          {
            eapply H1; basic_utils_crush.
          }
          {
            eapply eq_args_wf_l; eauto with lang_core.
            2: eapply eq_args_sym; eauto  with lang_core.
            1,3:assert (In (v, sort_rule c' args) l)
                by (apply H1; basic_utils_crush);
              use_rule_in_wf; basic_core_crush.
            1: apply core_model_ok; eauto.
            eapply all2_Symmetric in H9; try apply lang_model_eq_PER; eauto.
            eapply all2_model_eq_eq_args; eauto.
            2:assert (In (v, sort_rule c' args) l)
                by (apply H1; basic_utils_crush);
              use_rule_in_wf; basic_core_crush.
            eapply wf_args_subst_monotonicity; eauto with lang_core.
            { eapply wf_args_lang_monotonicity; eauto. }
            { eapply wf_ctx_lang_monotonicity; eauto. }
            {
              assert (In (v, sort_rule c' args) l)
                by (apply H1; basic_utils_crush).
              use_rule_in_wf;
                basic_core_crush.
            }
            {
              eapply wf_subst_from_wf_args; eauto.
            }
          }
        }
        cbn beta; intros; break.
        unfold option_relation; cbn.
        unfold atom_sound_for_model in H11; cbn in H11.
        eapply Mmap_extends in Hma; eauto; cbn in *.
        rewrite Hma in H11; cbn in *.
        iss_case.
        pose proof H1.
        eapply interprets_to_sort_rule in H11; eauto; break.
        2:apply H1; basic_utils_crush.
        subst.
        pose proof (lang_model_eq_PER _ H).
        etransitivity; [symmetry; constructor; eauto|].
        symmetry.
        constructor.
        eapply sort_con_congruence; eauto.
        { apply H1; basic_utils_crush. }
        eapply all2_model_eq_eq_args; eauto.
        2:assert (In (v, sort_rule c' args) l)
                by (apply H1; basic_utils_crush);
              use_rule_in_wf; basic_core_crush.
        2:{ apply all2_Symmetric; eauto; apply H11. }
        eapply wf_args_subst_monotonicity; eauto.
        { eapply wf_args_lang_monotonicity; eauto. }
        { eapply wf_ctx_lang_monotonicity; eauto. }
        {
          assert (In (v, sort_rule c' args) l)
            by (apply H1; basic_utils_crush).
          use_rule_in_wf;
            basic_core_crush.
        }
        {
          eapply wf_subst_from_wf_args; eauto.
        }
      }
    Qed.
  (*
    Lemma add_open_term'_sound e t
      : wf_term l c e t ->
        forall i', map.extends i' i ->
        state_sound_for_model lang_model i'
          (add_open_term' succ sort_of l with_sorts add_open_sort r e)
          (fun i x => map.get i x = Some (inl e[/s/])).
    Proof.
      intro Hwf.
      pattern e.
      pattern t.
      revert e t Hwf.
      apply WfCutElim.wf_term_cut_ind; intros;
        cbn [add_open_term'].
      {
        pose proof H0;
          eapply all_fresh_named_list_lookup_err_in in H0; eauto with lang_core.
        rewrite <- H0; clear H0.
        ssm_bind.
        {
          eapply state_sound_for_model_Mmap_dep.
          {
            
            
          TODO: should I just write the mutual one for ease of access?
        case
        cb
        WfCutElim.wf_cut_ind
    Admitted.
    *)

      (*
    Lemma add_open_term'_sound (i : V_map _) with_sorts r s c e t
      : wf_subst l [] s c ->
        wf_term l c e t ->
        assign_subst_in_instance s i r ->
        state_sound_for_model lang_model i
          (add_open_term' succ sort_of l with_sorts r e)
          (fun i x => map.get i x = Some (inl e[/s/])).
    Proof.
      unfold add_open_term.
      intros Hsub H.
      pattern e.
      pattern t.
      revert e t H.
      apply WfCutElim.wf_term_cut_ind; intros.
      {
    Admitted.
       *)
    
    Context (l : lang) (Hwf : wf_lang l) (sort_of_fresh : fresh sort_of l).
    
    Lemma add_open_sort_sound (i : V_map _) with_sorts r s c t
      : wf_args l [] s c ->
        wf_sort l c t ->
        wf_ctx l c ->
        map fst c = map fst r ->
        args_in_instance l s i (map snd r) ->
        state_sound_for_model (lang_model l) i
          (add_open_sort succ sort_of l with_sorts r t)
          (fun i x => option_relation (lang_model l).(domain_eq _)
                      (map.get i x) (Some (inr t[/with_names_from c s/]))).
    Proof.
      unfold add_open_sort.
      intros; eapply add_open_sort'_sound; try eassumption.
      all: eauto with utils.
    Qed.
    
    Lemma add_open_term_sound (i : V_map _) with_sorts r s c e t
      : wf_args l [] s c ->
        wf_term l c e t ->
        wf_ctx l c ->
        map fst c = map fst r ->
        args_in_instance l s i (map snd r) ->
        state_sound_for_model (lang_model l) i
          (add_open_term succ sort_of l with_sorts r e)
          (fun i x => option_relation (lang_model l).(domain_eq _)
                      (map.get i x) (Some (inl e[/with_names_from c s/]))).
    Proof.
      unfold add_open_term.
      intros; eapply add_open_sound; try eassumption.
      2: eauto with utils.
      intros; apply add_open_sort_sound; eauto.
      { eapply wf_sort_lang_monotonicity; eauto. }
      { eapply wf_ctx_lang_monotonicity; eauto. }       
    Qed.
    
  
  Lemma add_ctx_sound (i : V_map _) with_sorts s c
    : wf_subst l [] s c ->
      wf_ctx l c ->
      state_sound_for_model (lang_model l) i
        (add_ctx succ sort_of l with_sorts c)
        (fun i r => map fst r = map fst c
                    /\ args_in_instance l (map snd s) i (map snd r)).
  Proof.
    unfold add_ctx.
    induction 1;
      intros;
      cbn [list_Mfoldr].
    { apply ret_sound_for_model'; cbn; auto. }
    {
      safe_invert H1.
      ssm_bind.
      ssm_bind.
      {
        eapply add_open_sort_sound; intuition eauto.
        apply wf_args_from_wf_subst; eauto.
      }
      ssm_bind.
      {
        eapply alloc_opaque_sound
          with (time_travel_term:= inl e : (lang_model l).(domain _));
          eauto.
        cbn; econstructor.
        eapply eq_term_refl; eauto.
      }
      ssm_bind.
      {
        eapply hash_entry_sound; eauto using lang_model_ok.
        {
          cbn.
          cbn in H9.
          rewrite H9; eauto.
        }
        { refine (interprets_to_sort_of _ _ _ _); eauto. }
      }
      ssm_bind.
      {
        clear IHwf_subst.
        eapply union_sound; eauto using lang_model_ok.
        unfold atom_sound_for_model in H11; cbn in H11.
        unfold  eq_sound_for_model; cbn.
        apply H10 in H9; cbn in *; rewrite H9 in H11; cbn in*.
        unfold option_relation in *.
        case_match; try congruence.
        apply H8 in case_match_eqn;apply H10 in case_match_eqn; cbn in *; rewrite case_match_eqn; cbn in*.
        repeat iss_case; cbn.
        assert (lang_model_interprets_to l sort_of [inl e] (inr t [/s /]))
          by (econstructor; eauto).
        pose proof (lang_model_eq_PER _ Hwf) as HPER.
        etransitivity; try eassumption.
        etransitivity.
        2:{ eapply interprets_to_functional with (m:=lang_model l); try apply H12; eauto using lang_model_ok.
            cbn.
            intuition subst.
            econstructor.
            eapply eq_term_refl; eauto.
        }
        econstructor.
        eapply eq_sort_subst; eauto.
        { eapply eq_sort_refl; eauto. }
        {
          replace  (with_names_from c' (map snd s)) with s.
          { eapply eq_subst_refl; eauto. }
          {
            revert H; clear; induction 1;
              basic_goal_prep;
              basic_utils_crush.
          }
        }
      }
      {
        apply ret_sound_for_model'; repeat basic_goal_prep; auto.
        subst; split; [ f_equal; eauto |].
        apply args_in_instance_cons; eauto.
        { repeat (eapply args_in_instance_monotone; eauto). }
        {
          apply H10 in H9; cbn in *; rewrite H9; cbn.
            econstructor.
            eapply eq_term_refl; eauto.
        }
      }
    }
  Qed.
          

    Lemma sequent_of_states_sound A B m i1 s1 Post Post2 rn
      (s2 : A -> state (instance _) B)
      : state_sound_for_model m i1 s1 Post ->
        (forall a i2, map.extends i2 i1 ->
                      Post i2 a ->
                      state_sound_for_model m i2 (s2 a) Post2) ->
        model_satisfies_rule m (sequent_of_states s1 s2 rn).
    Proof.
      intros.
      unfold sequent_of_states.
      unfold curry.
      cbn [fst curry uncurry snd].
    Abort.


    Hint Rewrite combine_nil : utils.
    Hint Rewrite @map.get_empty : utils.

    (*TODO: generalize, move*)
    Lemma map_extends_empty A (i1 : V_map A) : map.extends i1 map.empty.
    Proof.
      clear succ lt_succ.
      unfold map.extends.
      basic_goal_prep.
      basic_utils_crush.
    Qed.
    Hint Resolve map_extends_empty  : utils.


    
    Lemma state_triple_lift_pre_ex S A Y P s (Q : A * S -> Prop)
      : (forall y, state_triple (P y) s Q) ->
        state_triple (fun x => exists y : Y, P y x) s Q.
    Proof.
      unfold state_triple; basic_goal_prep;
        intuition eauto.
    Qed.
    
    Lemma state_triple_lift_pre_ex_rw S A Y P s (Q : A * S -> Prop)
      : (forall y, state_triple (P y) s Q) <->
        state_triple (fun x => exists y : Y, P y x) s Q.
    Proof.
      unfold state_triple; basic_goal_prep;
        intuition eauto.
      break.
      firstorder.
    Qed.
    Hint Rewrite <- state_triple_lift_pre_ex_rw : utils.

    Lemma state_triple_lift_pre_l_rw S
     : forall (A : Type) (H4 : Prop) (P : S -> Prop) (e0 : state S A) (Q : A * S -> Prop),
        (H4 -> state_triple P e0 Q) <-> state_triple (fun i : S => H4 /\ P i) e0 Q.
    Proof.
      unfold state_triple; basic_goal_prep;
        intuition eauto.
    Qed.
    Hint Rewrite <- state_triple_lift_pre_l_rw : utils.
    
    Lemma state_triple_lift_pre_r_rw S
     : forall (A : Type) (H4 : Prop) (P : S -> Prop) (e0 : state S A) (Q : A * S -> Prop),
        (H4 -> state_triple P e0 Q) <-> state_triple (fun i : S => P i /\ H4) e0 Q.
    Proof.
      unfold state_triple; basic_goal_prep;
        intuition eauto.
    Qed.
    Hint Rewrite <- state_triple_lift_pre_r_rw : utils.

    Definition term_of_sort (t : sort) := let (n,s) := t in con n s.

    
    (*
    Lemma add_open_sort'_sound_for_model i1 c args t var_to_idx fuel
      : fuel > length l -> (*TODO: need to quatify over l*)
        wf_sort l c t ->
        wf_args l [] args c ->
        map fst var_to_idx = map fst c ->
        map.extends i1 (map.of_list (combine (map snd var_to_idx) args)) ->
        state_sound_for_model lang_model i1
          (add_open_sort' succ sort_of l false fuel var_to_idx t)
          (fun x i' => map.extends i' (map.singleton x (term_of_sort t[/with_names_from c args/])))
          (fun x => True).
    Proof.
      revert i1 c args t var_to_idx.
      induction fuel; try Lia.lia.
      intros.
      safe_invert H0.
      cbn -[Mbind].
      eapply state_triple_bind; eauto.
      {
        TODO: term, args lemmas
      basic_goal_prep.
    Qed.

    
    Lemma add_open_term'_sound_for_model i1 c args t var_to_idx add_sort
      : fuel > length l -> (*TODO: need to quatify over l*)
        wf_term l c e t ->
        wf_args l [] args c ->
        map fst var_to_idx = map fst c ->
        map.extends i1 (map.of_list (combine (map snd var_to_idx) args)) ->
        state_sound_for_model lang_model i1
          (add_open_term' succ sort_of l false add_sort var_to_idx t)
          (fun x => exists y, interp sort_of [x] = interp y /\
                                (map.of_list [(x,e[/with_names_from c args/])))
                      (*TODO: also want to say that x has the right type*)
          (fun x => True).
    Proof.
    
    Lemma add_open_sort_sound_for_model i1 c args t var_to_idx
      : wf_sort l c t ->
        wf_args l [] args c ->
        map fst var_to_idx = map fst c ->
        map.extends i1 (map.of_list (combine (map snd var_to_idx) args)) ->
        state_sound_for_model lang_model i1
          (add_open_sort succ sort_of l false var_to_idx t)
          (fun x => (map.singleton x (term_of_sort t[/with_names_from c args/])))
          (fun x => True).
    Proof.
      destruct t; basic_goal_prep.
      safe_invert H.
      unfold add_open_sort.
      TODO: fueled functions. manage cleanly
      cbn.
    Qed.


    Lemma add_ctx_sound_for_model i1 c args
      : wf_ctx l c ->
        wf_args l [] args c ->
                     (*interprets_subst_of_type l i c ->
          TODO: need that i is bounded by allocations;
          next allocation must be fresh
          TODO: is exists i' enough for queries? no!
          what I want is that any i' of the right shape
          works
                      *)
                     state_sound_for_model lang_model i1 (add_ctx succ sort_of l false c)
                       (fun var_to_idx =>(*assume same order on var_to_idx as args, c*)
                          (map.of_list (combine (map snd var_to_idx) args)))
                       (fun var_to_idx => map fst var_to_idx = map fst c).
    Proof.
      intros H1 H2.
      revert H1.
      induction H2;
        basic_goal_prep;
        autorewrite with lang_core inversion in *.
      {
        cbn.
        unfold state_sound_for_model.
        eapply state_triple_wkn_ret; eauto.
        intros.
        repeat (basic_goal_prep; subst).
        exists i1.
        basic_utils_crush.
      }
      {
        autorewrite with model in *.
        break.
        unfold add_ctx in *.
        cbn [list_Mfoldr].
        eapply state_triple_bind; eauto.
        { eapply IHwf_args; auto. }
        clear IHwf_args.
        unfold curry; intros.
        eapply state_triple_bind; eauto.
        {
          repeat (autorewrite with utils; basic_goal_prep).
          
          TODO: forgot that map fst a = map fst c. Need a postcondition for that!

    Lemma add_open_sort_sound_for_model i1 c args
      : wf_sort l c t ->
        wf_args l [] args c ->
        map fst var_to_idx = map fst c ->
        map.extends i1 (map.of_list (combine (map snd var_to_idx) s)) ->
                     (*interprets_subst_of_type l i c ->
          TODO: need that i is bounded by allocations;
          next allocation must be fresh
          TODO: is exists i' enough for queries? no!
          what I want is that any i' of the right shape
          works
                      *)
          state_sound_for_model lang_model i1
          (add_open_sort succ sort_of l false var_to_idx t)
                       (fun x i2 => map.extends i2 (map.singleton x t[/with_names_from c args/])).
    Proof.

          
          TODO: add_open_sort lemma
          
                  state_triple_lift_pre
          TODO: lift precondition
          
    Lemma add_ctx_sound_for_model i1 c args
      : wf_ctx l c ->
        wf_args l [] args c ->
                     (*interprets_subst_of_type l i c ->
          TODO: need that i is bounded by allocations;
          next allocation must be fresh
          TODO: is exists i' enough for queries? no!
          what I want is that any i' of the right shape
          works
                      *)
                     state_sound_for_model lang_model i1 (add_ctx succ sort_of l false c)
                       (fun var_to_idx i2 =>(*assume same order on var_to_idx as args, c*)
                          map.extends i2 (map.of_list (combine (map snd var_to_idx) args))).
    Proof.
          
          TODO: add_open_sort lemma!
        basic_goal_prep.
        
        TODO: use primitive pairs or something?
        cbn.
      }
        
        basic_goal_prep.
        
        state_sound_for_model_id
          : 
        exists (fun _ => i1); split.
        {
          intros.
          basic_utils_crush.
        }
        {
          unfold state_sound_for_model, state_triple, Sep.and1.
          basic_goal_prep.
          basic_utils_crush.
        }
      }
      {
        unfold state_sound_for_model, state_triple, Sep.and1.
        autorewrite with inversion lang_core model in *.
        basic_goal_prep.
        intuition idtac.
        basic_goal_prep.
        TODO: fold things into the state triple
        map.putmany
        TODO: i2 a fix;
        let i2 := open_constr:(fun vti => match vti with [] => i1 | p::vti' => _ end) in
        exists i2.
        intuition eauto.
        {
          destruct var_to_idx.
          1: basic_utils_crush.
          cbn.
          eapply Properties.map.put_extends.
          eapply H4.
          basic_goal_prep; Lia.lia.
        }
        2:{
          
        }
        {
          unfold add_ctx in *.
          basic_goal_prep.
        }        
      }
          cbn.
          TODO: do I need a post, pre?
          TODO: what is the relationship between post and pre?.
          TODO: should post, pre be monotonic? the'n Post = pre /\....
          monotonic conditions sounds attractive.
          extends clause here an instance of it.
                                                                                
          TODO: should post have access to i? then the extends clause could be included
        }
        
        basic_core_crush.
      TODO: is the model lang_model, or lang_model extended w/ some variables?.
      Need to model open terms here? no.
      Just pick an interpretation that has the ctx vars assigned appropriately.
      means we need access to the interpretations
     *)
    (*
    Lemma lang_model_satisfies_rules v r
      : In (v, r) l ->
        model_satisfies_rule V V_Eqb V lang_model (rule_to_log_rule V_map_plus V_trie succ sort_of l v r).
    Proof.
      destruct r; basic_goal_prep.
      {
        eapply sequent_of_states_sound.
        {
          unfold state_sound_for_model.
        sequent_of_states_sound
        TODO: sequent_of_states lemma, properties
      }

    Qed.
*)
    
    (*TODO: encapsulate trivial analysis*)
  (*  Theorem lang_model_of
      : model_of lang_model (map (uncurry (rule_to_log_rule _ _ succ sort_of l
                                             (H:= unit_analysis))) l).
    Proof.
      constructor; eauto using lang_model_eq_PER.
      {
        unfold interprets_to.
        basic_goal_prep.
        repeat case_match; basic_utils_crush.
        {
          pose proof H0 as H0';
            eapply interp_sort_of_unary  in H0';
            rewrite H0' in *; clear H0'.
          pose proof H1 as H1';
            eapply interp_sort_of_unary  in H1';
            rewrite H1' in *; clear H1'.
          cbn in H; break.
          inversion H; clear H; subst.
          {
            eapply lang_model_sort_of_sound in H0, H1.
            2,3: basic_core_crush.
            eapply lm_eq_sorts.
            assert (eq_sort l [] (sort_of_term d)  (sort_of_term d')).
            {
              apply eq_sort_trans with (t12 :=t);
                eapply term_sorts_eq; auto;
                basic_core_crush.
              1:eapply eq_term_wf_r; eauto with lang_core.
              all:admit.
            } *)
            (*
            repeat case_match;
              basic_goal_prep;
              rewrite ?lang_model_no_vars in *;
              tauto.
          }
          {
            repeat (case_match;
              basic_goal_prep;
                    cbn in *;
                    cbv [option_default default] in *;
                    try congruence).
            exfalso.
            symmetry in case_match_eqn2;
              eapply named_list_lookup_err_in in case_match_eqn2.
            eapply eq_sort_wf_l in H5; basic_core_crush.
          }
        }
        {
          inversion H2; inversion H3; subst.
          {
            eapply eq_term_wf_l in H0; basic_core_crush.
            eapply wf_term_con_inv in H0.
            break.
            eapply all_lang_model_args in H; eauto.
            eapply all2_eq_to_eq_args in H; eauto with lang_core.
            eapply lm_eq_terms.
            eapply term_con_congruence; eauto.
          }
          {
            exfalso.
            eapply term_sort_impossible_helper;
              try eapply eq_sort_wf_l;
              eauto using term_sort_impossible_helper, eq_sort_wf_l, eq_term_wf_l with model lang_core.
            all: eauto using term_sort_impossible_helper, eq_sort_wf_l, eq_term_wf_l with model lang_core.
          }
          {
            exfalso.
            eapply term_sort_impossible_helper;
              try eapply eq_sort_wf_l;
              eauto using term_sort_impossible_helper, eq_sort_wf_l, eq_term_wf_l with model lang_core.
            all: eauto using term_sort_impossible_helper, eq_sort_wf_l, eq_term_wf_l with model lang_core.
          }
          {
            eapply eq_sort_wf_l in H0; basic_core_crush.
            safe_invert H0.
            eapply all_lang_model_args in H; eauto.
            eapply all2_eq_to_eq_args in H; eauto with lang_core.
            eapply lm_eq_sorts.
            eapply sort_con_congruence; eauto.
          }
        }
      }            
      {
        (* TODO: this accudentally pulls in spurious section vars*)
        eapply all_wkn with (P:= fun _ => True); eauto.
        2: eapply PosListMap.all_True; eauto.
        basic_goal_prep.
        rewrite in_map_iff in H.
        basic_goal_prep.
        subst.



        
        basic_utils_crush.
        
        4:
      }
    Qed.
*)
(*Abort.*)
        

    (*
    Lemma sort_pat_to_clauses_next_var_fresh t l1 v v' vt
      : sort_pat_to_clauses succ sort_of l t v = (l1, (vt, v')) ->
        ~In v' (query_fvs l1).
    Proof.
      unfold sort_pat_to_clauses.
      generalize (length l).
      induction n;
        unfold writer in *;
        basic_goal_prep;
        basic_utils_crush.
      destruct t.
      unfold Basics.compose in *.
      revert H; case_match.
      unfold uncurry.
      break.
      unfold gensym.
      cbn.
      basic_goal_prep;
        basic_utils_crush.
    Admitted.
      
    Lemma ctx_to_clauses_next_var_fresh c l1 v
      : ctx_to_clauses succ sort_of l c (succ (supremum (map fst c))) = (l1, (tt, v)) ->
        ~In v (query_fvs l1).
    Proof.
      unfold ctx_to_clauses.
      remember (succ (supremum (map fst c))) as next_var.
      assert (forall x, In x (map fst c) -> lt_V x next_var).
      {
        intros.
        eapply supremum_le in H.
        cbv [le_V lt_V] in *.
        subst.
        rewrite  VtN_succ.
        shelve.
      }
      {
    Abort.

*)

    (*
    Lemma rule_model_sound n r query_assignment
      : all_fresh query_assignment ->
        In (n,r) l ->
        let r' := (rule_to_log_rule succ sort_of supremum l n r) in
        map fst query_assignment = r'.(query_vars _ _) ->
        assignment_satisfies lang_model query_assignment r'.(query_clauses _ _) ->
        exists out_assignment,
          assignment_satisfies lang_model (query_assignment ++ out_assignment)
            r'.(write_clauses _ _)
          /\ assignment_unifies lang_model (query_assignment ++ out_assignment)
               r'.(write_unifications _ _).
    Proof.
      intros.
      subst r'.
      destruct r;
        basic_goal_prep.
      all: repeat lazymatch goal with
             H : context [let '(_,_) := ?e in _ ] |- _ =>
               let Htuple := fresh "Htuple" in
               destruct e as [? [ [] ? ] ] eqn:Htuple
             end.
      all: basic_goal_prep.
      {
        (* TODO: ctx lemma to imply wf args at right types*)
        assert(exists l2, incl l2 query_assignment
                          /\ wf_subst l [] l2 n0)
          by admit.
        break.
        assert (all_fresh x).
        {
          use_rule_in_wf.
          basic_core_crush.
        }
        eexists [(v,con n (map snd x))]; cbn; intuition eauto.
        replace (list_Mmap (named_list_lookup_err (query_assignment
                                                     ++ [(v, con n (map snd x))]))
                   (map fst n0))
          with (Some (map snd x)).
        2:{
          erewrite list_Mmap_ext with (g:= named_list_lookup_err x).
          2:{
            intros.
            erewrite <- wf_subst_dom_eq in H6; eauto.
            eapply pair_fst_in_exists in H6; break.
            erewrite named_list_lookup_prefix with (v:=x1); [|symmetry].
            all: rewrite all_fresh_named_list_lookup_err_in; eauto.
          }
          {            
            erewrite <- wf_subst_dom_eq; eauto.
            eapply Mmap_lookup_self; eauto.
          }
        }
        {
          eqb_case n sort_of.
          {
            exfalso.
            eapply pair_fst_in in H0.
            eapply sort_of_fresh in H0; eauto.
          }
          {
            cbn.
            assert (~In v (query_fvs l1)) by admit (*holds b/c v is fresh after ctx_to_clauses*).        
            lazymatch goal with
              |- named_list_lookup_err (?query_assignment ++ ?out) ?v <$> ?RHS =>
                replace (named_list_lookup_err (query_assignment ++ out) v)
                with (named_list_lookup_err out v)
            end.
            {
            cbn.
            autorewrite with utils bool.
            cbn.
            eapply lm_eq_sorts.
            eapply eq_sort_refl.
            econstructor; eauto with lang_core.
            }
            {
              eapply named_list_lookup_suffix; eauto.
              congruence.
            }
          }
        }
      }
      (*}*)
        (*
        Lemma ctx_to_clauses_var
          : next_var > all map fst c ->
          ctx_to_clauses succ sort_of n0 next_var = (l1, (tt, next_var')) ->
          next_var' > fvs l1.
          
        Lemma ctx_to_clauses_sound
          : next_var > all map fst c ->
          ctx_to_clauses succ sort_of n0 next_var = (l1, (tt, next_var')) ->
          matches assignment l1 ->
          wf_subst l [] (combine (map fst c) (map (lookup assignment) (map fst c))) c.

          (* TODO: does this depend on being conjoined w/ ctx_clauses?
             TODO: what to say about wf type clauses added?

             TODO: need separate lemma for query and for add?
             Probably no?
           *)
        Lemma term_pat_to_clauses_sound
          :  next_var > fvs e ->
             term_pat_to_clauses succ e next_var = (l1, (x, next_var')) ->
             matches assignment l1 ->
             let s := (combine (fvs e) (map (lookup assignment) (fvs e))) in
             lookup assignment x = Some e [/s/].
                
        
        TODO: ctx_to_clauses lemma
        eqb_case n sort_of.
        {
          revert dependent l1.
          TODO: stateT writer tactics?
          Or, as thought, change to reuse more code first?
          TODO: some kind of nested induction?
                     should be a cleaner way?
        lazymatch goal with
        | H : Is_Some_satisfying ?P ?ma |- _ =>
            let Hopt := fresh "Hopt" in
            destruct ma eqn:Hopt
        end.
        unfold Is_Some_satisfying in H0.
        revert H0.
        case_match. [| tauto].
        eqb_case n sort_of.
        {
        TODO: ctx_to_clauses lemma


          destruct (ctx_to_clauses succ sort_of n0 (supremum (map fst n0))) as [? [ [] ?] ] eqn:Hctx.
        TODO: 
        cbn in *.
        basic_goal_prep.
        TODO: why false assumption?
        basic_utils_crush.
    Qed.
         *)
    Abort.

    Theorem lang_model_of
      : model_of lang_model (map (uncurry (rule_to_log_rule succ sort_of supremum l)) l).
    Proof.

      
    Abort.

    *)
    
    (*TODO: many of these relations can be functions. what's the best way to define them?*)
    (*Fixpoint open_term_in_egraph sub e ex :=
      match e with
      | var x => In (x,ex) sub
      | con n s =>
          exists s',
          atom_in_egraph (Build_atom n s' ex) i
          /\ all2 (open_term_in_egraph sub) s s'
      end.

    Definition open_sort_in_egraph sub t tx :=
      match t with
      | scon n s =>
          exists s',
          atom_in_egraph (Build_atom n s' tx) i
          /\ all2 (open_term_in_egraph sub) s s'
      end.

    Local Notation sort_in_egraph := (open_sort_in_egraph []).
    Local Notation term_in_egraph := (open_term_in_egraph []).
*)

    (* Note: not using a sort_of analog disallows presorts. Is that ever a downside?*)
    (*Definition egraph_wf_sort t :=
      exists tx, sort_in_egraph t tx.

    Definition has_sort_idx ex tx := atom_in_egraph (Build_atom sort_of [ex] tx) i.
    

    Definition has_sort ex sub t :=      
      exists tx,
        open_sort_in_egraph sub t tx
        /\ has_sort_idx ex tx.


    Definition egraph_wf_term e t :=
      exists ex tx,
        term_in_egraph e ex
        /\ sort_in_egraph t tx
        /\ has_sort_idx ex tx.

    Definition egraph_eq_sort t1 t2 :=
      exists tx,
        sort_in_egraph t1 tx
        /\ sort_in_egraph t2 tx.
    
    Definition egraph_eq e1 e2 t :=
      exists ex tx,
        term_in_egraph e1 ex
        /\ term_in_egraph e2 ex
        /\ sort_in_egraph t tx
        /\ atom_in_egraph (Build_atom sort_of [ex] tx) i.

    
    Fixpoint idxs_have_sorts s (c:ctx) :=
      match s, c with
      | [], [] => True
      | i::s, (x,t)::c =>
          has_sort i (combine (map fst c) s) t
          /\ idxs_have_sorts s c
      | _, _ => False
      end.
*)

    (*
    Definition sort_atom_wf '(Build_atom f s out) (i : V) :=
      match named_list_lookup_err f l with
      | Some (sort_rule c args) => idxs_have_sorts s c
      | _ => False
      end.
    
    Definition term_atom_wf '(Build_atom f s out) i :=
      match named_list_lookup_err f l with
      | Some (term_rule c args t) =>
          exists tx,
          idxs_have_sorts s c
          /\ sort_in_egraph t tx
          /\ has_sort i tx
      | _ => False
      end.
    *)

    (*TODO: Should it derivable from atom_eq? Any reason to keep 2nd def?*)
   (* Definition atom_wf '(Build_atom f s out) :=
      (* TODO: do I need to add any properties for the sort_of atoms?*)
      match named_list_lookup_err l f with
      | Some (sort_rule c args) => idxs_have_sorts s c
      | Some (term_rule c args t) =>
          idxs_have_sorts s c
          /\ has_sort out (combine (map fst c) s) t
      (*TODO: has_sort here or in sort_of case? shouldn't have both*)
      | None =>
          f = sort_of
         (* /\ match s with
             | [ex] => exists f' args', atom_in_egraph (f',args',ex)
                                        /\ open_sort_in_egraph (sort_of f') out
             | _ => False
             end*)
      | _ => False
      end.
*)
    
    (*
    Definition atom_eq '(Build_atom f s out) f' s' :=
      TODO: need to inspect atoms of s, s'?.
    Answer: this is a union-find property.
    Question: would this be easier to manage if the egraph didn't replace output idxs?.
              No, merging also changes idxs.

    How to define?

     *)
    Arguments uf_rel {idx}%type_scope {idx_map rank_map} uf1 _ _.

    (*TODO: move to FunctionalDB.v*)
    (* TODO: invariant currently depends on i! Seems undesirable*)

    (*


        : forall a b,
          atom_in_egraph a ->
          atom_in_egraph b ->
          let a' := fst (canonicalize a i) in
          let b' := fst (canonicalize b i) in
          a.(atom_ret) = b.(atom_ret) ->
          invariant a' b.(atom_fn) b.(atom_args);

    Class egraph_wf : Prop :=
      {
        egraph_wf_is_ok :> egraph_ok;
        egraph_sound_eq_sort
        : forall t1 t2, egraph_eq_sort t1 t2 -> eq_sort l [] t1 t2;
        egraph_sound_eq_term
        : forall e1 e2 t, egraph_eq e1 e2 t -> eq_term l [] t e1 e2;
        (*needed for intermetiate steps.
          TODO: can I extract this out?
         *)
        egraph_sound_union_find
        : 
      }.
      
      (forall a, atom_in_egraph a -> atom_wf a)
      (* TODO: union-find;
         Note: exists implies forall
       *)
      /\ (forall x y,
             interp_uf _ _ _ _ i.(equiv _ _ _ _ _) x y ->
             exists e1 e2 t,
               eq_term l [] t e1 e2
               /\ term_in_egraph e1 x
               /\ term_in_egraph e2 y
         ).
    
    Context (Hwf : egraph_wf).
     *)

    (*equivalent to the longer one below*)
    (*Theorem egraph_sound_eq
      : (forall t1 t2, egraph_eq_sort t1 t2 -> eq_sort l [] t1 t2)
        /\ (forall e1 e2 t, egraph_eq e1 e2 t -> eq_term l [] t e1 e2).
    Proof.
      split.
      2:{
        unfold egraph_eq.
        intros.
        destruct H as [ex [tx H] ].
        intuition idtac.
        cbn in *.
        assert (interp_uf _ _ _ _ i.(equiv) ex ex) by admit
        (*TODO: need to know ex in uf*).
       (* eapply Hwf in H2.
        break.
        TODO: not sufficient? also need pretty much this properrty in assumption.
        Question: is there anything to prove here?.
        The egraph invariant might be precisely the end theorem.
        Question: how to connect egraph invariant at the FnDb interface?.
        Want a way to prove things on the FnDb side w/out term knowledge.
        Need to prove that rw_set preserves invariant, right?.
        And that it holds for empty (or can that be implied by its structure?).
        Separation of concerns:
          - this file only proves facts about EqLog clauses & terms
          - all proofs about the egraph data structure are in fndb
        revert e2 t ex tx H.
        
        TODO: how to prove this?
        *)
    Admitted.
     *)

    (*
    Lemma egraph_sound_wf_sort t : egraph_wf_sort t -> wf_sort l [] t.
    Proof.
      destruct 1; eapply eq_sort_wf_l; eauto with lang_core.
      eapply egraph_sound_eq; econstructor; eauto.
    Qed.
    
    Lemma egraph_sound_wf e t : egraph_wf_term e t -> wf_term l [] e t.
    Proof.
      destruct 1 as [x H].
      destruct H as [x' ?].
      eapply eq_term_wf_l; eauto with lang_core.
      eapply egraph_sound_eq; repeat econstructor; intuition eauto.
    Qed.
    *)

End WithVar.
