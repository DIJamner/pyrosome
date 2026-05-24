From Stdlib Require Import Lists.List Classes.RelationClasses.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC.
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
    (* TODO (Layer C): discharge using WfCutElim.wf_cut_ind.  Sketch:
       - var case: result id is [named_list_lookup default r x]; use
         [args_in_instance_in] to recover its interpretation.
       - con case (with_sorts = false): vc_bind over the recursive
         [list_Mmap (add_open_term' ...)], then [hash_entry_sound]
         from Semantics.v.  The interprets_to witness comes from
         [interprets_to_term_rule] (above in this file).
       - con case (with_sorts = true): same plus
         [add_open_sort_inner_sound] for the type and
         [update_entry_sound] for the sort_of annotation.
       - cons-arg case for [list_Mmap]: chain via [vc_list_Mmap_outputs]
         (Utils/VC.v) and [args_in_instance_cons]. *)
    Admitted.

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
        (* TODO: discharge hash_entry step using hash_entry_sound (admitted).
           Inputs: a_out is sound for s_t[/with_names_from c s/] via
           open_args_post; the model's interprets_to witness comes from
           interprets_to_sort applied to eq_sort_refl on wf_sort_by Hrule
           against the substituted args. Output value: inr (scon n
           s_t[/with_names_from c s/]). *)
        unfold vc, hash_entry.
        admit.
    Admitted.

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
        exists i. split.
        + unfold extending_sound.
          split; [exact Hok|].
          split; [apply Properties.map.extends_refl|].
          split; [exact Hsound|].
          intros; assumption.
        + split.
          * cbn. reflexivity.
          * cbn. unfold args_in_instance. cbn. constructor.
      - (* cons case: chain vc_bind over
           add_open_sort_sound -> alloc_opaque_sound -> hash_entry_sound -> union_sound,
           then construct the extended ctx_post. *)
        admit.
    Admitted.

  End AddOpenSound.
End WithVar.
