Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.



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

  Section Terms.
    Context (l : lang).

    Fixpoint compute_noconv_wf_term c e fuel : option sort :=
      match e with
      | var x => named_list_lookup_err c x
      | con name s =>
          @! let (S fuel') <?- @! ret fuel in
             let (term_rule c' args t) <?- named_list_lookup_err l name in
             let tt <- compute_noconv_wf_args c s c' fuel' in
             ret t[/with_names_from c' s/]
      end
    with compute_noconv_wf_args c s c' fuel : option unit :=
           match c', s with
           | [], [] => @! ret tt
           | [], _ => None
           | (name,t)::c'', [] => None
           | (name,t')::c'', e::s' =>
               @! let (S fuel') <?- @! ret fuel in
                  let t <- compute_noconv_wf_term c e fuel' in
                  let !(eqb t t'[/with_names_from c'' s'/]) in
                  let tt <- compute_noconv_wf_args c s' c'' fuel' in
                  ret tt
           end.

    Arguments compute_noconv_wf_term c !e !fuel /.
    Arguments compute_noconv_wf_args c !s !c' !fuel/.

    (*TODO: deprecate when feasible? *)
    Lemma compute_noconv_wf_term_sound c e t fuel
      : wf_lang l ->
        wf_ctx l c ->
        Some t = compute_noconv_wf_term c e fuel ->
        wf_term l c e t
    with compute_noconv_wf_args_sound c s c' fuel
      : wf_lang l ->
        wf_ctx l c ->
        wf_ctx l c' ->
        Some tt = compute_noconv_wf_args c s c' fuel ->
        wf_args l c s c'.
    Proof.
      all: intros wfl wfc.
      {
        destruct e; destruct fuel; basic_goal_prep; basic_core_firstorder_crush.
        revert H; case_match; basic_goal_prep; [|basic_core_crush].
        (*TODO: Some = default rewrite?*)
        unfold default, option_default in H.
        revert H; case_match; basic_goal_prep; try congruence.
        revert H; case_match; basic_goal_prep; try congruence.
        (*TODO: why is this slow? basic_core_firstorder_crush.*)
        autorewrite with utils in *.
        subst.
        eapply wf_term_by;
          eauto with lang_core model utils.
      }
      {
        destruct s; destruct c'; destruct fuel;
          basic_goal_prep;
          intuition break;
          autorewrite with utils model term lang_core in *;
          try tauto.
        (*TODO: automation for pushing props under matches?
          What about rewriting matches to existential or?
          The latter is probably bad.
         *)
        revert H0.
        case_match; basic_goal_prep; [|basic_core_crush].
        revert H0.
        case_match; basic_goal_prep; [|basic_core_crush].
        revert H0.
        case_match; basic_goal_prep; [|basic_core_crush].
        (* TODO: why does this take a long time?
          basic_core_crush. *)
        autorewrite with utils model term lang_core in *.
        subst.
        split; eauto.
      }
    Qed.

    Fixpoint compute_noconv_wf_subst c s c' fuel : option unit :=
      match c', s with
      | [], [] => @! ret tt
      | [], _ => None
      | (name,t)::c'', [] => None
      | (name,t')::c'', (name',e)::s' =>
          @! let ! eqb name name' in
             let t <- compute_noconv_wf_term c e fuel in
             let !(eqb t t'[/ s'/]) in
             let tt <- compute_noconv_wf_subst c s' c'' fuel in
             ret tt
      end.

    Lemma compute_noconv_wf_subst_sound c s c' fuel
      : wf_lang l ->
        wf_ctx l c ->
        wf_ctx l c' ->
        Some tt = compute_noconv_wf_subst c s c' fuel ->
        wf_subst l c s c'.
    Proof using V_Eqb_ok.
      intros wfl wfc.
      revert c'.
      induction s; destruct c'; basic_goal_prep; [basic_core_crush..|].
      repeat (revert H0; case_match; basic_goal_prep; [|basic_core_crush]).
      autorewrite with utils model term lang_core in *.
      subst.
      intuition eauto.
      eapply compute_noconv_wf_term_sound; eauto.
    Qed.
    
    
    Definition compute_noconv_wf_sort c t fuel : option unit :=
      match t with
      | scon name s =>
          @! let (S fuel') <?- @! ret fuel in
             let (sort_rule c' args) <?- named_list_lookup_err l name in
             let tt <- compute_noconv_wf_args c s c' fuel' in
             ret tt
      end.

    Lemma compute_noconv_wf_sort_sound c t fuel
      : wf_lang l ->
        wf_ctx l c ->
        Some tt = compute_noconv_wf_sort c t fuel ->
        wf_sort l c t.
    Proof.
      intros wfl wfc.
      
      destruct t; destruct fuel; basic_goal_prep; basic_core_firstorder_crush.
      
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      destruct r; basic_goal_prep; basic_core_firstorder_crush.
      
      revert H; case_match; basic_goal_prep; [|basic_core_crush].

      safe_invert H.
      eapply wf_sort_by; eauto with utils.
      eapply compute_noconv_wf_args_sound; eauto.
      basic_core_crush.
    Qed.

    Fixpoint compute_noconv_wf_ctx c fuel : option unit :=
      match c with
      | [] => @! ret tt
      | (name,t)::c' =>
          @! let ! freshb name c' in
             let tt <- compute_noconv_wf_sort c' t fuel in
             let tt <- compute_noconv_wf_ctx c' fuel in
             ret tt
      end.
    
    Lemma compute_noconv_wf_ctx_sound c fuel
      : wf_lang l ->
        Some tt = compute_noconv_wf_ctx c fuel ->
        wf_ctx l c.
    Proof.
      intro wfl.
      induction c; basic_goal_prep.
      { basic_core_crush. }
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      basic_core_firstorder_crush.
      - apply use_compute_fresh; congruence.
      - eapply compute_noconv_wf_sort_sound; eauto.
    Qed.

    
    Definition compute_noconv_wf_rule r fuel : option unit :=
      match r with
      | sort_rule c args =>
          @! let ! sublistb args (map fst c) in
             let tt <- compute_noconv_wf_ctx c fuel in
             ret tt
      | term_rule c args t =>
          @! let ! sublistb args (map fst c) in
             let tt <- compute_noconv_wf_ctx c fuel in
             let tt <- compute_noconv_wf_sort c t fuel in 
             ret tt
      | sort_eq_rule c t t'=>
          @! let tt <- compute_noconv_wf_ctx c fuel in
             let tt <- compute_noconv_wf_sort c t fuel in 
             let tt <- compute_noconv_wf_sort c t' fuel in
             ret tt
      | term_eq_rule c e e' t =>
          @! let tt <- compute_noconv_wf_ctx c fuel in
             let tt <- compute_noconv_wf_sort c t fuel in
             let t1 <- compute_noconv_wf_term c e fuel in
             let t2 <- compute_noconv_wf_term c e' fuel in 
             let ! eqb t1 t in
             let ! eqb t2 t in
             ret tt
      end.

    
    Lemma compute_noconv_wf_rule_sound r fuel
      : wf_lang l ->
        Some tt = compute_noconv_wf_rule r fuel ->
        wf_rule l r.
    Proof.
      intro wfl.
      destruct r; basic_goal_prep.
      all: repeat (revert H; case_match; basic_goal_prep; [|basic_core_crush]).

      all:autorewrite with lang_core utils in *.
      all:subst.
      
      all: intuition eauto using compute_noconv_wf_ctx_sound,
        compute_noconv_wf_sort_sound,
        compute_noconv_wf_term_sound,
        use_sublistb.
    Qed.

  End Terms.  
  

  Fixpoint compute_noconv_wf_lang l fuel : option unit :=
    match l with
    | [] => @! ret tt
    | (name,t)::l' =>
        @! let ! (freshb name l') in
           let tt <- compute_noconv_wf_rule l' t fuel in
           let tt <- compute_noconv_wf_lang l' fuel in
           ret tt
    end.

  Lemma compute_noconv_wf_lang_sound l fuel
    : Some tt = compute_noconv_wf_lang l fuel ->
      wf_lang l.
  Proof.
    induction l; basic_goal_prep.
    { basic_core_crush. }
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    basic_core_crush.
    - apply use_compute_fresh; congruence.
    - eapply compute_noconv_wf_rule_sound; eauto.
  Qed.

End WithVar.



Ltac solve_wf_ctx :=
  (apply compute_noconv_wf_ctx_sound with (fuel := 100); [ assumption | vm_compute; reflexivity ]).

Ltac compute_noconv_subst_wf :=
  apply compute_noconv_wf_subst_sound with (fuel := 100);
  [ assumption
  | solve_wf_ctx
  | solve_wf_ctx
  | vm_compute; reflexivity ].


Ltac compute_noconv_term_wf :=  
    apply compute_noconv_wf_term_sound with (fuel := 100);
    [assumption
    | solve_wf_ctx
    | vm_compute; reflexivity].
