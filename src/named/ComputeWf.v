Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Term Core.
Import Core.Notations.

Import OptionMonad.

Section Terms.
  Context (l : lang).
  

Fixpoint compute_noconv_wf_term c e fuel : option sort :=
  match e with
  | var x => named_list_lookup_err c x
  | con name s =>
    do (S fuel') <- do ret fuel;
       (term_rule c' args t) <- named_list_lookup_err l name;
         tt <- compute_noconv_wf_args c s c' fuel';
         ret t[/with_names_from c' s/]
    end
with compute_noconv_wf_args c s c' fuel : option unit :=
       match c', s with
       | [], [] => do ret tt
       | [], _ => None
       | (name,t)::c'', [] => None
       | (name,t')::c'', e::s' =>
         do (S fuel') <- do ret fuel;
            t <- compute_noconv_wf_term c e fuel';
            !(sort_eq_dec t t'[/with_names_from c'' s'/]);
            tt <- compute_noconv_wf_args c s' c'' fuel'; 
            ret tt
    end.

  Arguments compute_noconv_wf_term c !e !fuel /.
  Arguments compute_noconv_wf_args c !s !c' !fuel/.
  
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
      destruct e; destruct fuel; basic_goal_prep; basic_core_crush.
      
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      destruct r; basic_goal_prep; basic_core_crush.
      
      revert H; case_match; basic_goal_prep; [|basic_core_crush].

      safe_invert H.
      eapply wf_term_by; eauto.
      eapply compute_noconv_wf_args_sound; eauto.
      use_rule_in_wf.
      safe_invert H.
      basic_core_crush.
    }
    {
      destruct s; destruct c'; destruct fuel; basic_goal_prep; basic_core_crush.
      revert H0.
      case_match; basic_goal_prep; [|basic_core_crush].
      revert H0.
      case_match; basic_goal_prep; [|basic_core_crush].
      revert H0.
      case_match; basic_goal_prep; [|basic_core_crush].
      subst.
      clear HeqH1 H0.
      constructor.
      eapply compute_noconv_wf_term_sound; eauto.
      eapply compute_noconv_wf_args_sound; eauto.
    }
  Qed.

  Fixpoint compute_noconv_wf_subst c s c' fuel : option unit :=
       match c', s with
       | [], [] => do ret tt
       | [], _ => None
       | (name,t)::c'', [] => None
       | (name,t')::c'', (name',e)::s' =>
         do ! string_dec name name';
            t <- compute_noconv_wf_term c e fuel;
            !(sort_eq_dec t t'[/ s'/]);
            tt <- compute_noconv_wf_subst c s' c'' fuel; 
            ret tt
    end.

  Lemma compute_noconv_wf_subst_sound c s c' fuel
       : wf_lang l ->
         wf_ctx l c ->
         wf_ctx l c' ->
         Some tt = compute_noconv_wf_subst c s c' fuel ->
         wf_subst l c s c'.
  Proof using.
    intros wfl wfc.
    revert c'.
    induction s; destruct c'; basic_goal_prep; [basic_core_crush..|].
    repeat (revert H0; case_match; basic_goal_prep; [|basic_core_crush]).
    subst.
    clear HeqH2 H0.
    constructor.
    basic_core_crush.
    eapply compute_noconv_wf_term_sound; eauto.
  Qed.
    
  
  Definition compute_noconv_wf_sort c t fuel : option unit :=
  match t with
  | scon name s =>
    do (S fuel') <- do ret fuel;
       (sort_rule c' args) <- named_list_lookup_err l name;
         tt <- compute_noconv_wf_args c s c' fuel';
         ret tt
  end.

  Lemma compute_noconv_wf_sort_sound c t fuel
    : wf_lang l ->
      wf_ctx l c ->
      Some tt = compute_noconv_wf_sort c t fuel ->
      wf_sort l c t.
  Proof.
    intros wfl wfc.
    
    destruct t; destruct fuel; basic_goal_prep; basic_core_crush.
    
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    destruct r; basic_goal_prep; basic_core_crush.
    
    revert H; case_match; basic_goal_prep; [|basic_core_crush].

    safe_invert H.
    eapply wf_sort_by; eauto.
    eapply compute_noconv_wf_args_sound; eauto.
    use_rule_in_wf.
    safe_invert H.
    basic_core_crush.
  Qed.

  Fixpoint compute_noconv_wf_ctx c fuel : option unit :=
       match c with
       | [] => do ret tt
       | (name,t)::c' =>
            do ! compute_fresh name c';
            tt <- compute_noconv_wf_sort c' t fuel;
            tt <- compute_noconv_wf_ctx c' fuel; 
            ret tt
       end.
   
  Lemma compute_noconv_wf_ctx_sound c fuel
       : wf_lang l ->
         Some tt = compute_noconv_wf_ctx c fuel ->
         wf_ctx l c.
  Proof.
    intro wfl.
    induction c; basic_goal_prep.
    basic_core_crush.
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    basic_core_crush.
    apply use_compute_fresh; congruence.
    eapply compute_noconv_wf_sort_sound; eauto.
  Qed.

  
  Definition compute_noconv_wf_rule r fuel : option unit :=
    match r with
    | sort_rule c args =>
      do ! compute_sublist string_dec args (map fst c);
         tt <- compute_noconv_wf_ctx c fuel; 
         ret tt
    | term_rule c args t =>
      do ! compute_sublist string_dec args (map fst c);
         tt <- compute_noconv_wf_ctx c fuel; 
         tt <- compute_noconv_wf_sort c t fuel; 
         ret tt
    | sort_eq_rule c t t'=>
      do tt <- compute_noconv_wf_ctx c fuel; 
         tt <- compute_noconv_wf_sort c t fuel; 
         tt <- compute_noconv_wf_sort c t' fuel; 
         ret tt
    | term_eq_rule c e e' t =>
      do tt <- compute_noconv_wf_ctx c fuel; 
         tt <- compute_noconv_wf_sort c t fuel;
         t1 <- compute_noconv_wf_term c e fuel;
         t2 <- compute_noconv_wf_term c e' fuel;  
         ! sort_eq_dec t1 t; 
         ! sort_eq_dec t2 t; 
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
    all: constructor; subst;
      eauto using compute_noconv_wf_ctx_sound,
      compute_noconv_wf_sort_sound,
      compute_noconv_wf_term_sound,
      use_compute_sublist.
  Qed.

End Terms.  
    

Fixpoint compute_noconv_wf_lang l fuel : option unit :=
  match l with
  | [] => do ret tt
  | (name,t)::l' =>
    do ! compute_fresh name l';
       tt <- compute_noconv_wf_rule l' t fuel;
       tt <- compute_noconv_wf_lang l' fuel; 
       ret tt
end.

Lemma compute_noconv_wf_lang_sound l fuel
  : Some tt = compute_noconv_wf_lang l fuel ->
    wf_lang l.
Proof.
  induction l; basic_goal_prep.
  basic_core_crush.
  revert H; case_match; basic_goal_prep; [|basic_core_crush].
  revert H; case_match; basic_goal_prep; [|basic_core_crush].
  revert H; case_match; basic_goal_prep; [|basic_core_crush].
  basic_core_crush.
  apply use_compute_fresh; congruence.
  eapply compute_noconv_wf_rule_sound; eauto.
Qed.




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
