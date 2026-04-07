From Stdlib Require Import Lists.List.
From coqutil Require Import Datatypes.String Datatypes.Result.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad GallinaHintDb Ltac Result.
From Utils Require Import EGraph.Defs.
From Pyrosome.Theory Require Import Core ModelImpls.
From Pyrosome.Tools Require Import Matches Resolution EGraph.Defs EGraph.Automation.
From Pyrosome.Compilers Require Import Compilers CompilerFacts
        (*TODO: refactor so I don't need this*)
        CompilerTransitivity.
Import Core.Notations.
Import PositiveInstantiation.


Section __.
  
  Notation named_list := (@named_list string).
  Notation named_map := (@named_map string).
  Notation term := (@term string).
  Notation ctx := (@ctx string).
  Notation sort := (@sort string).
  Notation subst := (@subst string).
  Notation rule := (@rule string).
  Notation lang := (@lang string).

  
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

  Section EGraph.
    Context (rebuild_fuel saturation_fuel efuel red_fuel : nat)
      (filter reversible : string * Rule.rule string -> bool)
      (inj_rules : list (string * list string)).
    
  Section Terms.
    Context (l : lang).

    Definition eq_term_oracle c e1 e2 :=
      (fst (egraph_reducing_equal'
              l filter reversible inj_rules rebuild_fuel
              saturation_fuel efuel red_fuel c e1 e2)).

    (*
    Fixpoint eq_args_oracle c s1 s2 c' :=
      match c', s1, s2 with
      | [], [], [] => true
      | (x,t)::c', e1::s1, e2::s2 =>
          if eq_term_oracle c e1 e2 t[/with_names_from c' s2/]
          then eq_args_oracle c s1 s2 c'
          else false
      | _, _, _ => false
      end. *)

    Definition eq_args_oracle c :=
      forallb2 (fun e1 e2 => if eq_term_oracle c e1 e2 then true else false).

    (*Assumes the sorts are wf.*)
    Definition eq_sort_oracle c (t1 t2 : sort) :=
      let (n1,s1) := t1 in
      let (n2,s2) := t2 in
      (* second condition for short-circuiting *)
      match eqb n1 n2, eqb t1 t2 (*, named_list_lookup_err l n1*) with
      | true, true (*, _*) => true
      | true, false (*, Some (sort_rule c' _)*) =>
          eq_args_oracle c s1 s2 (*c'*)
      | _, _ (*, _*) => false
      end.

    Lemma eq_args_oracle_sound c s1 s2 c'
      : wf_lang l ->
        wf_ctx l c ->
        wf_ctx l c' ->
        wf_args l c s1 c' ->
        wf_args l c s2 c' ->
        Is_true (eq_args_oracle c s1 s2) ->
        eq_args l c c' s1 s2.
    Proof.
      intros wfl wfc wfc' H1.
      revert s2 wfc';
        induction H1;
        inversion 2;
        basic_goal_prep;
        basic_core_crush.
      {
        case_match; cbn in *; try tauto.
        eapply egraph_sound; eauto.
        2:{
          unfold eq_term_oracle in *.
          erewrite case_match_eqn.
          exact I.
        }
        {
          eapply wf_term_conv; eauto.
          eapply eq_sort_subst; eauto with lang_core.
          eapply eq_args_implies_eq_subst.
          eapply IHwf_args; eauto.
        }
      }
    Qed.
    
    Lemma eq_sort_oracle_sound c t1 t2
      : wf_lang l ->
        wf_ctx l c ->
        wf_sort l c t1 ->
        wf_sort l c t2 ->
        Is_true (eq_sort_oracle c t1 t2) ->
        eq_sort l c t1 t2.
    Proof.
      destruct t1, t2.
      cbn.
      eqb_case s s0; basic_goal_prep; try tauto.
      eqb_case l0 l1; basic_goal_prep; eauto with lang_core.
      safe_invert H1.
      safe_invert H2.
      use_rule_in_wf.
      eapply in_all_fresh_same in H8;[ | clear H8; eauto with lang_core ..].
      basic_core_crush.
      eapply sort_con_congruence; eauto; try typeclasses eauto.
      eapply eq_args_oracle_sound; eauto.
    Qed.

    Fixpoint compute_wf_term c e fuel : option sort :=
      match e with
      | var x => named_list_lookup_err c x
      | con name s =>
          @! let (S fuel') <?- @! ret fuel in
             let (term_rule c' args t) <?- named_list_lookup_err l name in
             let tt <- compute_wf_args c s c' fuel' in
             ret t[/with_names_from c' s/]
      end
    with compute_wf_args c s c' fuel : option unit :=
           match c', s with
           | [], [] => @! ret tt
           | [], _ => None
           | (name,t)::c'', [] => None
           | (name,t')::c'', e::s' =>
               @! let (S fuel') <?- @! ret fuel in
                  let t <- compute_wf_term c e fuel' in
                  let !(eq_sort_oracle c t t'[/with_names_from c'' s'/]) in
                  let tt <- compute_wf_args c s' c'' fuel' in
                  ret tt
           end.

    Arguments compute_wf_term c !e !fuel /.
    Arguments compute_wf_args c !s !c' !fuel/.

    (*TODO: deprecate when feasible? *)
    Lemma compute_wf_term_sound c e t fuel
      : wf_lang l ->
        wf_ctx l c ->
        Some t = compute_wf_term c e fuel ->
        wf_term l c e t
    with compute_wf_args_sound c s c' fuel
      : wf_lang l ->
        wf_ctx l c ->
        wf_ctx l c' ->
        Some tt = compute_wf_args c s c' fuel ->
        wf_args l c s c'.
    Proof.
      all: intros wfl wfc.
      {
        destruct e; destruct fuel; basic_goal_prep.
        1,2:constructor;
        eapply named_list_lookup_err_in; now eauto.
        1: now safe_invert H.
        case_match; basic_goal_prep; [|basic_core_crush].
        (*TODO: Some = default rewrite?*)
        unfold default, option_default in H.
        case_match; basic_goal_prep; try congruence.
        case_match; basic_goal_prep; try congruence.
        (*TODO: why is this slow? basic_core_firstorder_crush.*)
        autorewrite with rw_prop inversion utils in *.
        subst.
        symmetry in case_match_eqn.
        eapply named_list_lookup_err_in in case_match_eqn.
        use_rule_in_wf.
        eapply wf_term_by;
          eauto with lang_core model utils.
      }
      {
        destruct s; destruct c'; destruct fuel;
          basic_goal_prep;
          intuition break;
          autorewrite with rw_prop inversion utils model term lang_core in *;
          try tauto.
        (*TODO: automation for pushing props under matches?
          What about rewriting matches to existential or?
          The latter is probably bad.
         *)
        repeat (case_match; basic_goal_prep; [|basic_core_crush]).
        (* TODO: why does this take a long time?
          basic_core_crush. *)
        autorewrite with bool utils model term lang_core in *.
        split; eauto.
        eapply wf_term_conv.
        1: eapply compute_wf_term_sound; eauto.
        eapply eq_sort_oracle_sound; eauto.
        {
          symmetry in case_match_eqn.
          eapply compute_wf_term_sound in case_match_eqn; eauto.
          eapply eq_term_wf_sort; eauto; try typeclasses eauto.
          eapply Core.eq_term_refl; eauto.
        }
        {
          eapply wf_sort_subst_monotonicity; eauto; try typeclasses eauto.
          eapply wf_subst_from_wf_args.
          eapply compute_wf_args_sound; eauto.
        }
      }
    Qed.

    Fixpoint compute_wf_subst c s c' fuel : option unit :=
      match c', s with
      | [], [] => @! ret tt
      | [], _ => None
      | (name,t)::c'', [] => None
      | (name,t')::c'', (name',e)::s' =>
          @! let ! eqb name name' in
             let t <- compute_wf_term c e fuel in
             let !(eqb t t'[/ s'/]) in
             let tt <- compute_wf_subst c s' c'' fuel in
             ret tt
      end.

    Lemma compute_wf_subst_sound c s c' fuel
      : wf_lang l ->
        wf_ctx l c ->
        wf_ctx l c' ->
        Some tt = compute_wf_subst c s c' fuel ->
        wf_subst l c s c'.
    Proof using.
      intros wfl wfc.
      revert c'.
      induction s; destruct c'; basic_goal_prep; [basic_core_crush..|].
      repeat (revert H0; case_match; basic_goal_prep; [|basic_core_crush]).
      autorewrite with bool utils model term lang_core in *.
      subst.
      intuition eauto.
      eapply compute_wf_term_sound; eauto.
    Qed.
    
    
    Definition compute_wf_sort c t fuel : option unit :=
      match t with
      | scon name s =>
          @! let (S fuel') <?- @! ret fuel in
             let (sort_rule c' args) <?- named_list_lookup_err l name in
             let tt <- compute_wf_args c s c' fuel' in
             ret tt
      end.

    Lemma compute_wf_sort_sound c t fuel
      : wf_lang l ->
        wf_ctx l c ->
        Is_Some (compute_wf_sort c t fuel) ->
        wf_sort l c t.
    Proof.
      intros wfl wfc.

      destruct t; destruct fuel; basic_goal_prep; basic_core_crush.
      
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      destruct r; basic_goal_prep; basic_core_crush.
      
      revert H; case_match; basic_goal_prep; [|basic_core_crush].

      safe_invert H.
      symmetry in case_match_eqn;
        eapply named_list_lookup_err_in in case_match_eqn.
      eapply wf_sort_by; eauto with utils.
      eapply compute_wf_args_sound; eauto.
      basic_core_crush.
    Qed.

    Fixpoint compute_wf_ctx c fuel : option unit :=
      match c with
      | [] => @! ret tt
      | (name,t)::c' =>
          @! let ! freshb name c' in
             let tt <- compute_wf_sort c' t fuel in
             let tt <- compute_wf_ctx c' fuel in
             ret tt
      end.
    
    Lemma compute_wf_ctx_sound c fuel
      : wf_lang l ->
        Is_Some (compute_wf_ctx c fuel) ->
        wf_ctx l c.
    Proof.
      intro wfl.
      induction c; basic_goal_prep.
      { basic_core_crush. }
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      revert H; case_match; basic_goal_prep; [|basic_core_crush].
      constructor; autorewrite with bool utils in *;
        eauto with utils;
        try typeclasses eauto.
      eapply compute_wf_sort_sound; eauto.
      rewrite case_match_eqn0; auto.
    Qed.

    (* For when the judgment has a non-trivial type *)
    Definition compute_wf_term' c e t fuel : option unit :=
      @!let _ <- compute_wf_sort c t fuel in
      let t' <- compute_wf_term c e fuel in
      let !(eq_sort_oracle c t t') in
      ret tt.
    
   Lemma compute_wf_term'_sound c e t fuel
      : wf_lang l ->
        wf_ctx l c ->
        Is_Some (compute_wf_term' c e t fuel) ->
        wf_term l c e t.
   Proof.
     unfold compute_wf_term'.
     basic_goal_prep.
     repeat (case_match;
             repeat (unfold default, option_default in *; basic_goal_prep);
             try tauto).
     assert (Is_Some (compute_wf_sort c t fuel)) as Hsort by (rewrite case_match_eqn; exact I).
     eapply compute_wf_sort_sound in Hsort; eauto.  
     symmetry in case_match_eqn0.
     eapply compute_wf_term_sound in case_match_eqn0; eauto.
     autorewrite with bool in *.
     eapply eq_sort_oracle_sound in case_match_eqn1; eauto using wf_term_conv, eq_sort_sym.
     eapply eq_term_wf_sort; eauto; try typeclasses eauto.
     eapply eq_term_refl; eauto.
   Qed.
       
    Definition compute_wf_rule r fuel : option unit :=
      match r with
      | sort_rule c args =>
          @! let ! sublistb args (map fst c) in
             let tt <- compute_wf_ctx c fuel in
             ret tt
      | term_rule c args t =>
          @! let ! sublistb args (map fst c) in
             let tt <- compute_wf_ctx c fuel in
             let tt <- compute_wf_sort c t fuel in 
             ret tt
      | sort_eq_rule c t t'=>
          @! let tt <- compute_wf_ctx c fuel in
             let tt <- compute_wf_sort c t fuel in 
             let tt <- compute_wf_sort c t' fuel in
             ret tt
      | term_eq_rule c e e' t =>
          @! let tt <- compute_wf_ctx c fuel in
             let tt <- compute_wf_sort c t fuel in
             let tt <- compute_wf_term' c e t fuel in
             let tt <- compute_wf_term' c e' t fuel in
             ret tt
      end.

    (*TODO: move to utils*)
    Lemma left_eq_to_Is_Some A e (x:A)
      : e = Some x -> Is_Some e.
    Proof. intro H; rewrite H; exact I. Qed.

    
    Lemma compute_wf_rule_sound r fuel
      : wf_lang l ->
        Is_Some (compute_wf_rule r fuel) ->
        wf_rule l r.
    Proof.
      intro wfl.
      destruct r; basic_goal_prep.
      all: repeat (revert H; case_match; basic_goal_prep; [|basic_core_crush]).
      all: repeat match goal with H : _ |- _ => apply left_eq_to_Is_Some in H end.
      all:autorewrite with lang_core bool utils in *.
      all:subst.
      
      all: intuition eauto using compute_wf_ctx_sound,
        compute_wf_sort_sound,
        compute_wf_term'_sound,
          use_sublistb.
      all: try tauto.
      all: apply use_sublistb; eauto; typeclasses eauto.
    Qed.

  End Terms.

  (*TODO: return result with useful error message *)
  Fixpoint compute_wf_lang l_pre l fuel : result unit :=
    match l with
    | [] => @! ret tt
    | (name,t)::l' =>
        @! let _ <- true_or (freshb name l_pre)
                      error:(name "not fresh in prefix:" (map fst l_pre)) in
           let _ <- true_or (freshb name l')
                      error:(name "not fresh in tail:" (map fst l')) in
           (* TODO: report detailed info from rule *)
           let tt <- Some_or (compute_wf_rule (l'++l_pre) t fuel)
                       error:(name "not proven to be a well-formed rule")
           in
           let tt <- compute_wf_lang l_pre l' fuel in
           ret tt
    end.

  Lemma compute_wf_lang_sound l_pre l fuel
    : wf_lang l_pre ->
      Is_Success (compute_wf_lang l_pre l fuel) ->
      wf_lang_ext l_pre l.
  Proof.
    induction l; basic_goal_prep.
    { basic_core_crush. }
    unfold true_or, Some_or in *.
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    revert H; case_match; basic_goal_prep; [|basic_core_crush].
    all: repeat match goal with H : _ |- _ => apply left_eq_to_Is_Some in H end.
    symmetry in case_match_eqn0.
    autorewrite with bool utils in *; try typeclasses eauto.
    basic_core_crush.
    eapply compute_wf_rule_sound; eauto using wf_lang_concat_hd.
    eapply wf_lang_concat_iff; intuition auto.
  Qed.

  Section __.
    Context (tgt src_pre : lang)
      (cmp_pre : @compiler string term sort)
      (fuel : nat).
    (* TODO: use Result for error reporting *)
    Fixpoint compute_preserving_compiler src cmp : option unit :=
      match src, cmp with
      | [], [] => Mret tt
      | ((n, sort_rule c args) :: src),
        ((n', sort_case cargs t) :: cmp) =>
          @!let !eqb n n' in
            let !eqb (map fst c) cargs in
            let _ <- compute_wf_sort tgt
                       (compile_ctx (cmp ++ cmp_pre) c) t fuel in
            (compute_preserving_compiler src cmp)
      | ((n, term_rule c args t) :: src),
        ((n', term_case cargs e) :: cmp) =>
          @!let !eqb n n' in
            let !eqb (map fst c) cargs in
            let _ <- compute_wf_term' tgt
                       (compile_ctx (cmp ++ cmp_pre) c) e
                       (compile_sort (cmp ++ cmp_pre) t) fuel in
            (compute_preserving_compiler src cmp)
      | ((n, sort_eq_rule c t1 t2) :: src), _ =>
          @!let!eq_sort_oracle tgt (compile_ctx (cmp ++ cmp_pre) c)
                 (compile_sort (cmp ++ cmp_pre) t1)
                 (compile_sort (cmp ++ cmp_pre) t2) in
            (compute_preserving_compiler src cmp)
      | ((n, term_eq_rule c e1 e2 t) :: src), _ =>
          @!let!eq_term_oracle tgt (compile_ctx (cmp ++ cmp_pre) c)
                 (compile (cmp ++ cmp_pre) e1)
                 (compile (cmp ++ cmp_pre) e2) in
            (compute_preserving_compiler src cmp)  
      | _,_ => None
      end.

    Context (wf_tgt : wf_lang tgt)
      (wf_src_pre : wf_lang src_pre)
      (preserving_cmp_pre
        : preserving_compiler_ext (tgt_Model:=core_model tgt)
          [] cmp_pre src_pre).

    Lemma compute_preserving_compiler_sound src cmp
      : Is_Some (compute_preserving_compiler src cmp) ->
        wf_lang_ext src_pre src ->
        preserving_compiler_ext (tgt_Model:=core_model tgt)
          cmp_pre cmp src.
    Proof.
      revert cmp; induction src;
        repeat (basic_goal_prep;
                case_match);
        basic_utils_crush;
        autorewrite with lang_core in *;
        constructor; intuition eauto;
        repeat match goal with H : _ |- _ => apply left_eq_to_Is_Some in H end.
      {
        eapply compute_wf_sort_sound; eauto.
        eapply inductive_implies_semantic; auto;
          try typeclasses eauto.
        4:eauto.
        2:eauto using wf_lang_concat.
        1:apply core_model_ok ; eauto; typeclasses eauto.
        eapply compiler_append; eauto; try typeclasses eauto;
          basic_core_crush.
        eapply all_fresh_compiler; eauto with lang_core.
      }
      {
        eapply compute_wf_term'_sound; eauto.
        eapply inductive_implies_semantic; auto;
          try typeclasses eauto.
        4: eauto.
        2:eauto using wf_lang_concat.
        1:apply core_model_ok ; eauto; typeclasses eauto.
        eapply compiler_append; eauto; try typeclasses eauto;
          basic_core_crush.
        eapply all_fresh_compiler; eauto with lang_core.
      }
      {
        eapply eq_sort_oracle_sound; eauto.
        all:eapply inductive_implies_semantic
          with (tgt_Model:=core_model tgt); auto;
          try typeclasses eauto.
        all: try (apply core_model_ok ; eauto; typeclasses eauto).
        3,5,6,7,9,10,11: eauto.
        all: try eauto using wf_lang_concat.
        all:eapply compiler_append; eauto; try typeclasses eauto;
            basic_core_crush.
        all:eapply all_fresh_compiler; eauto with lang_core.
      }
      {
        (*TODO: write lemma*)
        unfold eq_term_oracle in *.
        eapply egraph_sound; eauto.
        4:{
          assert(Is_Success(fst
      (egraph_reducing_equal' tgt filter reversible inj_rules rebuild_fuel
         saturation_fuel efuel red_fuel (compile_ctx (cmp ++ cmp_pre) n)
         (compile (cmp ++ cmp_pre) t) (compile (cmp ++ cmp_pre) t0))))
            by  (erewrite case_match_eqn; exact I).
          apply H5.
        }
        all:eapply inductive_implies_semantic
          with (tgt_Model:=core_model tgt); auto;
          try typeclasses eauto.
        all: try (apply core_model_ok ; eauto; typeclasses eauto).
        3,5,6,7,9,10,11: eauto.
        all: try eauto using wf_lang_concat.
        all:eapply compiler_append; eauto; try typeclasses eauto;
            basic_core_crush.
        all:eapply all_fresh_compiler; eauto with lang_core.
      }
    Qed.
  End __.

  (*TODO: would ideally like to infer src_pre from src &/or cmp via dbs *)
  Definition compute_preserving_compiler_with_side_conditions db db_cmp
    tgt src_pre cmp_pre fuel src cmp
    : option _ :=
    if (lang_wf_in_db db [] tgt)
       && (lang_wf_in_db db [] src_pre)
       && (lang_wf_in_db db src_pre src)
       && if (cmp_wf_in_db db_cmp tgt [] cmp_pre src_pre) then true else false
    then compute_preserving_compiler tgt cmp_pre fuel src cmp
    else None.

  Lemma compute_preserving_compiler_sound_with_side_conditions src cmp
     (tgt src_pre : lang) (cmp_pre : compiler string) (fuel : nat)
     (db : { db | lang_db_sound (V:=string) db })
     (db_cmp : { db | cmp_db_sound (V:=string) db })
     : Is_Some (compute_preserving_compiler_with_side_conditions
                  (proj1_sig db) (proj1_sig db_cmp)
                  tgt src_pre cmp_pre fuel src cmp) ->
       preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src.
  Proof.
    unfold compute_preserving_compiler_with_side_conditions, andb.
    repeat case_match; cbn; try tauto.
    intros.
    eapply compute_preserving_compiler_sound; eauto.
    1,2:apply lang_wf_in_db_correct with (db:=proj1_sig db);
    [typeclasses eauto|apply (proj2_sig db) | basic_utils_crush].
    1:apply cmp_wf_in_db_correct with (db:=proj1_sig db_cmp);
      [typeclasses eauto|apply (proj2_sig db_cmp) | basic_utils_crush].
    (*apply lang_wf_in_db_correct with (db:=proj1_sig db);
    [typeclasses eauto|apply (proj2_sig db) | basic_utils_crush].
  Qed.*)
  Admitted.

  Definition compute_wf_lang_with_side_conditions db l_pre l fuel
    : result unit :=
    @! let _ <- true_or (lang_wf_in_db db [] l_pre)
                  error:("Could not validate prefix:" (map fst l_pre)) in
      (compute_wf_lang l_pre l fuel).
  
  Lemma compute_wf_lang_sound_with_side_conditions l_pre l fuel
    (db : { db | lang_db_sound (V:=string) db })
    : Is_Success (compute_wf_lang_with_side_conditions (proj1_sig db) l_pre l fuel) ->
      wf_lang_ext l_pre l.
  Proof.
    unfold compute_wf_lang_with_side_conditions, true_or.
    repeat case_match; cbn; try tauto.
    eapply compute_wf_lang_sound.  
    apply lang_wf_in_db_correct with (db:=proj1_sig db);
    [typeclasses eauto|apply (proj2_sig db) | basic_utils_crush].
  Qed.    
    
End EGraph.

End __.

Ltac solve_wf_ctx :=
  (apply compute_wf_ctx_sound
    with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=filter_rules)
         (reversible:=fun _ => true)
         (inj_rules := empty_inj_rules);
   [ assumption | flagged_exact I ]).

Ltac compute_subst_wf :=
  apply compute_wf_subst_sound
    with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=filter_rules)
         (reversible:=fun _ => true)
         (inj_rules := empty_inj_rules);
  [ assumption
  | solve_wf_ctx
  | solve_wf_ctx
  (* TODO: update to flagged_exact *)
  | vm_compute; reflexivity ].


Ltac compute_sort_wf :=  
    apply compute_wf_sort_sound with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=filter_rules)
         (reversible:=fun _ => true)
         (inj_rules := empty_inj_rules);
    [ assumption
    | solve_wf_ctx
    | flagged_exact I].


Ltac compute_term_wf :=  
    apply compute_wf_term'_sound with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=filter_rules)
         (reversible:=fun _ => true)
         (inj_rules := empty_inj_rules);
    [ assumption
    | solve_wf_ctx
    | flagged_exact I].

Ltac compute_wf_rule :=
  apply compute_wf_rule_sound
    with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=Automation.filter_rules)
         (reversible:=fun _ => true)
         (inj_rules := empty_inj_rules);
  [ assumption | flagged_exact I].

Ltac compute_wf_lang' reverse inj :=
  let lang_db := ltac2val:(Ltac1.of_constr (hint_db_list "wf_lang_db")) in
  apply  compute_wf_lang_sound_with_side_conditions
    with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=Automation.filter_rules)
         (reversible:=reverse)
         (inj_rules := inj)
         (db := db_append_lang_list (V:=string) lang_db);
  flagged_exact I.

Ltac compute_wf_lang :=
  compute_wf_lang'
    (fun _ : string * Rule.rule string => true)
    empty_inj_rules.

Ltac compute_preserving_compiler' cmp_pre_src reverse inj :=
  let lang_db := ltac2val:(Ltac1.of_constr (hint_db_list "wf_lang_db")) in
  let cmp_db := ltac2val:(Ltac1.of_constr (hint_db_list "preserving_db")) in
  apply compute_preserving_compiler_sound_with_side_conditions
    with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=Automation.filter_rules)
         (reversible:=reverse)
         (inj_rules := inj)
         (src_pre:= cmp_pre_src)
         (db := db_append_lang_list (V:=string) lang_db)
         (db_cmp := db_append_cmp_list (V:=string) cmp_db);
  flagged_exact I.

(* TODO: automatically infer cmp_pre *)
Ltac compute_preserving_compiler cmp_pre_src :=
  compute_preserving_compiler' cmp_pre_src
    (fun _ : string * Rule.rule string => true)
    empty_inj_rules.

Ltac compute_args_wf :=
  apply compute_wf_args_sound
    with (fuel := 100)
         (rebuild_fuel := 100)
         (saturation_fuel := 10)
         (efuel := 100)
         (red_fuel := 100)
         (filter:=filter_rules)
         (reversible:=fun _ => true)
         (inj_rules := empty_inj_rules);
  [ assumption
  | solve_wf_ctx
  | solve_wf_ctx
  (* TODO: use flagged_exact *)
  | vm_compute; reflexivity].

Require Import Pyrosome.Elab.Elab.


Notation wf_args l :=
  (wf_args (Model:= core_model l)).
(*TODO: reorganize so that I don't have to do this
 *)
 Ltac t' ::=
  match goal with
  | [|- fresh _ _ ]=> compute_fresh
  | [|- sublist _ _ ]=> apply (use_sublistb); vm_compute; reflexivity
  | |- In _ _ => solve [solve_in | simpl; intuition fail]
  | |- Model.wf_term _ _ _ => cbn [Model.wf_term core_model]
  | |- wf_term ?l ?c ?e ?t =>
        let c' := eval vm_compute in c in
        let e' := eval vm_compute in e in
        let t' := eval vm_compute in t in
            change_no_check (wf_term l c' e' t');
    tryif first [has_evar c'| has_evar e' | has_evar t']
    then assumption || eapply wf_term_var || eapply wf_term_by'
    else compute_term_wf (* changed from Matches.t' to use the e-graph version *)
  | [|-wf_args ?l ?c ?s ?c'] =>
      (* changed from Matches.t' to use e-graph compute *)
        let c0 := eval vm_compute in c in
        let s0 := eval vm_compute in s in
        let c'0 := eval vm_compute in c' in
            change_no_check (wf_args l c0 s0 c'0);
    tryif first [has_evar c0| has_evar s0 | has_evar c'0]
    then simple apply wf_args_nil
         || simple eapply wf_args_cons2
         || simple eapply wf_args_cons
    else compute_args_wf
  | [|-wf_subst _ _ _] => constructor
  | |- wf_ctx (Model:= ?m) ?c =>
    let c' := eval vm_compute in c in
        change_no_check (wf_ctx (Model:= m) c');
    tryif has_evar c'
    then assumption || constructor
    else solve_wf_ctx (* changed from Matches.t' to use the e-graph version *)
  | |- wf_sort ?l ?c ?t =>
        let c' := eval vm_compute in c in
        let t' := eval vm_compute in t in
        change_no_check (wf_sort l c' t'); eapply wf_sort_by
  | [|- wf_lang _] => solve[prove_from_known_elabs]
  (*Don't use vm_compute here*)
  | [|- _ = _] => compute; reflexivity
  end.
