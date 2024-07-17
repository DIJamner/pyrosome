Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Tools.AllConstructors Compilers.Compilers
  Elab.Elab Elab.ElabCompilers.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


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
  Notation compiler := (@compiler V term sort).
  Notation compiler_case := (@compiler_case V term sort).

  Section LangWithDb.
    Context (db : named_list (lang * rule)).

    Definition rule_wf_in_db l n r :=
      match named_list_lookup_err db n with
      | Some (l', r') =>
          (eqb r r') && (inclb l' l)
      | None => false
      end.

    Fixpoint lang_wf_in_db' l_pre l :=
      match l with
      | [] => true
      | (n,r)::l' =>
          (lang_wf_in_db' l_pre l')
          && (rule_wf_in_db (l'++l_pre) n r)
      end.

    Definition lang_wf_in_db l_pre l :=
      (lang_wf_in_db' l_pre l)
      && (all_freshb (l++l_pre)).

    Definition lang_db_sound :=
      all_fresh db
      /\ all (fun '(_,(l,r)) => wf_rule l r) db.

  End LangWithDb.

  Fixpoint lang_to_db l_pre l : named_list (lang * rule) :=
      match l with
      | [] => []
      | (n,r)::l' => (n,(l'++l_pre,r))::(lang_to_db l_pre l')
      end.
  
  Lemma lang_to_db_fresh n l_pre l
    : fresh n l -> fresh n (lang_to_db l_pre l).
  Proof.    
    induction l;
      basic_goal_prep;
      basic_core_crush.
  Qed.

  Lemma wf_lang_sound_db l_pre l
    : wf_lang_ext l_pre l ->
      lang_db_sound (lang_to_db l_pre l).
  Proof.
    unfold lang_db_sound.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    apply lang_to_db_fresh; eauto.
  Qed.

 (* #[local] Hint Resolve use_compute_fresh use_inclb use_compute_all_fresh  : utils.*)
  Lemma lang_wf_in_db_correct db l_pre l
    : lang_db_sound db ->
      Is_true(lang_wf_in_db db l_pre l) ->
      wf_lang_ext l_pre l.
  Proof.
    unfold lang_db_sound, lang_wf_in_db.
    intro Hdb.
    induction l;
      basic_goal_prep.
    1: basic_core_crush.
    unfold rule_wf_in_db in *.
    revert H; case_match; [|basic_core_crush].
    apply named_list_lookup_err_in in HeqH.
    pose proof H1 as H1'.
    eapply in_all in H1'; eauto.
    basic_goal_prep.
    autorewrite with bool utils in *.
    break; subst.
    pose proof (use_compute_fresh _ _ H2).
    pose proof (use_compute_all_fresh _ H3).
    pose proof (use_inclb _ _ H5).
    basic_core_crush.
    eapply wf_rule_lang_monotonicity; eauto.
  Qed.

  Lemma lang_db_append_sound db1 db2
    : Is_true(all_freshb (db1++db2)) ->
      lang_db_sound db1 ->
      lang_db_sound db2 ->
      lang_db_sound (db1++db2).
  Proof.
    intro H.
    apply use_compute_all_fresh in H.
    unfold lang_db_sound.
    intuition eauto.
    clear H H2 H0.
    revert H3.
    induction db1;
      basic_goal_prep;
      basic_core_crush.
  Qed.

  Lemma empty_lang_db_sound : lang_db_sound [].
  Proof.
    unfold lang_db_sound.
    basic_goal_prep;
      intuition eauto.
  Qed.

  Definition empty_lang_dbP := exist _ _ empty_lang_db_sound.

  Definition lang_dbP_append
    (dbP1 dbP2 : { db | lang_db_sound db })
    (check : Is_true(all_freshb (proj1_sig dbP1 ++ proj1_sig dbP2))) : { db | lang_db_sound db } :=
    exist _ (proj1_sig dbP1 ++ proj1_sig dbP2)
      (lang_db_append_sound check (proj2_sig dbP1) (proj2_sig dbP2)).

  
  Definition db_append_lang l_pre l (wfl : wf_lang_ext l_pre l)
    (dbP2 : { db | lang_db_sound db }) :=
    let db1 := (lang_to_db l_pre l) in
    let pf1 := wf_lang_sound_db wfl in 
    fun (check : Is_true(all_freshb (db1 ++ proj1_sig dbP2))) =>
      exist _ (db1 ++ proj1_sig dbP2)
        (lang_db_append_sound check pf1 (proj2_sig dbP2)).


  
  Record compiler_db_entry : Type :=
    {
      entry_tgt : lang;
      entry_cmp_pre : compiler;
      entry_rule : rule;
      (* should be None iff rule is an equation *)
      entry_case : option compiler_case;
    }.

  
  (*TODO: move to CompilerDefs.v*)
  Instance compiler_case_eqb : Eqb compiler_case :=
    fun c1 c2 =>
      match c1, c2 with
      | term_case args e, term_case args' e' => (eqb args args') && (eqb e e')
      | sort_case args t, sort_case args' t' => (eqb args args') && (eqb t t')
      | _, _ => false
      end.

  Instance compiler_case_eqb_ok : Eqb_ok compiler_case_eqb.
  Proof.
    intros a b;
      destruct a, b;
      cbn; try congruence.
    all: lazymatch goal with
         | |- if eqb ?x ?y && eqb ?v ?w then _ else _ =>
             eqb_case x y;
             eqb_case v w;
             eauto; try congruence
         end.
  Qed.
    
  Section WithCompilerDb.    
    Context (db : named_list compiler_db_entry).

    Context (tgt : lang).
    

    Definition case_wf_in_db cmp_pre n r mc :=
      match named_list_lookup_err db n with
      | Some entry =>
          (eqb r entry.(entry_rule))
          && (eqb mc entry.(entry_case))
          && (inclb entry.(entry_tgt) tgt)
          && (inclb entry.(entry_cmp_pre) cmp_pre)
      | None => false
      end.

    Definition rule_is_eqn (r:rule) :=
      match r with
      | sort_rule x x0
      | term_rule x x0 _ => false
      | sort_eq_rule x x0 x1
      | term_eq_rule x x0 x1 _ => true
      end.

    Fixpoint cmp_wf_in_db cmp_pre cmp src :=
      match src with
      | [] => true
      | (n,r)::src' =>
          if rule_is_eqn r
          then (case_wf_in_db (cmp++cmp_pre) n r None)
               && (cmp_wf_in_db cmp_pre cmp src')
          else match cmp with
               | [] => false
               | (n', cc)::cmp' =>
                   (eqb n n')
                   && (case_wf_in_db (cmp++cmp_pre) n r (Some cc))
                   && (cmp_wf_in_db cmp_pre cmp' src')
               end
      end.

    (*TODO: move to utils*)
    Definition option_to_list {A} ma : list A :=
      match ma with Some x => [x] | None => [] end.

    Definition wf_entry '(n,e) :=
      preserving_compiler_ext
        (tgt_Model := core_model e.(entry_tgt))
        e.(entry_cmp_pre)
            (map (pair n) (option_to_list e.(entry_case)))
            [(n,e.(entry_rule))].
    
    Definition cmp_db_sound :=
      all_fresh db
      (* TODO: need an isolate sim. to wf_rule *)
      /\ all wf_entry db.

  End WithCompilerDb.
  
End WithVar.
  
Ltac prove_by_lang_db dbP :=
  apply (lang_wf_in_db_correct _ _ (proj2_sig dbP));
  vm_compute; exact I.

(*TODO: this doesn't work since if 2 files overwrite it, importing 1 will erase the other*)
(* set up a default db 
Ltac2 mutable lang_db () := constr:(empty_dbP (V:=string)).

*)

(*TODO: update coq minimum version to use ltac2val 
Tactic Notation "by_lang_db" :=
  ltac2:(ltac1:(x|- prove_by_lang_db x)
                 (Ltac1.of_constr (lang_db ()))).
Tactic Notation "by_lang_db" constr(db) := prove_by_lang_db db.
*)
