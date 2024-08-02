Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Tools.AllConstructors
  Compilers.Compilers Compilers.CompilerFacts
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
          && (freshb n entry.(entry_cmp_pre))
          && (all_freshb entry.(entry_cmp_pre))
      | None => false
      end.

    Definition rule_is_eqn (r:rule) :=
      match r with
      | sort_rule x x0
      | term_rule x x0 _ => false
      | sort_eq_rule x x0 x1
      | term_eq_rule x x0 x1 _ => true
      end.

    Fixpoint cmp_wf_in_db' cmp_pre cmp src :=
      match src with
      | [] => eqb cmp []
      | (n,r)::src' =>
          if rule_is_eqn r
          then (case_wf_in_db (cmp++cmp_pre) n r None)
               && (cmp_wf_in_db' cmp_pre cmp src')
          else match cmp with
               | [] => false
               | (n', cc)::cmp' =>
                   (eqb n n')
                   && (case_wf_in_db (cmp++cmp_pre) n r (Some cc))
                   && (cmp_wf_in_db' cmp_pre cmp' src')
               end
      end.
    
    Definition cmp_wf_in_db cmp_pre cmp src :=
      (cmp_wf_in_db'  cmp_pre cmp src )
      && (all_freshb (cmp++cmp_pre)).

    (*TODO: move to utils*)
    Definition option_to_list {A} ma : list A :=
      match ma with Some x => [x] | None => [] end.

    Definition wf_entry '(n,e) :=
      preserving_compiler_ext
        (tgt_Model := core_model e.(entry_tgt))
        e.(entry_cmp_pre)
            (map (pair n) (option_to_list e.(entry_case)))
            [(n,e.(entry_rule))]
      /\ AllConstructors.all_constructors_rule
           (fun n0 : V => In n0 (map fst e.(entry_cmp_pre)))
           e.(entry_rule).
    
    Definition cmp_db_sound :=
      all_fresh db
      (* TODO: need an isolate sim. to wf_rule *)
      /\ all wf_entry db.

  End WithCompilerDb.
    
  Lemma empty_cmp_db_sound : cmp_db_sound [].
  Proof.
    unfold cmp_db_sound.
    basic_goal_prep;
      intuition eauto.
  Qed.

    (*TODO: move to CompilerFacts*)
  Lemma compile_strengthen_ctx_incl (cmp1 cmp2 : compiler) c
    : all_fresh cmp1 ->
      all_fresh cmp2 ->
      incl cmp1 cmp2 ->
      AllConstructors.all_constructors_ctx (fun n0 : V => In n0 (map fst cmp1)) c ->
      compile_ctx cmp1 c = compile_ctx cmp2 c.
  Proof.
    intros ? ? ?.
    induction c;
      basic_goal_prep;
      eauto.
    erewrite compile_strengthen_sort_incl;
      auto;
      try eassumption;
      basic_core_crush.
  Qed.

  Definition empty_cmp_dbP := exist _ _ empty_cmp_db_sound.

  Hint Resolve use_compute_all_fresh : utils.
    

  Lemma cmp_wf_in_db_correct db tgt cmp_pre cmp src
    : cmp_db_sound db ->
      Is_true(cmp_wf_in_db db tgt cmp_pre cmp src) ->
      preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src.
  Proof.
    unfold cmp_db_sound, cmp_wf_in_db.
    intro Hdb.
    autorewrite with bool utils.
    revert cmp.
    induction src;
      basic_goal_prep.
    1: basic_core_crush.
    unfold case_wf_in_db in *.
    revert H; destruct r; cbn; repeat case_match;
      basic_goal_prep; subst; intuition eauto.
    all: basic_utils_crush.
    1,2: destruct c0, c1; basic_goal_prep.
    5,6: destruct c; basic_goal_prep; subst.
    1,2: destruct entry_case0.
    all: lazymatch goal with
         | H : Some _ = named_list_lookup_err ?db _,
           Hall: all wf_entry ?db |-_=>
             apply named_list_lookup_err_in in H;
             eapply in_all in H; eauto;
             unfold wf_entry in H;
             cbn in *;
             basic_core_crush;
             try safe_invert H
         end.
    all: cbn in *;
      try lazymatch goal with
        | H : preserving_compiler_ext _ (_::_) (_::_) |-_=>
            try safe_invert H
        | H : preserving_compiler_ext _ [] (_::_) |-_=>
            try safe_invert H
           end.
    all: try econstructor; eauto.
    all: basic_goal_prep;basic_core_crush.
    (*TODO: make rewrites *)
    all: repeat lazymatch goal with
            | H : Is_true (freshb _ _) |- _ =>
               eapply use_compute_fresh in H
            | H : Is_true (all_freshb _) |- _ =>
               eapply use_compute_all_fresh in H
            | H : Is_true (inclb _ _) |- _ =>
               eapply use_inclb in H               
           end.
    {
      eapply wf_sort_lang_monotonicity; eauto.
      erewrite <- compile_strengthen_ctx_incl; [eassumption| ..];
        eauto.
      all: basic_utils_crush.
      intros [x c] Hin.
      assert (x <> v1).
      {
        intro; subst.
        basic_utils_crush.
      }                    
      eapply H12 in Hin.
      basic_goal_prep;basic_core_crush.
    }
    {
      eapply wf_term_lang_monotonicity; eauto.
      erewrite <- compile_strengthen_sort_incl,
         <- compile_strengthen_ctx_incl;
        [eassumption| ..];
        eauto.
      all: basic_utils_crush.
      all:intros [x c] Hin;
      assert (x <> v1) by (basic_goal_prep;basic_core_crush).                   
      all:eapply H12 in Hin; basic_goal_prep;basic_core_crush.
    }
    {
      eapply eq_sort_lang_monotonicity; eauto.
      erewrite <- compile_strengthen_sort_incl,
         <- compile_strengthen_ctx_incl; eauto.
      1:erewrite <- compile_strengthen_sort_incl with (t:=s2); eauto.
    }
    {
      eapply eq_term_lang_monotonicity; eauto.
      erewrite <- compile_strengthen_sort_incl,
         <- compile_strengthen_incl,
         <- compile_strengthen_ctx_incl; eauto.
      1:erewrite <- compile_strengthen_incl with (e:=t2); eauto.
    }
  Qed.
  
  Lemma cmp_db_append_sound db1 db2
    : Is_true(all_freshb (db1++db2)) ->
      cmp_db_sound db1 ->
      cmp_db_sound db2 ->
      cmp_db_sound (db1++db2).
  Proof.
    intro H.
    apply use_compute_all_fresh in H.
    unfold cmp_db_sound.
    intuition eauto.
    clear H H2 H0.
    revert H3.
    induction db1;
      basic_goal_prep;
      basic_core_crush.
  Qed.

  Definition cmp_dbP_append
    (dbP1 dbP2 : { db | cmp_db_sound db })
    (check : Is_true(all_freshb (proj1_sig dbP1 ++ proj1_sig dbP2))) : { db | cmp_db_sound db } :=
    exist _ (proj1_sig dbP1 ++ proj1_sig dbP2)
      (cmp_db_append_sound check (proj2_sig dbP1) (proj2_sig dbP2)).

  Fixpoint cmp_to_db tgt cmp_pre (src : lang) (cmp : compiler) : named_list _ :=
    match src with
    | [] => []
    | (n,r)::src' =>
        if rule_is_eqn r
        then (n,Build_compiler_db_entry tgt (cmp++cmp_pre) r None)
               :: (cmp_to_db tgt cmp_pre src' cmp)
        else match cmp with
             | [] => [] (* never happens*)
             | (_,cc)::cmp' =>
                 (n,Build_compiler_db_entry tgt (cmp'++cmp_pre) r (Some cc))
                   :: (cmp_to_db tgt cmp_pre src' cmp')
             end
    end.
  
  Lemma cmp_to_db_fresh n tgt cmp_pre src cmp
    : fresh n src -> fresh n (cmp_to_db tgt cmp_pre src cmp).
  Proof.
    revert cmp;
      induction src;
      destruct cmp;
      basic_goal_prep;
      basic_core_crush.
    all:destruct r;
      basic_goal_prep;
      basic_core_crush.
  Qed.

  (* TODO: move to AllCOnstructors *)
  Fixpoint all_constructorsb (P : V -> bool) e : bool :=
    match e with
    | var _ => true
    | con n s => P n && forallb (all_constructorsb P) s
    end.
  
  Definition all_constructors_sortb (P : V -> bool) t : bool :=
    match t with
    | scon n s => P n && forallb (all_constructorsb P) s
    end.

  Notation all_constructors_ctxb P c :=
    (forallb (fun p => all_constructors_sortb P (snd p)) c).
  
  Definition all_constructors_ruleb P r :=
    match r with
    | sort_rule c _ => all_constructors_ctxb P c
    | term_rule c _ t => all_constructors_ctxb P c && all_constructors_sortb P t
    | sort_eq_rule c t1 t2 =>
        all_constructors_ctxb P c
        && all_constructors_sortb P t1
        && all_constructors_sortb P t2
    | term_eq_rule c e1 e2 t =>
        all_constructors_ctxb P c
        && all_constructors_sortb P t
        && all_constructorsb P e1
        && all_constructorsb P e2
    end.

  Fixpoint all_constructors_in_lang ctrs_pre l :=
    match l with
    | [] => True
    | (n,r)::l' =>
        let l_ctrs := map fst (filter (fun x => negb (rule_is_eqn (snd x))) l') in
        all_constructors_rule (fun n0 : V => In n0 (l_ctrs ++ ctrs_pre)) r
        /\ all_constructors_in_lang ctrs_pre l'
    end.
  
  Fixpoint all_constructors_in_langb ctrs_pre l :=
    match l with
    | [] => true
    | (n,r)::l' =>
        let l_ctrs := map fst (filter (fun x => negb (rule_is_eqn (snd x))) l') in
        all_constructors_ruleb (fun n0 : V => inb n0 (l_ctrs++ctrs_pre)) r
        && all_constructors_in_langb ctrs_pre l'
    end.

  
  Lemma all_constructorsb_spec Pb P e
    : (forall x, Is_true (Pb x) <-> P x) ->
      Is_true (all_constructorsb Pb e) <-> all_constructors P e.
  Proof.
    intro Prw.
    induction e;
      basic_goal_prep;
      autorewrite with utils bool;
      try tauto.
    rewrite Prw.
    revert H; clear;
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  Lemma all_constructors_sortb_spec Pb P t
    : (forall x, Is_true (Pb x) <-> P x) ->
      Is_true (all_constructors_sortb Pb t) <-> all_constructors_sort P t.    
  Proof.
    intro Prw.
    destruct t;
      basic_goal_prep;
      autorewrite with utils bool;
      try tauto.
    rewrite Prw.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    { rewrite <- all_constructorsb_spec; eauto. }
    { rewrite all_constructorsb_spec; eauto. }      
  Qed.

  
    
  Lemma all_constructors_ctxb_spec Pb (P : V -> Prop) (c : ctx)
    : (forall x, Is_true (Pb x) <-> P x) ->
      Is_true (all_constructors_ctxb Pb c) <-> all_constructors_ctx P c.    
  Proof.
    intro Prw.
    induction c;
      basic_goal_prep;
      basic_utils_crush.
    { rewrite <- all_constructors_sortb_spec; eauto. }
    { rewrite all_constructors_sortb_spec; eauto. }      
  Qed.

  (*TODO: copied; move to lists*)
   Lemma all_implies A (P Q : A -> Prop) l
    : (forall x,  P x -> Q x) -> all P l -> all Q l.
  Proof.
      induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  Lemma all_constructors_ruleb_spec Pb (P : V -> Prop) (r : rule)
    : (forall x, Is_true (Pb x) <-> P x) ->
      Is_true (all_constructors_ruleb Pb r) <-> all_constructors_rule P r.    
  Proof.
    intro Prw.
    destruct r;
      basic_goal_prep;
      autorewrite with utils bool in *.
    all: rewrite ?all_constructors_ctxb_spec,
        ?all_constructors_sortb_spec,
        ?all_constructorsb_spec in *;
      try eassumption.
    all: intuition eauto.
    all: eapply all_implies; try eassumption.
    all: basic_goal_prep.
    all: rewrite ?all_constructors_ctxb_spec,
        ?all_constructors_sortb_spec,
        ?all_constructorsb_spec in *;
      try eassumption.
  Qed.   

  Lemma all_constructors_in_langb_spec l_pre l
    : Is_true (all_constructors_in_langb l_pre l) <-> all_constructors_in_lang l_pre l.
  Proof.
    induction l;
      basic_goal_prep;
      try tauto.
    autorewrite with bool utils.
    rewrite !all_constructors_ruleb_spec,
      !IHl.
    1:reflexivity.
    basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma fst_filter_lang_cmp tgt cmp_pre cmp l
    :  preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp l ->
       map fst (filter (fun x : V * rule => negb (rule_is_eqn (snd x))) l)
       = map fst cmp.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
  Qed.

  Lemma wf_cmp_sound_db tgt cmp_pre src cmp
    : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
      Is_true (all_freshb src && all_constructors_in_langb (map fst cmp_pre) src) ->
      cmp_db_sound (cmp_to_db tgt cmp_pre src cmp).
  Proof.
    unfold cmp_db_sound.
    intros H1 H2.
    autorewrite with bool utils in *; break.
    apply all_constructors_in_langb_spec in H0.
    apply use_compute_all_fresh in H.
    revert H1 H H0.
    induction 1;
      basic_goal_prep;
      try tauto;
      autorewrite with utils bool lang_core term model in *.
    all: basic_goal_prep.
    all: intuition eauto using cmp_to_db_fresh with lang_core.
    all: try eapply all_implies; eauto.
    all: basic_goal_prep.
    all: try eapply all_constructors_sort_weaken; eauto.
    all: try eapply all_constructors_term_weaken; eauto.
    all: basic_goal_prep.
    all: erewrite fst_filter_lang_cmp in *; eauto.
    all: rewrite map_app.
    all: eauto.
  Qed.
  
  (*TODO: whole-compiler append*)
  Definition db_append_cmp tgt cmp_pre cmp src
    (wfc : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src)
    (checks : Is_true (all_freshb src && all_constructors_in_langb (map fst cmp_pre) src))
    (dbP2 : { db | cmp_db_sound db }) :=
    let db1 := (cmp_to_db tgt cmp_pre src cmp) in
    let pf1 := wf_cmp_sound_db wfc checks in 
    fun (check : Is_true(all_freshb (db1 ++ proj1_sig dbP2))) =>
      exist _ (db1 ++ proj1_sig dbP2)
        (cmp_db_append_sound check pf1 (proj2_sig dbP2)).

  
End WithVar.
  
Ltac prove_by_lang_db dbP :=
  apply (lang_wf_in_db_correct _ _ (proj2_sig dbP));
  vm_compute; exact I.


Ltac prove_by_cmp_db dbP :=
  apply (cmp_wf_in_db_correct _ _ (proj2_sig dbP));
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
