Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.ModelImpls Theory.CutFreeInd (*Theory.ConvElim*)
  Compilers.Compilers Compilers.OperationalBridge.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS
  SimpleUnit NatHeap SimpleVCPSHeap
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC SimpleVCCHeap SimpleVFix
  CombinedThm.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Local Definition src := (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Local Definition tgt := (fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang ++ block_subst ++ value_subst).

(* TODO: move somewhere. New tools file? *)
Definition no_sort_eqnsb : lang -> bool :=
  forallb (fun r => match snd r with sort_eq_rule _ _ _ => false | _ => true end).

Lemma sort_no_eqns_fwd (l : lang) c (t1 t2 : sort)
  : wf_lang l ->
    Is_true (no_sort_eqnsb l) ->
    (let (n1,s1):= t1 in
    let (n2,s2):= t2 in
    n1=n2 /\
    match named_list_lookup_err l n1 with
    | Some (sort_rule c' args) =>
        Model.eq_args (Model:=core_model l) c c' s1 s2
    | _ => False
    end) ->
    eq_sort l c t1 t2.
Proof.
  repeat case_match; intros; basic_goal_prep; subst; try tauto.
  eapply named_list_lookup_err_in in HeqH1.
  eapply sort_con_congruence; eauto.
  typeclasses eauto.
Qed.

Lemma sort_invert_no_eqns (l : lang) c (t1 t2 : sort)
  : wf_lang l ->
    Is_true (no_sort_eqnsb l) ->
    eq_sort l c t1 t2 ->
    (let (n1,s1):= t1 in
     let (n2,s2):= t2 in
     n1=n2 /\
       match named_list_lookup_err l n1 with
       | Some (sort_rule c' args) =>
           Model.eq_args (Model:=core_model l) c c' s1 s2
       | _ => False
       end).
Proof.
  induction 3.
  {
    exfalso.
    unfold no_sort_eqnsb in *.
    basic_utils_crush.
    (*TODO: uldate this library lemma*)
    revert H0.
    unfold Is_true.
    case_match; eauto.
    symmetry in HeqH0.
    rewrite forallb_forall in HeqH0.
    eapply HeqH0 in H1; cbn in *.
    congruence.
  }
  {
    destruct t1', t2';
    basic_goal_prep.
    case_match; try tauto.
    case_match; try tauto.
    subst.
    split; auto.
    eapply @eq_args_subst_monotonicity with (Model:= core_model l).
    1:eapply ModelImpls.core_model_ok; eauto; typeclasses eauto.
    all: eauto.
    eapply named_list_lookup_err_in in HeqH6.
    basic_core_crush.
  }
  {
    destruct t;
      basic_goal_prep.
    split; auto.
    safe_invert H1.
    case_match; try tauto.
    2:{
      rewrite named_list_lookup_none_iff in HeqH1.
      basic_core_crush.
    }
    eapply named_list_lookup_err_in in HeqH1.
    eapply in_all_fresh_same in H5; eauto;
      basic_core_crush.
    eapply eq_args_refl; eauto.
    (*TODO: why isn't this inferred?*)
    apply ModelImpls.core_model_ok; eauto; typeclasses eauto.
  }
  {
    destruct t1, t12, t2;
      basic_goal_prep.
    subst.
    split; auto.
    case_match; try tauto.
    case_match; try tauto.
    eapply eq_args_trans; eauto.
    1:eapply ModelImpls.core_model_ok; eauto; typeclasses eauto.
    subst.
    eapply named_list_lookup_err_in in HeqH1.
    use_rule_in_wf.
    basic_core_crush.    
  }
  {
    destruct t1, t2;
      basic_goal_prep;
      subst.
    case_match; try tauto.
    case_match; try tauto.
    subst.
    split; auto.
    eapply named_list_lookup_err_in in HeqH2.
    eapply eq_args_sym.
    1:eapply ModelImpls.core_model_ok; eauto; typeclasses eauto.
    2:eauto.
    basic_core_crush.
  }
Qed.

Lemma sort_rewrite_no_eqns (l : lang) c (t1 t2 : sort)
  : wf_lang l ->
    Is_true (no_sort_eqnsb l) ->
    eq_sort l c t1 t2 <->
    (let (n1,s1):= t1 in
     let (n2,s2):= t2 in
     n1=n2 /\
       match named_list_lookup_err l n1 with
       | Some (sort_rule c' args) =>
           Model.eq_args (Model:=core_model l) c c' s1 s2
       | _ => False
       end).
Proof.
  split.
  { eapply sort_invert_no_eqns; eauto. }
  {
    intros.
    eapply sort_no_eqns_fwd; eauto.
  }
Qed.

(* TODO: move somewhere. New tools file? *)
Definition no_eqnsb (s : string) : lang -> bool :=
  forallb (fun r => match snd r with
                    | term_eq_rule _ _ _ (scon name _) => negb (eqb name s)
                    | _ => true
                    end).

(*
Lemma no_eqns_fwd (l : lang) s c (t1 t2 : sort)
  : wf_lang l ->
    Is_true (no_sort_eqnsb l) ->
    Is_true (no_eqnsb s l) ->
    (let (n1,s1):= t1 in
    let (n2,s2):= t2 in
    n1=n2 /\
    match named_list_lookup_err l n1 with
    | Some (sort_rule c' args) =>
        eq_args (Model:=core_model l) c c' s1 s2
    | _ => False
    end) ->
    eq_sort l c t1 t2.
Proof.
  repeat case_match; intros; basic_goal_prep; subst; try tauto.
  eapply named_list_lookup_err_in in HeqH1.
  eapply sort_con_congruence; eauto.
  typeclasses eauto.
Qed.*)


Lemma no_eqnsb_not_in name (l : lang) name0 c' e0 e3 l0
  : Is_true (no_eqnsb name l) -> ~ In (name0, term_eq_rule c' e0 e3 (scon name l0)) l.
Proof.
  unfold no_eqnsb.
  induction l;
    basic_goal_prep;
    basic_core_crush.
Qed.

Lemma invert_no_eqns (l : lang) c t name e1 e2
  : wf_lang l ->
    wf_ctx (Model:=core_model l) c ->
    Is_true (no_sort_eqnsb l) ->
    Is_true (no_eqnsb name l) ->
    Core.eq_term l c t e1 e2 ->
    forall args,
    t = (scon name args) ->
    match e1, e2 with
    | var x, var y => x = y
    | con n1 s1, con n2 s2 =>
        n1 = n2
        /\ match named_list_lookup_err l n1 with
           | Some (term_rule c' args t) =>
               Model.eq_args (Model:=core_model l) c c' s1 s2
           | _ => False
           end
    | _, _ => False
    end.
Proof.
  intros wfl wfc Hseqns Heqns.
  intro Heq.
  pattern t, e1, e2.
  revert Heq.
  (*simple apply (term_conv_ind _ l wfl c wfc); intros; subst.*)
  (*
  {
    exfalso.
    destruct t0; basic_goal_prep.
    autorewrite with utils term in *.
    intuition subst.
    eapply no_eqnsb_not_in; eauto.
  }
  {
    destruct t0; basic_goal_prep.
    autorewrite with utils term in *.
    intuition subst.
*)

(*
  TODO
  {
    destruct t; basic_goal_prep.
    safe_invert H5.
    specialize (IHeq_term _ eq_refl).
    TODO: this is the subst case.
    Does not seem to work well.
    switch alternate inductive/induction scheme w/out subst case?
    exfalso.
    unfold no_sort_eqnsb in *.
    basic_utils_crush.
    (*TODO: uldate this library lemma*)
    revert H0.
    unfold Is_true.
    case_match; eauto.
    symmetry in HeqH0.
    rewrite forallb_forall in HeqH0.
    eapply HeqH0 in H1; cbn in *.
    congruence.
  }
  {
    destruct t1', t2';
    basic_goal_prep.
    case_match; try tauto.
    case_match; try tauto.
    subst.
    split; auto.
    eapply @eq_args_subst_monotonicity with (Model:= core_model l).
    1:eapply ModelImpls.core_model_ok; eauto; typeclasses eauto.
    all: eauto.
    eapply named_list_lookup_err_in in HeqH6.
    basic_core_crush.
  }
  {
    destruct t;
      basic_goal_prep.
    split; auto.
    safe_invert H1.
    case_match; try tauto.
    2:{
      rewrite named_list_lookup_none_iff in HeqH1.
      basic_core_crush.
    }
    eapply named_list_lookup_err_in in HeqH1.
    eapply in_all_fresh_same in H5; eauto;
      basic_core_crush.
    eapply eq_args_refl; eauto.
    (*TODO: why isn't this inferred?*)
    apply ModelImpls.core_model_ok; eauto; typeclasses eauto.
  }
  {
    destruct t1, t12, t2;
      basic_goal_prep.
    subst.
    split; auto.
    case_match; try tauto.
    case_match; try tauto.
    eapply eq_args_trans; eauto.
    1:eapply ModelImpls.core_model_ok; eauto; typeclasses eauto.
    subst.
    eapply named_list_lookup_err_in in HeqH1.
    use_rule_in_wf.
    basic_core_crush.    
  }
  {
    destruct t1, t2;
      basic_goal_prep;
      subst.
    case_match; try tauto.
    case_match; try tauto.
    subst.
    split; auto.
    eapply named_list_lookup_err_in in HeqH2.
    eapply eq_args_sym.
    1:eapply ModelImpls.core_model_ok; eauto; typeclasses eauto.
    2:eauto.
    basic_core_crush.
  }
Qed. *)
Abort.

(*
Lemma sort_rewrite_no_eqns (l : lang) c (t1 t2 : sort)
  : wf_lang l ->
    Is_true (no_sort_eqnsb l) ->
    eq_sort l c t1 t2 <->
    (let (n1,s1):= t1 in
     let (n2,s2):= t2 in
     n1=n2 /\
       match named_list_lookup_err l n1 with
       | Some (sort_rule c' args) =>
           eq_args (Model:=core_model l) c c' s1 s2
       | _ => False
       end).
Proof.
  split.
  { eapply sort_invert_no_eqns; eauto. }
  {
    intros.
    eapply sort_no_eqns_fwd; eauto.
  }
Qed.
 *)

Local Lemma wf_src : wf_lang src.
Proof.
  unfold src.
  prove_from_known_elabs.
  {
    (*TODO; AUTO_ELAB Db empty?*)
Admitted.


Fixpoint sort_rule_in name c args (l : lang) :=
  match l with
  | [] => False
  | (name',sort_rule c' args')::l' =>
      (name = name' /\ c = c' /\ args = args') \/ sort_rule_in name c args l'
  | _::l' => sort_rule_in name c args l'
  end.

Fixpoint term_rule_in name c args t (l : lang) :=
  match l with
  | [] => False
  | (name',term_rule c' args' t')::l' =>
      (name = name' /\ c = c' /\ args = args' /\ t = t') \/ term_rule_in name c args t l'
  | _::l' => term_rule_in name c args t l'
  end.

Fixpoint sort_eq_rule_in name c t1 t2 (l : lang) :=
  match l with
  | [] => False
  | (name', sort_eq_rule c' t1' t2')::l' =>
      (name = name' /\ c = c' /\ t1 = t1' /\ t2 = t2') \/ sort_eq_rule_in name c t1 t2 l'
  | _::l' => sort_eq_rule_in name c t1 t2 l'
  end.

Fixpoint term_eq_rule_in name c e1 e2 t (l : lang) :=
  match l with
  | [] => False
  | (name', term_eq_rule c' e1' e2' t')::l' =>
      (name = name' /\ c = c' /\ t = t' /\ e1 = e1' /\ e2 = e2') \/ term_eq_rule_in name c e1 e2 t l'
  | _::l' => term_eq_rule_in name c e1 e2 t l'
  end.

(*To be used when l and (at least) the top level constructor of r are concrete *)
Definition rule_in name r : lang -> Prop :=
  match r with
  | sort_rule c args => sort_rule_in name c args  
  | term_rule c args t => term_rule_in name c args t
  | sort_eq_rule c t t' => sort_eq_rule_in name c t t'
  | term_eq_rule c e e' t =>  term_eq_rule_in name c e e' t
  end.

Lemma In_rule_in name r (l : lang)
  : In (name,r) l <-> rule_in name r l.
Proof.
  destruct r;
    induction l;
    basic_goal_prep;
    try case_match.
  all: intuition congruence.
Qed.


Definition terms_syntactic_of (l : lang) name :=
  forall c sargs e1 e2,
    eq_term l c (scon name sargs) e1 e2 ->
    e1 = e2.

Definition sort_injective (l : lang) name :=
  forall c sargs name' sargs',
    wf_ctx (Model:=core_model l) c ->
    eq_sort l c (scon name sargs) (scon name' sargs') ->
    forall args,
    In (name, sort_rule {c' args) l ->
    name = name' /\ eq_args (Model:=core_model l) c c' sargs sargs'.

Definition terms_injective_of (l : lang) name :=
  forall c sargs e1 e2,
    wf_ctx (Model:=core_model l) c ->
    eq_term l c (scon name sargs) e1 e2 ->
    match e1, e2 with
    | con n1 s1, con n2 s2 =>
        n1 = n2
        /\ match named_list_lookup_err l n1 with
           | Some (term_rule c' _ (scon name' _)) =>
               name' = name
               /\ eq_args (Model:=core_model l) c c' s1 s2
           | _ => False
           end
    | var x, var y =>
        x = y
    | _, _ => False
    end.

(*
Definition has_dep dep (p : list string * string) : bool :=
  inb dep (fst p).*)

Definition removeb {A} `{Eqb A} : A -> list A -> list A :=
  List.removeb (eqb (A:=A)).

(*TODO: issue: by-sort injectivity not sufficient.
  Once we add polymorphism, have to deal with substitutions on types.
  Similar ideas required for that and for value forms.
  Idea: admissible canonical forms.
  Recognize admissible ops like subst & generate the list of constructors that are canonical.
  (note: admissible means closed env)

  When this should apply:
  when all the rules of a sort match:
  (ni x...) in (t y...)
  (mj x...) in (t y...)
  (mj x...) = (ni z ...) in (t y...)

  and all mj are totally covered.
  Then all mj are admissible and if x : (t y...) then x is equiv to some (ni z...)

  Complicating note on eqns: term subst/ty subst each apply to eachother.
  to solve this, 1. look for covering where x... don't use admissible features
  2. convert extra rules between admissible features into obligations?
     - above is not automatic
 *)
Definition compute_rule_injectivity '(name,r) inj : list string := 
match r with
| sort_rule c args => name::inj  
| term_rule c args (scon tname _) => inj
| sort_eq_rule c (scon tname _) (scon t'name _) =>
    (* sound approximation *)
    removeb tname (removeb t'name inj)
| term_eq_rule c e e' (scon tname _) =>
    removeb tname inj
end.

Definition compute_injectivity (l : lang) :=
  fold_right compute_rule_injectivity [] l.

(*TODO: move to Utils *)
Lemma all_fresh_named_list_lookup_err_in_rw:
  forall [S : Type] {EqbS : Eqb S},
  Eqb_ok EqbS ->
  forall (A : Type) (c : NamedList.named_list S A) (n : S) (t : A),
    all_fresh c ->  In (n, t) c -> named_list_lookup_err c n = Some t.
Proof.
  intros.
  symmetry.
  eapply all_fresh_named_list_lookup_err_in; eauto.
Qed.


Lemma sort_initially_injective n c args l
  : wf_lang ((n, sort_rule c args) :: l) ->
    sort_injective ((n, sort_rule c args) :: l) n.
Proof.
  
Lemma sort_initially_injective n c args l
  : wf_lang ((n, sort_rule c args) :: l) ->
    terms_injective_of ((n, sort_rule c args) :: l) n.
Proof.
  unfold terms_injective_of; intros.
  enough
    (match e1, e2 with
     | var x, var y => x = y
     | _, _ => False
     end).
  {
    repeat case_match; subst; intuition eauto.
  }

  remember (scon n sargs) as t.
  assert (eq_sort ((n, sort_rule c args) :: l) c0 t (scon n sargs)) as H'.
  {
    subst.
    eapply eq_sort_refl.
    eapply eq_term_wf_sort; eauto;
      typeclasses eauto.
  }
  clear Heqt.
  revert H'.
  pattern t, e1, e2.
  revert t e1 e2 H1.
  apply term_cut_ind; eauto;
    try typeclasses eauto;
    basic_goal_prep.
  {
    exfalso.
    intuition try congruence.
    safe_invert H.
    use_rule_in_wf.
    safe_invert H.
    destruct t;
      basic_goal_prep.
    autorewrite with term utils lang_core in *.
    safe_invert H12.
    Lemma
    basic_utils_crush.
  }
  {
    intuition try congruence.
    destruct t.
    basic_goal_prep.
    autorewrite with term utils lang_core in *.
    intuition subst.
    exfalso.
    use_rule_in_wf.
    autorewrite with term utils lang_core in *.
    intuition subst.
    safe_invert H10. (*TODO: add rewrite *)
    basic_utils_crush.
  }
  {
    subst.
    destruct e1, e12, e2; intuition subst; eauto.
  }
  {
    subst;
      destruct e1, e2; intuition eauto.    
  }
  {
    eapply H3.
    subst.
    
    
    TODO: depends on sort being syntactic
  }
Qed.
    

Lemma compute_injectivity_sound l
  : wf_lang l ->
    all (sort_injective l) (compute_injectivity l).
Proof.
  induction 1;
    basic_goal_prep;
    auto.
  destruct r;
    basic_goal_prep;
    autorewrite with utils lang_core in *.
  {
    split.
    {
      clear IHwf_lang_ext.
      unfold sort_injective; intros.
      destruct e1, e2;
        subst; intuition eauto.
      {
        
        
    

Definition compute_rule_syntactic inj '(name,r) syn : list string := 
match r with
| sort_rule c args =>
    if (inb name inj)
    then name::syn
    else syn
| term_rule c args (scon tname _) => inj
| _ => syn
end.

Definition compute_syntactic (l : lang) :=
  let inj := compute_injectivity l in
  fold_right (compute_rule_syntactic inj) [] l.

Definition injectivity_holds (l : lang) (inj : injectivity) : Prop :=
  match inj with
  | Some inj_list =>
      all (fun p => all (sort_injective l) (fst p) -> sort_injective l (snd p)) inj_list
  | None => True
  end.

(*TODO: show first implies this for compute_injectivity's outputs*)
Definition injectivity_holds' (l : lang) (inj : injectivity) : Prop :=
  match inj with
  | Some inj_list =>
      all (fun p => sort_injective l (snd p)) inj_list
  | None => True
  end.

(*
Lemma sort_injective_cons_term l s n c args t
  : sort_injective l s ->
    sort_injective ((n, term_rule c args t) :: l) s.
Proof.
  unfold sort_injective.
  intros.
  eapply H.
  TODO: is this true? no (side conditions).
  TODO: how to recover extra invariants that make this true?.
  Needed: no eqns on s, recursively that have a t side-condition.
  Sufficient: no eqns on s, recursively.
  Idea: no-eqn inductive?.
  Idea: proof-prop?.*)

Lemma injectivity_holds_cons_term l n c args t inj
  : injectivity_holds l inj ->
    injectivity_holds ((n, term_rule c args t) :: l) inj.
Proof.
  destruct inj;
    basic_goal_prep;
    auto.
  revert H; induction l0;
    basic_goal_prep;
    auto.
  intuition auto.
  Lemma sort_injective_incl
    : incl l l' ->
      
  
  unfold sort_injective.
    

Lemma compute_injectivity_correct' l
  : wf_lang l ->
    injectivity_holds l (compute_injectivity l).
Proof.
  induction 1;
    basic_goal_prep;
    auto;
    case_match;
    basic_core_crush.
  2:{
  

Lemma sort_injective_cong (l : lang) name c' args
  : @wf_lang_ext string string_Eqb [] l ->
    In (name,(sort_rule c' args)) l ->
    Is_true (no_sort_eqnsb l) ->
    Is_true (no_eqnsb name l) ->
    Forall (fun '(_,scon name _) => sort_injective l name) c' ->
    forall c, wf_ctx (Model:=core_model l) c ->
              forall t e1 e2,
                eq_term l c t e1 e2 ->
                forall sargs,
                t = (scon name sargs) ->
                e1 = e2.
Proof.
  unfold sort_injective.
  rewrite Forall_forall.
  intros until c.
  intros wfc t e1 e2 H'.
  pattern t, e1, e2.
  revert t e1 e2 H'.
  eapply term_cut_ind with (V:= string);
    eauto;
    try typeclasses eauto;
    basic_goal_prep.
  {
    destruct t.
    safe_invert H7.
    exfalso.
    eapply no_eqnsb_not_in; eauto.
  }
  {
    TODO: need inductive property; working on a single name isn't good enough?
    I need the list of injective types?
    f_equal.
    clear H4.
    (*TODO: issues w/ t[//]=?*)
    revert sargs H7 H6.
    induction H5;
      basic_goal_prep;
      break;
      f_equal; eauto.
    {
      eapply H8; eauto.
      rewrite <- H8.
      
      intros; subst;
      f_equal; eauto.
    
    TODO: lost relationship between e0,e3 & args?
  2:{
    Set Printing All.
     exact H.
  {
  induction H3; intuition eauto.
  2:{
  
    

Lemma invert_no_eqns (l : lang) c t name e1 e2
  : wf_lang l ->
    wf_ctx (Model:=core_model l) c ->
    Is_true (no_sort_eqnsb l) ->
    Is_true (no_eqnsb name l) ->
    Core.eq_term l c t e1 e2 ->
    forall args,
    t = (scon name args) ->
    match e1, e2 with
    | var x, var y => x = y
    | con n1 s1, con n2 s2 =>
        n1 = n2
        /\ match named_list_lookup_err l n1 with
           | Some (term_rule c' args t) =>
               Model.eq_args (Model:=core_model l) c c' s1 s2
           | _ => False
           end
    | _, _ => False
    end.
Proof.
  

Lemma type_unique t e1 e2
  : Core.eq_term src [] t e1 e2 ->
    t = {{s #"ty" }} ->
    e1 = e2.
Proof.
  intro H.
  pattern t, e1, e2.
  simple eapply term_cut_ind with (l:=src) (c:=[]); eauto using wf_src with lang_core; try typeclasses eauto.
  all: intros; break; subst.
  {
    apply In_rule_in in H0.
    compute in H0.
    intuition subst.
    (*TODO: these subst cases should ideally be computed away*)
    all: repeat lazymatch goal with
           | H : _ = _ |- _ =>
               compute in H;
               now safe_invert H || clear H
           end.
  }
  {
    apply In_rule_in in H0.
    compute in H0.
    intuition subst.
    all: repeat lazymatch goal with
           | H : _ = _ |- _ =>
               compute in H;
               now safe_invert H || clear H
           end.
    all: f_equal.
    all: repeat lazymatch goal with
           | H : eq_args _ (_::_) _ _ |- _=>
               safe_invert H
           | H : eq_args _ [] _ _ |- _=>
               safe_invert H
           | H : P_args _ _ _ _ _ |- _ => cbn in H
           end.
    all: repeat f_equal.
    all: intuition subst.    
  }
  {
    rewrite H1; eauto.
  }
  {
    rewrite H1; eauto.
  }
  {
    eapply H2.
    eapply sort_rewrite_no_eqns in H0; eauto.
    2: apply wf_src.
    2: reflexivity.
    destruct t0.
    revert H0; repeat case_match; intros; intuition subst.
    safe_invert H4.
    reflexivity.
  }
Qed.
  

Lemma bool_type_unique t e1 e2
  : Core.eq_term src [] t e1 e2 ->
    t = {{s #"ty" }} ->
    e2 = {{e #"bool" }} <->
    e1 = {{e #"bool" }}.
Proof.
  intro H.
  pattern t, e1, e2.
  simple eapply term_cut_ind with (l:=src) (c:=[]); eauto using wf_src with lang_core; try typeclasses eauto.
  all: intros; break; subst.
  {
    apply In_rule_in in H0.
    compute in H0.
    intuition subst.
    (*TODO: these subst cases should ideally be computed away*)
    all: repeat lazymatch goal with
           | H : _ = _ |- _ =>
               compute in H;
               now safe_invert H || clear H
           end.
  }
  {
    apply In_rule_in in H0.
    compute in H0.
    intuition subst.
    all: repeat lazymatch goal with
           | H : _ = _ |- _ =>
               compute in H;
               now safe_invert H || clear H
           end.
  }
  {
    safe_invert H0.
  }
  {
    rewrite H3; eauto.
  }
  {
    rewrite H1; eauto.
    reflexivity.
  }
  {
    eapply sort_rewrite_no_eqns in H0; [| eapply wf_src | compute; reflexivity].
    destruct t0.
    break; subst.
    compute in H3.
    safe_invert H3.
    intuition congruence.
  }
Qed.
  
  
  (*
Lemma bool_val_sort_unique t
  : eq_sort src {{c }} t {{s #"val" #"emp" #"bool"}} -> t = {{s #"val" #"emp" #"bool"}}.
Proof.
  intros.
  eapply sort_rewrite_no_eqns in H; [| eapply wf_src | reflexivity].
  destruct t.
  break; subst.
  compute in H0.
  inversion H0; eauto.
  subst.
  clear H0.
  inversion H5; eauto.
  clear H5.
  subst.
  inversion H4; eauto.
  clear H4.
  subst.
  f_equal.
  f_equal.
  {
    clear H9.
    revert H8.
    TODO: induction
    safe_invert H0.
  revert H0.
  compute.
  cbn in *.
  safe_invert H0.
  safe_invert H5.
  TODO: 'sort_has_no_eqns' property, the term version of the above, enough for env.
  TODO: what about val? need custom lemma for bool
  basic_goal_prep.
f  basic_goal_prep.
*)

(*
Lemma bool_inversion_src' c v t
  : wf_term src c v t ->
    t = {{s #"val" #"emp" #"bool" }} ->
    c = [] ->
    match v with con n s => s = [ con "emp" [] ] /\ (n = "true" \/ n = "false") | var _ => False end.
Proof.
  induction 1; eauto; intros; subst; eauto with utils.
  2:{
    

  av    basic_goal_prep; subst.
  all: eauto.
  2:{
    eapply IHwf_term; eauto.
  }
  
    basic_core_crush.
    v = {{e #"true" }} \/ v = {{e #"false" }}.
  

        (*TODO: generalize to include optimization pass
          TODO: generalize beyond emp; bool
         *)
Lemma combined_compiler_cross_language' c t e s
  :  eq_term src c t e {{e #"config" "H" #"emp" #"bool" (#"ret" #"emp" #"bool" "v") }} [/s/] ->
      eq_term tgt (compile_ctx full_compiler c) (compile_sort full_compiler t)
        (compile full_compiler e) (*(compile_fn tgt c t e)*)
        {{e #"config" "H" "G" "A" (#"jmp" (#".2" #"hd") "v") }}[/compile_subst full_compiler s/].
Proof.
  intros.
  eapply full_compiler_semantic in H1.
  eapply H1 in H0; clear H1.
  eapply eq_term_trans; [ exact H0 |].
  clear H0.
  change  (CompilerTransitivity.compile_cmp
          (fix_cc ++ heap_cc ++ heap_id' ++ cc ++ prod_cc_compile ++ subst_cc ++ [])
          (fix_cps ++ cps ++ heap_ctx_cps ++ Ectx_cps ++ heap_cps ++ heap_id ++ cps_subst ++ []))
    with full_compiler.
  cbn [compile map].
  Ltac compute_match :=
    lazymatch goal with
    | |- context c [match ?e with _ => _ end] =>
        let e' := eval compute in e in
          change e with e'
    end.
  compute_match.
  cbn beta match.
  compute_match.
  cbn beta match.
                cbn -[compile compile_sort compile_ctx full_compiler tgt].
                TODO: what are the defaults? prob jmp .2 related
                cbn [combine_r_padded apply_subst term_substable substable_term term_subst syntax_model apply_subst0 substable0_is_substable term_substable premodel core_model].
                cbn.
                cbv [apply_subst0 term_substable  substable_term syntax_model].
                 unfold map.
      fold compile.
       {{e #"config" {H} {G} {A} (#"ret" {v})}})
  with 
  eapply eq_term_refl.
  unfold compile_fn.
  eapply eq_term_trans;
    [ eapply PartialEval.partial_eval_correct;
      eauto;
      try typeclasses eauto |].
  1:admit (*TODO*).
  admit (*TODO: generalize full_ *)
  eapply 
  cbn.
  [| assumption].
  2: basic
  all:eauto.


  Definition redex_step H e : option (term * term) :=
    match e with
    | {{e #"app" {G} {_} {_}
          (#"ret" {_} {_} (#"lambda" {_} {A} {B} {e}))
          (#"ret" {_} {_} {v}) }} =>
        {{e #"exp_subst" {G} (#"ext" {G} {A}) {B} (#"snoc" {G} {A} (#"id" {G}) {v}) {e} }}
    | {{e #"app" {G} {_} {_}
          (#"ret" {_} {_} (#"fix" {_} {A} {B} {e}))
          (#"ret" {_} {_} {v}) }} =>
        (*TODO: update this*)
        {{e #"exp_subst" {G} (#"ext" {G} {A}) {B} (#"snoc" {G} {A} (#"id" {G}) {v}) {e} }}
    end.
    
  
  Variant redex_step (G A : term) : term -> term -> term -> term -> Prop :=
    (* TODO: check elab *)
    (*Note: A and A1 should be equivalent, but we don't want to force syntactic equality*)
    | red_beta : redex_step H {{e #"app" {G} {A} {B}
                                  (#"ret" {G1} (#"->" {A1} {B1})
                                     (#"lambda" {G2} {A2} {e}))
                                  (#"ret" {v}) }}
                   {{e #"exp_subst" (#"snoc" #"id" {v}) {e} }}.

Inductive plug : term -> term -> term -> Prop :=.

Definition src_step t c c' : Prop :=
  match t, c, c' with
  | {{s #"configuration" {G} {A} }},
    {{e #"config" {H} {_} {_} {e} }},
    {{e #"config" {H'} {_} {_} {e'} }} =>
      exists E r r', redex_step G A H r H' r'
                     /\ plug E r e
                     /\ plug E r' e'
  | _, _, _ => False
  end.

Definition src_observable c : Prop :=
  match c with
  (*TODO: elaborate ret*)
  | {{e #"config" {H} {_} {_} (#"ret" {v}) }} => True
  | _ => False
  end.

Definition tgt_observable c : Prop :=
  match c with
  (*TODO: elaborate*)
  | {{e #"config" {H} {_} {_} (#"jmp" (#".2" #"hd") {v}) }} => True
  | _ => False
  end.

Definition value_relation a b : Prop :=
  (*TODO: add cases, elab*)
  match a, b with
  | con "true" _,  con "true" _ => True
  |  con "false" _, con "false" _ => True
  | {{e #"nv" {_} {n} }}, {{e #"nv" {_} {n'} }} => n = n'
  | _, _ => False
  end.

(*TODO: relate heaps too? *)
Definition cross_lang_relation a b : Prop :=
  (*TODO: elab*)
  match a, b with
  | {{e #"config" {H} {_} {_} (#"ret" {v}) }},
    {{e #"config" {H'} {_} {_} (#"jmp" (#".2" #"hd") {v'}) }} =>
      value_relation v v'
  | _, _ => False
  end.




operational_bridge
*)

