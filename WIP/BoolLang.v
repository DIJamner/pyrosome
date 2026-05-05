Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Lang.SimpleVSubst Lang.SimpleVCPS Lang.SimpleVSTLC Lang.NatHeap Tools.Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Local Notation compiler := (compiler string).


Definition bool_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| 
      -----------------------------------------------
      #"bool" : #"ty"
  ];
  [:| "G" : #"env"
       -----------------------------------------------
       #"true" : #"val" "G" #"bool"
  ];
  [:| "G" : #"env"
       -----------------------------------------------
       #"false" : #"val" "G" #"bool"
  ];
  [:| "G" : #"env",
       "c" : #"exp" "G" #"bool",
       "A" : #"ty",
       "e" : #"exp" "G" "A",
       "e'" : #"exp" "G" "A"
       -----------------------------------------------
       #"ite" "c" "e" "e'" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
       "A" : #"ty",
       "e" : #"exp" "G" "A",
       "e'" : #"exp" "G" "A"
      ----------------------------------------------- ("ite-true")
       #"ite" (#"ret" #"true") "e" "e'" = "e" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
       "A" : #"ty",
       "e" : #"exp" "G" "A",
       "e'" : #"exp" "G" "A"
      ----------------------------------------------- ("ite-false")
       #"ite" (#"ret" #"false") "e" "e'" = "e'" : #"exp" "G" "A"
  ]
  ]}.

Derive bool_lang
       SuchThat (elab_lang_ext (exp_subst++value_subst) bool_def bool_lang)
       As bool_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve bool_wf : elab_pfs.

Definition nat_cps_def : lang :=
  {[l/subst [block_subst++nat_exp++nat_lang ++value_subst]
  [:| "G" : #"env",
       "c" : #"val" "G" #"nat",
       "b" : #"blk" "G",
       "b'" : #"blk" "G"
       -----------------------------------------------
       #"if0" "c" "b" "b'" : #"blk" "G"
  ];
  [:= "G" : #"env",
       "b" : #"blk" "G",
       "b'" : #"blk" "G"
       ----------------------------------------------- ("if0-0")
       #"if0" (#"nv" #"0") "b" "b'" = "b" : #"blk" "G"
  ];
  [:= "n" : #"natural",
       "G" : #"env",
       "b" : #"blk" "G",
       "b'" : #"blk" "G"
       ----------------------------------------------- ("if0-1+")
       #"if0" (#"nv" (#"1+" "n")) "b" "b'" = "b'" : #"blk" "G"
  ]
  ]}.

Derive nat_cps_lang
  SuchThat (elab_lang_ext (block_subst++nat_exp++nat_lang ++value_subst)
              nat_cps_def nat_cps_lang)
       As nat_cps_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_cps_lang_wf : elab_pfs.

Definition bool_cps_def : compiler :=
  match # from (bool_lang) with
  | {{e #"bool"}} => {{e #"nat" }}
  | {{e #"false" "G"}} => {{e #"nv" #"0" }}
  | {{e #"true" "G"}} => {{e #"nv" (#"1+" #"0") }}
  | {{e #"ite" "G" "c" "A" "e" "e'"}} =>
    bind_k 1 (var "c") {{e #"nat"}}
    {{e #"if0" {ovar 0} (#"blk_subst" #"wkn" "e'") (#"blk_subst" #"wkn" "e") }}
  end.


Derive bool_cps
       SuchThat (elab_preserving_compiler cps_subst
                                          (cps_lang
                                             ++ nat_cps_lang
                                             ++ block_subst
                                             ++nat_exp
                                             ++nat_lang
                                             ++ value_subst)
                                          bool_cps_def
                                          bool_cps
                                          bool_lang)
       As bool_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve bool_cps_preserving : elab_pfs.

Require Pyrosome.Theory.WfCutElim Pyrosome.Theory.CutFreeInd.


Lemma val_rule_in_stlc_bool name c args G A
  : In (name, term_rule c args {{s #"val" {G} {A} }})
      (stlc ++ bool_lang ++ exp_subst ++ value_subst) ->
    In name ["lambda";"false"; "true";"hd"; "val_subst"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Ltac resolve_in H2 :=
  eapply Parameterizer.named_list_lookup_in with (a:=default) in H2;
  eauto; try typeclasses eauto;[| compute_all_fresh];
  vm_compute in H2;
  safe_invert H2.

Ltac cbn_substs :=
  cbn [apply_subst substable_sort substable_term sort_substable
         substable0_is_substable core_model
         premodel syntax_model with_names_from sort_subst map
         args_subst substable_args apply_subst0 term_subst term_subst_lookup
         term_var_map named_list_lookup eqb string_Eqb String.eqb Ascii.eqb Bool.eqb]   
    in *.

Lemma sort_eq_stlc_bool name c s1 s2
  : ~In (name, sort_eq_rule c s1 s2)
      (stlc ++ bool_lang ++ exp_subst ++ value_subst).
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
Qed.


Lemma ty_eq_rules name c' e1 e2
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    ~In (name, term_eq_rule c' e1 e2 {{s #"ty"}}) l.
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Lemma ty_rules name c' args
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    In (name, term_rule c' args {{s #"ty"}}) l ->
    In name ["->";"bool"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Lemma env_eq_rules name c' e1 e2
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    ~In (name, term_eq_rule c' e1 e2 {{s #"env"}}) l.
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Lemma env_rules name c' args
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    In (name, term_rule c' args {{s #"env"}}) l ->
    In name ["ext";"emp"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.



Lemma ty_sort_eq_trivial t1 t2
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    eq_sort l [] t1 t2 ->
    t2 = scon "ty" [] \/ t1 = scon "ty" [] ->
    t1 = t2.
Proof.
  intro l; subst l.
  induction 1; intros; subst; eauto.
  { eapply sort_eq_stlc_bool in H; tauto. }
  {
    intuition subst.
    {
      destruct t2'; cbn in H3; inversions.
      destruct l; cbn in H5; inversions; try tauto.
      intuition subst; auto.
    }
    {
      destruct t1'; cbn in H3; inversions.
      destruct l; cbn in H5; inversions; try tauto.
      intuition subst; auto.
    }
  }
  { intuition subst; try congruence; eauto. }
  { intuition subst; try congruence; eauto. }
Qed.

Lemma env_sort_eq_trivial t1 t2
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    eq_sort l [] t1 t2 ->
    t2 = scon "env" [] \/ t1 = scon "env" [] ->
    t1 = t2.
Proof.
  intro l; subst l.
  induction 1; intros; subst; eauto.
  { eapply sort_eq_stlc_bool in H; tauto. }
  {
    intuition subst.
    {
      destruct t2'; cbn in H3; inversions.
      destruct l; cbn in H5; inversions; try tauto.
      intuition subst; auto.
    }
    {
      destruct t1'; cbn in H3; inversions.
      destruct l; cbn in H5; inversions; try tauto.
      intuition subst; auto.
    }
  }
  { intuition subst; try congruence; eauto. }
  { intuition subst; try congruence; eauto. }
Qed.

Lemma ty_eq_trivial t e1 e2
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    eq_term l [] t e1 e2 ->
    t = scon "ty" [] ->
    e1 = e2.
Proof.
  intros l H.
  subst l.
  pattern e2; pattern e1; pattern t; revert t e1 e2 H.
  apply CutFreeInd.term_cut_ind; try typeclasses eauto; auto.
  1: prove_from_known_elabs.
  1: constructor.
  all: intros; subst; try now intuition congruence.
  {
    destruct t; cbn in H2; inversions.
    destruct l; cbn in H3; inversions; try tauto.
    pose proof H.
    eapply ty_eq_rules in H; cbn in H; intuition subst; resolve_in H2.
  }
  {
    destruct t; cbn in H2; inversions.
    destruct l; cbn in H3; inversions; try tauto.
    pose proof H.
    eapply ty_rules in H; cbn in H; intuition subst; resolve_in H2.
    all:repeat lazymatch goal with
           | H : eq_args _ _ _ _ |- _ => safe_invert H
           end; auto.
    cbn [CutFreeInd.P_args] in *.
    intuition subst; auto.
  }
  { apply ty_sort_eq_trivial in H; intuition auto. }
  Unshelve.
  all: constructor; eauto.
Qed.
  
Lemma env_eq_trivial t e1 e2
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    eq_term l [] t e1 e2 ->
    t = scon "env" [] ->
    e1 = e2.
Proof.
  intros l H.
  subst l.
  pattern e2; pattern e1; pattern t; revert t e1 e2 H.
  apply CutFreeInd.term_cut_ind; try typeclasses eauto; auto.
  1: prove_from_known_elabs.
  1: constructor.
  all: intros.
  {
    destruct t; cbn in H2; inversions.
    destruct l; cbn in H3; inversions; try tauto.
    pose proof H.
    eapply env_eq_rules in H; cbn in H; intuition subst; resolve_in H2.
  }
  {
    destruct t; cbn in H2; inversions.
    destruct l; cbn in H3; inversions; try tauto.
    pose proof H.
    eapply env_rules in H; cbn in H; intuition subst; resolve_in H2.
    all:repeat lazymatch goal with
           | H : eq_args _ _ _ _ |- _ => safe_invert H
           end; auto.
    cbn [CutFreeInd.P_args] in *; intuition subst.
    f_equal.
    eapply ty_eq_trivial; eauto.
  }
  { subst; intuition congruence. }
  { subst; intuition congruence. }
  {
    subst; intuition auto.
    apply env_sort_eq_trivial in H; subst; intuition eauto.
  }
  Unshelve.
  all: constructor; eauto.
Qed.

Lemma wf_sort_shape_stlc_bool c s
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    wf_sort l c s ->
    s = scon "env" []
    \/ s = scon "ty" []
    \/ (exists a b, s = scon "sub" [a;b])
    \/ (exists a b, s = scon "val" [a;b])
    \/ (exists a b, s = scon "exp" [a;b]).
Proof.
  induction 1; subst; eauto.  
  vm_compute in H; intuition auto.
  all: repeat match goal with
         | H : _ = _ |- _ => safe_invert H
         | H : wf_args _ _ _ |- _ => safe_invert H
         end.
  all: intuition eauto.
Qed.


Lemma eq_sort_shape_stlc_bool c s' s
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    eq_sort l c s' s ->
    s = scon "env" [] /\ s' = scon "env" []
    \/ s = scon "ty" [] /\ s' = scon "ty" []
    \/ (exists a b, s = scon "sub" [a;b]) /\ (exists a b, s' = scon "sub" [a;b])
    \/ (exists a b, s = scon "val" [a;b]) /\ (exists a b, s' = scon "val" [a;b])
    \/ (exists a b, s = scon "exp" [a;b]) /\ (exists a b, s' = scon "exp" [a;b]).
Proof.
  induction 1; subst; eauto.  
  { apply sort_eq_stlc_bool in H; tauto. }
  { intuition break; subst; cbn; intuition eauto. }
  { eapply wf_sort_shape_stlc_bool in H; intuition subst; eauto. }
  {
    intuition break; subst; cbn; intuition eauto.
    all: repeat match goal with
         | H : _ = _ |- _ => safe_invert H
         | H : wf_args _ _ _ |- _ => safe_invert H
           end.
  }
  {
    intuition break; subst; cbn; intuition eauto.
    all: repeat match goal with
         | H : _ = _ |- _ => safe_invert H
         | H : wf_args _ _ _ |- _ => safe_invert H
           end.
  }
Qed.


    
Lemma sort_rules name c' args
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    In (name, sort_rule c' args) l ->
    In name ["exp";"val"; "sub"; "env"; "ty"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Local Notation eq_subst l := (eq_subst (Model:= core_model l)).
Local Notation eq_args l := (eq_args (Model:= core_model l)).
Local Notation wf_args l := (wf_args (Model:= core_model l)).

Lemma eq_sort_trivial_cut_helper
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    (forall t t0, eq_sort l [] t t0 -> t = t0) /\
            (forall s t t0, eq_term l [] s t t0 -> True) /\
            (forall c0 s s0, eq_subst l [] c0 s s0 -> True) /\
      (forall c0 s s0, eq_args l [] c0 s s0 -> True).
Proof.
  apply CutFreeInd.cut_ind; try typeclasses eauto; eauto; intros.
  { prove_from_known_elabs. }
  { constructor. }
  { apply sort_eq_stlc_bool in H; tauto. }
  {
    pose proof H.
    eapply sort_rules in H; cbn in H.
    intuition subst;
      resolve_in H2.
    all:repeat lazymatch goal with
           | H : eq_args _ _ _ _ _ |- _ => safe_invert H
          end; auto; repeat f_equal.
    all: try now (eapply env_eq_trivial; eauto).
    all: try now (eapply ty_eq_trivial; eauto).
  }
  { congruence. }
  Unshelve.
  all:constructor; eauto.
Qed.    
    

Lemma eq_sort_trivial_stlc_bool s1 s2
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    eq_sort l [] s1 s2 -> s1 = s2.
Proof.
  intros; subst l; eapply eq_sort_trivial_cut_helper; eauto.
Qed.

Compute value_subst.
Inductive is_wkn : term -> Prop :=
| is_wkn_cmp s
  :is_wkn (con "wkn" s)
| is_wkn_wkn g f G3 G2 G1
  : is_wkn g ->
    is_wkn f ->
    is_wkn (con "cmp" [g;f;G3; G2; G1]).
Hint Constructors is_wkn : term.

Variant stlc_bool_nf : term -> Prop :=
| nf_hd s : stlc_bool_nf (con "hd" s)
| nf_var e3 e2 e1 e0 s'
  : is_wkn e1 ->
  stlc_bool_nf {{e #"val_subst" {e3} {e2} {e1} {e0} {(con "hd" s')} }}
| nf_lambda e B A G : stlc_bool_nf (con "lambda" [e;B;A;G])
| nf_true G : stlc_bool_nf (con "true" [G])
| nf_false G : stlc_bool_nf (con "false" [G]).
Hint Constructors stlc_bool_nf : term.
Compute value_subst.
Variant sub_nf : term -> Prop :=
| nf_wkn s : sub_nf (con "wkn" s)
| nf_forget s : sub_nf (con "forget" s)
| nf_snoc s : sub_nf (con "snoc" s)
| nf_id s : sub_nf (con "id" s).
Hint Constructors sub_nf : term.


Compute value_subst.
Lemma sub_rule_in_stlc_bool name c args G A
  : In (name, term_rule c args {{s #"sub" {G} {A} }})
      (stlc ++ bool_lang ++ exp_subst ++ value_subst) ->
    In name ["forget"; "snoc";"cmp"; "wkn"; "id"].
Proof.
  vm_compute; intuition auto.
  all: repeat match goal with H : _ = _ |- _ => safe_invert H end.
  all: intuition eauto.
Qed.

Lemma closed_sub_stlc_bool_nf e G G'
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    wf_term l [] e {{s #"sub" {G} {G'} }} ->
    exists e', eq_term l [] (scon "sub" [G';G]) e e' /\ sub_nf e'.
Proof.
  intro l; subst l.
  remember (scon "sub" [G';G]) as s.
  intro H.
  revert G G' Heqs.
  pattern s.
  pattern e.
  revert e s H.
  apply WfCutElim.wf_term_cut_ind;
    intros; subst.
  {
     destruct t as [sn l];
      destruct l; cbn in Heqs;
      inversions; try tauto.
    destruct l; cbn in H4;
      inversions; try tauto.
    destruct l; cbn in H3;
      inversions; try tauto.
    pose proof H;
      apply sub_rule_in_stlc_bool in H.
    cbn in H; intuition subst;
      resolve_in H2.
    1,2,4,5:eexists; split;
        [eapply eq_term_refl;
         eapply wf_term_by; eauto;
         apply named_list_lookup_err_in;
         reflexivity
        | eauto with term].
    repeat lazymatch goal with
           | H : wf_args _ _ _ _ |- _ => safe_invert H
          end; eauto with term.
    cbv [Model.wf_term core_model] in *.
    cbn [WfCutElim.P_args] in H1.
    cbn_substs.
    intuition.
    specialize (H0 _ _ eq_refl).
    specialize (H2 _ _ eq_refl).
    break.
    clear H9 H10 H H11.
    Compute value_subst.
    inversion H2; subst.
    all: eapply eq_term_wf_r in H1; eauto; try typeclasses eauto;
          [| prove_from_known_elabs | constructor].
    all: eapply WfCutElim.invert_wf_term_con in H1; break.
    all:repeat lazymatch goal with
           | H : wf_args _ _ _ _ |- _ => safe_invert H
          end; eauto with term.
    all: eexists.
    
    (*inversion H1; clear H1; subst.
      {
*)
Abort.

Lemma wf_implies_stlc_bool_nf e G t
  : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
    wf_term l [] e (scon "val" [t;G]) ->
    exists e', eq_term l [] (scon "val" [t;G]) e e' /\ stlc_bool_nf e'.
Proof.
  intro l; subst l.
  remember (scon "val" [t;G]) as s.
  intro H.
  revert G t Heqs.
  pattern s.
  pattern e.
  revert e s H.
  apply WfCutElim.wf_term_cut_ind;
    intros; subst.
  {
    destruct t as [sn l];
      destruct l; cbn in Heqs;
      inversions; try tauto.
    destruct l; cbn in H4;
      inversions; try tauto.
    destruct l; cbn in H3;
      inversions; try tauto.
    pose proof H;
      apply val_rule_in_stlc_bool in H.
    cbn in H; intuition subst;
      resolve_in H2.
    1-4:eexists; split;
        [eapply eq_term_refl;
         eapply wf_term_by; eauto;
         apply named_list_lookup_err_in;
         reflexivity
        | eauto with term].
    all:repeat lazymatch goal with
           | H : wf_args _ _ _ _ |- _ => safe_invert H
           end; eauto with term.
    cbv [Model.wf_term core_model] in *.
    cbn [WfCutElim.P_args] in H1.
    cbn_substs.
    intuition.
    specialize (H0 _ _ eq_refl).
    break.
    clear H2 H9 H10 H H11.
    inversion H1; clear H1; subst.
    {
      exists {{e #"val_subst" {e3} {e2} {e1} {e0} {(con "hd" s)} }}.
      split; eauto with term.
      {
        term_cong; try now (apply eq_term_refl; eauto).
        assumption.
      }
      {
        constructor.
        shelve.
      }
    }
    {
      assert (wf_term (stlc ++ bool_lang ++ exp_subst ++ value_subst) [] e5 {{s #"env" }}).
      {
        eapply eq_term_wf_r in H0; eauto; try typeclasses eauto;
          [| prove_from_known_elabs | constructor].
        eapply WfCutElim.invert_wf_term_con in H0; break.
        (*
        destruct H1 as [H1 | H1]; [ apply eq_sort_trivial_stlc_bool in H1|];
          destruct x1; cbn in H1; inversions; try tauto.
        all:destruct l; cbn in H2; inversions; try tauto.
        all: repeat lazymatch goal with
           | H : wf_args _ _ _ _ |- _ => safe_invert H
               end; 
          cbv [Model.wf_term core_model] in *.
        all:resolve_in H.
        all: cbn_substs; eauto.
      }
      
      assert (wf_term (stlc ++ bool_lang ++ exp_subst ++ value_subst) [] e6 {{s #"sub" {e4} {e5} }}).
      {
        eapply eq_term_wf_r in H0; eauto; try typeclasses eauto;
          [| prove_from_known_elabs | constructor].
        eapply invert_wf_term_con in H0; break.
        destruct H2 as [H2 | H2]; [ apply eq_sort_trivial_stlc_bool in H2|];
          destruct x1; cbn in H2; inversions; try tauto.
        all:destruct l; cbn in H3; inversions; try tauto.
        all: repeat lazymatch goal with
           | H : wf_args _ _ _ _ |- _ => safe_invert H
               end; 
          cbv [Model.wf_term core_model] in *.
        all:resolve_in H0.
        all: cbn_substs; eauto.
      }    
      exists {{e #"val_subst" {e3} {e5} (#"cmp" {e3} {e2} {e5} {e1} {e6}) {e0} {con "hd" s'} }}.
      split; eauto with term.
      pose proof H0.
      eapply eq_term_wf_r in H0; eauto; try typeclasses eauto;
        [| prove_from_known_elabs | constructor].
      eapply invert_wf_term_con in H0; break.
      destruct H10; subst.
      2:{
        resolve_in H0.
        cbn in H10.
        safe_invert H10.
        eapply eq_term_trans.
        {
          term_cong.
          6:exact H2.
          all:try now (apply eq_term_refl; eauto).
          right; reflexivity.
        }
        change {{e #"val_subst" {e3} {e2} {e1} {e0} (#"val_subst" {e2} {e5} {e6} {e0} {con "hd" s'})}}
        with {{e #"val_subst" "G1" "G2" "f" "A" (#"val_subst" "G2" "G3" "g" "A" "v") }}
             [/[("v", con "hd" s');("A", e0);
                ("g", e6);("f", e1);
                ("G3", e5);("G2", e2);("G1", e3)]/].
        change {{e #"val_subst" {e3} {e5} (#"cmp" {e3} {e2} {e5} {e1} {e6}) {e0} {con "hd" s'} }}
          with {{e #"val_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "A" "v" }}
               [/[("v", con "hd" s');("A", e0);
                ("g", e6);("f", e1);
                  ("G3", e5);("G2", e2);("G1", e3)]/].
        change {{s #"val" {e3} {e0} }} with
          {{s  #"val" "G1" "A" }}  [/[("v", con "hd" s');("A", e0);
                ("g", e6);("f", e1);
                  ("G3", e5);("G2", e2);("G1", e3)]/].
        eapply eq_term_by_with_subst with (name:= "val_subst_cmp").
        { prove_from_known_elabs. }
        { solve_in. }
        unshelve (repeat t'); eauto with lang_core.
        safe_invert H9.
        exact H12.
      }
      {
        eapply eq_sort_trivial_stlc_bool in H10; subst.
        
        resolve_in H0.
        cbn in H10.
        safe_invert H10.
        eapply eq_term_trans.
        {
          term_cong.
          6:exact H2.
          all:try now (apply eq_term_refl; eauto).
          right; reflexivity.
        }
        change {{e #"val_subst" {e3} {e2} {e1} {e0} (#"val_subst" {e2} {e5} {e6} {e0} {con "hd" s'})}}
        with {{e #"val_subst" "G1" "G2" "f" "A" (#"val_subst" "G2" "G3" "g" "A" "v") }}
             [/[("v", con "hd" s');("A", e0);
                ("g", e6);("f", e1);
                ("G3", e5);("G2", e2);("G1", e3)]/].
        change {{e #"val_subst" {e3} {e5} (#"cmp" {e3} {e2} {e5} {e1} {e6}) {e0} {con "hd" s'} }}
          with {{e #"val_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "A" "v" }}
               [/[("v", con "hd" s');("A", e0);
                ("g", e6);("f", e1);
                  ("G3", e5);("G2", e2);("G1", e3)]/].
        change {{s #"val" {e3} {e0} }} with
          {{s  #"val" "G1" "A" }}  [/[("v", con "hd" s');("A", e0);
                ("g", e6);("f", e1);
                  ("G3", e5);("G2", e2);("G1", e3)]/].
        eapply eq_term_by_with_subst with (name:= "val_subst_cmp").
        { prove_from_known_elabs. }
        { solve_in. }
        unshelve (repeat t'); eauto with lang_core.
        safe_invert H9.
        exact H12.
      }
    }
    2:{
      exists {{e #"true" {e3} }}.
      split; eauto with term.
      pose proof H0.
      eapply eq_term_wf_r in H0; eauto; try typeclasses eauto;
        [| prove_from_known_elabs | constructor].
      assert ({{s #"val" "G" #"bool"}} [/with_names_from [("G", {{s #"env"}})] [G] /]
              = {{s #"val" {e2} {e0} }}).
      {
        eapply invert_wf_term_con in H0; break.
        resolve_in H0.
        intuition auto.
        apply eq_sort_trivial_stlc_bool in H0; eauto.
      }
      cbn in H1.
      safe_invert H1.
      eapply eq_term_trans.
      {
        term_cong.
        6:exact H.
        all:try now (apply eq_term_refl; eauto).
        right; reflexivity.
      }
      change {{e #"val_subst" {e3} {e2} {e1} #"bool" (#"true" {e2})}}
        with {{e #"val_subst" "G'" "G" "g" #"bool" (#"true" "G")}}
             [/[("g",e1);("G'",e3);("G",e2)]/].
      change {{e #"true" {e3} }}
        with {{e #"true" "G'" }}
             [/[("g",e1);("G'",e3);("G",e2)]/].
      change {{s #"val" {e3} #"bool"}}
        with {{s  #"val" "G'" #"bool" }}
             [/[("g",e1);("G'",e3);("G",e2)]/].
      eapply eq_term_by_with_subst with (name:= "val_subst true").
      { prove_from_known_elabs. }
      { solve_in. }
      unshelve (repeat t'); eauto with lang_core.
    }
    2:{
      exists {{e #"false" {e3} }}.
      split; eauto with term.
      pose proof H0.
      eapply eq_term_wf_r in H0; eauto; try typeclasses eauto;
        [| prove_from_known_elabs | constructor].
      assert ({{s #"val" "G" #"bool"}} [/with_names_from [("G", {{s #"env"}})] [G] /]
              = {{s #"val" {e2} {e0} }}).
      {
        eapply invert_wf_term_con in H0; break.
        resolve_in H0.
        intuition auto.
        apply eq_sort_trivial_stlc_bool in H0; eauto.
      }
      cbn in H1.
      safe_invert H1.
      eapply eq_term_trans.
      {
        term_cong.
        6:exact H.
        all:try now (apply eq_term_refl; eauto).
        right; reflexivity.
      }
      change {{e #"val_subst" {e3} {e2} {e1} #"bool" (#"false" {e2})}}
        with {{e #"val_subst" "G'" "G" "g" #"bool" (#"false" "G")}}
             [/[("g",e1);("G'",e3);("G",e2)]/].
      change {{e #"false" {e3} }}
        with {{e #"false" "G'" }}
             [/[("g",e1);("G'",e3);("G",e2)]/].
      change {{s #"val" {e3} #"bool"}}
        with {{s  #"val" "G'" #"bool" }}
             [/[("g",e1);("G'",e3);("G",e2)]/].
      eapply eq_term_by_with_subst with (name:= "val_subst false").
      { prove_from_known_elabs. }
      { solve_in. }
      unshelve (repeat t'); eauto with lang_core.
    }
    {
      pose proof H0.
      eapply eq_term_wf_r in H0; eauto; try typeclasses eauto;
        [| prove_from_known_elabs | constructor].
      assert ({{s #"val" {G} (#"->" {A} {B})}} = {{s #"val" {e2} {e0} }}).
      {
        eapply invert_wf_term_con in H0; break.
        resolve_in H0.
        intuition auto.
        1:apply eq_sort_trivial_stlc_bool in H0; eauto.
        all: cbv in H0; inversions.
        all: eauto.
      }
      break.
      inversions.
      let x1 := open_constr:(_) in
      let x2 := open_constr:(_) in
      let x3 := open_constr:(_) in
      let x4 := open_constr:(_) in
      let x5 := open_constr:(_) in
      exists {{e #"lambda" {e3} {A} {B} (#"exp_subst" {x1} {x2} {x3} {x4} {x5})}}.
      split; eauto with term.
      eapply eq_term_trans.
      {
        term_cong.
        6:exact H.
        all:try now (apply eq_term_refl; eauto).
        right; reflexivity.
      }
      change {{e #"val_subst" {e3} {e2} {e1} (#"->" {A} {B}) (#"lambda" {e2} {A} {B} {e4})}}
        with {{e #"val_subst" "G'" "G" "g" (#"->" "A" "B") (#"lambda" "G" "A" "B" "e") }}
             [/[("g",e1);("G'",e3);("e",e4);("B",B);("A",A);("G",e2)]/].
      lazymatch goal with
      |- eq_term _ _ _ _ ?e =>
      replace e
        with {{e #"lambda" "G'" "A" "B" (#"exp_subst" (#"ext" "G'" "A") (#"ext" "G" "A") (
                                                    #"snoc" (#"ext" "G'" "A") "G" (
                                                            #"cmp" (#"ext" "G'" "A") "G'" "G" (
                                                                   #"wkn" 
                                                                   "G'" "A") "g") "A" (
                                                        #"hd" "G'" "A")) "B" "e") }}
             [/[("g",e1);("G'",e3);("e",e4);("B",B);("A",A);("G",e2)]/]
             by reflexivity
      end.
      change {{s #"val" {e3} (#"->" {A} {B})}}
        with {{s #"val" "G'" (#"->" "A" "B") }}
             [/[("g",e1);("G'",e3);("e",e4);("B",B);("A",A);("G",e2)]/].
      eapply eq_term_by_with_subst with (name:= "val_subst lambda").
      { prove_from_known_elabs. }
      { solve_in. }
      
        eapply invert_wf_term_con in H0; break.
        resolve_in H0.
        intuition auto.
        all:repeat lazymatch goal with
              | H : wf_args _ _ _ _ |- _ => safe_invert H
              end; eauto with term.
        all: unshelve (repeat t'); eauto with lang_core.
    }
  }
  { cbn in H; intuition. }
  {
    apply eq_sort_trivial_stlc_bool in H1; subst; eauto.
  }
  Unshelve.
  all: repeat constructor; eauto.
Qed.  
            
Lemma bool_inversion b
    : let l := (stlc ++ bool_lang ++ exp_subst++value_subst) in
      wf_term l [] b {{s #"val" #"emp" #"bool"}} ->
      eq_term l [] {{s #"val" #"emp" #"bool"}} b {{e #"true" #"emp" }} 
      \/ eq_term l [] {{s #"val" #"emp" #"bool"}} b {{e #"false" #"emp" }}.
Proof.
  intros; subst l.
  pose proof H; apply wf_implies_stlc_bool_nf in H.
  break.
  inversion H1; subst; intuition eauto.
  {
    pose proof H.
    eapply eq_term_wf_r in H; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    eapply invert_wf_term_con in H; break.
    intuition.
    all:eapply eq_term_wf_r in H2; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    all:eapply invert_wf_term_con in H2; break.
    all:resolve_in H2.
    all:resolve_in H.
    all: intuition try congruence.
    all:try apply eq_sort_trivial_stlc_bool in H5;
      try apply eq_sort_trivial_stlc_bool in H;
      subst; eauto; cbn in H5; congruence.
  }
  2:{
    pose proof H.
    eapply eq_term_wf_r in H; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    eapply invert_wf_term_con in H; break.
    intuition.
    all:eapply eq_term_wf_r in H2; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    all:eapply invert_wf_term_con in H2; break.
    all:resolve_in H2.
    all:resolve_in H.
    all: intuition try congruence.
    all:try apply eq_sort_trivial_stlc_bool in H5;
      try apply eq_sort_trivial_stlc_bool in H;
      subst; eauto; cbn in H5; congruence.
  }
  2:{
    pose proof H.
    eapply eq_term_wf_r in H; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    eapply invert_wf_term_con in H; break.
    intuition.
    1:try apply eq_sort_trivial_stlc_bool in H5.
    all: 
    destruct x1 as [sn l];
      destruct l; cbn in H5;
      inversions; try tauto.
    all:destruct l; cbn in H6;
      inversions; try tauto.
    all:destruct l; cbn in H6;
      inversions; try tauto.
    all: resolve_in H.
    all:cbn in H4; subst; intuition.
  }
  2:{
    pose proof H.
    eapply eq_term_wf_r in H; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    eapply invert_wf_term_con in H; break.
    intuition.
    1:try apply eq_sort_trivial_stlc_bool in H5.
    all: 
    destruct x1 as [sn l];
      destruct l; cbn in H5;
      inversions; try tauto.
    all:destruct l; cbn in H6;
      inversions; try tauto.
    all:destruct l; cbn in H6;
      inversions; try tauto.
    all: resolve_in H.
    all:cbn in H4; subst; intuition.
  }
  {
    exfalso.


    
    2:{
    all:eapply eq_term_wf_r in H2; eauto; try typeclasses eauto;
      [| prove_from_known_elabs | constructor].
    all:eapply invert_wf_term_con in H2; break.
    all:resolve_in H2.
    all:resolve_in H.
    all: intuition try congruence.
    all:try apply eq_sort_trivial_stlc_bool in H5;
      try apply eq_sort_trivial_stlc_bool in H;
      subst; eauto; cbn in H5; congruence.
  }
    { apply eq_sort_trivial_stlc_bool in H5; subst; eauto; cbn in H5; congruence. }
    { apply eq_sort_trivial_stlc_bool in H5; subst; eauto; cbn in H5; congruence. }
    { subst; eauto; cbn in H5; congruence. }
    { apply eq_sort_trivial_stlc_bool in H5; subst; eauto; cbn in H5; congruence. }
    { apply eq_sort_trivial_stlc_bool in H5; subst; eauto; cbn in H5; congruence. }
    { apply eq_sort_trivial_stlc_bool in H5; subst; eauto; cbn in H5; congruence. }
    { apply eq_sort_trivial_stlc_bool in H5; subst; eauto; cbn in H5; congruence. }
    all: 
    destruct x1 as [sn l];
      destruct l; cbn in H4;
      inversions; try tauto.
    all:destruct l; cbn in H5;
      inversions; try tauto.
    all:destruct l; cbn in H5;
      inversions; try tauto.
    {
      assert (wf_lang (stlc ++ bool_lang ++ exp_subst ++ value_subst))
        by prove_from_known_elabs.
      pose proof H.
      resolve_in H.
      use_rule_in_wf.
      clear H7.
      autorewrite with utils lang_core in *; break.
      
      
    all:destruct t0 as [sn l];
      destruct l; cbn in H4;
      inversions; try tauto.
    2:{
    all:inversions.
    resolve_in H0.





Qed.
         *)
Abort.

Fixpoint env_nth G n :=
  match G, n with
  | {{e #"ext" {G'} {A} }}, 0 => Some A
  | {{e #"ext" {G'} {A} }}, S n' => env_nth G' n'
  | _, _ => None
  end.

Fixpoint env_skipn G n {struct n} :=
  match n, G with
  | 0, _ => Some G
  | S n', {{e #"ext" {G'} {A} }} => env_skipn G' n'
  | _, _ => None
  end.
Import Monad.
Fixpoint var_n G n : option _ :=
  match G, n with
  | {{e #"ext" {G'} {A} }}, 0 => Some ({{e #"hd" {G'} {A} }}, A)
  | {{e #"ext" {G'} {A} }}, S n' =>
      @!let (v,An) <- var_n G' n' in
        ret ({{e #"val_subst" {G} {G'} (#"wkn" {G'} {A}) {An} {v} }}, An)
  | _, _ => None
  end.

Variant base_val_rel G : term -> term -> Prop :=
| rel_true : base_val_rel G {{e #"bool" }} {{e #"true" {G} }}
| rel_false : base_val_rel G {{e #"bool" }} {{e #"false" {G} }}
| rel_lam A B e
  : (*TODO: do I need the wfness?*)
   (* let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e {{s #"val" (#"ext" {G} {A}) {B} }} ->*)
    base_val_rel G {{e #"->" {A} {B} }}
      {{e #"lambda" {G} {A} {B} {e} }}
| rel_var A n v
  : var_n G n = Some (v,A) ->
    base_val_rel G A v.

Variant LR_val : term -> term -> term -> Prop :=
| LR_v G A v v'
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    eq_term l [] {{s #"val" {G} {A} }} v v' ->
    base_val_rel G A v' ->
    LR_val G A v.


Inductive base_subst_rel G : term -> term -> Prop :=
  | rel_emp : base_subst_rel G {{e#"emp"}} {{e #"forget" {G} }}
  | rel_snoc' G' g A v g'
    : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
      eq_term l [] {{s #"sub" {G} {G'} }} g g' ->
      base_subst_rel G G' g' ->
      LR_val G A v ->
      base_subst_rel G {{e #"ext" {G'} {A} }}
        {{e #"snoc" {G} {G'} {g} {A} {v} }}.

Variant LR_sub : term -> term -> term -> Prop :=
| LR_s G G' s s'
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    eq_term l [] {{s #"sub" {G} {G'} }} s s' ->
    base_subst_rel G G' s' ->
    LR_sub G G' s.

Lemma rel_snoc G G' g A v
  : LR_sub G G' g ->
    LR_val G A v ->
    base_subst_rel G {{e #"ext" {G'} {A} }}
      {{e #"snoc" {G} {G'} {g} {A} {v} }}.
Proof.
  intros H ?; destruct H;
  econstructor; eauto.
Qed.  

Lemma LR_val_eq G A v1 v2
  : let l := stlc ++ bool_lang ++ exp_subst ++ value_subst in
    eq_term l [] {{s #"val" {G} {A} }} v1 v2 ->
    LR_val G A v1 -> LR_val G A v2.
Proof.
  destruct 2; econstructor; eauto.
  eapply eq_term_trans; eauto.
  eapply eq_term_sym; eauto.
Qed.


Lemma sb_invert_closed e t
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l {{c }} e t ->
    exists c' args t' n s,
      e = con n s /\
        In (n, term_rule c' args t') l /\
        wf_args l [] s c' /\
        (t' [/with_names_from c' s /] = t).
Proof.
    intros l H.
    pattern t.
    pattern e.
    revert e t H.
    apply WfCutElim.wf_term_cut_ind;
      intros; subst; inversions; try tauto.
    {
      repeat eexists; intuition eauto.
    }
    { basic_goal_prep; intuition auto. }
    {
      repeat eexists; intuition eauto.
      eauto using eq_sort_trivial_stlc_bool.
    }
  Qed.


Ltac env_cases' H :=
  let H' := fresh in
  pose proof H as H';
  apply env_rules in H';
  cbv in H';
  intuition subst;
  resolve_in H;
  repeat lazymatch goal with
    | H : wf_args _ _ _ (_::_) |- _ =>
        safe_invert H
    | H : wf_args _ _ _ [] |- _ =>
        safe_invert H
    end;      
  cbn [WfCutElim.P_args] in *;
  cbn_substs.

Ltac env_cases :=
  lazymatch goal with
  | H : In (_, term_rule _ _ {{s #"env"}}) _ |- _ =>
      env_cases' H
  end.

Ltac step l r :=
  eredex_steps_with l r;  eauto with lang_core;
  [repeat (eapply wf_subst_cons; cbn_substs; eauto with lang_core)
  | assert (wf_lang (stlc ++ bool_lang ++ exp_subst ++ value_subst))
    by prove_from_known_elabs; ComputeWf.solve_wf_ctx].

Ltac term_cong' :=
  term_cong; cbn_substs; eauto;
  try eapply eq_term_refl.

Lemma LR_subst_n G G1 g A n v
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    var_n G n = Some (v,A) ->
    LR_sub G1 G g ->
    LR_val G1 A {{e #"val_subst" {G1} {G} {g} {A} {v} }}.
Proof.
  intros.
  safe_invert H0.
  eapply LR_val_eq.
  {
    eapply eq_term_sym.
    term_cong; cbn_substs.
    1: right; reflexivity.
    3: eassumption.
    all: eapply eq_term_refl.
    all: cbn_substs; try eassumption.
    all:admit (*TODO: var_n wf *).
  }

  clear g l H1.
  generalize dependent G.
  revert v s'.
  induction n;
    intros.
  all: assert (wf_term l0 [] G {{s #"env"}}) as Hwf by admit.
  all: eapply sb_invert_closed in Hwf; break; subst.
  all: destruct x1; cbn in H4; inversions.
  all: destruct l; cbn in H4; inversions; try tauto.
  {
    env_cases; cbn in H; inversions; try tauto.
    safe_invert H2.
    eapply LR_val_eq; eauto.
    cbn_substs.
    eapply eq_term_sym.
    step value_subst "snoc_hd"; admit.
  }
  {
    env_cases; cbn in H; inversions; try tauto.
    case_match; try congruence.
    break.
    inversions.
    safe_invert H2.
    eapply IHn in H3; eauto.
    eapply LR_val_eq; eauto.
    eapply eq_term_sym.
    eapply eq_term_trans; [step value_subst "val_subst_cmp"; admit|].
    cbn_substs.
    term_cong'.
    1,2,4,5: admit.
    eapply eq_term_trans; [step value_subst "wkn_snoc"; admit|].
    cbn_substs.
    eauto.
  }
  Unshelve.
  all:constructor; eauto.
Admitted.

Lemma LR_val_judgment G A v
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    LR_val G A v -> wf_term l [] v {{s #"val" {G} {A} }}.
Proof.
  destruct 1.
  eapply eq_term_wf_l; eauto with lang_core;
    try typeclasses eauto.
  subst l; prove_from_known_elabs.
Qed.

Lemma LR_sub_judgment G G' g
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    LR_sub G G' g -> wf_term l [] g {{s #"sub" {G} {G'} }}.
Proof.
  destruct 1.
  eapply eq_term_wf_l; eauto with lang_core;
    try typeclasses eauto.
  subst l; prove_from_known_elabs.
Qed.



Lemma LR_cong_val_subst G1 G2 g A v
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    LR_val G2 A v ->
    LR_sub G1 G2 g ->
    LR_val G1 A {{e #"val_subst" {G1} {G2} {g} {A} {v} }}.
Proof.
  destruct 2 as [? ? ? ? ? ? Hv ].
  inversion Hv; subst; clear Hv.
  {
    intros; econstructor.
    2:eapply rel_true.
    eapply eq_term_trans.
    2: step bool_lang "val_subst true".
    1:cbn_substs.
    1:term_cong'.
    all: admit.
  }
  {
    intros; econstructor.
    2:eapply rel_false.
    eapply eq_term_trans.
    2: step bool_lang "val_subst false".
    1:cbn_substs.
    1:term_cong'.
    all: admit.
  }
  {
    intros; econstructor.
    2:eapply rel_lam.
    eapply eq_term_trans.
    {
      term_cong.
      { right; reflexivity. }
      5:{ cbn_substs. eassumption. }
      all: apply eq_term_refl.
      all: cbn_substs; try eassumption.
      all: admit.
    }
    step stlc "val_subst lambda".
    all: admit.
  }
  {
    intros.
    eapply LR_val_eq.
    {
      eapply eq_term_sym.
      term_cong; unfold Model.eq_term; cbn_substs.
      1: right; reflexivity.
      5: eassumption.
      all: apply eq_term_refl; cbn_substs; try eassumption.
      all: admit.
    }
    eapply LR_subst_n; eauto.
  }    
  Unshelve.
  all: constructor; eauto.
Admitted.



Lemma LR_sub_eq G A v1 v2
  : let l := stlc ++ bool_lang ++ exp_subst ++ value_subst in
    eq_term l [] {{s #"sub" {G} {A} }} v1 v2 ->
    LR_sub G A v1 -> LR_sub G A v2.
Proof.
  destruct 2; econstructor; eauto.
  eapply eq_term_trans; eauto.
  eapply eq_term_sym; eauto.
Qed.

Lemma LR_sub_forget e
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e {{s #"env"}} ->
    LR_sub e {{e #"emp"}} {{e #"forget" {e} }}.
Proof.
  econstructor.
  2:econstructor.
  eapply eq_term_refl.
  eapply wf_term_by'; [ solve_in | | left; reflexivity].
  repeat (constructor; try eassumption).
Qed.


Lemma LR_sub_snoc e e0 e1 e2 e3
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    LR_val e3 e0 e ->
    LR_sub e3 e2 e1 ->
    LR_sub e3 {{e #"ext" {e2} {e0} }} {{e #"snoc" {e3} {e2} {e1} {e0} {e} }}.
Proof.
  intros.
  safe_invert H0.
  econstructor.
  2:econstructor; eauto.
  eapply eq_term_refl.
Admitted.

Lemma LR_sub_cmp_cong e3 e2 e1 e0 e
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    LR_sub e2 e1 e ->
    LR_sub e3 e2 e0 ->
    LR_sub e3 e1 {{e #"cmp" {e3} {e2} {e1} {e0} {e} }}.
Proof.
  intros.
  destruct H.
  eapply LR_sub_eq.
  {
    eapply eq_term_sym.
    term_cong.
    1:right; reflexivity.
    all:cbn_substs.
    all: try eassumption.
    all: eapply eq_term_refl; admit.
  }
  clear s H l0.
  revert e3 e0 H0.
  induction H1; intros.
  {
    econstructor.
    2: constructor.
    step value_subst "cmp_forget".
    all: admit.
  }
  {
    econstructor.
    {
      step value_subst "cmp_snoc".
      all: admit.
    }
    cbn_substs.
    eapply rel_snoc.
    {
      eapply LR_sub_eq; eauto.
      eapply eq_term_sym.
      term_cong'.
      all:admit.
    }
    eapply LR_cong_val_subst; eauto.
  }
Admitted.

Lemma LR_val_cong_hd e e0
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e0 {{s #"env"}} ->
    wf_term l [] e {{s #"ty"}} ->
    LR_val {{e #"ext" {e0} {e} }} e {{e #"hd" {e0} {e} }}.
Proof.
  econstructor.
  2: eapply rel_var with (n:=0); reflexivity.
  cbn [wkn_n].
  eapply eq_term_refl.
  eapply wf_term_by'.
  1:solve_in.
  1: eauto with lang_core.
  left; reflexivity.
Qed.

Lemma eq_term_by_with_subst' [V : Type] {V_Eqb : Eqb V} (name : V)
  [l : Rule.lang V] [c c' : Term.ctx V]
  (e1 e2 : Term.term V) (t : Term.sort V) [s : Term.subst V]
  : wf_lang l ->
    In (name, term_eq_rule c' e1 e2 t) l ->
    forall e1' e2' t',
    e1' = e1 [/s /] ->
    e2' = e2 [/s /] ->
    t' = t [/s /] ->
    wf_subst (Model:=core_model l) c s c' -> eq_term l c t' e1' e2'.
Proof.
  intros; subst; eapply eq_term_by_with_subst; eauto.
Qed.

Fixpoint wkn_n n G : option _ :=
  match n, G with
  | 0, _ => Some ({{e #"id" {G} }}, G)
  | S n', {{e #"ext" {G'} {A} }} =>
      @! let (g,G_out) <- wkn_n n' G' in
        ret ({{e #"cmp" {G} {G'} {G_out} (#"wkn" {G'} {A}) {g} }}, G_out)
  | _, _ => None
  end.


Lemma emp_sub_unique g G
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] g {{s #"sub" {G} #"emp"}} ->
    eq_term l [] {{s #"sub" {G} #"emp"}} g {{e #"forget" {G} }}.
Proof.
  intros.
  eapply eq_term_trans.
  1: eapply eq_term_sym;step value_subst "id_right"; admit.
  cbn_substs.
  eapply eq_term_trans.
  {
    subst l.
    term_cong.
    1: right; reflexivity.
    all:cbn_substs.
    1-4: eapply eq_term_refl; admit.
    unfold Model.eq_term.
    eredex_steps_with value_subst "id_emp_forget"; constructor.
  }
  cbn_substs.
  step value_subst "cmp_forget".
Admitted.

Ltac sub_cong :=
  repeat lazymatch goal with
         | H : ?t [/_/] = scon _ _ |- _=> destruct t; cbn in H; inversions
         | H : ?t [/_/] = [] |- _=> destruct t; cbn in H; inversions
         | H : ?t [/_/] = _::_ |- _=> destruct t; cbn in H; inversions
    end; try tauto.


Fixpoint env_depth G := 
  match G with
  | {{e #"ext" {G'} {A} }} => S (env_depth G')
  | _ => 0
  end.

Ltac measure' exp f :=  
  let P := lazymatch goal with |- ?g => g end in
  let m := fresh "m" in
  let H := fresh in
  enough (forall m, f m > exp -> P) as H
      by (apply H with (m:=f exp + 1); Lia.lia);
  intro m.

Ltac measure exp := measure' exp (fun x:nat => x).

TODO: am I composing in the wrong order ?
Lemma wkn_n_ext n G g G' A
  : wkn_n n G = Some (g, {{e #"ext" {G'} {A} }}) ->
    exists G1 A1,
      G = {{e #"ext" {G1} {A1} }}
      /\ wkn_n (S n) G = Some ({{e #"cmp" {G} {G1} {G'} (#"wkn" {G1} {A1}) {g} }}, G').
Proof.
  intros.  
  apply sb_invert_closed in H0; break; sub_cong.
  env_cases.
  2:{ destruct n; cbn in H; inversions; tauto. }
  destruct n; cbn in H; inversions; try tauto.

  
Lemma wkn_n_snoc n G g G' A
  : wkn_n n G = Some (g, {{e #"ext" {G'} {A} }}) ->
    let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] G {{s #"env" }} ->
    exists g' x, wkn_n (S n) G = Some (g', G')
               /\ var_n G n = Some (x, A)
               /\ eq_term l [] {{s #"sub" {G} (#"ext" {G'} {A}) }}
                    g {{e #"snoc" {G} {G'} {g'} {A} {x} }}.
Proof.
  intros.  
  apply sb_invert_closed in H0; break; sub_cong.
  env_cases.
  2:{ destruct n; cbn in H; inversions; tauto. }
  destruct n; cbn in H; inversions; try tauto.

  TODO: a way w/out induction
  2:{



  
  measure (env_depth G').
  revert n G g G' A.
  induction m; intros; try Lia.lia.
  apply sb_invert_closed in H1; break; sub_cong.
  env_cases.
  2:{ destruct n; cbn in H0; inversions; tauto. }
  TODO: depth seems 1 too small
  TODO: eq_term an unneeded complication here?
  destruct n; cbn in H0; inversions; try tauto.
  {
    cbn in H.
    cbn -[l].
    eexists; eexists; intuition auto.
    eapply eq_term_trans.
    2:{
      subst l; term_cong; cbn_substs.
      3: eapply eq_term_sym; unfold Model.eq_term; step value_subst "id_right".
      all: try apply eq_term_refl.
      all: admit.
    }
    eapply eq_term_sym.
    cbn_substs.
    eredex_steps_with value_subst "snoc_wkn_hd".
    all: admit.
  }
  {
    case_match; try congruence.
    break; inversions.
    cbn in H.
    eapply IHm in case_match_eqn; eauto.
    2:{
      TOD: why hasn't it changed?
      Lia.lia.
      TODO: not actually smaller???
      Lia.lia.
  
  TODO: don't want induction on G, want induction on base of G

Lemma LR_sub_wkn_n_cong n G g G'
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] G {{s #"env" }} ->
    wkn_n n G = Some (g,G') ->
    LR_sub G G' g.
Proof.
  intros l H.
  (*
  measure ((Nat.max 1 n) + 2 * env_depth G).
  revert n G g G' H.
  induction m; try Lia.lia.
  intros.
  apply sb_invert_closed in H; break; sub_cong.
  env_cases.
  2:{
    destruct n; cbn in H1; inversions; try tauto.
    econstructor;[|constructor].
    eredex_steps_with value_subst "id_emp_forget"; constructor.
  }      
  destruct n; cbn in H1; inversions; try tauto.
  {
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "snoc_wkn_hd".
      all: admit.
    }
    cbn_substs.
    econstructor.
    1: eapply eq_term_refl; admit.
    eapply rel_snoc.
    2: eapply LR_val_cong_hd; eauto.
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "id_right".
      all: admit.
    }
    cbn_substs.
    eapply IHm with (n:=1); eauto.
    1:admit.
    cbn;cbn in H0.
    Lia.lia.
  }
  {
    case_match; break; inversions; try tauto.
    eapply LR_sub_cmp_cong.
    {
      TODO: why is depth in terms of G'?
      eapply IHm; eauto.
      pose proof (PeanoNat.Nat.max_spec 1 (S n)).
      pose proof (PeanoNat.Nat.max_spec 1 n).
      change PeanoNat.Nat.max with Nat.max in *.
      intuition try Lia.lia.
      replace n with 0 in * by Lia.lia.
      TODO: doesn't work when n = 0
      (*TODO: missing finite cases: n in (0,1)*)
      shelve.
    }
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "id_right".
      all: admit.
    }
    cbn_substs.
    eapply IHm with (n:=1); eauto.
    1:admit.
   1:admit (* Lia.lia.*).
    eapply LR_sub_cmp_cong.
    {
      eapply IHm with (n:=0); eauto.
      TODO: not decreasing. Lia.lia.
    }
    eapply IHm with (n:=1); eauto.
    1:Lia.lia.
    }
    *)
  assert (wf_term l {{c }} G' {{s #"env"}}) by admit.
  revert n g G H.
  remember {{s #"env" }} as t in H0.
  revert Heqt.
  pattern t; pattern G'; revert G' t H0.
  apply WfCutElim.wf_term_cut_ind.
  2: basic_goal_prep; subst; tauto.
  2:{
    intros.
    apply eq_sort_trivial_stlc_bool in H1; subst; eauto.
  }
  intros; sub_cong.
  env_cases.
  2:{
    econstructor.
    1: eapply emp_sub_unique; admit.
    constructor.
  }
  intuition.
  clear H0 H1.

      
  
  destruct n; cbn in H3; inversions.
  {
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "snoc_wkn_hd".
      all: admit.
    }
    cbn_substs.
    econstructor.
    1: eapply eq_term_refl; admit.
    eapply rel_snoc.
    2: eapply LR_val_cong_hd; eauto.
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "id_right".
      all: admit.
    }
    cbn_substs.
    eapply H with (n:=1); eauto.
  }
  eapply sb_invert_closed in H2; break; sub_cong.
  env_cases; try congruence.
  case_match; break; inversions; try tauto.
  eapply LR_sub_cmp_cong.
  {
    
    
    TODO: can't apply H. Should this be induction on n?.
    What I want: IH for n'<n or e < G'.
    measure: n + |G'| + 2
    eapply H2; eauto.
    cbn in H3.
  destruct n; cbn in H3; inversions.
  {
    clear H2; intuition.
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "snoc_wkn_hd".
      all: admit.
    }
    cbn_substs.
    econstructor.
    1: eapply eq_term_refl; admit.
    eapply rel_snoc.
    2: eapply LR_val_cong_hd; eauto.
    TODO: how to use IH?.
    Wrong induction? want induction on |G| - n? how to handle base case then?.
    induction on output! not input.

Lemma LR_sub_wkn_cong e e0
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e {{s #"env" }} ->
    wf_term l [] e0 {{s #"ty" }} ->
    LR_sub {{e #"ext" {e} {e0} }} e {{e #"wkn" {e} {e0} }}.
Proof.
  intros l H.
  revert e0.

  
  wkn = cmp wkn id = cmp wkn (snoc wkn hd) = snoc (wkn . wkn) (wkn hd).
  id = snoc wkn hd = snoc (cmp wkn id) hd.
  order of ops: wkn_n cong, id cong
  rel_var

Lemma LR_sub_id_cong e
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e {{s #"env" }} ->
    LR_sub e e {{e #"id" {e} }}.
Proof.

Lemma LR_sub_id_wkn_cong e
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e {{s #"env" }} ->
    LR_sub e e {{e #"id" {e} }}
    /\ (forall e0, wf_term l [] e0 {{s #"ty" }} ->
        LR_sub {{e #"ext" {e} {e0} }} e {{e #"wkn" {e} {e0} }}).
Proof.
  intros l H.
  remember {{s #"env"}} as t.
  revert Heqt.
  pattern t; pattern e; revert e t H.
  apply WfCutElim.wf_term_cut_ind.
  2: basic_goal_prep; subst; tauto.
  2:{
    intros.
    apply eq_sort_trivial_stlc_bool in H1; subst; eauto.
  }
  intros.
  destruct t; cbn in Heqt;
    inversions.
  destruct l0; cbn in H3; inversions; try tauto.
  pose proof H as H';
    eapply env_rules in H';
    cbn in H';
    intuition subst; auto;
    resolve_in H;
      repeat lazymatch goal with
      | H : wf_args _ _ _ (_::_) |- _ =>
          safe_invert H
      | H : wf_args _ _ _ [] |- _ =>
          safe_invert H
      end;      
      cbn [WfCutElim.P_args] in *;
    (intuition;[]); cbn_substs.
  3:{
    econstructor.
    2:econstructor.
    eredex_steps_with value_subst "id_emp_forget".
    constructor.
  }
  3:{
    intros.
    econstructor.
    2:econstructor.
    eapply eq_term_trans.
    {
      eapply eq_term_sym.
      eredex_steps_with value_subst "id_right".
      2:{
        assert (wf_lang (stlc ++ bool_lang ++ exp_subst ++ value_subst))
          by prove_from_known_elabs.
        ComputeWf.solve_wf_ctx.
      }
      {
        repeat eapply wf_subst_cons; cbn_substs; unfold Model.wf_term;
          try eassumption.
        1:constructor.
        all:admit.
      }
    }
    cbn_substs.
    eapply eq_term_trans.
    {
      term_cong; cbn_substs; unfold Model.eq_term.
      1: right; reflexivity.
      5: eredex_steps_with value_subst "id_emp_forget"; cbn_substs; eauto with lang_core.
      all: eapply eq_term_refl; eauto.
      all: admit.
    }
    cbn_substs.
    eredex_steps_with value_subst "cmp_forget".
    2:{
      assert (wf_lang (stlc ++ bool_lang ++ exp_subst ++ value_subst))
        by prove_from_known_elabs.
      ComputeWf.solve_wf_ctx.
    }
    admit.
  }
  {
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "snoc_wkn_hd".
      2:{
        assert (wf_lang (stlc ++ bool_lang ++ exp_subst ++ value_subst))
          by prove_from_known_elabs.
        ComputeWf.solve_wf_ctx.
      }      
      {
        repeat eapply wf_subst_cons; cbn_substs; unfold Model.wf_term;
          try eassumption.
        1:constructor.
      }
    }
    cbn_substs.
    eapply LR_sub_snoc; eauto.
    1-3:admit.
    apply LR_val_cong_hd; eauto.
  }
  {
    
    wkn (G) B = forget (G,B), var n,..var0.
    id G = forget G, var n,..var0.

    sim proofs, but not mutual.
    
    TODO: a high-level issue, not technical
    wkn G A = 
    eapply LR_sub_eq.
    {
      eredex_steps_with value_subst "id_right".
      2:{
        assert (wf_lang (stlc ++ bool_lang ++ exp_subst ++ value_subst))
          by prove_from_known_elabs.
        ComputeWf.solve_wf_ctx.
      }
      {
        repeat eapply wf_subst_cons; cbn_substs; unfold Model.wf_term;
          try eassumption.
        1:constructor.
        all:admit.
      }
    }
    cbn_substs.
    eapply LR_sub_cmp_cong; eauto.
    1-5:admit.
    
    TODO: wkn too large! need an assymetric induction w/ id larger than wk
  }
Qed.
                             
Lemma LR_sub_wkn_cong e0 e
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e0 {{s #"env" }} ->
    wf_term l [] e {{s #"ty" }} ->
    LR_sub {{e #"ext" {e0} {e} }} e0 {{e #"wkn" {e0} {e} }}.
Proof.
  intros l H.
  remember {{s #"env"}} as t.
  revert Heqt e.
  pattern t; pattern e0; revert e0 t H.
  apply WfCutElim.wf_term_cut_ind.
  2: basic_goal_prep; subst; tauto.
  2:{
    intros.
    apply eq_sort_trivial_stlc_bool in H1; subst; eauto.
  }
  intros.
  destruct t; cbn in Heqt;
    inversions.
  destruct l0; cbn in H4; inversions; try tauto.
  pose proof H as H';
    eapply env_rules in H';
    cbn in H';
    intuition subst; auto;
    resolve_in H;
      repeat lazymatch goal with
      | H : wf_args _ _ _ (_::_) |- _ =>
          safe_invert H
      | H : wf_args _ _ _ [] |- _ =>
          safe_invert H
      end;      
      cbn [WfCutElim.P_args] in *;
      (intuition;[]); cbn_substs.
  {
    Compute value_subst.
    TODO: id lemma; wkn -> wkn. id -> apply id lemma
    "cmp_forget"

  

Theorem fundamental e s G X
  : let l := (stlc ++ bool_lang ++ exp_subst ++ value_subst) in
    wf_term l [] e (scon s [X;G]) ->
    (s = "val" -> LR_val G X e)
    /\ (s = "sub" -> LR_sub G X e).
Proof.
  cbv [In].
  intros.
  remember {{s #s {G} {X} }} as t.
  revert s G X Heqt.
  pattern t.
  pattern e.
  revert e t H.
  simple apply WfCutElim.wf_term_cut_ind.
  2: basic_goal_prep; subst; tauto.
  2:{
    intros.
    apply eq_sort_trivial_stlc_bool in H1; subst; eauto.
  }
  intros.
  destruct t; cbn in Heqt;
    inversions.
  destruct l; cbn in H3; inversions; try tauto.
  destruct l; cbn in H3; inversions; try tauto.
  destruct l; cbn in H3; inversions; try tauto.
  intuition subst; auto.
  {
    pose proof H as H';
      apply val_rule_in_stlc_bool in H';
      cbn in H'; intuition subst;
      resolve_in H;
      repeat lazymatch goal with
      | H : wf_args _ _ _ (_::_) |- _ =>
          safe_invert H
      | H : wf_args _ _ _ [] |- _ =>
          safe_invert H
      end;      
      cbn [WfCutElim.P_args] in *;
      (intuition;[]); cbn_substs.
    {
      econstructor.
      2: econstructor.
      eapply eq_term_refl.
      eapply wf_term_by'.
      1:solve_in.
      1: eauto with lang_core.
      left; reflexivity.
    } 
    {
      econstructor.
      2: eapply rel_false.
      eapply eq_term_refl.
      eapply wf_term_by'.
      1:solve_in.
      1: eauto with lang_core.
      left; reflexivity.
    }      
    {
      econstructor.
      2: eapply rel_true.
      eapply eq_term_refl.
      eapply wf_term_by'.
      1:solve_in.
      1: eauto with lang_core.
      left; reflexivity.
    }
    2:{
      repeat multimatch goal with
             | H : forall _ _ _, _ = _ -> _ |- _ =>
                 specialize (H _ _ _ eq_refl)
             end.
      intuition.      
      eapply LR_cong_val_subst; eauto.
    }
    { eapply LR_val_cong_hd; auto. }
  }
  {
    pose proof H as H';
      apply sub_rule_in_stlc_bool in H';
      cbn in H'; intuition subst;
      resolve_in H;
      repeat lazymatch goal with
        | H : wf_args _ _ _ (_::_) |- _ =>
            safe_invert H
        | H : wf_args _ _ _ [] |- _ =>
            safe_invert H
        end;      
      cbn [WfCutElim.P_args] in *;
      (intuition;[]); cbn_substs.
    { eapply LR_sub_forget; eauto. }
    {
      unfold Model.wf_term in *.
      cbn [core_model] in *.      
      repeat multimatch goal with
             | H : forall _ _ _, _ = _ -> _ |- _ =>
                 specialize (H _ _ _ eq_refl)
             end.
      break.
      repeat multimatch goal with
             | H : _ = _ -> _ |- _ =>
                 specialize (H eq_refl)
             end.
      apply LR_sub_snoc; eauto.
    }
    all:
      unfold Model.wf_term in *;
      cbn [core_model] in *; 
      repeat multimatch goal with
        | H : forall _ _ _, _ = _ -> _ |- _ =>
            specialize (H _ _ _ eq_refl)
        end;
      break;
      repeat multimatch goal with
        | H : _ = _ -> _ |- _ =>
            specialize (H eq_refl)
        end.
    {
      clear H9 H10 H11 H0 H1 H.
      apply LR_sub_cmp_cong; eauto.
    }
    {
      TODO: need lemma; induction in this case
      econstructor.
    all: econstructor; [|econstructor; eauto].
    
  intros.
  safe_invert H4;
    safe_invert H5.
  econstructor.
  2:econstructor; eauto.
  term_cong; unfold Model.wf_term; cbn_substs.
  all: try assumption.
  all: eapply eq_term_refl.
  all: eauto.
    
      
    TODO: what is this case?
  
Inductive is_wkn : term -> Prop :=
| is_wkn_cmp s
  :is_wkn (con "wkn" s)
| is_wkn_wkn g f G3 G2 G1
  : is_wkn g ->
    is_wkn f ->
    is_wkn (con "cmp" [g;f;G3; G2; G1]).
Hint Constructors is_wkn : term.

Variant stlc_bool_nf : term -> Prop :=
| nf_hd s : stlc_bool_nf (con "hd" s)
| nf_var e3 e2 e1 e0 s'
  : is_wkn e1 ->
  stlc_bool_nf {{e #"val_subst" {e3} {e2} {e1} {e0} {(con "hd" s')} }}
| nf_lambda e B A G : stlc_bool_nf (con "lambda" [e;B;A;G])
| nf_true G : stlc_bool_nf (con "true" [G])
| nf_false G : stlc_bool_nf (con "false" [G]).
Hint Constructors stlc_bool_nf : term.
Compute value_subst.
Variant sub_nf : term -> Prop :=
| nf_wkn s : sub_nf (con "wkn" s)
| nf_forget s : sub_nf (con "forget" s)
| nf_snoc s : sub_nf (con "snoc" s)
| nf_id s : sub_nf (con "id" s).
Hint Constructors sub_nf : term.
