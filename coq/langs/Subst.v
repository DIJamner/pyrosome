
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* TODO: change from loads to imports *)
From excomp Require Import Exp CoreDefs Core.

Ltac easy_wf_lang :=
  first [ constructor
        |  econstructor; unfold is_nth; simpl; eauto];
  let n := numgoals in
  guard n < 2.

Definition ctx_lang : lang :=
  [:: {| [:: [2(*tp*)|]; [1(*ctx*)|]] |- (*C,t*) [1(*ctx*)|]};
     {| [::] |- (*.*) [0 (*ctx*)|]};
     {| [::] |- (*ctx*) sort };
     {| [::] |- (*tp*) sort }].

Lemma wf_ctx_lang : wf_lang ctx_lang.
Proof.
  pose p := eqP.
  repeat easy_wf_lang.
Qed.  

Definition subst_lang : lang :=
  [::
    (* {| [:: [5(*tp*)|];[1(*var*)| var 1; var 0];[5(*tp*)|]; [4(*ctx*)|]]
        |- (*S x*) [1(*var*)| [2(*C,t'*)| var 3; var 0];var 2]};
     *){| [:: [4(*tp*)|]; [3(*ctx*)|]] |- (*Z*) [0(*var*)| [1(*C,t*)| var 1; var 0] ; var 0]};
     {| [:: [3(*tp*)|]; [2(*ctx*)|]] |- (*var(C|-t)*) sort}]
++ ctx_lang.
(* TODO: substitutions, judgments, equalities *)

Lemma wf_subst_lang : wf_lang subst_lang.
Proof.
  pose p := eqP.
  pose cl := wf_ctx_lang.
  repeat easy_wf_lang.
  constructor.
  constructor.
  constructor.
  repeat easy_wf_lang.
  (*TODO: issue: seems to be a +1 that isn't happening in the var C,t substitution*)
  give_up.
  repeat easy_wf_lang.
  

  match goal with
    |- wf_subst ?L _ _ _ =>
    suff: wf_lang L
  end.
  give_up.
  repeat constructor.
  match goal with
    |- wf_sort ?L _ _ =>
    enough (wf_lang L)
  end;[| repeat easy_wf_lang].
  repeat easy_wf_lang.
  constructor.
  constructor.
  repeat easy_wf_lang.
  give_up.
  unfold exp_subst; simpl.
  change (0+3) with 3.
  change [3|] with ([3|][/[:: var 1; var 0]/]).
  eapply wf_term_by.
  unfold is_nth; simpl. eauto.
  simpl.
  repeat easy_wf_lang.
  econstructor; unfold is_nth; simpl; eauto.
  



  
  give_up.
  repeat easy_wf_lang.
  repeat constructor.
  econstructor; unfold is_nth; simpl; eauto.
  repeat constructor.
  econstructor; unfold is_nth; simpl; eauto.
  
  
  
  match goal with
    |- wf_sort ?L _ _ =>
    enough (wf_lang L)
  end;repeat easy_wf_lang.
  let n := numgoals in
  idtac numgoals.
  - move => wfl.
    constructor.
    give_up.
    + constructor.
      constructor.
      constructor.
  - do 2 easy_wf_lang.
    + do 3 easy_wf_lang.
      * repeat easy_wf_lang.
      * repeat easy_wf_lang.
        give_up.
      * 
        repeat constructor.
        -- repeat easy_wf_lang.
        -- unfold rule_in; simpl; eauto.
 
    econstructor; unfold is_nth; simpl; eauto.
      repeat constructor.
      econstructor; unfold is_nth; simpl; eauto.
      repeat constructor.
      econstructor; unfold is_nth; simpl; eauto.
      repeat constructor.
      * econstructor; unfold is_nth; simpl; eauto.
        repeat constructor.
        econstructor; unfold is_nth; simpl; eauto.
        repeat constructor.
        econstructor; unfold is_nth; simpl; eauto.
        repeat constructor.
        econstructor; unfold is_nth; simpl; eauto.
        repeat constructor.
        econstructor; unfold is_nth; simpl; eauto.
        repeat constructor.
        econstructor; unfold is_nth; simpl; eauto.
        repeat constructor.
        econstructor; unfold is_nth; simpl; eauto.
        repeat constructor;
        econstructor; unfold is_nth; simpl; eauto;
        repeat constructor.
      *
    

Definition subst_lang : lang subst_syn :=
  (* terms *)
  [::
     (* ctxts*)
     {| [::] |- empty_ctxt' .: ctxt'};
     {| [:: term_var ctxt' ; term_var tp' ] |- cons_ctxt' (var 0) (var 1) .: ctxt'} ;
     (* variables *)
     {| [:: term_var tp'] |- zv' .: var_srt'(judg' (@! ,, (var 0)) (var 0))};
     {| [:: term_var (var_srt' (judg' (var 0) (var 1))); term_var ctxt'; term_var tp']
        |- (sv' (var 0)) .: var_srt' (judg' (@! ,, (var 0)) (var 0))};
     (* judgments *)
     {| [:: term_var (var 0); term_var (var_srt' (var 0)); sort_var]
        |- (var 0) .: (var 2)}
  ] ++
    (* sorts *)
    [:: {| [:: term_var ctxt' ; term_var tp' ] |- judg' (var 0) (var 1)} ;
       {| [:: sort_var ] |- var_srt' (var 0)};
       {| [::] |- ctxt' };
       {| [::] |- tp' }
    ].

Definition list_syn : polynomial :=
  [:: (unit, 0) (* nil *)
   ; (unit, 2) (* cons*)].

Definition subst_syn : polynomial :=
  [:: (unit, 0) (* tp *)]
    ++  [:: (unit, 0) (* ctxt *)]
    ++ list_syn (* ctxt := . | ctxt, t:tp*)
    ++ [:: (unit,2) (* jdg := ctxt |- t:tp *)]
    ++ [:: (unit,0) ; (unit,1) (* var := 0 | S var*)]
    ++ list_syn (* subst := . | subst, v:type*)
    ++ [:: (unit,1) (*var := jdg*)].

Definition tp {T} : constr subst_syn T := [{subst_syn,T}> 0 | tt, [*]].

Definition ctxt {T} : constr subst_syn T := [{subst_syn,T}> 1 | tt, [*]].

Definition empty_ctxt {T} := [{subst_syn,T}> 2 | tt, [*]].
Definition cons_ctxt {T} a b := [{subst_syn,T}> 3 | tt, [* a; b]].

Definition judg {T} c t := [{subst_syn,T}> 4 | tt, [* c; t]].

Definition zv {T} := [{subst_syn,T}> 5 | tt, [*]].
Definition sv {T} x := [{subst_syn,T}> 6 | tt, [* x]].

Definition empty_sub {T} := [{subst_syn,T}> 7 | tt, [*]].
Definition cons_sub {T} a b := [{subst_syn,T}> 8 | tt, [* a; b]].

Definition tp' := [{subst_syn} 0 | tt, [*]].
Definition ctxt' := [{subst_syn} 1 | tt, [*]].

Definition empty_ctxt' := [{subst_syn} 2 | tt, [*]].
Definition cons_ctxt' a b := [{subst_syn} 3 | tt, [* a; b]].

Definition judg' c t := [{subst_syn} 4 | tt, [* c; t]].

Definition zv' := [{subst_syn} 5 | tt, [*]].
Definition sv' x := [{subst_syn} 6 | tt, [* x]].

Definition empty_sub' := [{subst_syn} 7 | tt, [*]].
Definition cons_sub' a b := [{subst_syn} 8 | tt, [* a; b]].

Definition var_srt' s :=  [{subst_syn} 9 | tt, [* s]].

Notation "@!" := empty_ctxt'.
Notation "C ,, t" := (cons_ctxt' C t) (at level 90).




Lemma wf_subst_lang : wf_lang subst_lang.
Proof.
  unfold subst_lang.
  constructor; constructor.
  constructor.
  constructor; constructor.
  - constructor; constructor.
    change ctxt
    eapply wf_sort_subst.
    constructor.
    Focus 2.
    simpl.
    eauto.

  eauto.
  constructor.
  - repeat constructor.

  simpl; eauto.
  constructor.
     (* TODO: how to talk about an arbitrary coefficient? needs to be 3rd ctxt option? *)
     {| [:: coeff] |- (svar' 0) .: judg' (@! ,, (var 0)) (var 0)}].
