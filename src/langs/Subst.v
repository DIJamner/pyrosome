
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Exp Rule CoreDefs Core EasyWF Named.
Require Import String.

Ltac guard_single_goal :=
  let n := numgoals in
  guard n < 2.


Ltac compute_adds :=
  repeat match goal with
           |- context [?X + ?Y] =>
           let res := eval compute in (X + Y) in
               change (X + Y) with res
         end.


Ltac clear_const_substs :=
  repeat match goal with
         | |- context [[ ?N |] [/?S/]] =>
           change [N |][/?S/] with [N|]
         end.


Ltac easy_wf_lang :=
  first [ constructor
        |  econstructor; unfold is_nth_level; unfold nth_level; simpl; eauto; 
           guard_single_goal
        | by eapply wf_to_ctx; eauto];
  compute_adds;
  clear_const_substs.

Ltac constructors :=
  progress repeat (constructor; guard_single_goal).

Ltac topswap :=
  let H1 := fresh in
  let H2 := fresh in
  move => H1 H2;
          move: H2 H1.

Definition ob := (con 1 [::]).
Definition hom a b := con 2 [:: b; a].
Definition id a := con 3 [:: a].
Definition cmp a b c g f := (con 4 [:: f; g; c; b; a]).

(* syntax of categories *)
Definition cat_stx : lang :=
  [::
     term_rule [:: hom (var 2) (var 3); hom (var 0) (var 1); ob; ob; ob]
               (hom (var 2) (var 4));
     term_rule [:: ob] (hom (var 0) (var 0));
     sort_rule [:: ob; ob];
     sort_rule [::]
  ].


Lemma cat_syx_wf : wf_lang cat_stx.
Proof.
  solve_easy_wf.
Qed.

(* TODO: use partial recognizer*)
Lemma wf_ob c : wf_ctx cat_stx c -> wf_sort cat_stx c ob.
Proof.
  easy_wf_lang.
Qed.

Lemma wf_hom c a b : wf_term cat_stx c a ob -> wf_term cat_stx c b ob -> wf_sort cat_stx c (hom a b).
Proof.
  easy_wf_lang.
  constructor; eauto.
  easy_wf_lang; eauto.
  easy_wf_lang; eauto.
  eapply wf_to_ctx.
  eauto.
Qed.

Lemma wf_id c a : wf_term cat_stx c a ob -> wf_term cat_stx c (id a) (hom a a).
Proof.
  intro.
  change (hom a a) with (hom (var 0) (var 0))[/[::a]/].
  easy_wf_lang.
  constructor.
  easy_wf_lang.
  eapply wf_to_ctx; eauto.
  done.
Qed.

(*
Lemma wf_hom_inversion c A B
  : wf_sort cat_stx c (hom A B) ->
    wf_term cat_stx c A ob /\ wf_term cat_stx c B ob.
Proof.
  inversion.
  move: H4.
  unfold is_nth.
  simpl.
  change (3+0) with 3.
  move /eqP.
  case => c'eq.
  move: H5.
  rewrite -c'eq.
  inversion.
  split; eauto.
  inversion H10.
  eauto.
Qed.*)


(* TODO: move to exp,core *)

Lemma
  exp_subst_ind' (P : exp -> Prop) (Q : subst -> Prop)
  : (forall n,  P (var n)) ->
    (forall n s,  Q s -> P (con n s)) ->
    Q [::] ->
    (forall e s, P e -> Q s -> Q (e :: s)) ->
    forall e, P e.
Proof.
  intros.
    elim: e; auto.
    move=> n.
    elim.
    auto.
    intros.
    simpl in H4.
    destruct H4.
    apply H0.
    apply H2; auto.
    clear H3.
    elim: l H5; auto.
    intros.
    destruct H5.
    apply H2; auto.
Qed.

Lemma
  exp_subst_ind (P : exp -> Prop) (Q : subst -> Prop)
  : (forall n,  P (var n)) ->
    (forall n s,  Q s -> P (con n s)) ->
    Q [::] ->
    (forall e s, P e -> Q s -> Q (e :: s)) ->
    (forall e, P e) /\ (forall s, Q s).
Proof.
  intros.
  assert ( alleP : forall e, P e).
  apply (@exp_subst_ind' P Q); auto.
  split; auto.
  clear H0 H.
  suff: (forall e s, Q s -> Q (e :: s)).
  intro; elim; eauto.
  eauto.
Qed.

Lemma var_lookup_cmp n s1 s2 : n < size s1 ->
                               var_lookup (subst_cmp s1 s2) n = exp_var_map (var_lookup s2) (var_lookup s1 n).
Proof.
  elim: s1 s2 n; simpl.
  {
    move => s2 n.
    by rewrite ltn0.
  }
  {
    intros.
    elim: n H0 s2; auto.
  }
Qed.

(* TODO: include output size for ws_subst? *)
Lemma subst_cmp_assoc'
  : (forall e s1 s2, ws_exp (size s1) e -> e[/subst_cmp s1 s2/] = e[/s1/][/s2/])
    /\ (forall s s1 s2, List.fold_right (fun e : exp => andb (ws_exp (size s1) e)) true s -> subst_cmp (subst_cmp s s1) s2 = subst_cmp s (subst_cmp s1 s2)).
Proof.
  apply exp_subst_ind; simpl; auto; intros.
  2: by rewrite !con_subst_cmp H.
  2: {
    move /andP in H1.
    destruct H1.
    rewrite H; auto.
    rewrite H0; auto.
  }
 intros.
 unfold exp_subst.
 simpl.
 by apply var_lookup_cmp.
Qed.

Lemma subst_cmp_assoc s s1 s2
  : List.fold_right (fun e : exp => andb (ws_exp (size s1) e)) true s ->
    subst_cmp (subst_cmp s s1) s2 = subst_cmp s (subst_cmp s1 s2).
Proof.
    by eapply subst_cmp_assoc'.
Qed.

Lemma sep_subst_cmp e s1 s2 :  ws_exp (size s1) e -> e[/subst_cmp s1 s2/] = e[/s1/][/s2/].
Proof.
    by eapply subst_cmp_assoc'.
Qed.
  
Scheme wf_sort_subst_props_ind := Minimality for wf_sort Sort Prop
  with wf_subst_subst_props_ind := Minimality for wf_subst Sort Prop
  with wf_term_subst_props_ind := Minimality for wf_term Sort Prop.

Combined Scheme subst_props_ind from
         wf_sort_subst_props_ind,
wf_subst_subst_props_ind,
wf_term_subst_props_ind.
(*TODO: will eventually want a library of betterinduction schemes for same reason I wantedparameters*)

Lemma wf_subst_props c s
  : (forall l c' t, wf_sort l c' t -> wf_subst l c s c' -> wf_sort l c t[/s/])
    /\ (forall l c' s2 c2', wf_subst l c' s2 c2' -> wf_subst l c s c' -> wf_subst l c (subst_cmp s2 s) c2')
    /\ (forall l c' e t, wf_term l c' e t -> wf_subst l c s c' -> wf_term l c e[/s/] t[/s/]).
Proof.
  apply: subst_props_ind.
  {  
    intros.
    rewrite con_subst_cmp.
    eauto.
  }
  {
    intros; simpl; constructor.
    by apply wf_to_ctx in H0.
  }
  {
    intros; simpl; constructor; eauto.
    rewrite sep_subst_cmp.
    auto.
    Check subst_props_ind.
    TODO: presupposition issue; adding presuppositions should make schemes better

    
  
Lemma wf_cmp c A B C g f
  : wf_term cat_stx c f (hom A B) ->
    wf_term cat_stx c g (hom B C) ->
    wf_term cat_stx c (cmp A B C g f) (hom A C).
Proof.
  intros.
  eapply wf_term_subst.
  change (hom A C) with (hom (var 4) (var 2)) [/[:: f; g; C; B; A]/].
  eapply wf_term_by.
  2:{
    easy_wf_lang; eauto.
    constructor; eauto.
    repeat easy_wf_lang; eauto.
    
  easy_wf_lang.
  easy_wf_lang.
  eapply wf_to_ctx; eauto
  
Goal wf_term cat_stx [:: ob]
     (cmp (var 0) (var 0) (var 0) (id (var 0)) (id (var 0))) (hom (var 0) (var 0)).
Proof.
  change (hom (var 0) (var 0)) with (hom (var 2) (var 3))[/[:: id (var 0); id (var 0); var 0; var 0; var 0]/].
  eapply wf_term_by.
  compute.
  match goal with
  | |- wf_term ?l ?c (con ?m ?s) [?n|] =>
    change (wf_term l c (con m s) [n|])
      with (wf_term l c (con m s) [n|][/s/])
  end.
  

Definition cat_lang' : seq named_rule :=
  [:: {<n 
  ]++cat_stx'.

           

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

Definition subst_lang' : lang :=
  [::
    (* {| [:: [5(*tp*)|];[1(*var*)| var 1; var 0];[5(*tp*)|]; [4(*ctx*)|]]
        |- (*S x*) [1(*var*)| [2(*C,t'*)| var 3; var 0];var 2]};
     *){| [:: [4(*tp*)|]; [3(*ctx*)|]] |- (*Z*) [0(*var*)| var 0; [1(*C,t*)| var 0; var 1]]};
     {| [:: [3(*tp*)|]; [2(*ctx*)|]] |- (*var(C|-t)*) sort}]
++ ctx_lang.
(* TODO: substitutions, judgments, equalities *)


Lemma wf_subst_lang : wf_lang subst_lang'.
Proof.
  pose p := eqP.
  pose cl := wf_ctx_lang.
  repeat easy_wf_lang.
  change [3|] with [3|][/[:: var 0; var 1]/].  
  apply: wf_term_by.
  unfold is_nth; simpl.
  compute_adds.
  apply /eqP; f_equal.
  repeat easy_wf_lang.
Qed.

Definition subst_lang'' : lang :=
  [:: {| [:: [5(*tp*)|];[1(*var*)| var 1; var 0];[4(*ctx*)|]; [5(*tp*)|]]
        |- (*S x*) [1(*var*)| var 3 ; [2(*C,t'*)| var 0; var 2]]}]
    ++ subst_lang'.

Lemma wf_subst_lang'' : wf_lang subst_lang''.
Proof.
  pose wfp :=  wf_subst_lang.
  repeat easy_wf_lang.
  match goal with
  | |- wf_term ?l ?c (con ?m ?s) [?n|] =>
    change (wf_term l c (con m s) [n|])
      with (wf_term l c (con m s) [n|][/s/])
  end.
  apply: wf_term_by.
  unfold is_nth; simpl.
  compute_adds.
  eauto.
  repeat easy_wf_lang.
Qed.

Definition subst_lang_syn : lang :=
  [::{| [:: [4 | var 0; var 1] ; [3(*tp*)|]; [2(*ctx*)|]] |- [0| var 1; var 2]};
     {| [:: [3(*tp*)|]; [2(*ctx*)|]] |- (*jdg(C|-t)*) sort}]
    ++ subst_lang''.

Lemma wf_syn : wf_lang subst_lang_syn

  
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

                                                                  
