
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core EasyWF.
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

Ltac constructors :=
  progress repeat (constructor; guard_single_goal).

Ltac topswap :=
  let H1 := fresh in
  let H2 := fresh in
  move => H1 H2;
          move: H2 H1.

Definition ob := (con 0 [::]).
Definition hom a b := con 1 [:: b; a].
Definition id a := con 2 [:: a].
Definition cmp a b c f g := (con 3 [:: f; g; c; b; a]).

(* syntax of categories *)
Definition cat_stx : lang :=
  [::
     term_rule [:: hom (var 1) (var 2); hom (var 0) (var 1); ob; ob; ob]
               (hom (var 0) (var 2));
     term_rule [:: ob] (hom (var 0) (var 0));
     sort_rule [:: ob; ob];
     sort_rule [::]
  ].

Ltac recognize_lang :=
  match goal with
    |- wf_lang ?L =>
    suff: type_wf_lang L = Some tt;
    [ by apply type_wf_lang_recognizes
    | by compute]
  end.

Ltac recognize_rule' :=
  match goal with
    |- wf_rule ?L ?R =>
    suff: type_wf_rule L R = Some tt;
    [ by apply type_wf_rule_recognizes
    | idtac]
  end.
Lemma cat_stx_wf : wf_lang cat_stx.
Proof using . recognize_lang. Qed.

Coercion var : nat >-> exp.

Definition cat_lang : lang :=
  (* compose associativity *)
  (term_le [:: hom 2 3; hom 1 2; hom 0 1; ob; ob; ob; ob]
           (cmp 0 1 3 (cmp 1 2 3 6 5) 4)
           (cmp 0 2 3 6 (cmp 0 1 2 5 4))
           (hom 0 3))::
  (* left identity *)
  (term_le [:: (hom 0 1); ob; ob]
               (cmp 0 1 1 (id 1) 2)
               2
               (hom 0 1))::
  (* right identity *)
  (term_le [:: (hom 0 1); ob; ob]
               (cmp 0 0 1 2 (id 0))
               2
               (hom 0 1))::cat_stx.


Lemma cat_lang_wf : wf_lang cat_lang.
Proof using .
  recognize_lang.
Qed.

Lemma wf_ob c : wf_ctx cat_stx c -> wf_sort cat_stx c ob.
Proof using .
  intros.
  suff: type_wf_sort cat_stx c ob = Some tt; first by apply type_wf_sort_recognizes.
  by compute.
Qed.


(* TODO: need decision instead of recognizer for this one  due to a, b*)
Lemma wf_hom c a b : wf_term cat_stx c a ob -> wf_term cat_stx c b ob -> wf_sort cat_stx c (hom a b).
Proof.
  intros.
  suff: type_wf_sort cat_stx c (hom a b) = Some tt; first by apply type_wf_sort_recognizes; eauto with judgment.
  
  compute.
Qed.

  easy_wf_lang; auto.
  constructor; eauto.
  easy_wf_lang; eauto.
  easy_wf_lang; eauto.
  eapply wf_to_ctx; eauto.
  solve_easy_wf.
  solve_easy_wf.
Qed.

Lemma wf_id c a : wf_term cat_stx c a ob -> wf_term cat_stx c (id a) (hom a a).
Proof.
  intro.
  change (hom a a) with (hom (var 0) (var 0))[/[::a]/].
  easy_wf_lang.
  constructor.
  easy_wf_lang.
  eapply wf_to_ctx; eauto.
  solve_easy_wf.
  easy_wf_lang.
  apply: le_sort_refl.
  solve_easy_wf.
  apply: wf_term_sort; eauto.
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

Scheme wf_sort_subst_props_ind := Minimality for wf_sort Sort Prop
  with wf_subst_subst_props_ind := Minimality for wf_subst Sort Prop
  with wf_term_subst_props_ind := Minimality for wf_term Sort Prop.

Combined Scheme subst_props_ind from
         wf_sort_subst_props_ind,
wf_subst_subst_props_ind,
wf_term_subst_props_ind.
(*TODO: will eventually want a library of betterinduction schemes for same reason I wantedparameters*)

(* TODO: move to utils*)
Lemma nth_error_size_lt {A} (l : seq A) n e : List.nth_error l n = Some e -> n < size l.
Proof.
  elim: n l => [| n IH];case; simpl; auto; try done.
Qed.

Lemma le_ctx_len_eq  l c c' : le_ctx l c c' -> size c = size c'
with le_sort_ctx_len_eq l c c' t t' : le_sort l c c' t t' -> size c = size c'.
Proof.
  case; simpl; auto; intros; f_equal.
  apply: le_sort_ctx_len_eq; eauto.
  intro les.
  eapply wf_to_ctx in les.
  apply: le_ctx_len_eq; eauto.
TODO: get a nicer induction w/ presuppositions
  
Lemma wf_is_ws : (forall l c t, wf_sort l c t -> ws_exp (size c) t)
                 /\ (forall l c s c', wf_subst l c s c' -> ws_subst (size c) s)
                 /\ (forall l c e t, wf_term l c e t -> ws_exp (size c) e).
Proof.
  apply: subst_props_ind; simpl; intros; try apply /andP; auto; try apply: nth_error_size_lt; eauto.
  eapply wf_to_ctx in H1.
  TODO: show cssame size
Qed.


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
    Search _ ws_subst.
    TODO: need wf ->ws

    
  
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

                                                                  
