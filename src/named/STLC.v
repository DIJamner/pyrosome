
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp Rule Core.
Require Import String.

(* constructors from subst*)
Parameter emp : exp -> exp.
Parameter snoc : exp -> exp -> exp -> exp -> exp -> exp -> exp.
Parameter el_subst : exp -> exp -> exp -> exp -> exp -> exp.
Parameter ty_subst : exp -> exp -> exp -> exp -> exp.
Parameter ovar : exp -> exp -> exp -> exp.
Parameter octxt : sort.


Notation ty G := (srt "ty" [:: G]).
Notation el G t := (srt "el" [:: t; G]).
Notation var_srt G t := (srt "var" [:: t; G]).

(* Note: the output substs intentionally
   do not satisfy the output ctx *)
Fixpoint alpha_eq_ctx_subst c : ctx * list exp * list exp * (exp -> exp) :=
  let TODO := (con "TODO" [::]) in
  match c with
  | [::] => ([::], [::], [::], fun G => (con "id" [::G]))
  | (n, var_srt G t)::c' =>
    match alpha_eq_ctx_subst c' with
      (c_a, s, s', rn) =>
      let n' := append n "$a"%string in
      ((n', var_srt G t)::(n, var_srt G t)::c_a,
       (var n)::s, (var n')::s', fun G => (snoc TODO G t (rn G) (var n) (var n')))
    end
  | (n, ty G)::c' =>
    match alpha_eq_ctx_subst c' with
      (c_a, s, s', rn) =>
      ((n,ty G)::c_a, (var n)::s, (ty_subst TODO G (rn G) (var n))::s', rn)
    end
  | (n, el G t)::c' =>
    match alpha_eq_ctx_subst c' with
      (c_a, s, s', rn) =>
      ((n,el G t)::c_a, (var n)::s, (el_subst TODO G t (rn G) (var n))::s', rn)
    end
  | (n, t)::c' =>
    match alpha_eq_ctx_subst c' with
      (c_a, s, s', rn) =>
      ((n,t)::c_a, (var n)::s, (var n)::s', rn)
    end
  end.

Definition alpha_eq_term name c t : rule :=
  match alpha_eq_ctx_subst c with
    (c, s, s', _) =>
    term_le c (con name s) (con name s') t
  end.

Notation "{[ G ]}" := G (G custom ctx).
Eval cbv in (alpha_eq_term "lam"
                           {[ "G" : #"env",
                              "A" : #"ty"(%"G"),
                              "x" : #"var"(%"G",%"A"),
                              "B" : #"ty"(%"G"),
                              "e" : #"el"(#"ext"(%"G",%"A",%"x"), %"B")
                           ]}
                           (srt "arr" [:: var "B"; var "A"])).

Fixpoint alpha_rules l :=
  match l with
  | [::] => [::]            
  | (n, term_rule c t)::l' =>
    (append n "$alpha", alpha_eq_term n c t)::(alpha_rules l')
  (*| (n, sort_rule c)::l' => TODO*)
  | _::l' => alpha_rules l'
  end.

Definition stlc' :=
  [:> "G" : #"env",
      "A" : #"ty"(%"G"),
      "x" : #"var"(%"G",%"A"),
      "B" : #"ty"(%"G"),
      "e" : #"el"(#"ext"(%"G",%"A",%"x"), %"B"),
      "e'" : #"el"(%"G", %"A")
   |- ("STLC-beta") #"app"(%"G", %"A", %"B", #"lambda"(%"G",%"A", %"x",%"B",%"e"), %"e'")
      = #"el_subst"(%"G", #"ext"(%"G",%"A",%"x"),
                    #"snoc"(%"G",%"G",%"A",%"x", #"id"(%"G"),%"e'"),
                    %"e")
   : #"el" (%"G", %"B")]::
                 
  [:| "G" : #"env", "A" : #"ty"(%"G"), "B" : #"ty"(%"G"),
      "e" : #"el"(%"G", #"->"(%"A",%"B")),
      "e'" : #"el"(%"G", %"A")
   |- "app" : #"el"(%"G",%"B")]::
  [:| "G" : #"env",
      "A" : #"ty"(%"G"),
      "x" : #"var"(%"G",%"A"),
      "B" : #"ty"(%"G"),
      "e" : #"el"(#"ext"(%"G",%"A",%"x"), %"B")
   |- "lambda" : #"el" (%"G", #"->"(%"G", %"A", %"B"))]::
  [:| "G" : #"env", "t" : #"ty"(%"G"), "t'": #"ty"(%"G") |- "->" : #"ty"(%"G")]::[::].

Definition stlc :=
  alpha_rules stlc' ++ stlc' ++ [::(*subst_lang*)].
Eval cbv in stlc.

  
Lemma stlc_wf : wf_lang stlc.
Proof using.
  pose p:= subst_lang_wf.
  cbv in p.
  (* TODO: improve this *)  
  wf_lang_eauto.
  all: try done.
  {
    constructor; eauto with judgment.
    eapply wf_term_conv.
    eauto with judgment.
    ltac2:(apply_term_constr ()).
    eapply wf_subst_cons; eauto with judgment.
    eapply wf_subst_cons; eauto with judgment.
    eapply wf_subst_cons; eauto with judgment.
    {
      ltac2:(apply_term_constr()).
      eapply wf_subst_cons; eauto with judgment.
      cbv.
      eapply wf_term_conv.
      eauto with judgmenxt.
      eapply wf_term_var.
      ltac2:(unify_nth_level()).
      eapply sort_con_mor.
      eapply subst_cons_mor.
      eauto with judgment.
      symmetry.
      instantiate (1 := ty 0).
      cbv.
      ltac2:(apply_term_rule constr:(11)).
      eauto with judgment.      
    }
    {
      cbv.
      eapply sort_con_mor.
      eapply le_subst_cons.
      eauto with judgment.
      instantiate (1:= ty 0).
      cbv.
      eapply le_term_trans.
      symmetry.
      Eval cbv in (nth_level (sort_rule [::]) subst_lang 12).
      instantiate
        (1:=ty_subst 0 0
                     (cmp 0 (ext 0 1) 0 (Subst.p 0 1)
                          (snoc 0 0 1 (id 0) 4)) 2).
      cbv.
      ltac2:(apply_term_rule constr:(12)).
      repeat (eapply le_subst_cons; eauto with judgment).
      eapply le_term_trans.
      {
        evar (s:subst).
        suff: (ty 0) = (ty 0)[/s/]; unfold s.
        intro ts.
        rewrite ->ts at 21.
        
        eapply term_con_mor.
        eapply le_subst_cons.
        2: eauto with judgment.
        eapply le_subst_cons.
        2:{
          
          instantiate (2:= hom 0 1).
          instantiate (2 := [:: var 0; var 0]).
          instantiate (1 := id 0).
          cbv.
          ltac2:(apply_term_rule constr:(23)).
          eapply le_subst_cons; eauto with judgment.
        }
        {          
          eapply le_subst_cons; eauto with judgment.
        }
      by compute.
      }
      {
        
        Eval cbv in (nth_level (sort_rule [::]) subst_lang 11).
        ltac2:(apply_term_rule constr:(11)).
        eauto with judgment.
      }
    }
  }

  Unshelve.
    all: solve [ exact (con 0 [::]) | exact [::]].
Qed.
(*
Notation bot g := (con 30 [::g]).
Definition tgt :=
  (term_rule [:: ob] (ty 0))::stlc.

Lemma wf_tgt : wf_lang tgt.
Proof using .
  constructor.
  apply stlc_wf.
  constructor; eauto with judgment.
  econstructor; eauto with judgment.
  ltac2:(unify_nth_level ()).
  constructor; eauto with judgment.
  econstructor; eauto with judgment.
  by cbv.
  Unshelve.
  all: solve [exact (con 0 [::]) | exact [::]].
Qed.
*)
From excomp Require Import Compilers.

Notation "'cfun' pat => e" :=
  (fun s =>
     match s with
     | pat => e
     | _ => con 0 [::]
     end)
    (at level 60, pat pattern).

(*
Definition cps : compiler :=
  [:: (*TODO*)
     (cfun [:: f; g; a; b; c] =>
        (cmp a b c f g)
     );
  (fun s =>
     let withK g := (ext g (bot g)) in
     (con 1 (map withK s)));
  (fun s => con 0 s)].
*)

Notation dyn g := (con 27 [:: g]%exp_scope).
Notation dlam g e := (con 29 [:: e; g]%exp_scope).
Notation dapp g e e' := (con 30 [:: e'; e; g]%exp_scope).

Notation dpair g e1 e2 := (con 32 [:: e2; e1; g]%exp_scope).
Notation dproj1 g e := (con 33 [:: e; g]%exp_scope).
Notation dproj2 g e := (con 34 [:: e; g]%exp_scope).

Notation unit g := (con 37 [:: g]%exp_scope).
Definition cc :=
  (term_rule [:: ob] (el 0 (dyn 0)))::
  (term_le [:: el 0 (dyn 0);
             el 0 (dyn 0);
             ob]
           (dproj2 0 (dpair 0 1 2))
           2
           (el 0 (dyn 0)))::
  (term_le [:: el 0 (dyn 0);
             el 0 (dyn 0);
             ob]
           (dproj1 0 (dpair 0 1 2))
           1
           (el 0 (dyn 0)))::
  (term_rule [:: el 0 (dyn 0); ob] (el 0 (dyn 0)))::
  (term_rule [:: el 0 (dyn 0); ob] (el 0 (dyn 0)))::
  (term_rule [:: el 0 (dyn 0);
             el 0 (dyn 0);
             ob]
             (el 0 (dyn 0)))::
  (term_le [:: el 0 (dyn 0);
               el (ext emp (dyn emp)) (dyn (ext emp (dyn emp))); ob]
           (dapp 0 (dlam 0 1) 2)
           (el_subst 0 (ext emp (dyn emp))
                     (snoc 0 emp (dyn emp) (forget 0) 2)
                     (dyn (ext emp (dyn emp))) 1)
           (el 0 (dyn 0)))::
  (term_rule [:: el 0 (dyn 0); el 0 (dyn 0); ob]
             (el 0 (dyn 0)))::
  (term_rule [:: el (ext emp (dyn emp)) (dyn (ext emp (dyn emp))); ob]
             (el 0 (dyn 0)))::
  (term_le [:: hom 0 1; ob; ob]
           (ty_subst 0 1 2 (dyn 1))
           (dyn 0)
           (ty 0))::
  (term_rule [:: ob] (ty 0))::
  subst_lang.

Lemma cc_wf : wf_lang cc.
Proof.
  pose swf := subst_lang_wf.
  wf_lang_eauto.
  2: by cbv.
   {
    constructor; eauto with judgment.
    eapply wf_term_conv.
    eauto with judgment.
    ltac2:(apply_term_constr ()).
    eapply wf_subst_cons; eauto with judgment.
    eapply wf_subst_cons; eauto with judgment.
    eapply wf_subst_cons; eauto with judgment.
    {
      cbv.
      ltac2:(apply_term_constr()).
      eapply wf_subst_cons; eauto with judgment.
      cbv.
      eapply wf_term_conv.
      eauto with judgment.
      eapply wf_term_var.
      ltac2:(unify_nth_level()).
      eapply sort_con_mor.
      eapply subst_cons_mor.
      eauto with judgment.
      symmetry.
      instantiate (1 := ty 0).
      cbv.
      ltac2:(apply_term_rule constr:(28)).
      eauto with judgment.      
    }
    {
      cbv.
      eapply sort_con_mor.
      eapply le_subst_cons.
      eauto with judgment.
      instantiate (1:= ty 0).
      cbv.
      ltac2:(apply_term_rule constr:(28)).
      repeat (eapply le_subst_cons; eauto with judgment).
    }
   }
Unshelve.
    all: solve [ exact (con 0 [::]) | exact [::]].
Qed.

Definition dummy := (fun s : subst => con 0 [::]).
Definition subst_id_comp : compiler :=
  [::
     dummy;
  dummy;
  dummy;
  dummy;
  con 22;
  con 21;
  con 20;
  con 19;
  dummy;
  dummy;
  con 16;
  con 15;
  dummy;
  dummy;
  dummy;
  dummy;
  con 10;
  con 9;
  con 8;
  con 7;
  dummy;
  dummy;
  dummy;
  con 3;
  con 2;
  con 1;
  con 0].

Print ("f":string).

Lemma subst_id_comp_preserves : preserving_compiler cc subst_id_comp subst_lang.
Proof.
  eapply preserving_compiler_term_le.
  2:{
    intro s.
    simpl.
    change (nth_level (fun=> ob) _ ?n) with (con n).
    inversion; subst.
    inversion H2; subst.
    inversion H3; subst.
    move: H5 H8.
    clear H3 H7 H2 H H4.
    change (var_lookup [:: e; e0] 0) with e0. 
    change (var_lookup [:: e; e0] 1) with e.
    intros.
    change (le_term cc [::] (hom (ext e0 e) (ext e0 e)) (id (ext e0 e))
    (snoc (ext e0 e) e0 e (p e0 e) (q e0 e))) with
        (le_term cc [::]
                 (hom (ext 0 1) (ext 0 1))[/[:: e; e0]/]
                 (id (ext 0 1))[/[:: e; e0]/]
                 (snoc (ext 0 1) 0 1 (p 0 1) (q 0 1))[/[:: e;e0]/]).
    eapply le_term_subst.
    2:{
      eapply le_term_by.
      by instantiate (1:= [:: ty 0; ob]).
    }
    {
      eauto with judgment.
    }
  }
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term.
  2:{
    intro s.
    simpl.
    change (nth_level (fun=> ob) _ ?n) with (con n).
    inversion; subst.
    inversion H2; subst.
    inversion H3; subst.
    change (var_lookup [:: e; e0] 0) with e0. 
    change (var_lookup [:: e; e0] 1) with e.
    ltac2:(apply_term_constr ()).
    econstructor; eauto with judgment.
    eapply wf_sort_by.
    ltac2:(unify_nth_level()).
    constructor; eauto with judgment.
    move: H5.
    change (var_lookup [:: e; e0] 0) with e0.
    change (ty 0)[/[::e0]/] with (ty e0).
    replace  (ty e0) [/[:: e0] /] with (ty e0); auto.
    unfold exp_subst.
    simpl.
    f_equal.
    f_equal.
    give_up(* TODO: lemma about closed terms*).
  }
  
  eapply preserving_compiler_term.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term.
  eapply preserving_compiler_sort.
  eapply preserving_compiler_term.
  eapply preserving_compiler_sort.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term.
  eapply preserving_compiler_sort.
  eapply preserving_compiler_sort.
  eapply preserving_compiler_nil.
Admitted.

Definition dweaken g t e :=
  el_subst (ext g t) g (p g t) (dyn g) e.
Fixpoint mkenv_tuple g : exp :=
  match g with
  | emp => (unit emp)
  | ext g' t => (dpair (ext g' t) (q g' t) (dweaken g' t (mkenv_tuple g')))
  | _ => con 0 [::]
  end.

Fixpoint mkenv_subst g pr : exp :=
  match g with
  | emp => id emp
  | ext g' t =>
    let ge := ext emp (dyn emp) in
    snoc ge g' t
         (mkenv_subst g' (dproj2 ge pr))
         (dproj1 ge pr)
  | _ => con 0 [::]
  end.

Definition compile_arr :=
  cfun [:: b; a; g] => dyn g.

Definition compile_abstr :=
 cfun [:: g; a; b; e] =>
   dpair g (dlam g (el_subst (ext emp (dyn emp))
                             (ext g a)
                             (mkenv_subst g (q emp (dyn emp)))
                             (dyn (ext g a)) e))
         (mkenv_tuple g). 

Definition cc_comp : compiler :=
  [:: dummy;
  dummy;
  compile_abstr;
  compile_arr
  ]++ subst_id_comp.

Lemma cc_comp_preserves
  : preserving_compiler cc cc_comp stlc.
Proof.
  eapply preserving_compiler_term_le.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term.
  eapply preserving_compiler_term.
  apply subst_id_comp_preserves.
  {
    intro s.
    simpl.
    change (nth_level (fun=> ob) _ ?n) with (con n).
    inversion;subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H6; subst.
    change (var_lookup _ 0) with e1.
    cbv.
    ltac2:(apply_term_constr()).
    constructor; eauto with judgment.
  }
  {
    intro s; simpl.               
    change (nth_level (fun=> ob) _ 27) with compile_arr.
    change (nth_level (fun=> ob) _ ?n) with (con n).
    inversion;subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H6; subst.
    inversion H9; subst.
    move: H5.
    change (var_lookup _ 0) with e2.
    change (var_lookup _ 1) with e1.
    change (var_lookup _ 2) with e0.
    unfold compile_arr.
    unfold compile_abstr.
    intro.
    ltac2:(apply_term_constr()).
    constructor; eauto with judgment.
