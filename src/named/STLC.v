
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import IExp IRule ICore Subst.
Require Import String.


Require Import Named.Tactics.
Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

Definition stlc :=
  [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B"),
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("lambda_subst")
      #"el_subst" %"g" (#"lambda" %"e")
      = #"lambda" (#"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e")
      : #"el" %"G'" (#"ty_subst" %"g" (#"->" %"A" %"B"))
  ]::
  [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "e" : #"el"%"G" (#"->" %"A" %"B"),
      "e'" : #"el" %"G" %"A",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("app_subst")
      #"el_subst" %"g" (#"app" %"e" %"e'")
      = #"app" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"el" %"G'" (#"ty_subst" %"g" %"B")
  ]::
  [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("->_subst")
      #"ty_subst" %"g" (#"->" %"A" %"B")
      = #"->" (#"ty_subst" %"g" %"A") (#"ty_subst" %"g" %"B")
      : #"ty" %"G'"
  ]::
  [:> "G" : #"env",
      "A" : #"ty"%"G",
      "B" : #"ty"%"G",
      "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B"),
      "e'" : #"el" %"G" %"A"
      ----------------------------------------------- ("STLC_beta")
      #"app" (#"lambda"%"e") %"e'"
      = #"el_subst" (#"snoc" #"id" %"e'") %"e"
      : #"el" %"G" %"B"
  ]::
  [:| "G" : #"env",
       "A" : #"ty" %"G",
       "B" : #"ty" %"G",
       "e" : #"el" %"G" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       "app" "e" "e'" : #"el" %"G" %"B"
  ]::
  [:| "G" : #"env",
       "A" : #"ty" %"G",
       "B" : #"ty" %"G",
       "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B")
       -----------------------------------------------
       "lambda" "e" : #"el" %"G" (#"->" %"A" %"B")
  ]::
  [:| "G" : #"env", "t" : #"ty" %"G", "t'": #"ty" %"G"
      -----------------------------------------------
      "->" "t" "t'" : #"ty" %"G"
  ]::subst_lang.

Derive elab_stlc
       SuchThat (elab_lang stlc elab_stlc)
       As elab_stlc_pf.
Proof.
  repeat (repeat (cbn;step_elab())).
  {
    apply elab_term_by'; try (fun () => solve [repeat (cbn;step_elab())]).
    cbn.
    step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    step_elab().
    solve [repeat (cbn;step_elab())].

    cbn. apply elab_term_by'.    
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].

    cbn. apply (@elab_term_var' "A"%string).
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn. step_elab ().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].

    cbn. apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    cbn. apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    
    cbn. apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. apply (@elab_term_var' "A"%string).
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    cbn. apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    
    cbn. apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].

    cbn. apply Core.wf_sort_by'.
    solve [repeat (cbn;step_elab())].

    cbn. constructor.
    solve [repeat (cbn;step_elab())].
    cbn. constructor. (* TODO add wf_args to step_elab()?*)
    solve [repeat (cbn;step_elab())].
    cbn. constructor. (* TODO add wf_args to step_elab()?*)
    solve [repeat (cbn;step_elab())].

    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].

    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    cbn. step_elab(). 
    solve [repeat (cbn;step_elab())].
    cbn. step_elab(). 
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].

    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].

    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].

    
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
  }
  {
    cbn.
    eapply elab_term_conv.
    
    apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    cbn; step_elab().
    solve [repeat (cbn;step_elab())].
    cbn. apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    repeat (cbn;step_elab()).
    apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    repeat (cbn;step_elab()).
    apply elab_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    repeat (cbn;step_elab()).

    cbn.
    eapply elab_term_conv.
    solve [repeat (cbn;step_elab())].
    repeat (cbn;step_elab()).
    cbn.
    apply (@Core.wf_term_var' "G"%string).
    solve [repeat (cbn;step_elab())].

    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    repeat (cbn;step_elab()).
    cbn. apply (@Core.wf_term_by' "id"%string).
    solve [repeat (cbn;step_elab())].
    repeat (cbn;step_elab()).

    cbn. apply (@Core.wf_term_var' "G"%string).
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].

    {
      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      symmetry.
      eapply (@Core.le_term_by' "ty_subst_id"%string); repeat (cbn; step_elab()); reflexivity.
    }
    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    solve [repeat (cbn;step_elab())].
    cbn. apply Core.wf_term_by'.
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    solve [repeat (cbn;step_elab())].
    {
      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      eapply Core.le_term_trans.
      Focus 2.
      eapply (@Core.le_term_by' "ty_subst_id"%string); repeat (cbn; step_elab()); reflexivity.
      eapply Core.le_term_trans.

      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab());
      try (fun ()=> reflexivity).
      eapply Core.le_term_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      eapply (@Core.le_term_by' "wkn_snoc"%string); repeat (cbn; step_elab());
      try (fun ()=> reflexivity).
    }
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    eapply elab_term_conv.
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    repeat (cbn; step_elab()).
    
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    {
       eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
       cbn.
      eapply (@Core.le_term_by' "->_subst"%string); repeat (cbn; step_elab()); reflexivity.
    }
    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    cbn. apply (@elab_term_var' "A"%string); repeat (cbn;step_elab()).
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    eapply elab_term_conv.
    (* TODO: move to tactics or utils*)
    Require Import Ltac2.Constr.
    Ltac2 refine_elab pat :=
      match! goal with
      [|- elab_term _ _ _ ?g _] =>
      match Unsafe.kind g with
      | Unsafe.Evar n _ => Control.new_goal n > [| refine pat]
      | _ => ()
      end
      end.
    refine_elab '(Exp.con "lambda" [:: _; _; Exp.con "ty_subst" [:: Exp.var "A" ;Exp.var "g"; _; _]; _]).
    apply elab_term_by'; repeat (cbn;step_elab()). cbn.
    apply elab_term_by'; repeat (cbn;step_elab()). cbn.
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()). cbn.
    
    apply elab_term_by'; repeat (cbn;step_elab()). cbn. Control.shelve().
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    cbn.
    
    eapply (@elab_term_by').
    ltac1:(instantiate (1:= "ty_subst"%string)).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    cbn. apply (@elab_term_var' "A"%string);
           repeat (cbn;step_elab()).
    cbn. apply (@elab_term_var' "g"%string);
           repeat (cbn;step_elab()).
    cbn. step_elab().
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    cbn. repeat (cbn; step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).


    Unshelve.
    Focus 12.
    cbn.
    eapply elab_term_conv.
    cbn.
    apply elab_term_by'; repeat (cbn;step_elab()).
    cbn.
    eapply (@elab_term_by').
    ltac1:(instantiate (1:= "ty_subst"%string)).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    cbn. apply (@elab_term_var' "A"%string);
           repeat (cbn;step_elab()).
    cbn. apply (@elab_term_var' "g"%string);
           repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    
      cbn.   
      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab());
        reflexivity.      
      cbn.
      apply (@Core.wf_term_var' "G'"%string);
           repeat (cbn;step_elab()).
      cbn.
      eapply (@Core.wf_term_by' "ty_subst"%string); repeat (cbn; step_elab()).
      repeat (cbn;step_elab()).
      cbn.
      apply (@Core.wf_term_var' "G"%string);
        repeat (cbn;step_elab()).
      cbn.
      apply (@Core.wf_term_var' "g"%string);
        repeat (cbn;step_elab()).
      cbn.
      apply (@Core.wf_term_var' "A"%string);
        repeat (cbn;step_elab()).
      cbn.
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    cbn.

     eapply (@Core.wf_term_by' "ty_subst"%string); repeat (cbn; step_elab()).
      repeat (cbn;step_elab()).
      cbn.
      apply (@Core.wf_term_var' "G"%string);
        repeat (cbn;step_elab()).
      cbn.
      apply (@Core.wf_term_var' "g"%string);
        repeat (cbn;step_elab()).
      cbn.
      apply (@Core.wf_term_var' "A"%string);
        repeat (cbn;step_elab()).
      cbn.
      

      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      TODO: things don't seem to quite line up
      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab());
        reflexivity.      
      cbn.
      
    apply Core.wf_term_by'; repeat (cbn;step_elab()).

    cbn.
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
      repeat (cbn;step_elab()).
).
  }
  
Qed. 
  
Instance elab_cat_lang_inst : Elaborated cat_lang :=
  {
  elaboration := elab_cat_lang;
  elab_pf := elab_cat_lang_pf;
  }.


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

(*
From excomp Require Import Compilers.*)

(* TODO: handle sort vs exp *)
Definition compiler' := string -> list exp -> exp.
(*Definition to_cmp l c' : compiler :=
  map c' (map fst l).*)

(*
Definition twkn g a b := {{#"ty_subst"(#"ext"(g,a),g,#"wkn"(g,a),b)}}.
Definition ewkn g a b e := {{#"el_subst"(#"ext"(g,a),g,#"wkn"(g,a),b,e)}}.*)
Fixpoint wkn_n n e :=
  match n with
  | 0 => e
  | n'.+1 =>
    let e' := wkn_n n' e in
    {{e #"el_subst" #"wkn" !e'}}
  end.

Definition let_bind e k :=
  {{e #"app" !e (#"snoc" #"id" (#"lambda" !k))}}.

Definition ret_val v :=
  {{e #"lambda" (#"app" #"hd" (#"el_subst" #"wkn" !v))}}.

(* TODO: I'm embedding full terms into inferred terms; need to make work.
   Add escape hatch constr?*)

Definition double_neg t :=
    {{e #"->" (#"->" !t #"bot") #"bot"}}.  

Definition lam e := {{e #"lambda" !e}}.

Definition cps (c : string) args : exp :=
  match c, args with
  | "->", [:: B; A; G] =>
    double_neg {{e #"->" !A !B}}
  | "lambda", [:: e; B; A; G] =>
    ret_val {{e #"lambda" !e}}
  | "app", [:: e2; e1; b; a; g] =>
    let k := wkn_n 2 {{e #"hd"}} in
    let x1 := wkn_n 1 {{e #"hd"}} in
    let x2 := {{e #"hd"}} in
    lam
      (let_bind (wkn_n 1 e1)
      (let_bind (wkn_n 2 e2)
      {{e #"app" !k (#"app" !x1 !x2)}}))
  | _,_ => con c args
  end%string.







