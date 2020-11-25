
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
      let g := match! goal with
                 | [|- elab_term _ _ _ ?g _] => g
                 | [|- elab_sort _ _ _ ?g ] => g
                 | [|- Core.wf_term _ _ ?g _] => g
                 | [|- Core.wf_sort _ _ ?g] => g
               end in
      match Unsafe.kind g with
      | Unsafe.Evar n _ => Control.new_goal n > [| refine pat]
      | _ => ()
      end.
    refine_elab '(Exp.con "lambda" [:: _; _; Exp.con "ty_subst" [:: Exp.var "A" ;Exp.var "g"; _; _]; _]).
    apply elab_term_by'; repeat (cbn;step_elab()). cbn.
    eapply elab_term_conv.
    {
      apply elab_term_by'; repeat (cbn;step_elab()). cbn.
      {
        apply elab_term_by'; repeat (cbn;step_elab()). cbn.
        apply elab_term_by'; repeat (cbn;step_elab()). cbn.
        apply elab_term_by'; repeat (cbn;step_elab()).
      }
      { cbn.
        apply elab_term_by'; repeat (cbn;step_elab()). cbn.
        eapply elab_term_conv.
        apply elab_term_by'; repeat (cbn;step_elab()). cbn.
        refine_elab '(Exp.con "ty_subst" [:: Exp.var "A" ;Exp.var "g"; _; _]).
        apply elab_term_by'; repeat (cbn;step_elab()). cbn.
        step_elab().
        cbn.
        apply Core.wf_sort_by'; repeat (cbn;step_elab()).
        refine_elab '( (Exp.con "ext"
       [:: Exp.con "ty_subst" [:: Exp.var "A"; Exp.var "g"; Exp.var "G"; Exp.var "G'"]; Exp.var "G'"])).
        cbn.
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        cbn.
        Focus 3.
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        cbn.
        {
          eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
          cbn.
          symmetry.
          eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
        }
        
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()). cbn.
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
      }
      {
        apply elab_term_by'; repeat (cbn;step_elab()).
      }
      {
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
      }
    }
    apply Core.wf_sort_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    cbn. apply (@Core.wf_term_var' "G'"%string);
           repeat (cbn;step_elab()).
    cbn.
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    cbn. repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    cbn.
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    cbn.
    refine_elab '(Exp.con "ty_subst"%string [:: Exp.var "B"%string ;Exp.var "g"%string;_;_]). (* TODO: check*)
    
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    progress (repeat (cbn;step_elab())).
    progress (repeat (cbn;step_elab())).
    cbn.
    {
      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      eapply Core.le_term_trans.
      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
      symmetry.
      eapply Core.le_term_trans.
      symmetry.      
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
      eapply Core.le_term_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      symmetry.
      eapply Core.le_term_trans.
      eapply (@Core.le_term_by' "wkn_snoc"%string); repeat (cbn; step_elab()); reflexivity.
      reflexivity.
    }
    
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    progress (repeat (cbn;step_elab())).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    progress (repeat (cbn;step_elab())).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    cbn.
    {
      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try (fun () => reflexivity).
      cbn.
      symmetry.
      eapply (@Core.le_term_by' "->_subst"%string); repeat (cbn; step_elab()); reflexivity.
    }      
  }
Qed.
  
Instance elab_stlc_inst : Elaborated stlc :=
  {
  elaboration := elab_stlc;
  elab_pf := elab_stlc_pf;
  }.

Definition stlc_bot :=
  [:| "G" : #"env"
      -----------------------------------------------
      "bot" : #"ty" %"G"
  ]::stlc.
  
Derive elab_stlc_bot
       SuchThat (elab_lang stlc_bot elab_stlc_bot)
       As elab_stlc_bot_pf.
Proof.
  repeat (repeat (cbn;step_elab())).
Qed.  

Instance elab_stlc_bot_inst : Elaborated stlc_bot :=
  {
  elaboration := elab_stlc_bot;
  elab_pf := elab_stlc_bot_pf;
  }.


From Named Require Import Compilers.

  
Fixpoint make_pre_compiler
           (cmp_sort : string -> list string -> sort)
           (cmp_exp : string -> list string -> exp)
           (l : lang) : compiler :=
  match l with
  | (n,sort_rule c _)::l' =>
    (sort_case (map fst c) (cmp_sort n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,term_rule c _ _)::l' => term_case (map fst c) (cmp_exp n (map fst c))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,_)::l' => 
    (make_compiler cmp_sort cmp_exp l')
  | [::] => [::]
  end.
  map (fun p => (p.1, make_cmp_rule cmp_sort cmp_exp p.1 p.2)) l.
  
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

Definition cps_sort (c:string) args : sort := srt c (map Exp.var args).
Definition cps (c : string) args : exp :=
  match c, args with
  | "->", [:: B; A; G] =>
    double_neg {{e #"->" !A !B}}
  | "lambda", [:: e; B; A; G] =>
    ret_val {{e #"lambda" %e}}
  | "app", [:: e2; e1; b; a; g] =>
    let k := wkn_n 2 {{e #"hd"}} in
    let x1 := wkn_n 1 {{e #"hd"}} in
    let x2 := {{e #"hd"}} in
    lam
      (let_bind (wkn_n 1 e1)
      (let_bind (wkn_n 2 e2)
      {{e #"app" %k (#"app" %x1 %x2)}}))
  | _,_ => con c args
  end%string.







