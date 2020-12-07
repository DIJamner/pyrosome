
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
  repeat (simpl; step_elab());
    try (solve[repeat (simpl; step_elab())
              | repeat(elab_term_by())]).
  { repeat (elab_term_by()). }
  { repeat (elab_term_by()). }
  { repeat (elab_term_by()). }
  {
    eapply elab_term_conv.

    {
      elab_term_by().
      {
        elab_term_by().
        elab_term_by().
        elab_term_by().
      }
      {
        elab_term_by(); repeat(simpl; step_elab()).
        {
          eapply elab_term_conv; repeat(simpl; step_elab()).
          eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try reflexivity.
          symmetry.
          eapply (@Core.le_term_by' "ty_subst_id"%string); repeat (simpl; step_elab()); reflexivity.
        }
        elab_term_by().    
        step_elab().
      }
      { repeat (elab_term_by()). }
      { step_elab(). }
    }
    { repeat (simpl;step_elab()).
      
      constructor.
      repeat (simpl;step_elab()).
      apply Core.wf_term_by';
        repeat (simpl; step_elab()).
      constructor; repeat (simpl; step_elab()).
      constructor; repeat (simpl; step_elab()).
      simpl.
      apply Core.wf_term_by';
        repeat (simpl; step_elab()).
      constructor.
      repeat (simpl; step_elab()).
      simpl.
      eapply Core.wf_term_conv>[| repeat (simpl; step_elab())|].
      repeat (simpl; step_elab()).
      simpl.
      {
        eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try reflexivity.
        symmetry.
        eapply (@Core.le_term_by' "ty_subst_id"%string); repeat (cbn; step_elab()); reflexivity.
      }
    }
    { 
      eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try reflexivity.
      eapply Core.le_term_trans.
      Focus 2.
      eapply (@Core.le_term_by' "ty_subst_id"%string); repeat (simpl; step_elab()); reflexivity.
      eapply Core.le_term_trans.

      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (simpl; step_elab());
      try reflexivity.
      eapply Core.le_term_refl'; repeat (simpl; step_elab()); try reflexivity.
      eapply (@Core.le_term_by' "wkn_snoc"%string); repeat (simpl; step_elab());
      reflexivity.
    }
  }
  {
    apply elab_term_by'; repeat (simpl;step_elab()).
    apply elab_term_by'; repeat (simpl;step_elab()).
    eapply elab_term_conv.
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    repeat (simpl; step_elab()).
    {
       eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try reflexivity.
       eapply (@Core.le_term_by' "->_subst"%string); repeat (cbn; step_elab()); reflexivity.
    }
    
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {    
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
    elab_term_by().
    eapply elab_term_conv.
    {
      elab_term_by().
      {
        solve [repeat (apply elab_term_by'; repeat (cbn;step_elab()))].
      }
      {
        elab_term_by().
        eapply elab_term_conv.
        elab_term_by().
        refine_elab '(Exp.con "ty_subst" [:: Exp.var "A" ;Exp.var "g"; _; _]).
        elab_term_by().
        step_elab().
        apply Core.wf_sort_by'; repeat (cbn;step_elab()).
         {
          eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try reflexivity.
          cbn.
          symmetry.
          eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
         }
         simpl.
         solve[repeat(elab_term_by())].
         solve[repeat(elab_term_by())].
      }
      { 
        solve[repeat(elab_term_by())].
      }
      { 
        solve[repeat(elab_term_by())].
      }
    }
    { repeat (simpl; step_elab()).
      constructor; repeat (simpl; step_elab()).
      simpl.
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        constructor; repeat (simpl; step_elab()).
        constructor; repeat (simpl; step_elab()).
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        constructor; repeat (simpl; step_elab()).
        eapply Core.wf_term_conv.
        Focus 2.
        apply Core.wf_term_by'; repeat (cbn;step_elab()).
        repeat (cbn;step_elab()).
        {
          eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try  reflexivity.
          symmetry.
          eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
        }
    }
     {
      eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try reflexivity.
      eapply Core.le_term_trans.
      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
      symmetry.
      eapply Core.le_term_trans.
      symmetry.      
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn; step_elab()); reflexivity.
      eapply Core.le_term_refl'; repeat (cbn; step_elab()); try reflexivity.
      symmetry.
      eapply Core.le_term_trans.
      eapply (@Core.le_term_by' "wkn_snoc"%string); repeat (cbn; step_elab()); reflexivity.
      reflexivity.
     }
     { 
       solve[repeat(elab_term_by())].
     }
     { 
       solve[repeat(elab_term_by())].
     }
     {
       solve[repeat(simpl; step_elab())].
     }
     {
       solve[repeat(simpl; step_elab())].
     }
     {
       eapply Core.le_sort_refl'; repeat (cbn; step_elab()); try reflexivity.
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
