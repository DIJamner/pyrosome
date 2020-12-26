
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp.
From Named Require Import IExp IRule ICore Subst Tactics.
Import IExp.Notations IRule.Notations Exp.Notations ARule.Notations.
Require Import String.

Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

Definition stlc :=
  [::[:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B"),
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("lambda_subst")
      #"el_subst" %"g" (#"lambda" %"e")
      = #"lambda" (#"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e")
      : #"el" %"G'" (#"ty_subst" %"g" (#"->" %"A" %"B"))
  ];
  [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "e" : #"el"%"G" (#"->" %"A" %"B"),
      "e'" : #"el" %"G" %"A",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("app_subst")
      #"el_subst" %"g" (#"app" %"e" %"e'")
      = #"app" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"el" %"G'" (#"ty_subst" %"g" %"B")
  ];
  [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("->_subst")
      #"ty_subst" %"g" (#"->" %"A" %"B")
      = #"->" (#"ty_subst" %"g" %"A") (#"ty_subst" %"g" %"B")
      : #"ty" %"G'"
  ];
  [:> "G" : #"env",
      "A" : #"ty"%"G",
      "B" : #"ty"%"G",
      "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B"),
      "e'" : #"el" %"G" %"A"
      ----------------------------------------------- ("STLC_beta")
      #"app" (#"lambda"%"e") %"e'"
      = #"el_subst" (#"snoc" #"id" %"e'") %"e"
      : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty" %"G",
       "B" : #"ty" %"G",
       "e" : #"el" %"G" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       #"app" "e" "e'" : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty" %"G",
       "B" : #"ty" %"G",
       "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B")
       -----------------------------------------------
       #"lambda" "e" : #"el" %"G" (#"->" %"A" %"B")
  ];
  [:| "G" : #"env", "t" : #"ty" %"G", "t'": #"ty" %"G"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty" %"G"
  ]]%irule++subst_lang.

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

(* Some starter code for an STLC-specific partial recognizer

TODO: do I want to try this approach?
Fixpoint unfold_stlc_subst_list (subst_list : list (Exp.exp * Exp.exp * Exp.exp))  (e : Exp.exp) : Exp.exp :=
  match subst_list with
  | [::] => e
  | (g,G',G)::sl => unfold_stlc_subst_list sl (Exp.con "ty_subst" [:: e; g; G'; G])
  end.

Lemma unfold_var_injective sl1 sl2 x1 x2
  : (unfold_stlc_subst_list sl1 (Exp.var x1) == unfold_stlc_subst_list sl2 (Exp.var x2))
    = (sl1 == sl2) && (x1 == x2).
Proof.
  revert sl2; induction sl1; intro sl2; destruct sl2; ltac1:(break); simpl; auto.
  admit.
  admit.
  Search foldl.
Admitted.

Fixpoint hnf_stlc_ty (subst_list : list (Exp.exp * Exp.exp * Exp.exp))  (e : Exp.exp) : Exp.exp :=
  match e with
  | (Exp.con "->" args) => Exp.con "->" (map (hnf_stlc_ty subst_list) args)
  | (Exp.con "ty_subst" [:: Exp.con "->" [:: B; A; G1']; g; G'; G]) =>
    let hnf := hnf_stlc_ty ((g,G',G)::subst_list) in
    Exp.con "->" [:: hnf B; hnf A; G]
  | _ => unfold_stlc_subst_list subst_list e
  end.

Definition stlc_type_eq t1 t2 :=
  (hnf_stlc_ty [::] t1) == (hnf_stlc_ty [::] t2).

(*
Lemma hnf_stlc_ty_con n s sb : exists n' s', hnf_stlc_ty sb (Exp.con n s) = Exp.con n' s'.
Admitted.
*)

Lemma stlc_type_eq_constr_inv n s x
  : ~~ (stlc_type_eq (Exp.con n s) (Exp.var x)).
Proof using .
  ltac1:(apply /negP).
  unfold stlc_type_eq.
  ltac1:(move /eqP).
  repeat (simpl; ltac1:(case_match;try by inversion)).
Qed.

Lemma stlc_type_eq_sym a b
  : (stlc_type_eq a b) = stlc_type_eq b a.
Proof using .
  apply eq_sym.
Qed.

Lemma stlc_type_eq_recognizes c e1 e2 G
 : Core.wf_term (strip_args elab_stlc) c e1 (Exp.srt "ty" [:: G]) ->
   Core.wf_term (strip_args elab_stlc) c e2 (Exp.srt "ty" [:: G]) ->
   stlc_type_eq e1 e2 ->
   Core.le_term (strip_args elab_stlc) c (Exp.srt "ty" [:: G]) e1 e2.
Proof.
  unfold stlc_type_eq.
  generalize (@nil (Exp.exp *Exp.exp*Exp.exp)).
  revert e2.
  induction e1; intro e2; destruct e2.
  {
    intros l _ _.
    intro stlceq.
    cbn in stlceq.
    simpl in stlceq.
    rewrite !unfold_var_injective in stlceq.
    ltac1:(break).
    ltac1:(move: stlceq=> /eqP => ->).
    reflexivity.
  }    
  {
    intros sl _ _.
    ltac1:(move /negPn).
    admit.
  }    
  { admit. }  
  {
    intros wf1 wf2.
    unfold stlc_type_eq.
    match! goal with
      [|- is_true(?a == ?b) -> _]=>
      remember $a as l_hnf;
        remember $b as r_hnf
    end.
    ltac1:(case neq: (n=="ty_subst"%string)).
    {
      ltac1:(move: neq => /eqP neq).
      rewrite neq in Heql_hnf.
      simpl in Heql_hnf.
      rewrite neq in wf1.
      
      
    issue: ty_substs
    repeat (simpl; ltac1:(case_match)).
  unfold stlc_type_eq in ty_eq.
  rewrite !hnf_stlc_ty_con in ty_eq.
  simpl in ty_eq.
  {
    destruct n0; try (inversion ty_eq).
  intro wft; induction wft.
  {
    

Fixpoint elab_lam_term (e : exp) (t : Exp.sort) : option Exp.exp :=
  match e, t with
  | con "lambda" [:: e], scon "el" [:: ty; G] =>
    match simpl_stlc_ty
  | _,_ => None
  end.
*)
