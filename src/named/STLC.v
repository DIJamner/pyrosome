
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp.
From Named Require ICore.
From Named Require Import Subst Tactics Decidable.
Import ICore.IndependentJudgment Exp.Notations ARule.Notations.
Require Import String.

Set Default Proof Mode "Ltac2".

Definition stlc :=
  [::[:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
      "e" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B"),
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("lambda_subst")
      #"el_subst" %"g" (#"lambda" %"A" %"e")
      = #"lambda" (#"ty_subst" %"g" %"A")
         (#"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e")
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
      #"app" (#"lambda" %"A" %"e") %"e'"
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
       #"lambda" "A" "e" : #"el" %"G" (#"->" %"A" %"B")
  ];
  [:| "G" : #"env", "t" : #"ty" %"G", "t'": #"ty" %"G"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty" %"G"
  ]]%arule++subst_lang.

Import OptionMonad.

Section InferSub.

  Context (subst_lang_el_ty : ctx -> exp (*G*) -> exp (*e*) -> option exp).

  
  Fixpoint sub_decompose' g f : option exp :=
    if f == g then do ret {{e #"id"}}
    else match f with
         | con "cmp" [:: h; f'] =>
           do ret {{e #"cmp" {sub_decompose g f'} {h} }}
         | _ => None
         end.
  
  Fixpoint sub_decompose g f : option exp :=
    match g with
    | con "cmp" [:: h; g'] =>
      do g'_minus_f <- sub_decompose g' f;
      res <- sub_decompose h (g'_minus_f);
           ret res
    | _ => sub_decompose' g f
    end.

  Definition ty_decompose g A :=
    if g == {{e #"id"}} then do ret A
    else match A with
         | con "ty_subst" [:: A; g'] =>
           do g'_minus_g <- sub_decompose g g';
           ret {{e #"ty_subst" {g'_minus_g} {A} }}
         | _ => None
         end.

  Fixpoint cat_lang_sub_r c e G_l : option exp :=
    match e with
    | con "id" [::] => G_l
    | con "cmp" [:: g; f] =>
      let G_lf := cat_lang_sub_r c f G_l in
      let G_lg := cat_lang_sub_r c g G_lf in
      G_lg
    | con "wkn" [::] =>
      match G_l with
      | con "ext" [:: _;G_r] => G_r
      | _ => {{e #"ERR"}}
      end
    | con "snoc" [:: e; f] =>
      let G' := cat_lang_sub_r c f G_l in
      let Af := subst_lang_el_ty c G' e in
      {{e #"ext" {G'} {ty_decompose f Af} }}
    | var x =>
      match named_list_lookup {{s #"ERR"}} c x with
      | scon "sub" [:: G; _] => G
      | _ => {{e #"ERR"}}
      end
    | _ => {{e #"ERR"}}
    end.

End InferSub.
  
Fixpoint subst_lang_el_ty c G e : exp :=
  match e,G with
  | var x,_ => 
    match named_list_lookup {{s #"ERR not in c"}} c x with
    | scon "el" [:: t; _] => t
    | _ => {{e #"ERR sort from c not in subst lang"}}
    end
  | con "hd" [::], con "ext" [:: A; G'] =>
    {{e #"ty_subst" #"wkn" %"A" }}
  | con "el_subst" [:: e'; g], _ =>
    let G' := cat_lang_sub_r subst_lang_el_ty c g G in
    let A := subst_lang_el_ty c G' e' in
    {{e #"ty_subst" {g} {A} }}
  | con "lambda" [:: e'; A], _ =>
    let Bwkn := subst_lang_el_ty c {{e #"ext" {G} {A} }} e' in
    {{e #"->" {A} {ty_decompose {{e#"wkn"}} Bwkn} }}
  | con "app" [:: e'; e], _ =>
    match subst_lang_el_ty c G e with
    | con "->" [:: B; _] => B
    | _ => {{e #"ERR: bad app"}}
    end
  | _, _ => {{e #"ERR: not in subst lang" }}
  end.


Instance rec_stlc : LangRecognize stlc :=
  {  le_sort_dec := generic_sort_dec_fuel 10 stlc;
    decide_le_sort := @generic_decide_le_sort 10 stlc;
    term_args_elab c s name t := 
      match name, t, s with
      | "app", scon "el" [:: T; G], [:: e'; e] =>
        match subst_lang_el_ty c G e with
        | con "->" [:: B; A] => [:: e'; e; B; A; G]
        | _ => [:: e';e; {{e #"ERR: bad app elab"}}]
        end          
      | "lambda", scon "el" [:: T; G], [:: e; A] =>
        let T' := term_par_step_n stlc T 100 in
        match T' with
        | con "->" [:: B; _] =>
          [:: e; B; A; G]
        | _ => [:: {{e #"ERR"}}]
        end
      | "->", scon "ty" [:: G], [:: t'; t] => [:: t'; t; G]
      | "forget", scon "sub" [:: _; G],_ => [:: G]
      | "id", scon "sub" [:: _; G],_ => [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r subst_lang_el_ty c f G1 in
        [:: g; f; G3; G2; G1]
      | "ty_subst", scon "ty" [:: G], [:: A; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        [:: A; g; G'; G]
      | "el_subst", scon "el" [:: _; G], [:: e; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        let A := subst_lang_el_ty c G' e in
        [:: e; A; g; G'; G]
      | "snoc", scon "sub" [:: con "ext" [:: A; G']; G], [:: e; g] =>
        [:: e; g; A; G'; G]
      | "wkn", scon "sub" [:: G; con "ext" [:: A; _]], [::] =>
        [:: A; G]
      | "hd", scon "el" [:: _; con "ext" [:: A; G]], [::] =>
        [:: A; G]
      | _,_,_ => s
      end%string;
    sort_args_elab c s _ := s
  }.

Ltac2 rec break_forall_goal ():=
  first [ apply List.Forall_nil
        | apply List.Forall_cons > [| break_forall_goal()]].

  
Lemma stlc_wf : wf_lang stlc.
Proof.
  apply (decide_wf_lang (fuel:=100)).
  match! goal with
    [|-dm_remaining_goals _ ?comp] =>
    let e := Std.eval_vm None comp in
    Message.print (Message.of_constr e)
  end.
  ().
  break_forall_goal ().
  constructor.
  apply (@decide_wf_lang _ _ 100).
  next_goal().
  simpl;
    rewrite unfold_wf_term_dec.
  break_dec_goal().
  next_goal().
  
  


  {
    simpl.
    rewrite unfold_wf_term_dec.
    next_goal().
    rewrite unfold_wf_args_dec.
    next_goal().
    simpl; rewrite unfold_wf_term_dec.
    next_goal().
    {
      simpl; rewrite unfold_wf_sort_dec.
      next_goal().
      simpl.
      rewrite unfold_wf_args_dec.
      next_goal().
      rewrite unfold_wf_term_dec.
      next_goal().
      rewrite unfold_wf_args_dec.
      next_goal().
      {
        cbn[with_names_from].
        cbn[cat_lang_sub_r subst_lang_el_ty].
        cbn [nth_tail named_list_lookup_err
                      named_list_lookup
              cat fst snd
              String.eqb Ascii.eqb Bool.eqb].
        simpl; rewrite unfold_wf_term_dec.
        todo
        next_goal().
      {
        simpl; rewrite unfold_wf_sort_dec.
        next_goal().
        simpl; rewrite unfold_wf_args_dec.
        next_goal().
        rewrite unfold_wf_term_dec.
        next_goal().
        rewrite unfold_wf_args_dec.
        next_goal().
        
        simpl; rewrite unfold_wf_term_dec.
      next_goal().
      
      rewrite unfold_wf_args_dec; rewrite ?eq_refl.
      repeat ltac1:(timeout 2 ltac2:(break_dec_goal())).
      repeat (first [ rewrite unfold_wf_sort_dec;
                     repeat ltac1:(timeout 2 ltac2:(break_dec_goal()))
                   | rewrite unfold_wf_term_dec;
                     repeat ltac1:(timeout 2 ltac2:(break_dec_goal()))
                   | rewrite unfold_wf_args_dec;
                     repeat ltac1:(timeout 2 ltac2:(break_dec_goal()))
             ]).
      match!goal with [|-is_true(_==?e)]=> remember $e as x end.
      means there is a weaken I don't want
      vm_compute in Heqx.
      cbn.
      
      break_dec_goal().
  break_dec_goal().
  break_dec_goal().
      
  
    cbn[with_names_from term_args_elab nth_tail named_list_lookup_err
              cat fst snd rec_stlc
              String.eqb Ascii.eqb Bool.eqb apply_subst sort_subst exp_subst].
    cbv[term_args_elab].
    simpl.
    break_dec_goal().
  vm_compute; reflexivity.
Qed.

  
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
    solve [repeat (apply elab_term_by'; repeat (simpl;step_elab()))].
    repeat (simpl; step_elab()).
    {
       eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try reflexivity.
       eapply (@Core.le_term_by' "->_subst"%string); repeat (simpl; step_elab()); reflexivity.
    }
    
    solve [repeat (apply elab_term_by'; repeat (simpl;step_elab()))].
    solve [repeat (apply elab_term_by'; repeat (simpl;step_elab()))].
  }
  {
    solve [repeat (apply elab_term_by'; repeat (simpl;step_elab()))].
  }
  {    
    solve [repeat (apply elab_term_by'; repeat (simpl;step_elab()))].
  }
  {
    eapply elab_term_conv.
    refine_elab '(Exp.con "lambda" [:: _; _; Exp.con "ty_subst" [:: Exp.var "A" ;Exp.var "g"; _; _]; _]).
    elab_term_by().
    eapply elab_term_conv.
    {
      elab_term_by().
      {
        solve [repeat (apply elab_term_by'; repeat (simpl;step_elab()))].
      }
      {
        elab_term_by().
        eapply elab_term_conv.
        elab_term_by().
        refine_elab '(Exp.con "ty_subst" [:: Exp.var "A" ;Exp.var "g"; _; _]).
        elab_term_by().
        step_elab().
        apply Core.wf_sort_by'; repeat (simpl;step_elab()).
         {
          eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try reflexivity.
          simpl.
          symmetry.
          eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (simpl; step_elab()); reflexivity.
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
        apply Core.wf_term_by'; repeat (simpl;step_elab()).
        constructor; repeat (simpl; step_elab()).
        constructor; repeat (simpl; step_elab()).
        apply Core.wf_term_by'; repeat (simpl;step_elab()).
        constructor; repeat (simpl; step_elab()).
        eapply Core.wf_term_conv.
        Focus 2.
        apply Core.wf_term_by'; repeat (simpl;step_elab()).
        repeat (simpl;step_elab()).
        {
          eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try  reflexivity.
          symmetry.
          eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (simpl; step_elab()); reflexivity.
        }
    }
     {
      eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try reflexivity.
      eapply Core.le_term_trans.
      symmetry.
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (simpl; step_elab()); reflexivity.
      symmetry.
      eapply Core.le_term_trans.
      symmetry.      
      eapply (@Core.le_term_by' "ty_subst_cmp"%string); repeat (simpl; step_elab()); reflexivity.
      eapply Core.le_term_refl'; repeat (simpl; step_elab()); try reflexivity.
      symmetry.
      eapply Core.le_term_trans.
      eapply (@Core.le_term_by' "wkn_snoc"%string); repeat (simpl; step_elab()); reflexivity.
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
       eapply Core.le_sort_refl'; repeat (simpl; step_elab()); try reflexivity.
       symmetry.
       eapply (@Core.le_term_by' "->_subst"%string); repeat (simpl; step_elab()); reflexivity.
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
