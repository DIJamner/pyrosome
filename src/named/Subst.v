Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp ARule.
From Named Require Import IExp IRule ICore.
Require Import String.

Require Import Named.Tactics.
Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".




(*Notation ob := (con 0 [::]).
Notation hom a b := (con 1 [:: b; a]%exp_scope).
Notation id a := (con 2 [:: a]%exp_scope).
Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).*)       

(* syntax of categories *)
Definition cat_lang : lang :=
  [::
     [:> "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" %"G1" %"G2",
         "g" : #"sub" %"G2" %"G3",
         "h" : #"sub"%"G3" %"G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" %"f" (#"cmp" %"g" %"h") = #"cmp" (#"cmp" %"f" %"g") %"h" : #"sub" %"G1" %"G4"
  ];  
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" %"f" = %"f" : #"sub" %"G"%"G'"
  ];
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
      ----------------------------------------------- ("id_right")
      #"cmp" %"f" #"id" = %"f" : #"sub" %"G" %"G'"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3"
       -----------------------------------------------
       "cmp" "f" "g" : #"sub" %"G1" %"G3"
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       "id" : #"sub" %"G" %"G"
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      "sub" "G" "G'" srt                     
  ];
  [s| (:)
      -----------------------------------------------
      "env" srt
  ]
  ].


(* TODO: move to ICore*)
Class Elaborated (l : IRule.lang) :=
  {
  elaboration : ARule.lang;
  elab_pf : elab_lang l elaboration;
  }.

(* TODO: move to tactics*)
(*
Ltac2 inline () :=
    cbn [fst snd named_list_lookup
           String.eqb Ascii.eqb Bool.eqb
           get_rule_args get_rule_ctx get_rule_sort zip
           strip_args strip_rule_args map
           Exp.apply_subst
           Exp.substable_sort Exp.sort_subst
           Exp.substable_exp Exp.exp_subst map
           Exp.exp_var_map Exp.subst_lookup
           elaboration proj1_sig];
repeat (rewrite Core.with_names_from_cons).
*)
Ltac2 Type exn ::= [SubstFormExn].

(* TODO: move*)
Definition id_subst : list string -> Exp.subst :=
  map (fun x => (x, Exp.var x)).

Lemma id_subst_exp_identity e args : Exp.exp_subst (id_subst args) e = e.
Admitted.
Lemma id_subst_sort_identity t args : Exp.sort_subst (id_subst args) t = t.
Admitted.

Lemma id_subst_fold x args : (x,Exp.var x)::(id_subst args) = id_subst (x::args).
Proof using.
  simpl; reflexivity.
Qed.

Lemma sort_subst_fold s n l
  : Exp.srt n (map (Exp.exp_subst s) l)
    = Exp.apply_subst s (Exp.srt n l).
Proof using .
  simpl; reflexivity.
Qed.

Ltac2 solve_in () :=
  solve [ cbv; reflexivity
        | repeat (rewrite in_cons);
          rewrite in_nil;
          rewrite Bool.orb_false_r;
          ltac1:(apply /eqP);
          reflexivity].

Ltac2 solve_fresh () := cbv; reflexivity.

Ltac2 step_elab () :=
  lazy_match! goal with
  | [|- elab_lang nil _] => constructor
  | [|- elab_lang _ _] => Control.plus (fun () => apply elab_pf) (fun _ => constructor)
  | [|- elab_rule _ _ _] => constructor
  | [|- elab_ctx _ _ _] => constructor
  | [|- elab_args _ _ _ _ _ [::]] => apply elab_args_nil
  | [|- elab_args _ _ _ (?n::_) _ ((?n,?t)::_)] =>
      apply elab_args_cons_ex
  | [|- elab_args _ _ _ _ _ ((?n,?t)::_)] =>
      eapply elab_args_cons_im
  (* special case to force existentials to the empty list*)
  | [|- elab_subst _ _ _ (Core.with_names_from [::] ?l) [::]] =>
        assert ($l = [::]) > [reflexivity | apply elab_subst_nil]
  | [|- elab_subst _ _ _ _ [::]] => apply elab_subst_nil
  | [|- elab_subst _ _ ((?n,?e)::_) ((?n,?ee)::_) ((?n,?t)::_)] =>
      apply elab_subst_cons_ex > [solve_fresh ()| | |]
  | [|- elab_subst _ _ _ ((?n,?ee)::_) ((?n,?t)::_)] =>
      eapply elab_subst_cons_im > [solve_fresh ()| | |]
  | [|- Core.le_args _ _ _ _ _] =>constructor
  | [|- Core.wf_args _ _ _ _] =>constructor
  | [|- Core.wf_subst _ _ _ _] =>constructor
  | [|- elab_sort _ _ _ _] => apply elab_sort_by'
  | [|- Core.wf_sort _ _ _] => apply Core.wf_sort_by'
  | [|- Core.wf_term _ _ (Exp.var _) _] => apply Core.wf_term_var
  | [|- elab_term _ _ (var _) _ _] => apply elab_term_var; solve_in()
  | [|- elab_term _ _ _ (Exp.var _) _] => apply elab_term_var; solve_in()
  | [|- is_true((?n,?e)\in ?l)]=> 
      assert ($e = named_list_lookup $e $l $n); cbv; solve[auto]
  | [|- is_true (_ \in _)] => solve_in ()
  | [|- is_true (Core.fresh _ _)] => solve_fresh ()
  | [|- is_true (subseq _ _)] => cbv; reflexivity
  | [|- is_true true] => reflexivity
  | [|- len_eq _ _] => constructor  
  | [|- _ = _] => try (fun ()=>solve[reflexivity| cbv; f_equal])          
end.

(* TODO: move to tactics or utils*)
Require Import Ltac2.Constr.
Ltac2 is_evar e :=
  match Unsafe.kind e with
  | Unsafe.Evar _ _ => true
  | _ => false
  end.

Ltac2 shelve_if b :=
  match b with
  | true => Control.shelve ()
  | false => ()
  end.

Ltac2 error_if b e :=
  match b with
  | true => Control.zero e
  | false => ()
  end.

(*
Ltac2 Type exn ::= [ElabExn(constr)].
Ltac2 rec elaborate () :=
  Control.enter (fun () =>
                   inline (); simpl;
                Control.plus (fun () =>
                                lazy_match! goal with
                             | [|- elab_lang nil _] => solve [constructor]
                             | [|- elab_lang _ _] =>
                               Control.plus (fun () => solve[apply elab_pf])
                                            (fun _ => constructor; elaborate())
                             | [|- elab_rule _ _ _] => constructor; elaborate()
                             | [|- elab_ctx _ _ _] => constructor; elaborate()
                             (* special case to force existentials to the empty list*)
                             | [|- elab_subst _ _ _ (Core.with_names_from [::] ?l) [::]] =>
                               assert ($l = [::]) > [reflexivity | solve [apply elab_subst_nil]]
                             | [|- elab_subst _ _ _ _ [::]] => solve [apply elab_subst_nil]
                             | [|- elab_subst _ _ ((?n,?e)::_) ((?n,?ee)::_) ((?n,?t)::_)] =>
                               apply elab_subst_cons_ex > [solve_fresh ()| | |]; elaborate ()
                             | [|- elab_subst _ _ _ ((?n,?ee)::_) ((?n,?t)::_)] =>
                               eapply elab_subst_cons_im > [solve_fresh ()| | |]; elaborate ()
                             | [|- Core.wf_subst _ _ _ _] => 
                               constructor; elaborate()
                             | [|- elab_sort _ _ _ _] => apply elab_sort_by'; elaborate ()
                             | [|- Core.wf_sort _ _ _] => apply Core.wf_sort_by'; elaborate ()
                             | [|- Core.wf_term _ _ (Exp.var _) _] => apply Core.wf_term_var; solve_in()
                             | [|- Core.wf_term _ _ ?e _] => 
                               (* if term is existential, shelve and come back later*)
                               shelve_if (is_evar e)
                             | [|- elab_term _ _ (var _) _ _] => try (fun () =>apply elab_term_var; solve_in())
                             | [|- elab_term _ _ _ (Exp.var _) _] => try(fun()=>apply elab_term_var; solve_in())
                             | [|- elab_term _ _ ?e ?ee _] =>
                               (* if both sides are existential, shelve and come back later*)
                               shelve_if (Bool.and (is_evar e) (is_evar ee))
                             | [|- is_true (_ \in _)] => solve_in ()
                             | [|- is_true (Core.fresh _ _)] => solve_fresh ()
                             | [|- is_true (subseq _ _)] => cbv; reflexivity
                             | [|- is_true true] => reflexivity
                end)
  (fun _ => lazy_match! goal with [|- ?g ] => Control.throw (ElabExn g)end)).
*)

(*_TODO: move *)
Transparent get_rule_args.
Transparent get_rule_ctx.


Ltac2 elab_term_by ():=
    apply elab_term_by'>
    [ simpl; solve_in()
    | simpl; reflexivity
    | repeat(simpl;step_elab())].

Derive elab_cat_lang
       SuchThat (elab_lang cat_lang elab_cat_lang)
       As elab_cat_lang_pf.
Proof.
  repeat (simpl;step_elab()).
  {
    apply elab_term_by'; repeat (simpl;step_elab()).
    apply elab_term_by'; repeat (simpl;step_elab()).
  }
  {
    apply elab_term_by'; repeat (simpl;step_elab()).
    apply elab_term_by'; repeat (simpl;step_elab()).
  }    
  {
    apply elab_term_by'; repeat (simpl;step_elab()).
    apply elab_term_by'; repeat (simpl;step_elab()).
  }   
  {
    apply elab_term_by'; repeat (simpl;step_elab()).
    apply elab_term_by'; repeat (simpl;step_elab()).
  }   
Qed. 
  
Instance elab_cat_lang_inst : Elaborated cat_lang :=
  {
  elaboration := elab_cat_lang;
  elab_pf := elab_cat_lang_pf;
  }.


Definition subst_lang' : lang :=
 [:> (:)
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ]::
  [:> "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" %"g" #"forget" = #"forget" : #"sub" %"G" #"emp"
  ]::
  [:| "G" : #"env" 
      -----------------------------------------------
      "forget" : #"sub" %"G" #"emp"
  ]::
  [:| (:)
      -----------------------------------------------
      "emp" : #"env"
  ]::
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3", "e" : #"el" %"G3" %"A"
       ----------------------------------------------- ("el_subst_cmp")
       #"el_subst" (#"cmp" %"f" %"g") %"e"
       = #"el_subst" %"f" (#"el_subst" %"g" %"e")
       : #"el" %"G1" (#"ty_subst" (#"cmp" %"f" %"g") %"A")
  ]:: 
  [:> "G" : #"env", "A" : #"ty" %"G", "e" : #"el" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"el" %"G" %"A"
  ]::
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" (#"cmp" %"f" %"g") %"A"
       = #"ty_subst" %"f" (#"ty_subst" %"g" %"A")
       : #"ty" %"G1"
  ]::              
  [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" %"A" = %"A" : #"ty" %"G"
  ]::
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'", "e" : #"el" %"G'" %"A"
       -----------------------------------------------
       "el_subst" "g" "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
  ]::
  [s| "G" : #"env", "A" : #"ty"(%"G")
      -----------------------------------------------
      "el" "G" "A" srt
  ]::
  [:| "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'"
       -----------------------------------------------
       "ty_subst" "g" "A" : #"ty" %"G"
  ]::
  [s| "G" : #"env" 
      -----------------------------------------------
      "ty" "G" srt
  ]::cat_lang.

Derive elab_subst_lang'
       SuchThat (elab_lang subst_lang' elab_subst_lang')
       As elab_subst_lang'_pf.
Proof.
  (* TODO: figure out how to get rid of the second repeat*)
  repeat (repeat (cbn;step_elab())); try (fun()=> solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))]).
  {
    eapply elab_term_conv.
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).

    cbn.
    eapply Core.le_sort_refl'; repeat (cbn; step_elab()).
    reflexivity.
    cbn.
    eapply (Core.le_term_by' "ty_subst_id"%string); repeat (cbn;step_elab()).
    reflexivity.
    reflexivity.
  }
  {
    eapply elab_term_conv; 
    repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).


    cbn.
    {
      eapply Core.wf_term_by'; repeat(cbn; step_elab()).
      eapply Core.wf_term_by'; repeat(cbn; step_elab()).
    }
    
    cbn.
    eapply Core.le_sort_refl'; repeat (cbn; step_elab()).
    reflexivity.
    cbn.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat (cbn;step_elab()); reflexivity.
  }
Qed.

Instance elab_subst_lang'_inst : Elaborated subst_lang' :=
  {
  elaboration := elab_subst_lang';
  elab_pf := elab_subst_lang'_pf;
  }.

Definition subst_lang : lang :=
   [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"id" = #"snoc" #"wkn" #"hd" : #"sub" (#"ext" %"G" %"A") (#"ext" %"G" %"A")
   ]::
   [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3",
       "e" : #"el" %"G2" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" %"f" (#"snoc" %"g" %"e")
       = #"snoc" (#"cmp" %"f" %"g") (#"el_subst" %"f" %"e")
       : #"sub" %"G1" (#"ext" %"G3" %"A")
   ]::
   [:> "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'",
       "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("snoc_hd")
       #"el_subst" (#"snoc" %"g" %"e") #"hd" = %"e"
       : #"el" %"G" (#"ty_subst" %"g" %"A")
  ]::
  [:> "G" : #"env", "G'" : #"env",
      "g" : #"sub" %"G" %"G'",
      "A" : #"ty" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" %"g" %"e") #"wkn" = %"g" : #"sub" %"G" %"G'"
  ]::
  [:| "G" : #"env", "A" : #"ty"(%"G")
       -----------------------------------------------
       "hd" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"A")
  ]::
  [:| "G" : #"env", "A" : #"ty" %"G"
       -----------------------------------------------
       "wkn" : #"sub" (#"ext" %"G" %"A") %"G"
  ]::
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty" %"G'",
      "g" : #"sub" %"G" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       -----------------------------------------------
       "snoc" "g" "e" : #"sub" %"G" (#"ext" %"G'" %"A")
  ]::
  [:| "G" : #"env", "A": #"ty" %"G"
       -----------------------------------------------
       "ext" "G" "A" : #"env"
  ]::subst_lang'.


Derive elab_subst_lang
       SuchThat (elab_lang subst_lang elab_subst_lang)
       As elab_subst_lang_pf.
Proof.
  (* TODO: figure out how to get rid of the second repeat*)
  repeat (repeat (cbn;step_elab())).
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    cbn.
    apply elab_term_by'; repeat (cbn;step_elab()).
    (* TODO: want to start w/ subgoal 2 for inference purposes?*)
    apply elab_term_by'; repeat (cbn;step_elab()).

    apply (@elab_term_var' "A"%string); reflexivity.
    
    apply elab_term_by'; repeat (cbn;step_elab()).
  }    
    
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).

    apply (@elab_term_var' "A"%string); reflexivity.    
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    cbn.
    eapply elab_term_conv.
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).

    apply (@elab_term_var' "A"%string); cbn; solve_in().    
    repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).

    
    eapply Core.le_sort_refl'; repeat (cbn;step_elab()).
    reflexivity.

    eapply Core.le_term_trans.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string);repeat (cbn;step_elab());
    reflexivity.
    eapply Core.le_term_refl';repeat (cbn;step_elab()).
    reflexivity.
    reflexivity.
    eapply (Core.le_term_by' "wkn_snoc"%string);repeat (cbn;step_elab());
      reflexivity.
    reflexivity.
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    eapply elab_term_conv.
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
    repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()). cbn.
    apply (@Core.wf_term_by' "cmp"%string); repeat (cbn;step_elab()).
    cbn. step_elab().
    step_elab().
    apply (@Core.wf_term_var' "G2"%string); reflexivity.    
    apply Core.wf_term_var; repeat (cbn;step_elab()).
    apply (@Core.wf_term_var' "f"%string); reflexivity. 
    apply (@Core.wf_term_var' "g"%string); reflexivity. 

    eapply Core.le_sort_refl'; repeat(cbn;step_elab()).
    reflexivity.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string);repeat (cbn;step_elab());
      reflexivity.
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].

    apply Core.wf_term_by'; repeat (cbn;step_elab()).
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    solve[repeat(apply elab_term_by'; repeat (cbn;step_elab()))].
  }
  {
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
  }
Qed.
 
    
Instance elab_subst_lang_inst : Elaborated subst_lang :=
  {
  elaboration := elab_subst_lang;
  elab_pf := elab_subst_lang_pf;
  }.
