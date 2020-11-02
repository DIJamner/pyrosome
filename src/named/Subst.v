
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import IExp IRule.
Require Import String.




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

Definition subst_lang' : lang :=
  [:> (:)
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ]::
  [:> "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" #"forget" %"g" = #"forget" : #"sub" %"G" #"emp"
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
       = #"el_subst" %"f" (#"el_subst" (#"cmp" %"f" %"g") %"e")
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
      "ty" srt
  ]::cat_lang.

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
       #"cmp" (#"snoc" %"g" %"e") %"f"
       = #"snoc" (#"cmp" %"g" %"f") (#"el_subst" %"f" %"e")
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
      #"cmp" #"wkn" (#"snoc" %"g" %"e") = %"g" : #"sub" %"G" %"G'"
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
       "ext" : #"env"
  ]::subst_lang'.

Require Import Setoid.

Require Import Named.Tactics.

Set Default Proof Mode "Ltac2".

Lemma nil_with_names c : with_names_from c [::] = [::].
Proof using.
  destruct c; auto.
Qed.

Ltac2 process_judgment () :=
  (simpl;lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ (con ?s _) _] => apply_rule s
  | [|- wf_term _ _ (var _) _] => eapply wf_term_var; unify_in()
   end).


Lemma subst_lang_wf : wf_lang subst_lang.
Proof using .
  constructor > [|repeat (process_judgment())].
  constructor > [|repeat (process_judgment())]. (* long *)
  constructor > [|repeat (process_judgment())].
  constructor > [|repeat (process_judgment())]. (* long *)

  constructor > [|repeat (process_judgment())]. (* long *) 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. (* long *)
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())].
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())].
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())].
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())]. 
  constructor > [|repeat (process_judgment())].
  constructor.
  {
    eapply wf_term_conv > [ repeat (process_judgment()) | repeat (process_judgment()) |].
    cbv.
    admit.
  }
  {
    eapply wf_term_conv.
    repeat (process_judgment()).
    apply_rule '"el_subst"%string.
    constructor; auto.
    constructor; auto.
    constructor; auto.
    constructor; auto.
    constructor; auto.
    constructor.
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()).
    
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()). cbv.
    admit. admit.
  }
  {
    eapply wf_term_conv.
    repeat (process_judgment()).
    repeat (process_judgment()).
    cbv. constructor.
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()).
    repeat (process_judgment()).



    
    eapply wf_term_var.
    
    change_cbv constr:((srt "sub" [:: var "G'"; var "G"]) [/[:: ("G'"%string, var "G3"); ("G"%string, var "G1")] /]).
      unify_in().

    
    admit.
  }    

  simpl.
  eapply wf_term_var.
  
  cbv.
  auto.
  Focus 1.
  lazy.
  Unset Printing Coercions.
  cbv. unify_in().
  process_judgment().
  Focus 2.
  process_judgment'().
  repeat (process_judgment ()).
  Focus 2.
  repeat (process_judgment ()).
  repeat (simpl;lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_lang _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ (con ?s _) _] => Control.plus (fun () => apply_rule s) (fun _ => eapply wf_term_conv)
  | [|- wf_term _ _ (var _) _] => eapply wf_term_var
  end).
  eapply wf_term_conv.

  
  repeat (simpl;lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_lang _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ (con ?s _) _] => apply_rule s
  | [|- wf_term _ _ (var _) _] => eapply wf_term_var
  end).

   
  repeat (simpl;lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_lang _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ (con ?s _) _] => apply_rule s
  | [|- wf_term _ _ (var _) _] => eapply wf_term_var
  end).

  cbv.
  eapply sort_con_mor.
  constructor.
  constructor.
  constructor.
  reflexivity.
  rewrite nil_with_names.
  reflexivity.
  admit.

  unfold with_names_from.
  simpl.
  eapply le_term_conv.
  admit.
  let rec print_map m :=
      match m with
      | MapEmpty => Message.of_string "[::]"
      | MapCons s v m' =>
        Message.concat
          (Message.of_string "(")
          (Message.concat (Message.of_constr s)
                          (Message.concat (Message.of_string ",")
                                          (Message.concat (Message.of_constr v)
                                                          (Message.concat (Message.of_string ")::")
                                                                          (print_map m)))))
      end in
      
  let name := '"ty_subst_id"%string in
  let l := goal_lang () in
  (* TODO: make d an evar so it isn't silently returned?*)
  let d := constr:(sort_rule [::]) in
  let r := Std.eval_cbv all_red_flags
           constr:(named_list_lookup $d $l $name) in
  lazy_match! r with
  | term_le ?c' ?e1' ?e2' ?t' =>
    lazy_match! goal with
    | [|- le_term ?l ?c ?t ?e1 ?e2] =>
      let m := (map_merge
                    (exp_match e1' e1)
                    (exp_match e2' e2)) in
      Message.print (print_map m)
      end end.
      
      let s := subst_of_map m c' in
      Message.print (Message.of_constr s) end end.
      
      my_change2
        '(le_term $l $c $t $e1 $e2)
        '(le_term $l $c $t'[/$s/] $e1'[/$s/] $e2'[/$s/]);
      eapply le_term_subst;
      Control.enter
        (fun () =>
           match! goal with
           | [|- le_term _ _ _ _ _] =>
             eapply le_term_by;
             unify_in ()
           | [|- le_subst _ _ _ _ _] => ()
           | [|- _] => Control.throw Match_failure
           end)
    | [|- ?j] =>
      Control.zero
        (JudgmentMismatchExn constr:(($name,$r)) j)
    end
      
end.
  unify_in ().
  apply_rule '"ty_subst_id"%string.
  
  
  simpl.
   (lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_lang _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ ?e _] =>
    simpl;
    lazy_match! e with
    | con ?s _ => apply_rule s
    | var _ => eapply wf_term_var
    end
    end).
   unify_in().
  TODO: should I always apply s?
  simpl.
  apply_rule '"cmp"%string.
  repeat (lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_lang _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ _ _] => try (fun () => simpl; eapply wf_term_var)
          end).
  simpl.
  apply_rule '"id"%string.

  repeat (lazy_match! goal with
  | [|- wf_ctx _ _] => constructor
  | [|- wf_lang _] => constructor
  | [|- wf_rule _ _] => constructor
  | [|- is_true(fresh _ _)] => trivial
  | [|- wf_sort _ _ _] => econstructor
  | [|- is_true(_ \in _)] => unify_in()
  | [|- wf_subst _ _ _ _] => rewrite ?nil_with_names; constructor
  | [|- wf_term _ _ _ _] => try (fun () => simpl; eapply wf_term_var)
  end).
  

  eapply wf_term_var.
  TODO: defaukt rule is showing up next to ext (from unify_in?)
  bugs: used ext as a sort somewhere
                      wf_subst _ (w_n_f ?c [::]) _ not recognized
   lazy_match! goal with
  end.
  
  wf_lang_eauto.

  {
    constructor; eauto with judgment.
  ltac2:(apply_term_constr()).
  repeat eapply wf_subst_cons; eauto with judgment.
  cbv.
  eapply wf_term_conv.
  eauto with judgment.
  ltac2:(apply_term_constr()).
  repeat eapply wf_subst_cons; eauto with judgment.
  eapply sort_con_mor.
  cbv.
  eapply le_subst_cons.
  2:{
    (* TODO: automate: *)
    instantiate (1 := ty 0).
    cbv.
    Eval cbv in (nth_level (sort_rule [::]) subst_lang 14).
    symmetry.
    ltac2:(apply_term_rule constr:(14)).
    eauto with judgment.
  }
  eauto with judgment.
  }  
  {
    constructor; auto with judgment.
    apply: wf_term_conv; first by auto with judgment.
    instantiate (1 := (el 0 (ty_subst 0 (ext 1 3) (snoc 0 1 3 2 4) (ty_subst (ext 1 3) 1 (p 1 3) 3)))).
    apply:type_wf_term_recognizes; eauto with judgment.
    unfold el_srt_subst.
    eapply sort_con_mor.
    repeat eapply subst_cons_mor.
    auto with judgment.
    auto with judgment.
    
    eapply le_term_trans.
    instantiate (2 := ty 0); cbv.
    - symmetry (* TODO: handle in tactic *).
      instantiate (1 := ty_subst 0 1
                           (cmp 0 (ext 1 3) 1
                                (p 1 3) (snoc 0 1 3 2 4))
                           3)
      (*TODO: handle in tactic*).
      ltac2:(apply_term_rule constr:(14)).
      eauto with judgment.
    -
      (* TODO: should be handled by tactic *)
      change (ty 0)[/[:: var 0]/]
        with (ty 0)[/[:: var 3; var 2; var 1; var 0]/].
      eapply term_con_mor.
      repeat eapply subst_cons_mor;
        auto with judgment.
      instantiate (1:= hom 0 1).
      cbv.
      ltac2:(apply_term_rule constr:(23)).
      eauto with judgment.
  }
  { (* element identity substitution *)
    constructor;auto with judgment.
    
    (*TODO: should be handledby this rewriting:
      match goal with
      |- wf_term ?l ?c _ _ => 
      setoid_replace (el 0 1) with (el 0 (ty_subst 0 0 (id 0) 1))
                             using relation (le_sort l c) at 2
    end.
     *)
    apply:wf_term_conv; first by auto with judgment.
    instantiate (1:= el 0 (ty_subst 0 0 (id 0) 1)).
    auto with judgment.

    eapply sort_con_mor.
    eapply subst_cons_mor.
    eapply subst_cons_mor; try reflexivity.
    eauto with judgment.
    change ( [:: el 0 1; ty 0; ob] ) with ( [:: el 0 1]++[:: ty 0; ob] ).
    eapply le_mono_ctx.
    eapply le_term_by.
    instantiate (1:= ty 0).
    by compute.
  }
  Unshelve.
  all: try exact (con 0 [::]).
  all: exact [::].
Qed.

