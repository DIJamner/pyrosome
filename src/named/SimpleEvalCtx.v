Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst SimpleVSTLC Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Set Default Proof Mode "Classic".

(*An extension to subst_lang *)
Definition subst_eval_ctx :=
  [(* TODO: do I want a substitution eval ctx? I think no
         [:> "G1" : #"env", "G2" : #"env", "G3" : #"env", "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3", "A" : #"ty", "e" : #"el" %"G3" %"A"
        ----------------------------------------------- ("el_subst_cmp")
        #"el_subst" %"f" (#"el_subst" %"g" %"e") = #"el_subst" (#"cmp" %"f" %"g") %"e" : #"el" %"G1" %"A"
    ]%arule;
  [:> "G" : #"env", "A" : #"ty", "B": #"ty", "E" : #"Ectx" %"G'" %"A" %"B"
        ----------------------------------------------- ("E_subst_id")
        #"E_subst" #"id" %"E" = %"E" : #"Ectx" %"G'" %"A" %"B"
    ]%arule;
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
      "A" : #"ty", "B" : #"ty", "E" : #"Ectx" %"G" %"A" %"B"
        -----------------------------------------------
        #"E_subst" "g" "E" : #"Ectx" %"G'" %"A" %"B"
    ];*)
     [:> "G" : #"env", "A" : #"ty",
         "e" : #"el" %"G" %"A"
        ----------------------------------------------- ("plug hole")
        #"plug" #"[ ]" %"e" = %"e" : #"el" %"G" %"A"
     ];
     [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
         "E" : #"Ectx" %"G" %"A" %"B",
         "e" : #"el" %"G" %"A"
        -----------------------------------------------
        #"plug" "E" "e" : #"el" %"G" %"B"
     ];
     [:| "G" : #"env", "A" : #"ty"
        -----------------------------------------------
        #"[ ]" : #"Ectx" %"G" %"A" %"A"
     ];
     [s| "G" : #"env", "A" : #"ty", "B" : #"ty"
        -----------------------------------------------
        #"Ectx" "G" "A" "B" srt
     ]
  ]%arule.



Ltac break_down_elab_lang' :=
  repeat ((eapply elab_lang_cons_nth_tail; [compute; reflexivity | compute; reflexivity| apply use_compute_fresh; compute; reflexivity | ..]));
  [solve [assumption | compute; apply elab_lang_nil]|..].

Local Ltac t :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> apply named_list_lookup_err_in; compute; reflexivity
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => eapply elab_args_cons_ex' || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_var || eapply elab_term_by'
  | [|-wf_term _ _ _ _] => shelve
  | [|-elab_rule _ _ _] => econstructor
  | [|- _ = _] => compute; reflexivity
  end.


Ltac auto_elab' :=
  match goal with
  | [|- elab_lang ?l ?el] =>
  rewrite (as_nth_tail l);
  rewrite (as_nth_tail el);
  break_down_elab_lang';
  unshelve solve[repeat t];
  cleanup_auto_elab
  end.

Derive subst_eval_ctx_elab
       SuchThat (elab_lang (subst_eval_ctx++subst_lang) (subst_eval_ctx_elab ++ subst_elab))
       As subst_eval_ctx_wf.
Proof.
  pose proof subst_lang_wf.
  TODO: nth_tail and app
  match goal with
  | [|- elab_lang ?l ?el] =>
  rewrite (as_nth_tail l);
    rewrite (as_nth_tail el)
  end.
  
  break_down_elab_lang'.
  unshelve solve[repeat t];
  cleanup_auto_elab
  end.
  auto_elab.
  Unshelve.
  all: cleanup_auto_elab.
Qed.

Derive subst_eval_ctx_elab
       SuchThat (is_pf_of_wf_lang (subst_eval_ctx ++ subst_lang) (subst_eval_ctx_elab ++ vsubst_elab)
         /\ lang_ok (subst_eval_ctx_elab ++ vsubst_elab))
       As subst_eval_ctx_elab_ok.
Proof.
  split.
  {
    simpl.
     repeat match goal with
             |[|- is_pf_of_wf_lang (_::_) (?el ++_)] =>
             let x := open_constr:(_::_) in unify el x; simpl; constructor
            end.
     match goal with
       [|- is_pf_of_wf_lang _ (?g ++ vsubst_elab)]=> unify g (@nil (string * rule_pf)%type); apply is_pf_of_wf_lang_vsubst
     end.
     all: try solve [repeat constructor; repeat first [pcon | pvar | by compute]].
  }
  {
    apply /check_lang_okP; by compute.
  }
Qed.

(*an extension to subst_eval_ctx++stlc*)
Definition Estlc :=  
  [::
     [:> "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" %"A",
       "v" : #"val" %"G" (#"->" %"A" %"B"),
       "e" : #"el" %"G" %"C"
       ----------------------------------------------- ("plug app_r")
       #"plug" (#"Eapp_r" %"v" %"E") %"e"
       = #"app" (#"ret" %"v") (#"plug" %"E" %"e")
      : #"el" %"G" %"B"
  ];
     [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "v" : #"val" %"G" (#"->" %"A" %"B"),
       "E" : #"Ectx" %"G" %"C" %"A"
       -----------------------------------------------
       #"Eapp_r" "v" "E" : #"Ectx" %"G" %"C" %"B"
  ];
     [:> "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A",
       "e" : #"el" %"G" %"C"
       ----------------------------------------------- ("plug app_l")
       #"plug" (#"Eapp_l" %"E" %"e'") %"e"
       = #"app" (#"plug" %"E" %"e") %"e'"
      : #"el" %"G" %"B"
  ];
     [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" %"G" %"C" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       #"Eapp_l" "E" "e'" : #"Ectx" %"G" %"C" %"B"
  ]]%arule.


(*Should be proven using above and embedding properties*)
Lemma tmp : is_pf_of_wf_lang (subst_eval_ctx ++ stlc) (subst_eval_ctx_elab ++ vstlc_elab).
Admitted.

Derive Estlc_elab
       SuchThat (is_pf_of_wf_lang (Estlc ++ subst_eval_ctx ++ stlc) (Estlc_elab ++ subst_eval_ctx_elab ++ vstlc_elab)
         /\ lang_ok (Estlc_elab ++ subst_eval_ctx_elab ++ vstlc_elab))
       As Estlc_elab_ok.
Proof.
  Arguments subst_eval_ctx : simpl never.
  Arguments subst_eval_ctx_elab : simpl never.
  split.
  {
    cbn -[subst_eval_ctx subst_eval_ctx_elab stlc vstlc_elab].
    repeat match goal with
           |[|-is_pf_of_wf_lang (subst_eval_ctx ++ stlc) (?g ++ subst_eval_ctx_elab ++ vstlc_elab)]=>
            unify g (@nil (string * rule_pf)%type);  cbn -[subst_eval_ctx subst_eval_ctx_elab stlc vstlc_elab]; apply tmp
           |[|- is_pf_of_wf_lang (_::_) (?el ++_)] =>
             let x := open_constr:(_::_) in unify el x;  cbn -[subst_eval_ctx subst_eval_ctx_elab stlc vstlc_elab]; constructor
           end.
    
    all: try solve [repeat constructor; simpl; repeat first [pcon | pvar | by compute]].
  }
  {
    apply /check_lang_okP; by compute.
  }
Qed.

