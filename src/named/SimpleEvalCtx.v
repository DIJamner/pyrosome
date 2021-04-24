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

(*TODO: move to utils*)
Lemma nth_tail_length_app A (l1 l2 : list A) n
  : n = length l1 ->
    nth_tail n (l1++l2) = l2.
Proof.
  intros; subst.
  induction l1; basic_goal_prep; basic_utils_crush.
Qed.

Lemma nth_tail_app A n (l l' : list A)
  : n < length l ->
    nth_tail n (l++l') = (nth_tail n l)++l'.
Admitted.

Lemma nth_tail_is_cons_bounds_n A n (l l' : list A) p
  : nth_tail n l = p::l' ->
    n < length l.
Admitted.

(*TODO: move to elab*)
Lemma elab_lang_cons_nth_tail_app
     : forall (n : nat) (l el l' el' el'' : list (string * rule)) (name : string) (r er : rule),
       nth_error l n = Some (name, r) ->
       nth_tail n el = (name, er) :: el'' ->
       fresh name (nth_tail (S n) (l++l')) ->
       elab_lang (nth_tail (S n) (l++l')) (nth_tail (S n) (el++el')) ->
       elab_rule (nth_tail (S n) (el++el')) r er ->
       elab_lang (nth_tail n (l++l')) (nth_tail n (el++el')).
Proof.
  intros.
  eapply elab_lang_cons_nth_tail; eauto.
  {
    rewrite nth_error_app1; eauto.
    apply nth_error_Some.
    intro H'.
    rewrite H in H'.
    inversion H'.
  }
  {
    rewrite nth_tail_app.
    rewrite H0.
    reflexivity.
    eapply nth_tail_is_cons_bounds_n; eauto.
  }
Qed.
    

(*TODO: move back to elab*)
Ltac break_down_elab_lang' :=
  repeat ((eapply elab_lang_cons_nth_tail_app
           || eapply elab_lang_cons_nth_tail);
              [compute; reflexivity
              | compute; reflexivity
              | apply use_compute_fresh; compute; reflexivity
              | ..]);
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
  match goal with
  | [|- elab_lang ?l ?el] =>
  rewrite (as_nth_tail l);
    rewrite (as_nth_tail el)
  end.
  repeat ((eapply elab_lang_cons_nth_tail_app
           || eapply elab_lang_cons_nth_tail);
              [compute; reflexivity
              | compute; reflexivity
              | apply use_compute_fresh; compute; reflexivity
              | ..]).
  
  rewrite !nth_tail_length_app; [assumption|..].
  cbn.
  match goal with
    [ |-context [length ?emp]] => unify emp (@nil (string*rule))
  end.
  reflexivity.
  reflexivity.
  
  all:unshelve solve[repeat t];
  cleanup_auto_elab.
  
Qed.

Axiom TODO : False.

(*an extension to subst_eval_ctx++stlc*)
Definition Estlc :=  
  [
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


Derive Estlc_elab
       SuchThat (elab_lang (Estlc++subst_eval_ctx++stlc)
                           (Estlc_elab++subst_eval_ctx_elab ++ stlc_elab))
       As subst_Estlc_wf.
Proof.
  assert (elab_lang (subst_eval_ctx ++ stlc)
                    (subst_eval_ctx_elab ++ stlc_elab)).
  destruct TODO (*TODO: extension lemma for elab*).
  match goal with
  | [|- elab_lang ?l ?el] =>
  rewrite (as_nth_tail l);
    rewrite (as_nth_tail el)
  end.
  repeat ((eapply elab_lang_cons_nth_tail_app
           || eapply elab_lang_cons_nth_tail);
              [compute; reflexivity
              | compute; reflexivity
              | apply use_compute_fresh; compute; reflexivity
              | ..]).
  
  rewrite !nth_tail_length_app; [assumption|..].
  cbn.
  match goal with
    [ |-context [length ?emp]] => unify emp (@nil (string*rule))
  end.
  reflexivity.
  reflexivity.

  all:(unshelve solve[repeat t];
  cleanup_auto_elab).
Qed.
