Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches.
Import Core.Notations.

Require Coq.derive.Derive.


(* syntax of categories *)
Definition cat_lang : lang :=
  [
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
       #"cmp" "f" "g" : #"sub" %"G1" %"G3"
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       #"id" : #"sub" %"G" %"G"
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      #"sub" "G" "G'" srt                     
  ];
  [s|
      -----------------------------------------------
      #"env" srt
  ]
  ]%arule.


    
Derive cat_lang_elab
       SuchThat (elab_lang cat_lang cat_lang_elab)
       As cat_lang_wf.
Proof.
  auto_elab.
  Unshelve.
  all: cleanup_auto_elab.
Qed.


Definition subst_lang : lang :=
   [[:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"id" = #"snoc" #"wkn" #"hd" : #"sub" (#"ext" %"G" %"A") (#"ext" %"G" %"A")
   ];
   [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3",
       "e" : #"el" %"G2" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" %"f" (#"snoc" %"g" %"e")
       = #"snoc" (#"cmp" %"f" %"g") (#"el_subst" %"f" %"e")
       : #"sub" %"G1" (#"ext" %"G3" %"A")
   ];
   [:> "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'",
       "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("snoc_hd")
       #"el_subst" (#"snoc" %"g" %"e") #"hd" = %"e"
       : #"el" %"G" (#"ty_subst" %"g" %"A")
  ];
  [:> "G" : #"env", "G'" : #"env",
      "g" : #"sub" %"G" %"G'",
      "A" : #"ty" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" %"g" %"e") #"wkn" = %"g" : #"sub" %"G" %"G'"
  ];
  [:| "G" : #"env", "A" : #"ty"(%"G")
       -----------------------------------------------
       #"hd" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"A")
  ];
  [:| "G" : #"env", "A" : #"ty" %"G"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" %"G" %"A") %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty" %"G'",
      "g" : #"sub" %"G" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       -----------------------------------------------
       #"snoc" "g" "e" : #"sub" %"G" (#"ext" %"G'" %"A")
  ];
  [:| "G" : #"env", "A": #"ty" %"G"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];
  [:> 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ];
  [:> "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" %"g" #"forget" = #"forget" : #"sub" %"G" #"emp"
  ];
  [:| "G" : #"env" 
      -----------------------------------------------
      #"forget" : #"sub" %"G" #"emp"
  ];
  [:| 
      -----------------------------------------------
      #"emp" : #"env"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3", "e" : #"el" %"G3" %"A"
       ----------------------------------------------- ("el_subst_cmp")
       #"el_subst" %"f" (#"el_subst" %"g" %"e")
       = #"el_subst" (#"cmp" %"f" %"g") %"e"
       : #"el" %"G1" (#"ty_subst" (#"cmp" %"f" %"g") %"A")
  ]; 
  [:> "G" : #"env", "A" : #"ty" %"G", "e" : #"el" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"el" %"G" %"A"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" %"f" (#"ty_subst" %"g" %"A")
       = #"ty_subst" (#"cmp" %"f" %"g") %"A"
       : #"ty" %"G1"
  ];              
  [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" %"A" = %"A" : #"ty" %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'", "e" : #"el" %"G'" %"A"
       -----------------------------------------------
       #"el_subst" "g" "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
  ];
  [s| "G" : #"env", "A" : #"ty"(%"G")
      -----------------------------------------------
      #"el" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'"
       -----------------------------------------------
       #"ty_subst" "g" "A" : #"ty" %"G"
  ];
  [s| "G" : #"env" 
      -----------------------------------------------
      #"ty" "G" srt
   ]]%arule++cat_lang.

(*TODO: move to elab or core*)
(*TODO: nth_tail wf*)



Lemma elab_lang_cons_nth_tail n l el name r er el'
  : nth_error l n = Some (name,r) ->
    nth_tail n el = (name, er)::el' ->
    fresh name (nth_tail (S n) l) ->
    elab_lang (nth_tail (S n) l) (nth_tail (S n) el) ->
    (elab_lang (nth_tail (S n) l) (nth_tail (S n) el) ->
     elab_rule (nth_tail (S n) el) r er) ->
    elab_lang (nth_tail n l) (nth_tail n el).
Proof.
  revert el n el'.
  induction l; destruct el; basic_goal_prep; basic_core_crush.
  {
    apply nth_error_In in H.
    basic_utils_crush.
  }
  {
    destruct n.
    {
      rewrite <-!as_nth_tail in *.
      basic_goal_prep;
        basic_core_crush.
    }
    {
      rewrite !nth_tail_S_cons in *.
      eauto.
    }
  }
Qed.

Ltac break_down_elab_lang :=
  repeat ((eapply elab_lang_cons_nth_tail; [compute; reflexivity | compute; reflexivity| apply use_compute_fresh; compute; reflexivity | ..]));
  [solve [assumption | compute; apply elab_lang_nil]|..].

Ltac setup_elab_lang_proof :=
  match goal with
  | |- elab_lang ?l ?el =>
    rewrite (as_nth_tail l); rewrite (as_nth_tail el); break_down_elab_lang;
      let ell := fresh "ell" in intro ell; pose proof (elab_lang_implies_wf ell); clear ell
  end.

Derive subst_lang_elab
       SuchThat (elab_lang subst_lang subst_lang_elab)
       As subst_lang_wf.
Proof.
  setup_elab_lang_proof.
  
Local Ltac t :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> apply named_list_lookup_err_in; compute; reflexivity
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => eapply elab_args_cons_ex' || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_conv; [eapply elab_term_var || eapply elab_term_by'|]
  | [|-wf_term _ _ _ _] => ()
  | [|-elab_rule _ _ _] => econstructor
  | [|- _ = _] => compute; reflexivity
  end.



Local Ltac t' :=
  cbn -[In];
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> apply named_list_lookup_err_in; compute; reflexivity
 (* | [|- eq_sort _ _ _ _] =>  sort_cong (*TODO: use reduction on sorts*)*)
  | [|- eq_args _ _ _ _ _] =>  constructor
  | [|- eq_term _ _ _ (var _) (var _)] =>  eapply eq_term_refl (*TODO: not generally sound, but very useful*)
  | [|- wf_term _ _ _ _] =>  eapply wf_term_var || eapply wf_term_by' (*TODO: add convs*)
  | [|- wf_sort _ _ _] => eapply wf_sort_by
  | [|-wf_args _ _ _ _] => econstructor
  | [|- _ = _] => compute; reflexivity
  end.

solve[ repeat t].
solve[ repeat t].
all: try solve[ repeat t; repeat t'].

Ltac solve_fresh := apply use_compute_fresh; compute; reflexivity.
Ltac solve_sublist := apply (use_compute_sublist string_dec); compute; reflexivity.


Ltac break_eq_args :=
  (apply eq_args_cons;[break_eq_args|])
  || apply eq_args_nil.

(*TODO: move to the right place*)
Ltac sort_cong :=
  eapply sort_con_congruence;
  [ solve_in
  | solve_len_eq
  | assumption || fail "could not find lang wf assumption" (*TODO: make work w/ nth_tail*)
  | break_eq_args].

Ltac compute_everywhere e :=
  let e' := eval compute in e in
      change e with e' in *.

Ltac process_eq_term :=
  simpl;
  match goal with
  (* in general not valid, but (pretty much) always good*)
  | [|- eq_term _ _ _ (var _) _] => term_refl
  (* might be more problematic w/ my left-to-right discipline*)
  | [|- eq_term _ _ _ _ (var _)] => term_refl
  | [|- eq_term ?l _ _ ?e1 ?e2] =>
    tryif is_evar e1; is_evar e2 then shelve
    else (try solve [compute_everywhere l; by_reduction])
  end.

(* elab_term -> maybe (eq_sort * list elab_term)
           should never fail
           shelves goal if both exp and elaborated exp are evars
           otherwise returns goal connecting derived sort to given sort
           and elab_term goals for alll subterms
 *)
Ltac try_break_elab_term :=
  simpl;
  lazymatch goal with
    [|- elab_term _ _ ?e ?ee ?t] =>
    tryif is_evar e; is_evar ee then shelve else
      eapply elab_term_conv;
    [ (eapply elab_term_var; [solve_in])
      || (eapply elab_term_by;[solve_in | break_down_elab_args])
    | try (sort_cong; process_eq_term)
           (*TODO: try because if we have an evar with a subst applied to it, the tactic fails;
                      should be able to make it succeed
                     *)
      (*TODO: assumes lang has no sort equations*)]
  end with
(*elab_args -> list elab_term; should never fail.
        returns goals for explicit terms,
        shelves goals for implicit terms *)
 break_down_elab_args :=
  (eapply elab_args_cons_ex'; [solve_len_eq |repeat try_break_elab_term | break_down_elab_args])
  || (eapply elab_args_cons_im; [break_down_elab_args | shelve (*TODO: what to run here?*)])
  || eapply elab_args_nil.



Ltac break_elab_sort :=
  eapply elab_sort_by; [solve_in |break_down_elab_args].

(*elab_ctx -> list elab_sort; should never fail*)
Ltac break_down_elab_ctx :=
  (eapply elab_ctx_cons;[solve_fresh| break_down_elab_ctx | break_elab_sort] || eapply elab_ctx_nil).

Ltac break_elab_rule :=
  match goal with
  | [|- elab_rule _ (sort_rule _ _) _] =>
    eapply elab_sort_rule; [break_down_elab_ctx | solve_sublist]
  | [|- elab_rule _ (term_rule _ _ _) _] =>
    eapply elab_term_rule; [break_down_elab_ctx | break_elab_sort | solve_sublist]
  | [|- elab_rule _ (term_eq_rule _ _ _ _) _] =>
  eapply eq_term_rule;[ break_down_elab_ctx | break_elab_sort| try_break_elab_term | try_break_elab_term]    
  end.
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
solve [break_elab_rule].
Unshelve.
all: try match goal with
     | [|- eq_term _ _ _ _ _] =>
       term_refl
         end.

all: try solve [repeat t'].

(*TODO: the above is definitely not sufficient in general *)
Unshelve.

all: try solve [repeat t'].
Qed.
