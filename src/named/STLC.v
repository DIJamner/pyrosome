Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches Subst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition stlc :=
  [[:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
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
  ]]%arule.


Derive stlc_elab
       SuchThat (Pre.elab_lang (subst_lang_elab++cat_lang_elab) stlc stlc_elab)
       As stlc_wf.
Proof.
  setup_elab_lang.

  solve [ break_elab_rule ].
  solve [ break_elab_rule ].
  solve [ break_elab_rule ].
  solve [ break_elab_rule; repeat process_eq_term (*TODO: why is this needed?*) ].
  solve [ break_elab_rule; repeat process_eq_term (*TODO: why is this needed?*) ].
  solve [ break_elab_rule; repeat process_eq_term (*TODO: why is this needed?*) ].
  {
     match goal with
  | |- elab_rule _ (sort_rule _ _) _ => eapply elab_sort_rule; [ break_down_elab_ctx | solve_sublist ]
  | |- elab_rule _ (term_rule _ _ _) _ => eapply elab_term_rule; [ break_down_elab_ctx | break_elab_sort | solve_sublist ]
  | |- elab_rule _ (term_eq_rule _ _ _ _) _ => eapply eq_term_rule
     end.
     break_down_elab_ctx.
     break_elab_sort.
     solve[try_break_elab_term].
  simpl;
   lazymatch goal with
   | |- elab_term _ _ ?e ?ee ?t =>
     tryif (is_evar e; is_evar ee) then shelve else eapply elab_term_conv
   end.
  eapply elab_term_by; [solve_in|].

  eapply elab_args_cons_ex'; [ solve_len_eq | |].

  simpl.

  {
    eapply elab_term_conv.
    eapply elab_term_by; [solve_in|].
    eapply elab_args_cons_ex'; [ solve_len_eq | |].
    solve[try_break_elab_term].

    eapply elab_args_cons_im; [ | shelve ].
    eapply elab_args_cons_ex'; [ solve_len_eq | |].
    {
      simpl.
      eapply elab_term_conv.
      eapply elab_term_by; [solve_in|].
      eapply elab_args_cons_ex'; [ solve_len_eq | |].
      {
        simpl.
        eapply elab_term_conv.
        eapply elab_term_by; [solve_in|].
        eapply elab_args_cons_im; [ | shelve ].
        eapply elab_args_cons_im; [ | shelve ].
        econstructor.

        {
          simpl.
          sort_cong.
          simpl.
          term_refl.
          simpl.
          shelve.
        }
      }
      {
        eapply elab_args_cons_ex'; [ solve_len_eq | |].
        {
          simpl.
          eapply elab_term_conv.
          eapply elab_term_by; [solve_in|].
          {
            eapply elab_args_cons_ex'; [ solve_len_eq | |].
            {
              simpl.
              eapply elab_term_var; solve_in.
            }
            
            eapply elab_args_cons_ex'; [ solve_len_eq | |].
            {
              simpl.
              eapply elab_term_conv.
              eapply elab_term_by; [solve_in|].
              eapply elab_args_cons_im; [ | shelve ].
              eapply elab_args_cons_im; [ | shelve ].
              constructor.
              
              simpl.
              sort_cong; term_refl.
            }
            eapply elab_args_cons_im; [ | shelve ].
            eapply elab_args_cons_im; [ | shelve ].
            eapply elab_args_cons_im; [ | shelve ].
            constructor.
          }

          simpl.
          sort_cong; term_refl.
        }
        
        eapply elab_args_cons_im; [ | shelve ].
        eapply elab_args_cons_im; [ | shelve ].
        eapply elab_args_cons_im; [ | shelve ].
        constructor.
      }
      {
        simpl.
        sort_cong; term_refl.
      }
    }
    
    eapply elab_args_cons_im; [ | shelve ].
    eapply elab_args_cons_im; [ | shelve ].
    constructor.

    {
      simpl.
      sort_cong; simpl.
      term_refl.
      instantiate (2:= {{e#"ty_subst" %"G'" %"G" %"g" %"A"}}).
      instantiate (1:= {{e#"ty_subst" %"G'" %"G" %"g" %"B"}}).
      compute_everywhere (nth_tail 1 stlc_elab).
      by_reduction.
      
      (*TODO: this is unwieldly, curr. have to write out instantiation for a; 
        need tactics (e.g. rewrite) that work w/ evars,
        or a way to better clear them before I get here.

        remainder of proof needed:    
        fill ?a with (ty_subst g B), reduce
       *)
    }
  }

  break_down_elab_args.

  sort_cong; process_eq_term.

  Unshelve.
  all: try cleanup_auto_elab.
  all: try apply eq_term_refl.
  all: try cleanup_auto_elab.
  {
    unshelve (repeat (constructor;[|try cleanup_auto_elab; shelve])).
    2: constructor.
    simpl.
    eapply wf_term_conv.
    eapply wf_term_by; [solve_in|].
    eapply wf_args_cons.
    simpl.
    {
      eapply wf_term_conv.
      eapply wf_term_var; [solve_in].
      sort_cong; by_reduction.
    }
    cleanup_auto_elab.

    simpl.
    sort_cong; term_refl.
  }
  {
    unshelve (repeat (constructor;[|try cleanup_auto_elab; shelve])).

    simpl.
    {
      eapply wf_term_conv.
      eapply wf_term_var; [solve_in].
      sort_cong; by_reduction.
    }

    
    cleanup_auto_elab.
  }
  {
      compute_everywhere (nth_tail 1 stlc_elab).
      by_reduction.
  }
  
  {
    unshelve (repeat (constructor;[|try cleanup_auto_elab; shelve])).

    simpl.
    {
      eapply wf_term_conv.
      eapply wf_term_by; [solve_in|].
      constructor.
      {
        simpl.
        eapply wf_term_conv.
        eapply wf_term_by; [solve_in|].
        
        cleanup_auto_elab.
        simpl.
        sort_cong; by_reduction.
      }
      cleanup_auto_elab.
      sort_cong; by_reduction.
    }
    constructor.
  }
  {
    unshelve (repeat (constructor;[|try cleanup_auto_elab; shelve])).
    simpl.
    {
      eapply wf_term_conv.
      eapply wf_term_by; [solve_in|].
      cleanup_auto_elab.

      simpl.
      sort_cong; by_reduction.
    }
    cleanup_auto_elab.
    
  }
  Unshelve.
  all: try cleanup_auto_elab.

  simpl.
  cleanup_auto_elab.
  }
Qed.  
#[export] Hint Resolve stlc_wf : elab_pfs.
