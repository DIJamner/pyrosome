Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.LinearSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Definition linear_stlc_no_subst_def : lang :=
  {[l (* /lin_subst *)
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"lolli" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"linear_lambda" "A" "e" : #"val" "G" (#"lolli" "A" "B")
  ];
  [:| "G" : #"env",
      "H" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"lolli" "A" "B"),
       "e'" : #"exp" "H" "A"
       -----------------------------------------------
       #"linear_app" "e" "e'" : #"exp" (#"conc" "G" "H") "B"
  ];
  [:= "G" : #"env",
      "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("Linear-STLC-beta")
      #"linear_app" (#"ret" (#"linear_lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" (#"conc" "G" "H") "B"
  ]
  ]}.

Definition linear_stlc_def : lang :=
  {[l (* /lin_subst *)
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"lolli" "t" "t'" : #"ty"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" (#"ext" "G" "A") "B"
       -----------------------------------------------
       #"linear_lambda" "A" "e" : #"val" "G" (#"lolli" "A" "B")
  ];
  [:| "G" : #"env",
      "H" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"exp" "G" (#"lolli" "A" "B"),
       "e'" : #"exp" "H" "A"
       -----------------------------------------------
       #"linear_app" "e" "e'" : #"exp" (#"conc" "G" "H") "B"
  ];
  [:= "G" : #"env",
      "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("Linear-STLC-beta")
      #"linear_app" (#"ret" (#"linear_lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" (#"conc" "G" "H") "B"
  ];

  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" "G" (#"lolli" "A" "B"),
      "e'" : #"exp" "H" "A",
      "G'" : #"env", "H'" : #"env",
      "g" : #"sub" "G'" "G",
      "h" : #"sub" "H'" "H"
      ----------------------------------------------- ("linear_app-subst")
      #"exp_subst" (#"csub" "g" "h") (#"linear_app" "e" "e'")
       = #"linear_app" (#"exp_subst" "g" "e") (#"exp_subst" "h" "e'")
       : #"exp" (#"conc" "G'" "H'") "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"exp" (#"ext" "G" "A") "B",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("linear_lambda-subst")
      #"val_subst" "g" (#"linear_lambda" "A" "e")
      = #"linear_lambda" "A" (#"exp_subst" (#"snoc" "g" #"hd") "e")
      : #"val" "G'" (#"lolli" "A" "B")
  ]
  ]}.

Derive linear_stlc
       SuchThat (elab_lang_ext (linear_exp_subst++linear_value_subst) linear_stlc_def linear_stlc)
       As linear_stlc_wf.
Proof. setup_elab_lang.
- break_elab_rule.
- break_elab_rule.
- break_elab_rule.
- break_elab_rule.
- eapply eq_term_rule.
  + break_down_elab_ctx.
  + break_elab_sort.
  + eapply elab_term_conv.
      -- eapply elab_term_by.
        ++ solve_in.
        ++ eapply elab_args_cons_ex'.
           { solve_len_eq. }
           { cbn_elab_goal.
              eapply elab_term_conv.
              { eapply elab_term_by.
                { solve_in. }
                eapply elab_args_cons_ex'.
                { solve_len_eq. }
                { cbn_elab_goal.
                  try_break_elab_term. }
                eapply elab_args_cons_ex'.
                { solve_len_eq. }
                { (* try_break_elab_term (* this should work *) *)
                  cbn_elab_goal.
                  eapply elab_term_var.
                  solve_in. }
                 break_down_elab_args. }
            compute_eq_compilation.
            sort_cong.
            { (* process_eq_term. *) (* fails *)
              term_refl. }
            process_eq_term. }
            (* eapp
      -- solve_in.
      -- eapply elab_args_cons_ex'.
         2: try_break_elab_term. *)
Abort.
(* #[export] Hint Resolve linear_stlc_wf : elab_pfs. *)


