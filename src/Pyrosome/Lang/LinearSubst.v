Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).


Definition linear_value_subst_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"env" srt
  ];
  [s| "G" : #"env", "G'" : #"env"
      -----------------------------------------------
      #"sub" "G" "G'" srt
  ];
  [:| "G" : #"env"
       -----------------------------------------------
       #"id" : #"sub" "G" "G"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" "G1" "G3"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" #"id" = "f" : #"sub" "G" "G'"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"sub" "G" "G'"
  ];
   [:= "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" "G1" "G2",
         "g" : #"sub" "G2" "G3",
         "h" : #"sub" "G3" "G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h" : #"sub" "G1" "G4"
  ];
  [s|
      -----------------------------------------------
      #"ty" srt
  ];
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"val" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty", "v" : #"val" "G'" "A"
       -----------------------------------------------
       #"val_subst" "g" "v" : #"val" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "e" : #"val" "G" "A"
       ----------------------------------------------- ("val_subst_id")
       #"val_subst" #"id" "e" = "e" : #"val" "G" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty", "v" : #"val" "G3" "A"
       ----------------------------------------------- ("val_subst_cmp")
       #"val_subst" "f" (#"val_subst" "g" "v")
       = #"val_subst" (#"cmp" "f" "g") "v"
       : #"val" "G1" "A"
  ];
  [:| -----------------------------------------------
      #"emp" : #"env"
  ];
  [:| "G" : #"env", "A": #"ty"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];

  [:| "G" : #"env", "G'" : #"env", "V": #"env",
      "A" : #"ty",
      "g" : #"sub" "G" "G'",
      "v" : #"val" "V" "A" (*we restrict substitutions to values *)
       -----------------------------------------------
       #"snoc" "g" "v" : #"sub" "G" (#"ext" "G'" "A")
  ];
  [:|  "A" : #"ty"
       -----------------------------------------------
       #"hd" : #"val" (#"ext" #"emp" "A") "A"
  ];
  [:= "A" : #"ty",
      "v" : #"val" #"emp" "A"
      ----------------------------------------------- ("snoc_hd")
      #"val_subst" (#"snoc" #"id" "v") #"hd" = "v"
      : #"val" #"emp" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
      "f" : #"sub" "G1" "G2",
      "g" : #"sub" "G2" "G3",
      "A" : #"ty",
      "v" : #"val" "G2" "A"
      ----------------------------------------------- ("cmp_snoc")
      #"cmp" "f" (#"snoc" "g" "v")
      = #"snoc" (#"cmp" "f" "g") (#"val_subst" "f" "v")
      : #"sub" "G1" (#"ext" "G3" "A")
  ];
  [:| "G": #"env", "H": #"env"
      -----------------------------------------------
      #"conc" "G" "H": #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("conc_emp")
      #"conc" "G" #"emp" = "G" : #"env"
  ];
  [:= "G": #"env", "H": #"env", "A": #"ty"
      ----------------------------------------------- ("conc_ext_right")
      #"conc" "G" (#"ext" "H" "A") =
      #"ext" (#"conc" "G" "H") "A" : #"env"
  ];

  [:| "G": #"env", "G'": #"env",
      "H": #"env", "H'": #"env",
      "g": #"sub" "G" "G'",
      "h": #"sub" "H" "H'"
      -----------------------------------------------
      #"csub" "g" "h":
      #"sub" (#"conc" "G" "H") (#"conc" "G'" "H'")
  ];
  [:= "G": #"env", "G'": #"env",
      "g": #"sub" "G" "G'"
      ----------------------------------------------- ("csub_emp")
      #"csub" "g" #"id" = "g":
      #"sub" "G" (#"conc" "G'" #"emp")
  ];
  [:= "G1": #"env", "G2": #"env", "G3": #"env",
      "H1": #"env", "H2": #"env", "H3": #"env",
      "g1": #"sub" "G1" "G2", "g2": #"sub" "G2" "G3",
      "h1": #"sub" "H1" "H2", "h2": #"sub" "H2" "H3"
      ----------------------------------------------- ("csub_subst_cmp")
      #"csub" (#"cmp" "g1" "g2") (#"cmp" "h1" "h2") =
      #"cmp" (#"csub" "g1" "h1") (#"csub" "g2" "h2"):
      #"sub" (#"conc" "G1" "H1") (#"conc" "G3" "H3")
  ];
  [:= "G": #"env", "G'": #"env",
      "H": #"env", "H'": #"env",
      "V": #"env",
      "g": #"sub" "G" "G'",
      "h": #"sub" "H" "H'",
      "A": #"ty",
      "v": #"val" "H" "A"
      ----------------------------------------------- ("conc_sub_snoc")
      #"csub" "g" (#"snoc" "h" "v") =
      #"snoc" (#"csub" "g" "h") "v":
      #"sub" (#"conc" "G" "H")
             (#"conc" "G'" (#"ext" "H'" "A"))
  ];

  [:| "G": #"env", "H": #"env",
      "A": #"ty", "B": #"ty"
      -----------------------------------------------
      #"exch" "G" "H" "A" "B":
      #"sub" (#"conc" (#"ext" (#"ext" "G" "A") "B") "H")
             (#"conc" (#"ext" (#"ext" "G" "B") "A") "H")
  ];
  [:= "G": #"env", "H": #"env",
      "V": #"env", "W": #"env",
      "A": #"ty", "B": #"ty",
      "v": #"val" "V" "A",
      "w": #"val" "W" "B"
      ----------------------------------------------- ("exch_spec")
      #"cmp" (#"csub" (#"snoc" (#"snoc" #"id" "v") "w") #"id")
             (#"exch" "G" "H" "A" "B") =
      #"csub" (#"snoc" (#"snoc" #"id" "w") "v") #"id" :
      #"sub" (#"conc" "G" "H")
             (#"conc" (#"ext" (#"ext" "G" "B") "A") "H")
  ]

  ]}.

(*TODO: use elab_lang notation?*)
(*
Derive linear_value_subst
       SuchThat (elab_lang_ext [] linear_value_subst_def linear_value_subst)
       As linear_value_subst_wf.
Proof.
  (* auto_elab. *)
  Print auto_elab.
setup_elab_lang.
  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  Print break_elab_rule.
  - eapply eq_term_rule.
    + break_down_elab_ctx.
    + break_elab_sort.
    + try_break_elab_term.
      * eredex_steps_with linear_value_subst "conc_emp".
      * term_refl.
    + try_break_elab_term.
        (* {solve_in. }
        eapply elab_args_cons_ex; cycle 1.
        1: eapply elab_args_cons_ex; cycle 1.
        1: eapply elab_args_cons_im.
        1: eapply elab_args_cons_im.
        1: eapply elab_args_cons_im.
        1: eapply elab_args_cons_im.
        1: eapply elab_args_nil.
        -- shelve.
        -- shelve.
        -- shelve.
        -- shelve.
        -- try_break_elab_term.
        -- try_break_elab_term.
      * compute_eq_compilation.
      * solve_in.
      * Print elab_args.
        eapply elab_args_cons_ex.
         [ break_down_elab_ctx
         | break_elab_sort
         | try_break_elab_term
         | try_break_elab_term ]. *)
  - Print break_elab_rule.
    eapply eq_term_rule.
    + break_down_elab_ctx.
    + break_elab_sort.
    + Print try_break_elab_term.
      Print elab_term.
      eapply elab_term_conv.
      *              (eapply elab_term_by; [ solve_in | break_down_elab_args ]).
      * sort_cong.
        Print process_eq_term.
        -- cbn_eq_goal. by_reduction. (* this should work but doesn't *)
          [ (eapply elab_term_var; [ solve_in ]) ||
              (eapply elab_term_by; [ solve_in | break_down_elab_args ])
          | try (sort_cong; repeat process_eq_term) ]
             [ break_down_elab_ctx
         | break_elab_sort
         | try_break_elab_term
         | try_break_elab_term ].

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).

  - (first
   [ unshelve (solve
	  [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab ]).
Qed.
#[export] Hint Resolve linear_value_subst_wf : elab_pfs.


Definition linear_exp_subst_def : lang :=
  {[l
      [s| "G" : #"env", "A" : #"ty"
          -----------------------------------------------
          #"exp" "G" "A" srt
      ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty", "e" : #"exp" "G'" "A"
       -----------------------------------------------
       #"exp_subst" "g" "e" : #"exp" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "e" : #"exp" "G" "A"
       ----------------------------------------------- ("exp_subst_id")
       #"exp_subst" #"id" "e" = "e" : #"exp" "G" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty", "e" : #"exp" "G3" "A"
       ----------------------------------------------- ("exp_subst_cmp")
       #"exp_subst" "f" (#"exp_subst" "g" "e")
       = #"exp_subst" (#"cmp" "f" "g") "e"
       : #"exp" "G1" "A"
  ];
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env",
       "g" : #"sub" "G1" "G2",
       "A" : #"ty", "v" : #"val" "G2" "A"
       ----------------------------------------------- ("exp_subst_ret")
       #"exp_subst" "g" (#"ret" "v")
       = #"ret" (#"val_subst" "g" "v")
       : #"exp" "G1" "A"
  ]
  ]}.


Derive linear_exp_subst
       SuchThat (elab_lang_ext linear_value_subst linear_exp_subst_def linear_exp_subst)
       As linear_exp_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve linear_exp_subst_wf : elab_pfs.
*)