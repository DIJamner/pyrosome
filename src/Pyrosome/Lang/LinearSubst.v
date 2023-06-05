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

  [:| "G": #"env", "H": #"env"
      -----------------------------------------------
      #"conc" "G" "H": #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("conc_emp")
      #"conc" "G" #"emp" = "G" : #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("emp_conc")
      #"conc" #"emp" "G" = "G" : #"env"
  ];
  [:= "G": #"env", "H": #"env", "A": #"ty"
      ----------------------------------------------- ("conc_ext_right")
      #"conc" "G" (#"ext" "H" "A") =
      #"ext" (#"conc" "G" "H") "A" : #"env"
  ];
  [:= "G1": #"env", "G2": #"env", "G3": #"env"
      ----------------------------------------------- ("conc_assoc")
      #"conc" (#"conc" "G1" "G2") "G3" =
      #"conc" "G1" (#"conc" "G2" "G3") : #"env"

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

  [:| "G" : #"env", "G'" : #"env", "V": #"env",
      "A" : #"ty",
      "g" : #"sub" "G" "G'",
      "v" : #"val" "V" "A" (*we restrict substitutions to values *)
       -----------------------------------------------
       #"snoc" "g" "v" : #"sub" (#"conc" "G" "V") (#"ext" "G'" "A")
  ];
  [:|  "A" : #"ty"
       -----------------------------------------------
       #"hd" : #"val" (#"ext" #"emp" "A") "A"
  ];
  [:= "V" : #"env",
      "A" : #"ty",
      "v" : #"val" "V" "A"
      ----------------------------------------------- ("snoc_hd")
      #"val_subst" (#"snoc" #"id" "v") #"hd" = "v"
      : #"val" "V" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
      "f" : #"sub" "G1" "G2",
      "g" : #"sub" "G2" "G3",
      "V" : #"env",
      "A" : #"ty",
      "v" : #"val" "V" "A"
      ----------------------------------------------- ("cmp_snoc")
      #"cmp" (#"csub" "f" #"id") (#"snoc" "g" "v")
      = #"snoc" (#"cmp" "f" "g") "v"
      : #"sub" (#"conc" "G1" "V") (#"ext" "G3" "A")
  ];
  [:= "G": #"env", "G'": #"env",
      "H": #"env", "H'": #"env",
      "V": #"env",
      "g": #"sub" "G" "G'",
      "h": #"sub" "H" "H'",
      "A": #"ty",
      "v": #"val" "V" "A"
      ----------------------------------------------- ("csub_snoc")
      #"csub" "g" (#"snoc" "h" "v") =
      #"snoc" (#"csub" "g" "h") "v":
      #"sub" (#"conc" "G" (#"conc" "H" "V"))
             (#"ext" (#"conc" "G'" "H'") "A")
  ];

  [:= "G": #"env", "H": #"env",
      "X": #"env", "Y": #"env"
      ----------------------------------------------- ("env_exch")
      #"conc" (#"conc" (#"conc" "G" "X") "Y") "H" =
      #"conc" (#"conc" (#"conc" "G" "Y") "X") "H" : #"env"
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
      ----------------------------------------------- ("snoc_exch")
      #"cmp" (#"csub" (#"snoc" (#"snoc" #"id" "v") "w") #"id")
             (#"exch" "G" "H" "A" "B") =
      #"csub" (#"snoc" (#"snoc" #"id" "w") "v") #"id" :
      #"sub" (#"conc" (#"conc" (#"conc" "G" "V") "W") "H")
             (#"conc" (#"ext" (#"ext" "G" "B") "A") "H")
  ]

  ]}.

(*TODO: use elab_lang notation?*)
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

  - eapply eq_term_rule.
    + break_down_elab_ctx.
    + break_elab_sort.
    + unshelve try_break_elab_term.
      all: try lazymatch goal with
             | |- term => shelve
             | |- wf_term _ _ _ _ => shelve
           end.
      3:eredex_steps_with linear_value_subst "conc_emp".
      3:term_refl.
      all: term_refl.
    + try_break_elab_term.

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

  - eapply eq_term_rule.
    + break_down_elab_ctx.
    + break_elab_sort.
    + unshelve try_break_elab_term.
      all: try lazymatch goal with
             | |- term => shelve
             | |- wf_term _ _ _ _ => shelve
           end.
      4:eredex_steps_with linear_value_subst "emp_conc".
      all: term_refl.
    + try_break_elab_term.

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

  - eapply eq_term_rule.
    + break_down_elab_ctx.
    + break_elab_sort.
    + unshelve try_break_elab_term.
      all: try lazymatch goal with
             | |- term => shelve
             | |- wf_term _ _ _ _ => shelve
           end.
      all: term_refl.
    + unshelve try_break_elab_term.
      all: try lazymatch goal with
             | |- term => shelve
             | |- wf_term _ _ _ _ => shelve
           end.
      5:eredex_steps_with linear_value_subst "env_exch".
      all: term_refl.

Unshelve.
all: cleanup_auto_elab.

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