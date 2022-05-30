Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst Matches NatHeap Linter.
Import Core.Notations.

Require Coq.derive.Derive.

Definition ch8_def : lang :=
  {[l
      [s| 
      -----------------------------------------------
        #"exp" srt
      ];
    [:| "n" : #"natural"
      -----------------------------------------------
      #"value" "n" : #"exp"
    ];
    [:| "n" : #"natural"
      -----------------------------------------------
      #"hvar" "n" : #"exp"
    ];
    [s| 
      -----------------------------------------------
      #"cmd" srt 
      ];
    [:|
       -----------------------------------------------
      #"skip" : #"cmd" 
   ];
    [:| 
        "x" : #"natural",
        "e" : #"exp"
        -----------------------------------------------
      #"assign" "x" "e" : #"cmd"
  ];
    [:| 
        "cmd1" : #"cmd",
        "cmd2" : #"cmd"
      -----------------------------------------------
      #"seq" "cmd1" "cmd2" : #"cmd" 
   ];     
    [:| "e" : #"exp", 
        "t" : #"cmd",
        "f" : #"cmd"
      -----------------------------------------------
      #"if" "e" "t" "f" : #"cmd"
    ];

    [:| "e" : #"exp", 
        "c" : #"cmd"
      -----------------------------------------------
      #"while" "e" "c" : #"cmd"
    ];
    [:| "H" : #"heap",
        "e" : #"exp"
      -----------------------------------------------
      #"eval" "H" "e" : #"natural"
    ];
    [:= "H" : #"heap",
        "n" : #"natural"
      ----------------------------------------------- ("eval_value")
      #"eval" "H" (#"value" "n") = "n" : #"natural"
    ];
    [:= "H" : #"heap",
        "n" : #"natural"
      ----------------------------------------------- ("eval_var")
      #"eval" "H" (#"hvar" "n") = #"lookup" "H" "n" : #"natural"
    ]
    ]}.

Derive ch8
       SuchThat (elab_lang_ext (heap++nat_lang) ch8_def ch8)
       As ch8_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve ch8_wf : elab_pfs.

Definition nat_eq_def : lang :=
  {[l
    [s| "n" : #"natural",
        "m" : #"natural"
      -----------------------------------------------
      #"eq" "n" "m" srt
    ];
    [:| "n": #"natural"
      -----------------------------------------------
      #"eq_0_0" : #"eq" #"0" #"0"
    ];
    [:| "n": #"natural", "m": #"natural",
        "p" : #"eq" "n" "m"
      -----------------------------------------------
      #"eq_1+" "p" : #"eq" (#"1+" "n") (#"1+" "m")
    ]
  ]}.

Derive nat_eq
       SuchThat (elab_lang_ext (nat_lang) nat_eq_def nat_eq)
       As nat_eq_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_eq_wf : elab_pfs.

Definition ch8_config_def : lang := 
  {[l
    [s| 
      -----------------------------------------------
      #"configuration" srt
    ];
    [:| "H" : #"heap",
        "c" : #"cmd"
      ----------------------------------------------- 
      #"config" "H" "c" : #"configuration"
    ];
    [:= "H" : #"heap",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_skip")
      #"config" "H" (#"seq" #"skip" "c") = #"config" "H" "c" : #"configuration"
    ];
    [:= "H" : #"heap",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_skip_seq")
      #"config" "H" (#"seq" "c" #"skip") = #"config" "H" "c" : #"configuration"
    ];
    (* TODO: The following rules are a hacky workaround for not being able to
     express (H, c1) -> (H', c1') in the context. This should be improved. *)
    [:= "H" : #"heap",
        "e" : #"exp",
        "x" : #"natural",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_assign")
      #"config" "H" (#"seq" (#"assign" "x" "e") "c")
      = #"config" (#"hset" "H" "x" (#"eval" "H" "e")) "c" : #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "t" : #"cmd",
        "f" : #"cmd",
        "c" : #"cmd",
        "p_neq" : #"neq" #"0" (#"eval" "H" "e")
      ----------------------------------------------- ("ss_seq_if_true")
      #"config" "H" (#"seq" (#"if" "e" "t" "f") "c")
      = #"config" "H" (#"seq" "t" "c"): #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "t" : #"cmd",
        "f" : #"cmd",
        "c" : #"cmd",
        "p_eq" : #"eq" #"0" (#"eval" "H" "e")
      ----------------------------------------------- ("ss_seq_if_false")
      #"config" "H" (#"seq" (#"if" "e" "t" "f") "c")
      = #"config" "H" (#"seq" "f" "c") : #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "c1" : #"cmd",
        "c2" : #"cmd",
        "p_neq" : #"neq" #"0" (#"eval" "H" "e")
      ----------------------------------------------- ("ss_seq_while_true")
      #"config" "H" (#"seq" (#"while" "e" "c1") "c2")
      = #"config" "H" (#"seq" "c1" (#"seq" (#"while" "e" "c1") "c2")) : #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "c1" : #"cmd",
        "c2" : #"cmd",
        "p_eq" : #"eq" #"0" (#"eval" "H" "e")
      ----------------------------------------------- ("ss_seq_while_false")
      #"config" "H" (#"seq" (#"while" "e" "c1") "c2")
      = #"config" "H" "c2" : #"configuration"
    ];
    [:= "H" : #"heap",
        "c1" : #"cmd",
        "c2" : #"cmd",
        "c3" : #"cmd"
      ----------------------------------------------- ("ss_seq_seq")
      #"config" "H" (#"seq" (#"seq" "c1" "c2") "c3")
      = #"config" "H" (#"seq" "c1" (#"seq" "c2" "c3")) : #"configuration"
    ]
  ]}.

Derive ch8_config
       SuchThat (elab_lang_ext (nat_eq ++ ch8 ++ heap++nat_lang) ch8_config_def ch8_config)
       As ch8_config_wf.
Proof.  auto_elab. Qed.
#[export] Hint Resolve ch8_config_wf : elab_pfs.

