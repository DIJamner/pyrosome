Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst SimpleVCC SimpleVFixCC SimpleVCPSHeap SimpleUnit SimpleVCCHeap SimpleVCPS Matches NatHeap Linter Compilers ElabCompilers.
Import Core.Notations.
Import CompilerDefs.Notations.
Local Notation compiler := (compiler string).

Require Coq.derive.Derive.

Locate nat_exp.

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
        "z" : #"cmd",
        "nz" : #"cmd"
      -----------------------------------------------
      #"if0" "e" "z" "nz" : #"cmd"
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
        "z" : #"cmd",
        "nz" : #"cmd",
        "c" : #"cmd",
        "p_neq" : #"neq" #"0" (#"eval" "H" "e")
      ----------------------------------------------- ("ss_seq_if_nonzero")
      #"config" "H" (#"seq" (#"if0" "e" "z" "nz") "c")
      = #"config" "H" (#"seq" "nz" "c"): #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "z" : #"cmd",
        "nz" : #"cmd",
        "c" : #"cmd",
        "p_eq" : #"eq" #"0" (#"eval" "H" "e")
      ----------------------------------------------- ("ss_seq_if_zero")
      #"config" "H" (#"seq" (#"if0" "e" "z" "nz") "c")
      = #"config" "H" (#"seq" "z" "c") : #"configuration"
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

Definition jmp_hd :=
  {{e #"jmp" #"hd" #"tt" }}.

Definition seq c1 c2 :=
  {{e #"blk_subst" (#"snoc" #"wkn" (#"closure" #"unit" {c2} #"hd")) {c1} }}.

Definition target_eval_ctx_def : lang :=
  {[l
    [s|
      -----------------------------------------------
      #"Ectx" srt
    ];
    [:|
      -----------------------------------------------
      #"[ ]" : #"Ectx"
    ];
    [:|
      "E" : #"Ectx",
      "e" : #"exp" #"emp" #"natural"
      ----------------------------------------------- 
      #"plug" "E" "e" : #"exp" #"emp" #"natural"
    ];
    [s|
      -----------------------------------------------
      #"Sctx" srt
    ];
    [:|
      "B" : #"Bctx",
      "e" : #"exp" #"emp" #"natural"
      ----------------------------------------------- 
      #"plug" "B" "e" : #"blk" (#"ext" #"emp" (#"neg" #"unit"))
    ];
    [:|
      "E" : #"Ectx",
      "z" : #"blk",
      "nz" : #"blk"
      -----------------------------------------------
      #"Eif0" "E" "z" "nz" : #"Bctx"
    ];
    [:|
      "vl" : #"val" #"emp" #"nat",
      "E" : #"Ectx",
      "e" : #"blk" (#"ext" #"emp" (#"neg" #"unit"))
      -----------------------------------------------
      #"Eset" "vl" "E" "e" : #"Bctx"
    ];

    [:|
      "x" : #"natural",
      "E" : #"Ectx"
      -----------------------------------------------
      #"Eset" "x" "E" : #"Bctx"
    ]
  ]}.

Definition forget2 blk :=
  {{e #"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {blk} }}.

Definition env_with_context :=
  {{e #"ext "#"emp" (#"neg" #"unit")}}.

Definition if0_exp e z nz :=
  {{e #"blk_subst"
      { e }
      (#"jmp"
        (#"closure"
          #"natural"
          (#"if0" (#".2" #"hd") {forget2 z }  {forget2 nz })
          #"tt")
        #"hd")}}.

Definition ch8_cc_def : compiler :=
  match # from (ch8_config ++ nat_eq ++ ch8 ++ heap ++ nat_lang) with
  | {{s #"exp"}} => {{s #"sub" {env_with_context} (#"ext" {env_with_context} #"natural") }}
  | {{s #"cmd"}} => {{s #"blk" {env_with_context} }}
  | {{s #"configuration"}} => {{s #"configuration" {env_with_context} }}
  | {{e #"value" "n"}} => {{e #"snoc" #"id" "n"}}
  | {{e #"hvar" "n"}} => {{e  #"snoc" #"id" (#"hvar" "n")}}
  | {{e #"skip"}} => jmp_hd
  | {{e #"assign" "x" "e" }} => {{e #"set" "x" "e" {jmp_hd} }}
  | {{e #"seq" "cmd1" "cmd2"}} => seq {{e "cmd1"}} (seq {{e "cmd2"}} jmp_hd)
  | {{e #"if0" "e" "z" "nz"}} => seq (if0_exp {{e "e"}} {{e "n"}} {{e "nz"}}) jmp_hd
  | {{e #"while" "e" "c"}} =>
      {{e #"jmp" (#"fix"
                   (#"closure"
                     (#"pair" (#"neg" #"unit") #"unit")
                     {if0_exp
                        {{e "e"}}
                        jmp_hd
                        (seq {{e "c" }} {{e #"jmp" (#".1" #"hd") #"tt" }})}
                     #"tt")
                   #"tt")
          #"tt"
      }}
  | {{e #"eval" "H" "e"}} => {{e #"get" "H" "e"}}
  | {{e #"config" "H" "c"}} => {{e #"config" "H" "c"}}
  end.

Definition target_lang : lang :=
(fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                forget_eq_wkn'++
                                cps_prod_lang ++ block_subst ++ value_subst).

Compute target_lang.

Derive ch8_cc
       SuchThat (elab_preserving_compiler
                   []
                   target_lang
                   ch8_cc_def
                   ch8_cc
                   (ch8_config++nat_eq++ch8++heap++nat_lang))
       As ch8_cc_preserving.
Proof.
auto_elab_compiler.
  cleanup_elab_after
    (reduce; eredex_steps_with unit_eta "unit eta").
Qed.
#[export] Hint Resolve subst_cc_preserving : elab_pfs.


