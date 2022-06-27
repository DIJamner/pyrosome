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
Require Coq.derive.Derive.
Notation compiler := (compiler string).

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
        "v" : #"natural",
        "x" : #"natural",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_assign")
      #"config" "H" (#"seq" (#"assign" "x" (#"value" "v")) "c")
      = #"config" (#"hset" "H" "x" "v") "c" : #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "z" : #"cmd",
        "nz" : #"cmd",
        "c" : #"cmd",
        "n" : #"natural"
      ----------------------------------------------- ("ss_seq_if_nonzero")
      #"config" "H" (#"seq" (#"if0" (#"value" (#"1+" "n"))"z" "nz") "c")
      = #"config" "H" (#"seq" "nz" "c"): #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "z" : #"cmd",
        "nz" : #"cmd",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_if_zero")
      #"config" "H" (#"seq" (#"if0" (#"value" #"0") "z" "nz") "c")
      = #"config" "H" (#"seq" "z" "c") : #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "c1" : #"cmd",
        "c2" : #"cmd",
        "n" : #"natural"
      ----------------------------------------------- ("ss_seq_while_true")
      #"config" "H" (#"seq" (#"while" (#"value" (#"1+" "n")) "c1") "c2")
      = #"config" "H" (#"seq" "c1" (#"seq" (#"while" "e" "c1") "c2")) : #"configuration"
    ];
    [:= "H" : #"heap",
        "e" : #"exp",
        "c1" : #"cmd",
        "c2" : #"cmd"
      ----------------------------------------------- ("ss_seq_while_false")
      #"config" "H" (#"seq" (#"while" (#"value" #"0") "c1") "c2")
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


Definition ch8_ectx_def : lang := 
  {[l
    [s|
      -----------------------------------------------
      #"Ectx" srt
    ];
    [:|
       -----------------------------------------------
      #"[ ]" : #"Ectx"
    ];
    [s|
      -----------------------------------------------
      #"Cctx" srt
    ];
    [:| "x" : #"natural",
        "E" : #"Ectx"
        -----------------------------------------------
        #"Eassign" "x" "E" : #"Cctx"
    ];
    [:| "E" : #"Ectx", 
        "z" : #"cmd",
        "nz" : #"cmd"
      -----------------------------------------------
      #"Eif0" "E" "z" "nz" : #"Cctx"
    ];
    [:| "E" : #"Ectx", 
        "c" : #"cmd"
      -----------------------------------------------
      #"Ewhile" "E" "c" : #"Cctx"
    ];
    [:| "C" : #"Cctx", 
        "e" : #"exp"
      -----------------------------------------------
      #"Cplug" "C" "e" : #"cmd"
    ];
    [:| "E" : #"Ectx", 
        "e" : #"exp"
      -----------------------------------------------
      #"Eplug" "E" "e" : #"exp"
    ];
    [:= "e" : #"exp"
      ----------------------------------------------- ("Eplug hole")
      #"Eplug" #"[ ]" "e" = "e" : #"exp"
    ];
    [:= "x" : #"natural",
        "E" : #"Ectx",
        "e" : #"exp"
      ----------------------------------------------- ("Cplug assign")
      #"Cplug" (#"Eassign" "x" "E") "e" = #"assign" "x" (#"Eplug" "E" "e") : #"cmd"
    ];
    [:= "E" : #"Ectx",
        "z" : #"cmd",
        "nz" : #"cmd",
        "e" : #"exp"
      ----------------------------------------------- ("Cplug if0")
      #"Cplug" (#"Eif0" "E" "z" "nz") "e" = #"if0" (#"Eplug" "E" "e") "z" "nz" : #"cmd"
    ];
    [:= "E" : #"Ectx",
        "c" : #"cmd",
        "e" : #"exp"
      ----------------------------------------------- ("Cplug while")
      #"Cplug" (#"Ewhile" "E" "c") "e" = #"while" (#"Eplug" "E" "e") "c" : #"cmd"
    ];
    [:= "H" : #"heap",
        "C" : #"Cctx",
        "n" : #"natural"
      ----------------------------------------------- ("plug hvar lookup")
      #"config" "H" (#"Cplug" "C" (#"hvar" "n")) =
           #"config" "H" (#"Cplug" "C" (#"value" (#"lookup" "H" "n"))) : #"configuration"
    ]
  ]}.

Derive ch8_ectx
       SuchThat (elab_lang_ext (ch8_config ++ nat_eq ++ ch8 ++ heap++nat_lang) ch8_ectx_def ch8_ectx)
       As ch8_ectx_wf.
Proof.  auto_elab. Qed.
#[export] Hint Resolve ch8_ectx_wf : elab_pfs.

Definition jmp_hd :=
  {{e #"jmp" #"hd" #"tt" }}.

Definition seq c1 c2 :=
  {{e #"blk_subst" (#"snoc" #"wkn" (#"closure" #"unit" {c2} #"hd")) {c1} }}.

Definition cmd_env :=
  {{e #"ext" #"emp" (#"neg" #"unit")}}.

Definition exp_env :=
  {{e #"ext" #"emp" (#"neg" #"natural")}}.

Definition plug_exp e c :=
  {{e #"blk_subst"
      (#"snoc" #"wkn" (#"closure" #"natural" {c} #"tt"))
      {e} }}.

Definition assign x e :=
  plug_exp e {{e #"set" (#"nv" {x}) (#".2" #"hd") (#"jmp" (#".1" #"hd") #"tt")}}.

Definition if0 e z nz :=
  seq (plug_exp e {{e #"if0" (#".2" #"hd") {z} {nz} }}) jmp_hd.

Definition while e c :=
  {{e #"jmp" (#"fix"
               (#"closure"
                 (#"pair" (#"neg" #"unit") #"unit")
                 {plug_exp
                    e
                    {{e #"if0" (#".2" #"hd")
                        {jmp_hd}
                        {seq c {{e #"jmp" (#".1" #"hd") #"tt" }} }
                    }}
                 }
                 #"tt")
               #"tt")
      #"tt"
  }}.

Definition blk_to_val b :=
  {{e #"closure" #"unit" (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {b}) #"hd"}}.

Definition plug E v :=
  {{e #"jmp" (#"closure" (#"neg" #"unit") (#"blk_subst" (#"snoc" (#"snoc" #"wkn" (#".2" #"hd")) (#".1" #"hd")) {E}) #"hd") {v} }}.

Definition ch8_cc_def : compiler :=
  match # from (ch8_config ++ nat_eq ++ ch8 ++ heap ++ nat_lang) with
  | {{s #"exp"}} => {{s #"blk" {exp_env} }}
  | {{s #"cmd"}} => {{s #"blk" {cmd_env} }}
  | {{s #"configuration"}} => {{s #"configuration" {cmd_env} }}
  | {{s #"Ectx"}} => {{s #"blk" (#"ext" {cmd_env} (#"neg" #"natural")) }}
  | {{s #"Cctx"}} => {{s #"blk" (#"ext" {cmd_env} (#"neg" #"unit")) }}
  | {{e #"value" "n"}} => {{e #"jmp" #"hd" (#"nv" "n")}}
  | {{e #"hvar" "n"}} => {{e  #"get" (#"nv" "n") (#"jmp" (#"wkn" #"hd") #"hd")}}
  | {{e #"skip"}} => jmp_hd
  | {{e #"assign" "x" "e" }} => assign {{e "x"}} {{e "e"}}
  | {{e #"seq" "cmd1" "cmd2"}} => seq {{e "cmd1"}} (seq {{e "cmd2"}} jmp_hd)
  | {{e #"if0" "e" "z" "nz"}} => if0 {{e "e"}} {{e "z"}} {{e "nz"}}
  | {{e #"while" "e" "c"}} => while {{e "e"}} {{e "c"}}
  | {{e #"config" "H" "c"}} => {{e #"config" "H" "c"}}
  | {{e #"[ ]"}} => {{e #"jmp" (#"closure" (#"neg" #"unit") (#"jmp" (#".2" #"hd") #"tt") #"tt") (#"val_subst" #"wkn" #"hd") }}
  | {{e #"Eassign" "x" "E"}} =>
      assign {{e "x"}} (plug {{e "E"}} {{e #"val_subst" #"wkn" #"hd"}})
  | {{e #"Eif0" "E" "z" "nz"}} =>
      if0 (plug {{e "E"}} {{e #"val_subst" #"wkn" #"hd"}}) {{e "z"}} {{e "nz"}}
  | {{e #"Ewhile" "E" "c"}} =>
      while (plug {{e "E"}} {{e #"val_subst" #"wkn" #"hd"}}) {{e "c"}}
  | {{e #"Cplug" "C" "e"}} => plug {{e "C"}} (blk_to_val {{e "e"}})
  | {{e #"Eplug" "E" "e"}} => plug {{e "E"}} (blk_to_val {{e "e"}})
  end.

Definition target_lang : lang :=
(fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                forget_eq_wkn'++
                                cps_prod_lang ++ block_subst ++ value_subst).

Derive ch8_cc
       SuchThat (elab_preserving_compiler
                   []
                   target_lang
                   ch8_cc_def
                   ch8_cc
                   (ch8_config++nat_eq++ch8++heap++nat_lang))
       As ch8_cc_preserving.
Proof.
  Print auto_elab_compiler.
  Print setup_elab_compiler.
  Ltac prove_from_known_elabs := admit.
  cleanup_elab_after (match goal with
  | |- elab_preserving_compiler _ ?tgt ?cmp ?ecmp ?src =>
        rewrite (as_nth_tail cmp); rewrite (as_nth_tail ecmp);
         rewrite (as_nth_tail src);
         assert (wf_lang tgt) by prove_from_known_elabs
  end; break_preserving); repeat Matches.t.
  Print auto_elab_compiler.
  all : cleanup_elab_after try (solve [ by_reduction ]) .
  Print auto_elab_compiler.
  setup_elab_compiler.
  cleanup_elab_after setup_elab_compiler.
  auto_elab_compiler.
  cleanup_elab_after setup_elab_compiler.
    (reduce; eredex_steps_with unit_eta "unit eta").
Qed.
#[export] Hint Resolve subst_cc_preserving : elab_pfs.


