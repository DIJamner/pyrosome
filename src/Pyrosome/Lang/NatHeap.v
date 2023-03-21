Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleUnit SimpleEvalCtx.
Import Core.Notations.

Require Coq.derive.Derive.

Definition nat_lang_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"natural" srt
  ];
  [:|  
       -----------------------------------------------
       #"0" : #"natural"
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"1+" "n" : #"natural"
  ];
  [s|  "n": #"natural", "m": #"natural"
       -----------------------------------------------
       #"neq" "n" "m" srt
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"neq_0_l" : #"neq" #"0" (#"1+" "n")
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"neq_0_r" : #"neq" (#"1+" "n") #"0"
  ];
  [:|  "n": #"natural", "m": #"natural",
       "p" : #"neq" "n" "m"
       -----------------------------------------------
       #"neq_1+" "p" : #"neq" (#"1+" "n") (#"1+" "m")
  ]
  ]}.


Derive nat_lang
       SuchThat (elab_lang_ext [] nat_lang_def nat_lang)
       As nat_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_lang_wf : elab_pfs.

Definition nat_exp_def : lang :=
  {[l/subst
  [:|
      -----------------------------------------------
      #"nat" : #"ty"
  ];
  [:|  "G" : #"env", "n": #"natural"
       -----------------------------------------------
       #"nv" "n" : #"val" "G" #"nat"
  ]]}.


Derive nat_exp
       SuchThat (elab_lang_ext (nat_lang ++ value_subst)
                               nat_exp_def
                               nat_exp)
       As nat_exp_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_exp_wf : elab_pfs.
  
(*TODO: might need set empty 0 = empty axiom *)
Definition heap_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"heap" srt
  ];
  [:| 
       -----------------------------------------------
       #"hempty" : #"heap"
  ];
  [:|  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural"
       -----------------------------------------------
       #"hset" "H" "l" "n" : #"heap"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural",
       "m" : #"natural"
       ----------------------------------------------- ("heap_shadow")
       #"hset" (#"hset" "H" "l" "n") "l" "m"
       = #"hset" "H" "l" "m"
       : #"heap"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural",
       "l'" : #"natural",      
       "m" : #"natural",        
       "p_neq" : #"neq" "n" "m"
       ----------------------------------------------- ("heap_comm")
       #"hset" (#"hset" "H" "l" "n") "l'" "m"
       = #"hset" (#"hset" "H" "l'" "m") "l" "n"
       : #"heap"
  ];
  [:|  "H" : #"heap",
       "l" : #"natural"
       -----------------------------------------------
       #"lookup" "H" "l" : #"natural"
  ];   
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural"
       ----------------------------------------------- ("lookup_found")
       #"lookup" (#"hset" "H" "l" "n") "l" = "n"
       : #"natural"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural",
       "l'" : #"natural",      
       "p_neq" : #"neq" "l" "l'"
       ----------------------------------------------- ("lookup_miss")
       #"lookup" (#"hset" "H" "l" "n") "l'"
       = #"lookup" "H" "l'"
       : #"natural"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural"
       ----------------------------------------------- ("lookup_empty")
       #"lookup" #"hempty" "l" = #"0"
       : #"natural"
  ]
  ]}.


Derive heap
       SuchThat (elab_lang_ext nat_lang
                               heap_def
                               heap)
       As heap_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve heap_wf : elab_pfs.

(*simple heap operations w/axioms avoiding an explicit heap 
  TODO: depends on let, unit, natural numbers, nat-as-exp
  TODO: subst rules
*)
Definition heap_ops_def : lang :=
  {[l/subst
  [:|  "G" : #"env",
       "e" : #"exp" "G" #"nat",
       "e'" : #"exp" "G" #"nat"
       -----------------------------------------------
       #"set" "e" "e'" : #"exp" "G" #"unit"
  ];
  [:|  "G" : #"env",
       "e" : #"exp" "G" #"nat"
       -----------------------------------------------
       #"get" "e" : #"exp" "G" #"nat"
  ];
  [s|  "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"configuration" "G" "A" srt
  ];
  [:|  "H" : #"heap",
       "G" : #"env", "A" : #"ty",
       "e" : #"exp" "G" "A"
       -----------------------------------------------
       #"config" "H" "e" : #"configuration" "G" "A"
  ];  
  [:=  "H" : #"heap",
       "n" : #"natural",
       "m" : #"natural",
       "G" : #"env"
       ----------------------------------------------- ("eval get")
       #"config" "H" (#"get" (#"ret" (#"nv" "n")))
       = #"config" "H" (#"ret" (#"nv" (#"lookup" "H" "n")))
       : #"configuration" "G" #"nat"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural",
       "G" : #"env"
       ----------------------------------------------- ("eval set")
       #"config" "H" (#"set" (#"ret" (#"nv" "l")) (#"ret" (#"nv" "n")))
       = #"config" (#"hset" "H" "l" "n") (#"ret" #"tt")
       : #"configuration" "G" #"unit"
  ]
  ]}.

Derive heap_ops
       SuchThat (elab_lang_ext (unit_lang ++ heap ++ nat_exp++ nat_lang ++ exp_subst ++ value_subst)
                               heap_ops_def
                               heap_ops)
       As heap_ops_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve heap_ops_wf : elab_pfs.

Definition heap_ctx_def : lang :=
  {[l
  [:|  "G" : #"env",
       "A" : #"ty",
       "E" : #"Ectx" "G" "A" #"nat",
       "e'" : #"exp" "G" #"nat"
       -----------------------------------------------
       #"Eset_l" "E" "e'" : #"Ectx" "G" "A" #"unit"
  ];
  [:|  "G" : #"env",
       "A" : #"ty",
       "v" : #"val" "G" #"nat",
       "E" : #"Ectx" "G" "A" #"nat"
       -----------------------------------------------
       #"Eset_r" "v" "E" : #"Ectx" "G" "A" #"unit"
  ];
  [:|  "G" : #"env",
       "A" : #"ty",
       "E" : #"Ectx" "G" "A" #"nat"
       -----------------------------------------------
       #"Eget" "E" : #"Ectx" "G" "A" #"nat"
  ];
  [:=  "G" : #"env",
       "A" : #"ty",
       "E" : #"Ectx" "G" "A" #"nat",
       "e" : #"exp" "G" "A"
       ----------------------------------------------- ("plug Eget")
       #"plug" (#"Eget" "E") "e"
       = #"get" (#"plug" "E" "e")
       : #"exp" "G" #"nat"
  ];
  [:=  "G" : #"env",
       "A" : #"ty",
       "E" : #"Ectx" "G" "A" #"nat",
       "e'" : #"exp" "G" #"nat",
       "e" : #"exp" "G" "A"
       ----------------------------------------------- ("plug Eset_l")
       #"plug" (#"Eset_l" "E" "e'") "e"
       = #"set" (#"plug" "E" "e") "e'"
       : #"exp" "G" #"unit"
  ];
  [:=  "G" : #"env",
       "A" : #"ty",
       "v" : #"val" "G" #"nat",
       "E" : #"Ectx" "G" "A" #"nat",
       "e" : #"exp" "G" "A"
       ----------------------------------------------- ("plug Eset_r")
       #"plug" (#"Eset_r" "v" "E") "e"
       = #"set" (#"ret" "v") (#"plug" "E" "e")
       : #"exp" "G" #"unit"
  ];
  [:=  "H" : #"heap",
       "n" : #"natural",
       "m" : #"natural",
       "G" : #"env",
       "A" : #"ty",
       "E" : #"Ectx" "G" #"nat" "A"
       ----------------------------------------------- ("eval E get")
       #"config" "H" (#"plug" "E" (#"get" (#"ret" (#"nv" "n"))))
       = #"config" "H" (#"plug" "E" (#"ret" (#"nv" (#"lookup" "H" "n"))))
       : #"configuration" "G" "A"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural",
       "G" : #"env",
       "A" : #"ty",
       "E" : #"Ectx" "G" #"unit" "A"
       ----------------------------------------------- ("eval E set")
       #"config" "H" (#"plug" "E" (#"set" (#"ret" (#"nv" "l")) (#"ret" (#"nv" "n"))))
       = #"config" (#"hset" "H" "l" "n") (#"plug" "E" (#"ret" #"tt"))
       : #"configuration" "G" "A"
  ]
  ]}.

Derive heap_ctx
       SuchThat (elab_lang_ext (eval_ctx ++ heap_ops
                                  ++ unit_lang
                                  ++ heap ++ nat_exp
                                  ++ nat_lang ++ exp_subst
                                  ++ value_subst)
                               heap_ctx_def
                               heap_ctx)
       As heap_ctx_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve heap_ctx_wf : elab_pfs.
