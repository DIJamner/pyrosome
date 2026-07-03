From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import PolySubst SimpleVSubst SimpleUnit SimpleEvalCtx.
Import Core.Notations.

From Stdlib Require derive.Derive.

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

Definition nat_lang_injectivity :=
  [("1+", ["n"]); ("neq_0_l", ["n"]); ("neq_0_r", ["n"]); ("neq", ["m"; "n"]); ("neq_1+", ["p"; "m"; "n"])].

Definition nat_lang :=
  Eval vm_compute in
    (infer_lang_ext_simple [] nat_lang_def nat_lang_injectivity).

Lemma nat_lang_wf : wf_lang_ext [] nat_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition nat_lang_entry := lang_entry nat_lang_wf.
#[export] Hint Resolve nat_lang_entry : wf_lang_db.

Definition nat_exp_def : lang :=
  {[l/subst [nat_lang ++ value_subst]
  [:|
      -----------------------------------------------
      #"nat" : #"ty"
  ];
  [:|  "G" : #"env", "n": #"natural"
       -----------------------------------------------
       #"nv" "n" : #"val" "G" #"nat"
  ]]}.

Definition nat_exp_injectivity :=
  [("val_subst", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("neq_1+", ["p"; "m"; "n"]); ("cmp", ["G3"; "G1"]);
   ("neq_0_r", ["n"]); ("nv", ["n"; "G"]); ("wkn", ["A"; "G"]); ("neq_0_l", ["n"]); ("ext", ["A"; "G"]); ("1+", ["n"]);
   ("sub", ["G'"; "G"]); ("val", ["A"; "G"]); ("id", ["G"]); ("hd", ["A"; "G"]); ("forget", ["G"]); ("neq", ["m"; "n"])].

Definition nat_exp :=
  Eval vm_compute in
    (infer_lang_ext_simple (nat_lang ++ value_subst) nat_exp_def nat_exp_injectivity).

Lemma nat_exp_wf : wf_lang_ext (nat_lang ++ value_subst) nat_exp.
Proof. compute_wf_lang. Qed.
#[local] Definition nat_exp_entry := lang_entry nat_exp_wf.
#[export] Hint Resolve nat_exp_entry : wf_lang_db.
  
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

Definition heap_injectivity :=
  [("lookup", ["l"]); ("neq_0_r", ["n"]); ("neq", ["m"; "n"]); ("1+", ["n"]); ("neq_1+", ["p"; "m"; "n"]); ("neq_0_l", ["n"])].

Definition heap :=
  Eval vm_compute in
    (infer_lang_ext_simple nat_lang heap_def heap_injectivity).

Lemma heap_wf : wf_lang_ext nat_lang heap.
Proof. compute_wf_lang. Qed.
#[local] Definition heap_entry := lang_entry heap_wf.
#[export] Hint Resolve heap_entry : wf_lang_db.

Definition heap_ops_def : lang :=
  {[l/subst [unit_lang ++ heap ++ nat_exp++ nat_lang ++ exp_subst ++ value_subst]
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

Definition heap_ops_injectivity :=
  [("tt", ["G"]); ("hd", ["A"; "G"]); ("ret", ["v"; "A"; "G"]); ("cmp", ["G3"; "G1"]); ("neq_0_r", ["n"]);
   ("val", ["A"; "G"]); ("id", ["G"]); ("lookup", ["l"]); ("nv", ["n"; "G"]); ("neq", ["m"; "n"]);
   ("configuration", ["A"; "G"]); ("1+", ["n"]); ("ext", ["A"; "G"]); ("config", ["A"; "G"]); ("exp_subst", ["A"; "G"]);
   ("neq_1+", ["p"; "m"; "n"]); ("val_subst", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("set", ["e'"; "e"; "G"]);
   ("sub", ["G'"; "G"]); ("get", ["e"; "G"]); ("neq_0_l", ["n"]); ("exp", ["A"; "G"]); ("forget", ["G"]); ("wkn", ["A"; "G"])].

Definition heap_ops :=
  Eval vm_compute in
    (infer_lang_ext_simple (unit_lang ++ heap ++ nat_exp++ nat_lang ++ exp_subst ++ value_subst) heap_ops_def heap_ops_injectivity).

Lemma heap_ops_wf : wf_lang_ext (unit_lang ++ heap ++ nat_exp++ nat_lang ++ exp_subst ++ value_subst) heap_ops.
Proof. compute_wf_lang. Qed.
#[local] Definition heap_ops_entry := lang_entry heap_ops_wf.
#[export] Hint Resolve heap_ops_entry : wf_lang_db.

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

Definition heap_ctx_injectivity :=
  [("exp_subst", ["A"; "G"]); ("ext", ["A"; "G"]); ("[ ]", ["A"; "G"]); ("id", ["G"]); ("config", ["A"; "G"]);
   ("Eset_l", ["e'"; "E"; "A"; "G"]); ("neq_0_l", ["n"]); ("Ectx", ["B"; "A"; "G"]); ("sub", ["G'"; "G"]); ("hd", ["A"; "G"]);
   ("Eget", ["E"; "A"; "G"]); ("get", ["e"; "G"]); ("cmp", ["G3"; "G1"]); ("set", ["e'"; "e"; "G"]); ("neq_1+", ["p"; "m"; "n"]);
   ("nv", ["n"; "G"]); ("val", ["A"; "G"]); ("wkn", ["A"; "G"]); ("configuration", ["A"; "G"]); ("forget", ["G"]); ("lookup", ["l"]);
   ("plug", ["e"; "E"; "B"; "A"; "G"]); ("val_subst", ["A"; "G"]); ("neq_0_r", ["n"]); ("exp", ["A"; "G"]); ("tt", ["G"]);
   ("neq", ["m"; "n"]); ("ret", ["v"; "A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("Eset_r", ["E"; "v"; "A"; "G"]); ("1+", ["n"])].

Definition heap_ctx :=
  Eval vm_compute in
    (infer_lang_ext_simple (eval_ctx ++ heap_ops
                                  ++ unit_lang
                                  ++ heap ++ nat_exp
                                  ++ nat_lang ++ exp_subst
                                  ++ value_subst) heap_ctx_def heap_ctx_injectivity).

Lemma heap_ctx_wf : wf_lang_ext (eval_ctx ++ heap_ops
                                  ++ unit_lang
                                  ++ heap ++ nat_exp
                                  ++ nat_lang ++ exp_subst
                                  ++ value_subst) heap_ctx.
Proof. compute_wf_lang. Qed.
#[local] Definition heap_ctx_entry := lang_entry heap_ctx_wf.
#[export] Hint Resolve heap_ctx_entry : wf_lang_db.
