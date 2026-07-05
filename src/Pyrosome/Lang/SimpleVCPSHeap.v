From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.InjRuleGen
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS SimpleUnit NatHeap.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.

(*simple heap operations w/axioms avoiding an explicit heap *)
Definition heap_cps_ops_def : lang :=
  {[l/subst [(unit_lang ++ heap ++ nat_exp++ nat_lang ++ block_subst ++ value_subst)]
  [:|  "G" : #"env",
       "vl" : #"val" "G" #"nat",
       "vn" : #"val" "G" #"nat",
       "e" : #"blk" "G"
       -----------------------------------------------
       #"set" "vl" "vn" "e" : #"blk" "G"
  ];
  [:|  "G" : #"env",
       "v" : #"val" "G" #"nat",
       "e" : #"blk" (#"ext" "G" #"nat")
       -----------------------------------------------
       #"get" "v" "e" : #"blk" "G"
  ];
  [s|  "G" : #"env"
       -----------------------------------------------
       #"configuration" "G" srt
  ];
  [:|  "H" : #"heap",
       "G" : #"env",
       "e" : #"blk" "G"
       -----------------------------------------------
       #"config" "H" "e" : #"configuration" "G"
  ];  
  [:=  "H" : #"heap",
       "n" : #"natural",
       "m" : #"natural",
       "G" : #"env",
       "e" : #"blk" (#"ext" "G" #"nat")
       ----------------------------------------------- ("eval get")
       #"config" "H" (#"get" (#"nv" "n") "e")
       = #"config" "H" (#"blk_subst" (#"snoc" #"id" (#"nv" (#"lookup" "H" "n"))) "e")
       : #"configuration" "G"
  ];
  [:=  "H" : #"heap",
       "l" : #"natural",
       "n" : #"natural",
       "G" : #"env",
       "e" : #"blk" "G"
       ----------------------------------------------- ("eval set")
       #"config" "H" (#"set" (#"nv" "l") (#"nv" "n") "e")
       = #"config" (#"hset" "H" "l" "n") "e"
       : #"configuration" "G"
  ];
  [:|  "G" : #"env",
       "v" : #"val" "G" #"nat",
       "z" : #"blk" "G",
       "nz" : #"blk" "G"
       -----------------------------------------------
       #"if0" "v" "z" "nz" : #"blk" "G"
  ];

  [:=  "G" : #"env",
       "n" : #"natural",
       "z" : #"blk" "G",
       "nz" : #"blk" "G"
       ----------------------------------------------- ("if nonzero")
       #"if0" (#"nv" (#"1+" "n")) "z" "nz" = "nz" : #"blk" "G"
  ];
  [:=  "G" : #"env",
       "z" : #"blk" "G",
       "nz" : #"blk" "G"
       ----------------------------------------------- ("if zero")
       #"if0" (#"nv" #"0") "z" "nz" = "z" : #"blk" "G"
  ]
  ]}.

Definition heap_cps_ops_injectivity :=
  [("blk", ["G"]); ("configuration", ["G"]); ("neq_0_r", ["n"]); ("tt", ["G"]); ("val", ["A"; "G"]);
   ("get", ["e"; "v"; "G"]); ("1+", ["n"]); ("config", ["G"]); ("forget", ["G"]); ("blk_subst", ["G"]);
   ("id", ["G"]); ("if0", ["nz"; "z"; "v"; "G"]); ("wkn", ["A"; "G"]); ("ext", ["A"; "G"]);
   ("neq_1+", ["p"; "m"; "n"]); ("val_subst", ["A"; "G"]); ("neq", ["m"; "n"]);
   ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("cmp", ["G3"; "G1"]); ("set", ["e"; "vn"; "vl"; "G"]);
   ("lookup", ["l"]); ("nv", ["n"; "G"]); ("hd", ["A"; "G"]); ("sub", ["G'"; "G"]); ("neq_0_l", ["n"])].

Definition heap_cps_ops :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100
      (unit_lang ++ heap ++ nat_exp++ nat_lang ++ block_subst ++ value_subst)
      heap_cps_ops_def.

Lemma heap_cps_ops_wf
  : wf_lang_ext (unit_lang ++ heap ++ nat_exp++ nat_lang ++ block_subst ++ value_subst) heap_cps_ops.
Proof. compute_wf_lang. Qed.
#[local] Definition heap_cps_ops_entry := lang_entry heap_cps_ops_wf.
#[export] Hint Resolve heap_cps_ops_entry : wf_lang_db.

Definition heap_id_def : compiler :=
  match # from (unit_lang ++ heap ++ nat_exp++ nat_lang) with
  | {{s #"heap"}} => {{s#"heap"}}
  end.

From Pyrosome.Tools.EGraph Require Import Automation.

Derive heap_id
       in (elab_preserving_compiler cps_subst
                                          (heap_cps_ops (*TODO: remove via lemma*)
                                             ++ cps_lang (*TODO: remove via lemma*)
                                             ++ unit_lang
                                             ++ heap
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          heap_id_def
                                          heap_id
                                          (unit_lang ++ heap ++ nat_exp++ nat_lang))
       as heap_id_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition heap_id_entry :=
  cmp_entry (elab_compiler_implies_preserving heap_id_preserving).
#[export] Hint Resolve heap_id_entry : preserving_db.

Definition heap_cps_def : compiler :=
  match # from heap_ops with
  | {{s #"configuration" "G" "A"}} =>
    {{s #"configuration" (#"ext" "G" (#"neg" "A"))}}
  | {{e #"config" "H" "G" "A" "e"}} =>
    {{e #"config" "H" "e"}}
  | {{e #"get" "G" "e"}} =>
    bind_k 1 (var "e") {{e #"nat"}}
    {{e #"get" {ovar 0} (#"jmp" {ovar 2} {ovar 0})}}
  | {{e #"set" "G" "e" "e'"}} =>
    bind_k 1 (var "e") {{e #"nat"}}
    (bind_k 2 (var "e'") {{e #"nat"}}
    {{e #"set" {ovar 1} {ovar 0} (#"jmp" {ovar 2} #"tt")}})
  end.    
    
Derive heap_cps
       in (elab_preserving_compiler (heap_id++cps_subst)
                                          (heap_cps_ops
                                             ++ cps_lang
                                             ++ unit_lang
                                             ++ heap
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          heap_cps_def
                                          heap_cps
                                          heap_ops)
       as heap_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition heap_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving heap_cps_preserving).
#[export] Hint Resolve heap_cps_entry : preserving_db.

Definition Ebind_k n e A k :=
  {{e #"blk_subst" (#"snoc"
                     (#"cmp" #"wkn"
                       (#"snoc" {wkn_n n} (#"cont" {A} {k})))
                     #"hd") {e} }}.
Arguments Ebind_k n e A k/.

Definition heap_ctx_cps_def : compiler :=
  match # from heap_ctx_def with
  | {{s #"configuration" "G" "A"}} =>
    {{s #"configuration" (#"ext" "G" (#"neg" "A"))}}
  | {{e #"config" "H" "G" "A" "e"}} =>
    {{e #"config" "H" "e"}}
  | {{e #"Eget" "G" "E"}} =>
    Ebind_k 1 (var "E") {{e #"nat"}}
    {{e #"get" {ovar 0} (#"jmp" {ovar 2} {ovar 0})}}
  | {{e #"Eset_l" "G" "E" "e'"}} =>
    Ebind_k 1 (var "E") {{e #"nat"}}
    (bind_k 2 (var "e'") {{e #"nat"}}
    {{e #"set" {ovar 1} {ovar 0} (#"jmp" {ovar 2} #"tt")}})
  | {{e #"Eset_r" "G" "v" "E"}} =>
    Ebind_k 1 (var "E") {{e #"nat"}}
    {{e #"set" (#"val_subst" {wkn_n 2} "v") {ovar 0} (#"jmp" {ovar 1} #"tt")}}
  end.    

Derive heap_ctx_cps
       in (elab_preserving_compiler (Ectx_cps++heap_cps++heap_id++cps_subst)
                                          (heap_cps_ops
                                             ++ cps_lang
                                             ++ unit_lang
                                             ++ heap
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          heap_ctx_cps_def
                                          heap_ctx_cps
                                          heap_ctx)
       as heap_ctx_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition heap_ctx_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving heap_ctx_cps_preserving).
#[export] Hint Resolve heap_ctx_cps_entry : preserving_db.

