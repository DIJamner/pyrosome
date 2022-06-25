Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers
     SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS SimpleUnit NatHeap Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


(*simple heap operations w/axioms avoiding an explicit heap *)
Definition heap_cps_ops_def : lang :=
  {[l/subst
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

  [:=  "H" : #"heap",
       "G" : #"env",
       "n" : #"natural",
       "z" : #"blk" "G",
       "nz" : #"blk" "G"
       ----------------------------------------------- ("if nonzero")
       #"config" "H" (#"if0" (#"nv" (#"1+" "n")) "z" "nz") =
         #"config" "H" "nz" : #"configuration" "G"
  ];
  [:=  "H" : #"heap",
       "G" : #"env",
       "z" : #"blk" "G",
       "nz" : #"blk" "G"
       ----------------------------------------------- ("if zero")
       #"config" "H" (#"if0" (#"nv" #"0") "z" "nz") =
         #"config" "H" "z" : #"configuration" "G"
  ]
  ]}.

Derive heap_cps_ops
       SuchThat (elab_lang_ext (unit_lang ++ heap ++ nat_exp++ nat_lang ++ block_subst ++ value_subst)
                               heap_cps_ops_def
                               heap_cps_ops)
       As heap_cps_ops_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve heap_cps_ops_wf : elab_pfs.

Definition heap_id_def : compiler :=
  match # from (unit_lang ++ heap ++ nat_exp++ nat_lang) with
  | {{s #"heap"}} => {{s#"heap"}}
  end.



Derive heap_id
       SuchThat (elab_preserving_compiler cps_subst
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
       As cps_preserving.
Proof.
  auto_elab_compiler.
  - cleanup_elab_after eredex_steps_with heap "heap_comm".
  - cleanup_elab_after eredex_steps_with heap "lookup_miss".
  - cleanup_elab_after eredex_steps_with heap "lookup_empty".
Qed.
#[export] Hint Resolve heap_id : elab_pfs.



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
       SuchThat (elab_preserving_compiler (heap_id++cps_subst)
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
       As heap_cps_preserving.
Proof.
  auto_elab_compiler.
  cleanup_elab_after
    (reduce;
    eapply eq_term_trans;
    [eredex_steps_with heap_cps_ops "eval get"|];
    by_reduction).
Qed.
#[export] Hint Resolve heap_cps_preserving : elab_pfs.

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
       SuchThat (elab_preserving_compiler (Ectx_cps++heap_cps++heap_id++cps_subst)
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
       As heap_ctx_cps_preserving.
Proof.
  auto_elab_compiler.
  cleanup_elab_after
    (reduce;
     eapply eq_term_trans;
     [eredex_steps_with heap_cps_ops "eval get"|];
     by_reduction).
Qed.
#[export] Hint Resolve heap_ctx_cps_preserving : elab_pfs.

