Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix
     SimpleVSubst SimpleVCPS SimpleEvalCtxCPS SimpleUnit NatHeap Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


(*simple heap operations w/axioms avoiding an explicit heap 
  TODO: substitution rules
*)
Definition heap_cps_ops_def : lang :=
  {[l
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
  [:=  "G" : #"env", "G'" : #"env",
       "v" : #"val" "G'" #"nat",
       "e" : #"blk" (#"ext" "G'" #"nat"),
       "g" : #"sub" "G" "G'"
       ----------------------------------------------- ("subst get")
       #"blk_subst" "g" (#"get" "v" "e")
       = #"get" (#"val_subst" "g" "v")
          (#"blk_subst" (#"snoc" (#"cmp" #"wkn" "g") #"hd") "e")
       : #"blk" "G"
  ];
  [:=  "G" : #"env", "G'" : #"env",
       "vl" : #"val" "G'" #"nat",
       "vn" : #"val" "G'" #"nat",
       "e" : #"blk" "G'",
       "g" : #"sub" "G" "G'"
       ----------------------------------------------- ("subst set")
       #"blk_subst" "g" (#"set" "vl" "vn" "e")
       = #"set" (#"val_subst" "g" "vl")
          (#"val_subst" "g" "vn")
          (#"blk_subst" "g" "e")
       : #"blk" "G"
  ]
  ]}.

Derive heap_cps_ops
       SuchThat (Pre.elab_lang (unit_lang ++ heap ++ nat_exp++ nat_lang ++ block_subst ++ value_subst)
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
  setup_elab_compiler.
  all: repeat t.
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  {
    eredex_steps_with heap "heap_comm".   
    repeat apply wf_subst_cons.
    constructor.
    all: repeat t.
  }
  solve [ compute_eq_compilation; by_reduction ].
  {
    eredex_steps_with heap "lookup_miss".
    repeat apply wf_subst_cons.
    constructor.
    all: repeat t.
  }
  {
    eredex_steps_with heap "lookup_empty".
    repeat apply wf_subst_cons.
    constructor.
    all: repeat t.
  }
  {
    eredex_steps_with unit_lang "tt_subst".
  }
  Unshelve.
  all: repeat t'.
  all: compute; intuition fail.
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
  setup_elab_compiler.
  all: repeat t.
  {
    reduce.
    eredex_steps_with heap_cps_ops "eval get".
    {
      (*TODO: roll into above tactic*)
      repeat apply wf_subst_cons;
        [ constructor|..];
        repeat t.
    }
    solve [ compute_eq_compilation; by_reduction ].
  }
  solve [ compute_eq_compilation; by_reduction ].

  Unshelve.
  all: repeat t';
    eauto with elab_pfs auto_elab.
  simpl; intuition.
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

Require Import SimpleEvalCtx.
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
  setup_elab_compiler.
  all: repeat t.
  unshelve (solve [ compute_eq_compilation; by_reduction ]);
    repeat t';
    eauto with elab_pfs auto_elab.
  unshelve (solve [ compute_eq_compilation; by_reduction ]);
    repeat t';
    eauto with elab_pfs auto_elab.
  unshelve (solve [ compute_eq_compilation; by_reduction ]);
    repeat t';
    eauto with elab_pfs auto_elab.
  {
    reduce.
    eredex_steps_with heap_cps_ops "eval get".
    {
      (*TODO: roll into above tactic*)
      repeat apply wf_subst_cons;
        [ constructor|..];
        repeat t.
    }
  }
  solve [ compute_eq_compilation; by_reduction ].
  Unshelve.
  (*TODO: why is this computationally intensive? *)
  all:  repeat t';
    eauto with elab_pfs auto_elab.
  simpl; intuition.
Qed.
#[export] Hint Resolve heap_ctx_cps_preserving : elab_pfs.

