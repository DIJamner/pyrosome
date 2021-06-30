Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix
     SimpleVSubst SimpleVCPS SimpleUnit NatHeap Matches.
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


(*TODO: duplicated; move to matches*)
Ltac unify_evar_fst_eq :=
  match goal with
  | [|- (let (x,_) := ?p in x) = ?y] =>
    let p':= open_constr:((y,_:term)) in
    unify p p';
    compute;
    reflexivity
  end.
Ltac unify_var_names s c :=
  let H' := fresh in
  assert (len_eq s c) as H';
  [ solve[repeat constructor]| clear H'];
  assert (map fst s = map fst c) as H';
  [ compute; repeat f_equal; unify_evar_fst_eq| clear H'].


Ltac eredex_steps_with lang name :=
  let mr := eval compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_:subst) in
          first [unify_var_names s c | fail 100 "could not unify var names"];
          first [ replace (eq_term l c' t e1 e2)
                    with (eq_term l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [| f_equal; compute; reflexivity (*TODO: is this general?*)]
                | fail 100 "could not replace with subst"];
          eapply (@eq_term_subst l c' s s c);
          [ try solve [cleanup_auto_elab]
          | eapply eq_subst_refl; try solve [cleanup_auto_elab]
          | eapply (@eq_term_by l c name tp e1p e2p); try solve [cleanup_auto_elab]]
        end
      | None =>
        fail 100 "rule not found in lang"
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
    compute_eq_compilation.
    eredex_steps_with heap "heap_comm".
    repeat apply wf_subst_cons.
    constructor.
    all: repeat t.
  }
  solve [ compute_eq_compilation; by_reduction ].
  {
    compute_eq_compilation.
    eredex_steps_with heap "lookup_miss".
    repeat apply wf_subst_cons.
    constructor.
    all: repeat t.
  }
  {
    compute_eq_compilation.
    eredex_steps_with heap "lookup_empty".
    repeat apply wf_subst_cons.
    constructor.
    all: repeat t.
  }
  {
    compute_eq_compilation.
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
    compute_eq_compilation.
    eapply eq_term_trans.
    ltac2:(step()).
    compute_eq_compilation.
    eapply eq_term_trans.
    eredex_steps_with heap_cps_ops "eval get".
    {
      repeat apply wf_subst_cons.
      constructor.
      repeat t.
      repeat t.
      repeat t.
      repeat t.
      repeat t.
    }
    compute_eq_compilation.
    by_reduction.
  }
  solve [ compute_eq_compilation; by_reduction ].

  Unshelve.
  all: repeat t';
    eauto with elab_pfs auto_elab.
  simpl; intuition.
Qed.
#[export] Hint Resolve heap_cps_preserving : elab_pfs.
