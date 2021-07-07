Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix SimpleVSubst SimpleVCPS Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.



(*
Definition value_cc_subst_def : lang :=
  {[l
      
  [s|  
      -----------------------------------------------
      #"ty" srt
  ];
  [s| "G" : #"ty", "A" : #"ty"
      -----------------------------------------------
      #"val" "G" "A" srt
  ];
  [:| "G" : #"ty" 
       -----------------------------------------------
       #"id" : #"val" "G" "G"
  ];
  [:| "G" : #"ty", "G'" : #"ty", "g" : #"val" "G" "G'",
       "A" : #"ty", "v" : #"val" "G'" "A"
       -----------------------------------------------
       #"val_subst" "g" "v" : #"val" "G" "A"
  ];
   
  [:= "G" : #"ty", "A" : #"ty", "e" : #"val" "G" "A"
       ----------------------------------------------- ("id_left")
       #"val_subst" #"id" "e" = "e" : #"val" "G" "A"
  ]; 
  [:= "G" : #"ty", "A" : #"ty", "e" : #"val" "G" "A"
       ----------------------------------------------- ("id_right")
       #"val_subst" "e" #"id" = "e" : #"val" "G" "A"
  ]; 
   [:= "G1" : #"ty",
         "G2" : #"ty",
         "G3" : #"ty",
         "G4" : #"ty",
         "f" : #"val" "G1" "G2",
         "g" : #"val" "G2" "G3",
         "h" : #"val" "G3" "G4"
         ----------------------------------------------- ("val_subst_assoc")
         #"val_subst" "f" (#"val_subst" "g" "h") = #"val_subst" (#"val_subst" "f" "g") "h" : #"val" "G1" "G4"
  ] ]}.


Derive value_cc_subst
       SuchThat (Pre.elab_lang []
                               value_cc_subst_def
                               value_cc_subst)
       As value_cc_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve value_cc_subst_wf : elab_pfs.
*)

Definition prod_cc_def : lang :=
  {[l
  [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
       -----------------------------------------------
       #".1" "v" : #"val" "G" "A"
  ];
  [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
       -----------------------------------------------
       #".2" "v" : #"val" "G" "B"
  ];
   [:= "G" : #"env", "A" : #"ty",
      "g" : #"val" "G" "A",
      "B" : #"ty",
      "v" : #"val" "G" "B"
      ----------------------------------------------- ("proj 1")
      #".1" (#"pair" "g" "v") = "g" : #"val" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty",
      "g" : #"val" "G" "A",
      "B" : #"ty",
      "v" : #"val" "G" "B"
      ----------------------------------------------- ("proj 2")
      #".2" (#"pair" "g" "v") = "v" : #"val" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "G" (#"prod" "A" "B")
      ----------------------------------------------- ("negative pair eta")
      #"pair" (#".1" "v") (#".2" "v") = "v" : #"val" "G" (#"prod" "A" "B")
  ];
  [:= "G" : #"env", "G'" : #"env",
      "f" : #"sub" "G" "G'",
      "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G'" (#"prod" "A" "B")
      ----------------------------------------------- ("subst .1")
       #"val_subst" "f" (#".1" "v")
       = #".1" (#"val_subst" "f" "v")
       : #"val" "G" "A"
  ];
  [:= "G" : #"env", "G'" : #"env",
      "f" : #"sub" "G" "G'",
      "A" : #"ty", "B" : #"ty",
      "v" : #"val" "G'" (#"prod" "A" "B")
      ----------------------------------------------- ("subst .2")
       #"val_subst" "f" (#".2" "v")
       = #".2" (#"val_subst" "f" "v")
       : #"val" "G" "B"
  ]
  ]}.


Derive prod_cc
       SuchThat (Pre.elab_lang (cps_prod_lang ++ block_subst ++value_subst) prod_cc_def prod_cc)
       As prod_cc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve prod_cc_wf : elab_pfs.

Definition cc_lang_def : lang :=
  {[l
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" "A" "B")),
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"closure" "B" "e" "v" : #"val" "G" (#"neg" "B")
   ];
   [:| "G" : #"env",
       "A" : #"ty",
       "v1" : #"val" "G" (#"neg" "A"),
       "v2" : #"val" "G" "A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" "G"
   ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" "A" "B")),
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"closure" "B" "e" "v") "v'"
      = #"blk_subst" (#"snoc" #"forget" (#"pair" "v" "v'")) "e"
      : #"blk" "G"
  ];
  [:= "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" (#"ext" #"emp" "A") (#"neg" "B")
      ----------------------------------------------- ("clo_eta")
      #"closure" "B"
        (#"jmp" (#"val_subst" (#"snoc" #"wkn" (#".1" #"hd")) "v") (#".2" #"hd"))
        #"hd"(*TODO: should really be env-capturing tuple*)
      = "v"
      : #"val" (#"ext" #"emp" "A") (#"neg" "B")
  ];
   (*
  TODO: what is the proper eta law?
  use subst as closure arg?
    *)
  [:= "G" : #"env", "A" : #"ty",
      "v1" : #"val" "G" (#"neg" "A"),
      "v2" : #"val" "G" "A",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("jmp_subst")
      #"blk_subst" "g" (#"jmp" "v1" "v2")
      = #"jmp" (#"val_subst" "g" "v1") (#"val_subst" "g" "v2")
      : #"blk" "G'"
  ];  
  [:= "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"blk" (#"ext" #"emp" (#"prod" "A" "B")),
      "v" : #"val" "G" "A",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("clo_subst")
      #"val_subst" "g" (#"closure" "B" "e" "v")
      = #"closure" "B" "e" (#"val_subst" "g" "v")
      : #"val" "G'" (#"neg" "B")
  ]
  ]}.


Derive cc_lang
       SuchThat (Pre.elab_lang (prod_cc ++ cps_prod_lang ++ block_subst ++value_subst)
                               cc_lang_def
                               cc_lang)
       As cc_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cc_lang_wf : elab_pfs.


Definition subst_cc_def : compiler :=
  match # from (block_subst ++ value_subst) with
  | {{s #"env" }} => {{s #"ty"}}
  | {{s #"val" "G" "B"}} => {{s #"val" (#"ext" #"emp" "G") "B"}}
  | {{s #"blk" "G"}} => {{s #"blk" (#"ext" #"emp" "G")}}
  | {{s #"sub" "G" "G'"}} => {{s #"val" (#"ext" #"emp" "G") "G'"}}
  | {{e #"cmp" "G" "G'" "A" "g" "g'"}} =>
    {{e #"val_subst" (#"snoc" #"wkn" "g") "g'"}}
  | {{e #"emp"}} => {{e#"unit"}}
  | {{e #"forget"}} => {{e# "tt"}}
  | {{e #"ext" "A" "B" }} => {{e #"prod" "A" "B"}}
  | {{e #"snoc" "G" "G'" "A" "g" "v"}} =>
    {{e #"pair" "g" "v"}}
  | {{e #"id" "G"}} => {{e #"hd"}}
  | {{e #"hd" "G" "A"}} => {{e #".2" #"hd"}}
  | {{e #"wkn" "G" "A"}} => {{e #".1" #"hd"}}
  | {{e #"val_subst" "G" "G'" "g" "A" "v"}} =>
    {{e #"val_subst" (#"snoc" #"wkn" "g") "v"}}
  | {{e #"blk_subst" "G" "G'" "g" "e"}} =>
    {{e #"blk_subst" (#"snoc" #"wkn" "g") "e"}}
  end.

Require Import SimpleUnit.

Derive subst_cc
       SuchThat (elab_preserving_compiler []
                                          (unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          subst_cc_def
                                          subst_cc
                                          (block_subst++value_subst))
       As subst_cc_preserving.
Proof.

  setup_elab_compiler.
  all: try solve [repeat t].
  all: try solve [ compute_eq_compilation; by_reduction ].
  {
    reduce.
    eredex_steps_with unit_eta "unit eta".
  }
  Unshelve.
  all: repeat t'; eauto with elab_pfs auto_elab.
Qed.
#[export] Hint Resolve subst_cc_preserving : elab_pfs.


(*TODO: redo for positive products *)
Definition prod_cc_compile_def : compiler :=
  match # from cps_prod_lang with
  | {{e #"pm_pair" "G" "A" "B" "v" "e"}} =>
    {{e #"blk_subst"
        (#"snoc" #"wkn" (#"pair" (#"pair" {ovar 0} (#".1" "v")) (#".2" "v")))
        "e"}}
    (*{{e #"pm_pair" "v"
        (#"blk_subst"
          (#"snoc" #"forget" (#"pair" (#"pair" {ovar 2} {ovar 1}) {ovar 0}))
          "e")}}*)
  end.

(*
TODO: should be supersceded by eredex_steps_with
(*TODO: only works if all variables appear on the rhs*)
Ltac redex_steps_with_rhs lang name :=
  let mr := eval compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
          let ms := eval compute in (matches e2 e2p (map fst c)) in
              lazymatch ms with
              | Some ?s =>
                replace (eq_term l c' t e1 e2)
                  with (eq_term l c' tp[/s/] e1p[/s/] e2p[/s/]);
                [| reflexivity];
                eapply eq_term_subst;
                [| | eq_term_by name];
                [solve [repeat t']|apply eq_subst_refl; solve [repeat t'] ]
              | None => fail "rhs" e2 "does not match rule" e2p
              end
        | _ => fail "Goal not a term equality"
        end
      | _ => fail "Rule not found"
      end.
 *)

(*TODO: move to value_subst? could conflict w/ cmp_forget
  not currently used
*)
(*TODO: generalize? reverse for tactics?*)
Definition forget_eq_wkn_def : lang :=
  {[l
      [:= "A" : #"ty"
         ----------------------------------------------- ("wkn_emp_forget")
         #"forget" = #"wkn"
         : #"sub" (#"ext" #"emp" "A") #"emp"
      ]
  ]}.
Derive forget_eq_wkn
       SuchThat (Pre.elab_lang value_subst
                               forget_eq_wkn_def
                               forget_eq_wkn)
       As forget_eq_wkn_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve forget_eq_wkn_wf : elab_pfs.


Derive prod_cc_compile
       SuchThat (elab_preserving_compiler subst_cc
                                          ( unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          prod_cc_compile_def
                                          prod_cc_compile
                                          cps_prod_lang)
       As prod_cc_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve prod_cc_preserving : elab_pfs.


Definition cc_def : compiler :=
  match # from (cps_lang) with
  | {{e #"neg" "A" }} => {{e #"neg" "A"}}
  | {{e #"cont" "G" "A" "e"}} =>
    {{e #"closure" "A" "e" #"hd"}}
  | {{e #"jmp" "G" "A" "v1" "v2"}} =>
    {{e #"jmp" "v1" "v2" }}
  end.

 
Derive cc
       SuchThat (elab_preserving_compiler (prod_cc_compile++subst_cc)
                                          (cc_lang
                                             ++ forget_eq_wkn
                                             ++ unit_eta
                                             ++ unit_lang
                                             ++ prod_cc
                                             ++ cps_prod_lang
                                             ++ block_subst
                                             ++value_subst)
                                          cc_def
                                          cc
                                          cps_lang)
       As cc_preserving.
Proof.
  setup_elab_compiler; repeat t.    
  solve[compute_eq_compilation;by_reduction].
  solve[compute_eq_compilation;by_reduction].
  solve[compute_eq_compilation;by_reduction].
  {
    reduce.
    eapply eq_term_trans.  
    eapply eq_term_sym.
    eredex_steps_with cc_lang "clo_eta".
    by_reduction.
  }
  Unshelve.
  all: repeat t'; eauto with elab_pfs auto_elab.
Qed.
#[export] Hint Resolve cc_preserving : elab_pfs.

