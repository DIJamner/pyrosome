Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers
     ElabCompilersWithPrefix SimpleVSubst SimpleVCPS SimpleVCC Matches NatHeap.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

(*TODO: how to do shifting?*)
Definition text_segment_def : lang :=
  {[l
  [:| "A" : #"ty"
      -----------------------------------------------
      #"box" "A" : #"ty"
  ];
  [s|
      -----------------------------------------------
      #"text" srt
  ];
  [:| 
      -----------------------------------------------
      #"Temp" : #"text"
  ];
  [:| "T" : #"text",
      "A" : #"ty", "v" : #"val" #"emp" "A"
      -----------------------------------------------
      #"Tcons" "T" "v" : #"text"
  ];
  [:| "G" : #"env", "A" : #"ty", "n" : #"natural"
      -----------------------------------------------
      #"ptr" "A" "n" : #"val" "G" (#"box" "A")
  ];
  [:= "G" : #"env", "G'" : #"env",
      "g" : #"sub" "G" "G'",
      "A" : #"ty", "n" : #"natural"
      ----------------------------------------------- ("ptr subst")
      #"val_subst" "g" (#"ptr" "A" "n")
      = #"ptr" "A" "n"
      : #"val" "G" (#"box" "A")
  ];
  [:| "G" : #"env",
      "A" : #"ty", "v" : #"val" "G" (#"box" "A"),
      "e" : #"blk" (#"ext" "G" "A")
      -----------------------------------------------
      #"deref" "v" "e" : #"blk" "G"
  ];
  [:= "G" : #"env", "G'" : #"env",
      "g" : #"sub" "G" "G'",
      "A" : #"ty", "v" : #"val" "G'" (#"box" "A"),
      "e" : #"blk" (#"ext" "G'" "A")
      ----------------------------------------------- ("deref subst")
      #"blk_subst" "g" (#"deref" "v" "e")
      = #"deref" (#"val_subst" "g" "v") (#"blk_subst" {under {{e"g"}} } "e")
      : #"blk" "G"
  ];
  [:| "T" : #"text", "G" : #"env",
      "A" : #"ty", "n" : #"natural"
      -----------------------------------------------
      #"Tlookup" "T" "A" "n" : #"val" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "T" : #"text",
      "v" : #"val" #"emp" "A"
      ----------------------------------------------- ("Tlookup 0")
      #"Tlookup" (#"Tcons" "T" "v") "A" #"0"
      = #"val_subst" #"forget" "v"
      : #"val" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "T" : #"text",
      "v" : #"val" #"emp" "A",
      "B" : #"ty",
      "n" : #"natural"
      ----------------------------------------------- ("Tlookup 1+")
      #"Tlookup" (#"Tcons" "T" "v") "B" (#"1+" "n")
      = #"Tlookup" "T" "B" "n"
      : #"val" "G" "B"
  ];
  [s| "G" : #"env"
      -----------------------------------------------
      #"program" "G" srt
  ];
  [:| "G" : #"env",
      "T" : #"text",
      "e" : #"blk" "G"            
      -----------------------------------------------
      #"prog" "T" "e" : #"program" "G"
  ];
  [:= "G" : #"env",
      "T" : #"text",
      "A" : #"ty",
      "e" : #"blk" (#"ext" "G" "A"),
      "n" : #"natural"
      ----------------------------------------------- ("eval deref")
      #"prog" "T" (#"deref" (#"ptr" "A" "n") "e")
      = #"prog" "T" (#"blk_subst" (#"snoc" #"id" (#"Tlookup" "T" "A" "n")) "e")
      : #"program" "G"
  ]
  ]}.

Derive text_segment
       SuchThat (Pre.elab_lang (nat_lang ++ block_subst ++ value_subst)
                               text_segment_def
                               text_segment)
       As text_segment_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve text_segment_wf : elab_pfs.


Definition hoist_lang_def : lang :=
  {[l
   [:| "A" : #"ty"
       -----------------------------------------------
       #"neg" "A" : #"ty"
   ];
   [:| "A" : #"ty"
       -----------------------------------------------
       #"code" "A" : #"ty"
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v_ptr" : #"val" "G" (#"box" (#"code" (#"prod" "A" "B"))),
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"closure" "B" "v_ptr" "v" : #"val" "G" (#"neg" "B")
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" #"emp" "A")
      -----------------------------------------------
      #"code_block" "e" : #"val" "G" (#"code" "A")
   ];
  [:| "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" (#"code" "A"),
      "v'" : #"val" "G" "A"
      -----------------------------------------------
      #"exec" "v" "v'" : #"blk" "G"
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
      "v_ptr" : #"val" "G" (#"box" (#"code" (#"prod" "A" "B"))),
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"closure" "B" "v_ptr" "v") "v'"
      = #"deref" "v_ptr" (#"exec" #"hd" (#"val_subst" #"wkn" (#"pair" "v" "v'")))
      : #"blk" "G"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" #"emp" "A"),
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("exec_beta")
      #"exec" (#"code_block" "e") "v"
      = #"blk_subst" (#"snoc" #"forget" "v") "e"
      : #"blk" "G"
  ];
   
(*
  [:= "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" (#"ext" #"emp" "A") (#"neg" "B")
      ----------------------------------------------- ("clo_eta")
      #"closure" "B"
        (#"jmp" (#"val_subst" (#"snoc" #"wkn" (#".1" #"hd")) "v") (#".2" #"hd"))
        #"hd"(*TODO: should really be env-capturing tuple*)
      = "v"
      : #"val" (#"ext" #"emp" "A") (#"neg" "B")
  ];*)
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
      "v_ptr" : #"val" "G" (#"box" (#"code" (#"prod" "A" "B"))),
      "v" : #"val" "G" "A",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("clo_subst")
      #"val_subst" "g" (#"closure" "B" "v_ptr" "v")
      = #"closure" "B"  (#"val_subst" "g" "v_ptr") (#"val_subst" "g" "v")
      : #"val" "G'" (#"neg" "B")
  ]
  ]}.


Derive hoist_lang
       SuchThat (Pre.elab_lang (text_segment ++ nat_lang++ prod_cc ++ cps_prod_lang ++ block_subst ++value_subst)
                               hoist_lang_def
                               hoist_lang)
       As hoist_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hoist_lang_wf : elab_pfs.

Definition hoist_helpers_def : lang :=
  {[l
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"val&text" "G" "A" srt
  ];
  [:| "T" : #"text",
      "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" "A"            
      -----------------------------------------------
      #"v&t" "T" "v" : #"val&text" "G" "A"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "vt" : #"val&text" "G" "A"    
      -----------------------------------------------
      #"v&t text" "vt" : #"text"
  ];
  [:| "G" : #"env",
      "A" : #"ty",
      "vt" : #"val&text" "G" "A"    
      -----------------------------------------------
      #"v&t val" "vt" : #"val" "G" "A"
  ];
  [:= "T" : #"text",
      "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" "A"            
      ----------------------------------------------- ("project v&t text")
      #"v&t text" (#"v&t" "T" "v") = "T" : #"text"
  ];
  [:= "T" : #"text",
      "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" "A"            
      ----------------------------------------------- ("project v&t val")
      #"v&t val" (#"v&t" "T" "v") = "v" : #"val" "G" "A"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "vt" : #"val&text" "G" "A"       
      ----------------------------------------------- ("v&t eta")
      #"v&t" (#"v&t text" "vt") (#"v&t val" "vt")
      = "vt" : #"val&text" "G" "A"
  ];
  [s| "G" : #"env", "G'" : #"env"
      -----------------------------------------------
      #"sub&text" "G" "G'" srt
  ];
  [:| "T" : #"text",
      "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" "G" "G'"            
      -----------------------------------------------
      #"s&t" "T" "g" : #"sub&text" "G" "G'"
  ];
  [:| "G" : #"env",
      "G'" : #"env",
      "gt" : #"sub&text" "G" "G'"    
      -----------------------------------------------
      #"s&t text" "gt" : #"text"
  ];
  [:| "G" : #"env",
      "G'" : #"env",
      "gt" : #"sub&text" "G" "G'"    
      -----------------------------------------------
      #"s&t sub" "gt" : #"sub" "G" "G'"
  ];
  [:= "T" : #"text",
      "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" "G" "G'"            
      ----------------------------------------------- ("project s&t text")
      #"s&t text" (#"s&t" "T" "g") = "T" : #"text"
  ];
  [:= "T" : #"text",
      "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" "G" "G'"            
      ----------------------------------------------- ("project s&t sub")
      #"s&t sub" (#"s&t" "T" "g") = "g" : #"sub" "G" "G'"
  ];
  [:= "G" : #"env",
      "G'" : #"env",
      "gt" : #"sub&text" "G" "G'"       
      ----------------------------------------------- ("s&t eta")
      #"s&t" (#"s&t text" "gt") (#"s&t sub" "gt")
      = "gt" : #"sub&text" "G" "G'"
  ];
  [:| "G" : #"env",
      "p" : #"program" "G"    
      -----------------------------------------------
      #"prog text" "p" : #"text"
  ];
  [:| "G" : #"env",
      "p" : #"program" "G" 
      -----------------------------------------------
      #"prog blk" "p" : #"blk" "G"
  ];
  [:= "T" : #"text",
      "G" : #"env",
      "e" : #"blk" "G"        
      ----------------------------------------------- ("project prog text")
      #"prog text" (#"prog" "T" "e") = "T" : #"text"
  ];
  [:= "T" : #"text",
      "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" "G"        
      ----------------------------------------------- ("project prog block")
      #"prog blk" (#"prog" "T" "e") = "e" : #"blk" "G"
  ];
  [:= "G" : #"env",
      "gt" : #"program" "G"     
      ----------------------------------------------- ("prog eta")
      #"prog" (#"prog text" "gt") (#"prog blk" "gt")
      = "gt" : #"program" "G"
  ];
  [:| "n" : #"natural",
      "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" "A"            
      -----------------------------------------------
      #"val_ptr_shift" "n" "v" : #"val" "G" "A"
  ];
  [:| "n" : #"natural",
      "G" : #"env",
      "e" : #"blk" "G"            
      -----------------------------------------------
      #"blk_ptr_shift" "n" "e" : #"blk" "G"
  ];
  [:| "n" : #"natural",
      "T" : #"text"            
      -----------------------------------------------
      #"text_ptr_shift" "n" "T" : #"text"
  ];
(*TODO: move to nat_lang*)
  [:| "n" : #"natural",
      "m" : #"natural"         
      -----------------------------------------------
      #"+" "n" "m" : #"natural"
  ];
  [:= "n" : #"natural",
      "m" : #"natural"         
      ----------------------------------------------- ("+ 1+")
      #"+" (#"1+" "n") "m" = #"1+" (#"+" "n" "m") : #"natural"
  ];
  [:= "m" : #"natural"         
      ----------------------------------------------- ("+ 0")
      #"+" #"0" "m" = "m" : #"natural"
  ];
  [:= "n" : #"natural",
      "G" : #"env",
      "A" : #"ty",
      "m" : #"natural"         
      ----------------------------------------------- ("ptr_shift")
      #"val_ptr_shift" "n" (#"ptr" "A" "m")
      = #"ptr" "A" (#"+" "n" "m")
      : #"val" "G" (#"box" "A")
  ]; (*TODO: eqns for other shifts*)
  [:= "n" : #"natural"        
      ----------------------------------------------- ("Temp_shift")
      #"text_ptr_shift" "n" #"Temp" = #"Temp" : #"text"
  ]; (*TODO: eqns for other shifts*)
  [:= "n" : #"natural",
      "T" : #"text",
      "A" : #"ty", "v" : #"val" #"emp" "A"
      ----------------------------------------------- ("Tcons_shift")
      #"text_ptr_shift" "n" (#"Tcons" "T" "v")
      = #"Tcons" (#"text_ptr_shift" "n" "T") (#"val_ptr_shift" "n" "v")
      : #"text"
  ]; (*TODO: eqns for other shifts*)
  [:| "T" : #"text"        
      -----------------------------------------------
      #"Tlen" "T" : #"natural"
  ];
  [:= "T" : #"text",
      "A" : #"ty", "v" : #"val" #"emp" "A"         
      ----------------------------------------------- ("Tlen cons")
      #"Tlen" (#"Tcons" "T" "v") = #"1+" (#"Tlen" "T") : #"natural"
  ];
  [:=         
      ----------------------------------------------- ("Tlen emp")
      #"Tlen" #"Temp" = #"0" : #"natural"
  ];
  [:| "T" : #"text", "T'" : #"text"        
      -----------------------------------------------
      #"Tapp" "T" "T'" : #"text"
  ];
  [:= "T" : #"text", "T'" : #"text",
      "A" : #"ty", "v" : #"val" #"emp" "A"         
      ----------------------------------------------- ("Tapp cons")
      #"Tapp" "T" (#"Tcons" "T'" "v")
      = #"Tcons" (#"Tapp" "T" "T'") "v"
      : #"text"
  ];
  [:= "T" : #"text"      
      ----------------------------------------------- ("Tapp emp right")
      #"Tapp" "T" #"Temp" = "T" : #"text"
  ];
  [:= "T" : #"text"      
      ----------------------------------------------- ("Tapp emp left")
      #"Tapp" #"Temp" "T" = "T" : #"text"
  ]
  ]}.


Derive hoist_helpers
       SuchThat (Pre.elab_lang (text_segment ++ nat_lang ++ block_subst ++value_subst)
                               hoist_helpers_def
                               hoist_helpers)
       As hoist_helpers_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hoist_helpers_wf : elab_pfs.

(*TODO: merge w/ above*)
Definition hoist_helpers2_def : lang :=
  {[l
  [:= "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" "A"            
      ----------------------------------------------- ("val_ptr_shift 0")
      #"val_ptr_shift" #"0" "v" = "v" : #"val" "G" "A"
  ];
  [:= "G" : #"env",
      "e" : #"blk" "G"         
      ----------------------------------------------- ("blk_ptr_shift 0")
      #"blk_ptr_shift" #"0" "e" = "e" : #"blk" "G"
  ];
  [:= "T" : #"text"            
      ----------------------------------------------- ("text_ptr_shift 0")
      #"text_ptr_shift" #"0" "T" = "T" : #"text"
  ]
  ]}.


Derive hoist_helpers2
       SuchThat (Pre.elab_lang (hoist_helpers ++ text_segment ++ nat_lang ++ block_subst ++value_subst)
                               hoist_helpers2_def
                               hoist_helpers2)
       As hoist_helpers2_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hoist_helpers2_wf : elab_pfs.

Definition plain_sub s := {{e #"s&t" #"Temp" {s} }}.
Definition plain_val s := {{e #"v&t" #"Temp" {s} }}.

Definition hoist_subst_def : compiler :=
  match # from (block_subst ++value_subst) with
  | {{s #"blk" "G"}} =>
    {{s #"program" "G"}}
  | {{s #"val" "G" "A"}} =>
    {{s #"val&text" "G" "A"}}
  | {{s #"sub" "G" "G'"}} =>
    {{s #"sub&text" "G" "G'"}}
  | {{e #"id" "G"}} =>
    plain_sub {{e #"id"}}
  | {{e #"snoc" "G" "G'" "A" "g" "v"}} =>
    {{e #"s&t" (#"Tapp" (#"text_ptr_shift" (#"Tlen" (#"s&t text" "g")) (#"v&t text" "v"))
                       (#"s&t text" "g"))
        (#"snoc" (#"s&t sub" "g") (#"v&t val" "v")) }}
  | {{e #"wkn" "G" "A"}} =>
    plain_sub {{e #"wkn"}}
  | {{e #"hd" "G" "A"}} =>
    plain_val {{e #"hd"}}
  | {{e #"cmp" "G1" "G2" "G3" "g" "h"}} =>
    {{e #"s&t" (#"Tapp" (#"text_ptr_shift" (#"Tlen" (#"s&t text" "g")) (#"s&t text" "h"))
                       (#"s&t text" "g"))
        (#"cmp" (#"s&t sub" "g") (#"s&t sub" "h")) }}
  | {{e #"val_subst" "G" "G'" "g" "A" "v"}} =>
    {{e #"v&t" (#"Tapp" (#"text_ptr_shift" (#"Tlen" (#"s&t text" "g")) (#"v&t text" "v"))
                       (#"s&t text" "g"))
        (#"val_subst" (#"s&t sub" "g") (#"v&t val" "v")) }}
  | {{e #"forget" "G"}} =>
    plain_sub {{e #"forget"}}
  end.

Derive hoist_subst
       SuchThat (elab_preserving_compiler []
                                          (hoist_helpers2
                                             ++ hoist_helpers
                                             ++ text_segment
                                             ++ nat_lang
                                             ++ block_subst
                                             ++value_subst)
                                          hoist_subst_def
                                          hoist_subst
                                          (block_subst++value_subst))
       As hoist_subst_preserving.
Proof.
  setup_elab_compiler.
  all: repeat t.
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  {
    reduce.
    solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  solve [ compute_eq_compilation; by_reduction ].
  {
    reduce.
    
    solve [ compute_eq_compilation; by_reduction ].
  
  unshelve (setup_elab_compiler; repeat t; (solve [ compute_eq_compilation; by_reduction ])); repeat t'; eauto
   with elab_pfs auto_elab.

  Qed.

(*TODO: add text*val syntax *)
(*TODO: split up?*)
Definition hoist_def : compiler :=
  match # from (cc_lang
                  ++ forget_eq_wkn
                  ++ unit_eta
                  ++ unit_lang
                  ++ prod_cc
                  ++ cps_prod_lang
                  ++ block_subst
                  ++value_subst) with
  | {{s #"blk" "G"}} =>
    {{s #"program" "G"}}
  | {{s #"val" "G" "A"}} =>
    {{s #"val & text" "G" "A"}}
  | {{e #"closure" "G" "A" "B" "e" "v"}} =>
    {{e #"v&t" (#"Tcons"
                 ("Tapp" (#"text_ptr_shift" (#"1+" (#"Tlen" (#"prog text" "e"))) (#"v&t text" "v"))
                         (#"text_ptr_shift" (#"1+" #"0") (#"prog text" "e")))
                 (#"code_block" (#"blk_ptr_shift" (#"1+" #"0")  (#"prog blk" "e"))))
        (#"closure" "B" (#"ptr" (#"code" (#"prod" "A" "B")) #"0") (#"v&t val" "v")}}
