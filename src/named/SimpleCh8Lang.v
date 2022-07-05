Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst SimpleVCC SimpleVFixCC SimpleVCPSHeap SimpleUnit SimpleVCCHeap SimpleVCPS Matches NatHeap Linter Compilers ElabCompilers TreeProofs.
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

(* Definition nat_eq_def : lang := *)
(*   {[l *)
(*     [s| "n" : #"natural", *)
(*         "m" : #"natural" *)
(*       ----------------------------------------------- *)
(*       #"eq" "n" "m" srt *)
(*     ]; *)
(*     [:| "n": #"natural" *)
(*       ----------------------------------------------- *)
(*       #"eq_0_0" : #"eq" #"0" #"0" *)
(*     ]; *)
(*     [:| "n": #"natural", "m": #"natural", *)
(*         "p" : #"eq" "n" "m" *)
(*       ----------------------------------------------- *)
(*       #"eq_1+" "p" : #"eq" (#"1+" "n") (#"1+" "m") *)
(*     ] *)
(*   ]}. *)

(* Derive nat_eq *)
(*        SuchThat (elab_lang_ext (nat_lang) nat_eq_def nat_eq) *)
(*        As nat_eq_wf. *)
(* Proof. auto_elab. Qed. *)
(* #[export] Hint Resolve nat_eq_wf : elab_pfs. *)

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
      #"config" "H" (#"seq" (#"while" "e" "c1") "c2")
      = #"config" "H" (#"seq" (#"if0" "e" #"skip" (#"seq" "c1" (#"while" "e" "c1") )) "c2") : #"configuration"
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
       SuchThat (elab_lang_ext (ch8 ++ heap++nat_lang) ch8_config_def ch8_config)
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
       SuchThat (elab_lang_ext (ch8_config ++ ch8 ++ heap++nat_lang) ch8_ectx_def ch8_ectx)
       As ch8_ectx_wf.
Proof.  auto_elab. Qed.
#[export] Hint Resolve ch8_ectx_wf : elab_pfs.

(* blk [... ; ~unit] *)
Definition jmp_hd :=
  {{e #"jmp" #"hd" #"tt" }}.

(*
 c2 : blk [~unit]
 c1 : blk [... ; ~unit]
 blk [... ; ~unit] *)
Definition seq c1 c2 :=
  {{e #"blk_subst" (#"snoc" #"wkn" (#"closure" #"unit" (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {c2}) #"hd")) {c1} }}.

(* env ([~unit]) *)
Definition cmd_env :=
  {{e #"ext" #"emp" (#"neg" #"unit")}}.

(* env ([~nat]) *)
Definition exp_env :=
  {{e #"ext" #"emp" (#"neg" #"nat")}}.

(* e : blk [... ; ~nat]
   c : blk [(A ; nat)]
   blk [... ; A] *)
Definition plug_exp e c :=
  {{e #"blk_subst"
      (#"snoc" #"wkn" (#"closure" #"nat" {c} #"hd"))
      {e} }}.

(* x : natural
   e : blk [... ; ~nat]
   blk [... ; ~unit] *)
Definition assign x e :=
  plug_exp e {{e #"set" (#"nv" {x}) (#".2" #"hd") (#"jmp" (#".1" #"hd") #"tt")}}.

(* e : blk [~nat]
   z : blk [~unit]
   nz : blk[~unit]
   blk [... ; ~unit] *)
Definition if0 e z nz :=
  plug_exp e {{e #"if0" (#".2" #"hd") (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {z}) (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {nz}) }}.

(* e : blk [... ; ~nat]
   c : blk [... ; ~unit]
   blk [... ; ~unit] *) 
Definition while e c :=
  {{e #"jmp" (#"fix"
               (#"closure"
                 (#"prod" (#"neg" #"unit") #"unit")
                 {plug_exp (* blk [(~unit, (~unit, unit))] *)
                    e
                    {{e #"if0" (#".2" #"hd") (* blk [((~unit, (~unit, unit)), nat)] *)
                        (#"jmp" (#".1" (#".1" #"hd")) #"tt")
                        (#"blk_subst" (#"snoc" #"wkn" (#".1" (#".2" (#".1" #"hd")))) {c})
                    }}
                 }
                 #"hd"))
      #"tt"
  }}.

(* b : blk [~nat]
   val [] ~~nat *)
Definition blk_to_val b :=
  {{e #"closure" (#"neg" #"nat") (#"blk_subst" (#"snoc" #"wkn" (#".2" #"hd")) {b}) #"tt"}}.

(* E : blk [A ; ~~nat]
   e : blk [~nat]
   blk [A] *)
Definition plug E e :=
  {{e #"blk_subst" (#"snoc" #"id" (#"val_subst" #"forget" {blk_to_val e} )) {E} }}.

Definition ch8_cc_def : compiler :=
  match # from (ch8_ectx ++ ch8_config ++ ch8 ++ heap ++ nat_lang) with
  | {{s #"exp"}} => {{s #"blk" {exp_env} }}
  | {{s #"cmd"}} => {{s #"blk" {cmd_env} }}
  | {{s #"configuration"}} => {{s #"configuration" {cmd_env} }}
  | {{s #"Ectx"}} => {{s #"blk" (#"ext" (#"ext" (#"emp" (#"neg" #"nat"))) (#"neg" (#"neg" #"nat"))) }}
  | {{s #"Cctx"}} => {{s #"blk" (#"ext" (#"ext" (#"emp" (#"neg" #"unit"))) (#"neg" (#"neg" #"nat"))) }}
  | {{e #"value" "n"}} => {{e #"jmp" #"hd" (#"nv" "n")}}
  | {{e #"hvar" "n"}} => {{e  #"get" (#"nv" "n") (#"jmp" (#"val_subst" #"wkn" #"hd") #"hd")}}
  | {{e #"skip"}} => jmp_hd
  | {{e #"assign" "x" "e" }} => assign {{e "x"}} {{e "e"}}
  | {{e #"seq" "cmd1" "cmd2"}} => seq {{e "cmd1"}} {{e "cmd2"}}
  | {{e #"if0" "e" "z" "nz"}} => if0 {{e "e"}} {{e "z"}} {{e "nz"}}
  | {{e #"while" "e" "c"}} => while {{e "e"}} {{e "c"}}
  | {{e #"config" "H" "c"}} => {{e #"config" "H" "c"}}
  | {{e #"[ ]"}} => {{e #"jmp" (#"closure" (#"neg" #"unit") (#"jmp" (#".2" #"hd") #"tt") #"tt") (#"val_subst" #"wkn" #"hd") }}
  | {{e #"Eassign" "x" "E"}} =>
      {{e #"blk_subst" (#"snoc" (#"snoc" #"forget" (#"closure" #"nat" (#"set" (#"nv" "x") (#".2" #"hd") (#"jmp" (#".1" #"hd") #"tt")) (#"val_subst" #"wkn" #"hd"))) #"hd") "E" }}
  | {{e #"Eif0" "E" "z" "nz"}} =>
      if0 (plug {{e "E"}} {{e #"val_subst" #"wkn" #"hd"}}) {{e "z"}} {{e "nz"}}
  | {{e #"Ewhile" "E" "c"}} =>
      while (plug {{e "E"}} {{e #"val_subst" #"wkn" #"hd"}}) {{e "c"}}
  | {{e #"Cplug" "C" "e"}} => plug {{e "C"}} {{e "e"}}
  | {{e #"Eplug" "E" "e"}} => plug {{e "E"}} {{e "e"}}
  end.

Definition target_lang : lang :=
(fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                forget_eq_wkn'++
                                cps_prod_lang ++ block_subst ++ value_subst).

Ltac try_term_cong :=
  repeat (try (term_cong; repeat (try apply eq_args_cons); try apply eq_args_nil; simpl; try term_refl; let n := numgoals in guard n <= 1)).

Ltac step_backward lang name :=
  eapply eq_term_trans;
  eapply eq_term_sym;
  try eredex_steps_with lang name;
  try_term_cong;
  eapply eq_term_sym.

Ltac setup_elab_compiler' :=
  match goal with
  | |- elab_preserving_compiler _ ?tgt ?cmp ?ecmp ?src =>
      rewrite (as_nth_tail cmp); rewrite (as_nth_tail ecmp);
      rewrite (as_nth_tail src);
      assert (wf_lang tgt) by admit
  end; break_preserving.

Ltac reduce :=
  repeat (
      eapply eq_term_trans;
      (try cleanup_elab_after step_if_concrete);
      try_term_cong).

From Utils Require Import Utils.
From Utils Require Export GoalDisplay.
From Named Require Import Core.
Import Core.Notations.


Definition as_ctx {V} (c:ctx V) :=c.
Notation "'{{c' c }}" := (as_ctx c) (at level 0, c custom ctx, only printing).

Ltac hide_implicits :=
  lazymatch goal with
  | |- eq_term ?l ?c ?t ?e1 ?e2 =>
      let c' := eval compute in (hide_ctx_implicits l c) in
        let t' := eval compute in (hide_sort_implicits l t) in
          let e1' := eval compute in (hide_term_implicits l e1) in
            let e2' := eval compute in (hide_term_implicits l e2) in
              change (eq_term l (lie_to_user (real:=c) (as_ctx c'))
                        (lie_to_user (real:=t) t')
                        (lie_to_user (real:=e1) e1')
                        (lie_to_user (real:=e2) e2'))
  end.

(*Use: `hide_implicits` shows the pre-elaboration terms,
  and `wysiwyg` shows the actual goal again.
 *)

Derive ch8_cc

       SuchThat (elab_preserving_compiler
                   []
                   target_lang
                   ch8_cc_def
                   ch8_cc
                   (ch8_ectx++ch8_config++ch8++heap++nat_lang))
       As ch8_cc_preserving.
Proof.
  setup_elab_compiler'; repeat Matches.t.
  28: {
    compute_eq_compilation.
    hide_implicits.
    reduce.
    hide_implicits.
    
  
  - by_reduction.
  - cleanup_elab_after eredex_steps_with heap "heap_comm".
  - by_reduction.
  - cleanup_elab_after eredex_steps_with heap "lookup_miss".
  - cleanup_elab_after eredex_steps_with heap "lookup_empty".
  - by_reduction.
  - compute_eq_compilation.
    reduce.
    eapply eq_term_sym.
    step_backward block_subst "blk_subst_id".
    step_backward value_subst "snoc_wkn_hd".
    step_backward cc_lang "clo_eta".
    reduce.
    eredex_steps_with unit_eta "unit eta".
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - compute_eq_compilation.
    reduce.
    hide_implicits.
    eapply eq_term_sym.
    eapply eq_term_trans.
    { eredex_steps_with block_subst "blk_subst_cmp". }
    simpl; hide_implicits.
    reduce.
    hide_implicits.
    eapply eq_term_sym.
    reduce.
    hide_implicits.
    step_backward cc_lang "clo_eta".
    reduce.
    hide_implicits.
    eapply eq_term_sym.
    step_backward cc_lang "clo_eta".
    reduce.
    hide_implicits.
    admit.
  - compute_eq_compilation.
    reduce.
    step_backward cc_lang "clo_eta".
    by_reduction.
  - simpl.

    step_backward cc_lang "clo_eta".
    hide_implicits.
    reduce.
    hide_implicits.

    simpl.
    hide_implicits.
    eapply eq_term_sym.
    reduce; hide_implicits.
    step_backward cc_lang "clo_eta".
    reduce; hide_implicits.
    eapply eq_term_sym.
    step_backward cc_lang "clo_eta".
    reduce; hide_implicits.
    step_backward cc_lang "clo_eta".
    reduce; hide_implicits.
    eapply eq_term_sym.
    step_backward cc_lang "clo_eta".
    hide_implicits.
    eredex_steps_with unit_eta "unit eta".
  - simpl.
    admit.
  - simpl.
    admit.
  - simpl.
    admit.
  - 
    
    
    by_reduction.
         step_if_concrete.

         
    1: eredex_steps_with cc_lang "clo_eta".
    step_backward cc_lang "clo_eta".
    hide_implicits.
    
    Print by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - by_reduction.
  - cleanup_elab_after eredex_steps_with heap "heap_comm".
  - cleanup_elab_after eredex_steps_with heap "lookup_miss".
  - cleanup_elab_after eredex_steps_with heap "lookup_empty".
  - simpl.
    admit.
  - admit.
  - admit.
  - admit.
  - reduce.
    cleanup_elab_after eredex_steps_with heap "".
  - cleanup_elab_after eredex_steps_with heap "".
  - cleanup_elab_after eredex_steps_with heap "".
  - cleanup_elab_after eredex_steps_with heap "".
  - cleanup_elab_after eredex_steps_with heap "".
  - cleanup_elab_after eredex_steps_with heap "".

Qed.
#[export] Hint Resolve subst_cc_preserving : elab_pfs.


