Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers Tools.Matches.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVCC SimpleVFixCC SimpleVCPSHeap SimpleUnit SimpleVCCHeap SimpleVCPS NatHeap.
Import Core.Notations.
Import CompilerDefs.Notations.
Require Coq.derive.Derive.

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
    [:= "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_skip")
      #"seq" #"skip" "c" ="c" : #"cmd"
    ];
    [:= "c" : #"cmd"
      ----------------------------------------------- ("ss_skip_seq")
      #"seq" "c" #"skip" = "c" : #"cmd"
    ];
    [:= "H" : #"heap",
        "v" : #"natural",
        "x" : #"natural",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_assign")
      #"config" "H" (#"seq" (#"assign" "x" (#"value" "v")) "c")
      = #"config" (#"hset" "H" "x" "v") "c" : #"configuration"
    ];
    [:= "e" : #"exp",
        "z" : #"cmd",
        "nz" : #"cmd",
        "c" : #"cmd",
        "n" : #"natural"
      ----------------------------------------------- ("ss_seq_if_nonzero")
      #"seq" (#"if0" (#"value" (#"1+" "n"))"z" "nz") "c"
      = #"seq" "nz" "c" : #"cmd"
    ];
    [:= "e" : #"exp",
        "z" : #"cmd",
        "nz" : #"cmd",
        "c" : #"cmd"
      ----------------------------------------------- ("ss_seq_if_zero")
      #"seq" (#"if0" (#"value" #"0") "z" "nz") "c"
      = #"seq" "z" "c" : #"cmd"
    ];
    [:= "e" : #"exp",
        "c1" : #"cmd",
        "c2" : #"cmd",
        "n" : #"natural"
      ----------------------------------------------- ("ss_seq_while_true")
      #"seq" (#"while" "e" "c1") "c2"
      = #"seq" (#"if0" "e" #"skip" (#"seq" "c1" (#"while" "e" "c1") )) "c2"
      : #"cmd"
    ];
    [:= "c1" : #"cmd",
        "c2" : #"cmd",
        "c3" : #"cmd"
      ----------------------------------------------- ("ss_seq_seq")
      #"seq" (#"seq" "c1" "c2") "c3"
      = #"seq" "c1" (#"seq" "c2" "c3") : #"cmd"
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
    (* Note: including this is incorrect
    [:| "E" : #"Ectx", 
        "c" : #"cmd"
      -----------------------------------------------
      #"Ewhile" "E" "c" : #"Cctx"
    ];*)
    [:| "C" : #"Cctx", 
        "c" : #"cmd"
      -----------------------------------------------
      #"Eseq" "C" "c" : #"Cctx"
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
    ];(*
    [:= "E" : #"Ectx",
        "c" : #"cmd",
        "e" : #"exp"
      ----------------------------------------------- ("Cplug while")
      #"Cplug" (#"Ewhile" "E" "c") "e" = #"while" (#"Eplug" "E" "e") "c" : #"cmd"
    ];*)
    [:= "C" : #"Cctx",
        "c" : #"cmd",
        "e" : #"exp"
      ----------------------------------------------- ("Cplug seq")
      #"Cplug" (#"Eseq" "C" "c") "e" = #"seq" (#"Cplug" "C" "e") "c" : #"cmd"
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

(* b : blk [... ; ~nat]
   val [...] ~~nat *)
Definition blk_to_val b :=
  {{e #"closure" (#"neg" #"nat") (#"blk_subst" (#"snoc" #"wkn" (#".2" #"hd")) {b}) #"tt"}}.

(* E : blk [A x nat]
   e : blk [~nat]
   blk [A]

E[e] = e[/g/]
where g : [A] => [~nat]
g = snoc id v
where v : val [A] ~nat
v = clo <b,hd>
where b : [A x nat]
b = E[(0,1)/0]

E[e] = e[/<id,clo<E[(0,1)/0],hd>>/]
 *)
Definition plug E e :=
  {{e #"blk_subst" (#"snoc" #"wkn" (#"closure" #"nat" {E} #"hd"))
      {e} }}.

Definition plug_Ectx e c :=
  {{e #"blk_subst"
      (#"snoc" #"wkn" (#"pair" (#"closure" #"nat" {c} (#".1" #"hd")) (#".2" #"hd")))
      {e} }}.

(* e : blk [A x ~nat]
   z : blk [~unit]
   nz : blk[~unit]
   blk [... ; ~unit] *)
Definition Eif0 E z nz :=
  plug_Ectx E {{e #"if0" (#".2" #"hd") (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {z}) (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) {nz}) }}.

(*
(* E : blk [ ~nat x nat]
   c : blk [... ; ~unit]
   blk [... ; ~unit x nat] *) 
Definition Ewhile E c :=
  {{e #"jmp" (#"fix"
                (#"closure"
                   (#"prod" (#"neg" #"unit") #"unit")
                   (*
                     [(~unit * nat) * (~unit * unit)]
                    *)
                   (#"blk_subst"
                      (#"snoc" #"wkn"
                         (#"pair" (#"closure" #"nat"
                                     (*
                                        [(k : ~unit * loop : ~unit ) * nat]
                                      *)
                                     (#"if0" (#".2" #"hd") (* blk [((~unit, (~unit, unit)), nat)] *)
                                        (#"jmp" (#".1" (#".1" #"hd")) #"tt")
                                        (#"blk_subst" (#"snoc" #"wkn" (#".2" (#".1" #"hd"))) {c}))
                                     (#"pair" (#".1" (#".1" #"hd")) (#".1" (#".2" #"hd"))))
                            (#".2" (#".1" #"hd")) ))
                      {E})
                   #"hd"))
      #"tt"
  }}.
*)
   (*   {{e #"jmp" (#"fix"
                   (#"closure"
                     (#"prod" (#"neg" #"unit") #"unit")
                     (#"blk_subst" (* [((~nat, ~~nat), (~unit, unit))] *)
                       (#"snoc"
                         (#"snoc" #"forget"
                           (#"closure" #"nat"
                             (#"if0" (#".2" #"hd")
                               (#"jmp" (#".1" (#".1" (#".1" #"hd"))) #"tt")
                               (#"blk_subst" (#"snoc" #"wkn" (#".1" (#".2" (#".1" #"hd")))) "c")
                             )
                             #"hd"
                           )
                         )
                         (#".2" (#".1" #"hd"))
                       )
                       "E"
                     )
                     (#"pair" (#"val_subst" #"wkn" #"hd") #"hd")
                   )
                 )
          #"tt"
  }}*)

(* x : natural
   e : blk [... ; ~nat]
   blk [... ; ~unit] *)
Definition Eassign x e :=
  plug_Ectx e {{e #"set" (#"nv" {x}) (#".2" #"hd") (#"jmp" (#".1" #"hd") #"tt")}}.

Definition ch8_cc_def : compiler :=
  match # from (ch8_ectx ++ ch8_config ++ ch8 ++ heap ++ nat_lang) with
  | {{s #"exp"}} => {{s #"blk" {exp_env} }}
  | {{s #"cmd"}} => {{s #"blk" {cmd_env} }}
  | {{s #"configuration"}} => {{s #"configuration" {cmd_env} }}
  | {{s #"Ectx"}} => {{s #"blk" (#"ext" #"emp" (#"prod" (#"neg" #"nat") #"nat")) }}
  | {{s #"Cctx"}} => {{s #"blk" (#"ext" #"emp" (#"prod" (#"neg" #"unit") #"nat")) }}
  | {{e #"value" "n"}} => {{e #"jmp" #"hd" (#"nv" "n")}}
  | {{e #"hvar" "n"}} => {{e  #"get" (#"nv" "n") (#"jmp" (#"val_subst" #"wkn" #"hd") #"hd")}}
  | {{e #"skip"}} => jmp_hd
  | {{e #"assign" "x" "e" }} => assign {{e "x"}} {{e "e"}}
  | {{e #"seq" "cmd1" "cmd2"}} => seq {{e "cmd1"}} {{e "cmd2"}}
  | {{e #"if0" "e" "z" "nz"}} => if0 {{e "e"}} {{e "z"}} {{e "nz"}}
  | {{e #"while" "e" "c"}} => while {{e "e"}} {{e "c"}}
  | {{e #"config" "H" "c"}} => {{e #"config" "H" "c"}}
  | {{e #"[ ]"}} => {{e #"jmp" (#".1" #"hd") (#".2" #"hd") }}
  | {{e #"Eassign" "x" "E"}} => Eassign {{e "x"}} {{e "E"}}
  | {{e #"Eif0" "E" "z" "nz"}} => Eif0 {{e "E"}} {{e "z"}} {{e "nz"}}
  (*| {{e #"Ewhile" "E" "c"}} => Ewhile {{e "E"}} {{e "c"}}*)
  | {{e #"Eseq" "E" "cmd2"}} => 
      {{e #"blk_subst" (#"snoc" #"wkn"
                          (#"pair" (#"closure" #"unit"
                                      (#"blk_subst" (#"snoc" #"wkn" (#".1" #"hd")) "cmd2") (#".1" #"hd"))
                             (#".2" #"hd")))
          "E" }}
  | {{e #"Cplug" "C" "e"}} => plug {{e "C"}} {{e "e"}}
  | {{e #"Eplug" "E" "e"}} => plug {{e "E"}} {{e "e"}}
  end.

Notation target_lang :=
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


Ltac reduce :=
  repeat (
      eapply eq_term_trans;
      (try cleanup_elab_after step_if_concrete);
      try_term_cong).

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
  auto_elab_compiler.
  
  Ltac clo_eta_cong :=
    eapply eq_term_trans;
    [ eapply eq_term_sym; now eredex_steps_with cc_lang "clo_eta"|];
    compute_eq_compilation;
    reduce_lhs;
    eapply eq_term_trans; cycle 1;
    [ now eredex_steps_with cc_lang "clo_eta"|];
    reduce_rhs;
    repeat (term_cong; 
            unfold Model.eq_term;
            try term_refl;[]).
  
  - cleanup_elab_after eredex_steps_with heap "heap_comm".
  - cleanup_elab_after eredex_steps_with heap "lookup_miss".
  - cleanup_elab_after eredex_steps_with heap "lookup_empty".
  - compute_eq_compilation.
    reduce.
    eapply eq_term_sym.
    step_backward block_subst "blk_subst_id".
    step_backward value_subst "snoc_wkn_hd".
    step_backward cc_lang "clo_eta".
    reduce.
    eredex_steps_with unit_eta "unit eta".
  - compute_eq_compilation.
    Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    (*TODO: expensive*)
    repeat clo_eta_cong.
    compute_eq_compilation.
    (*TODO: why aren't all unit terms reduced to tt?
    Matches.reduce.*)
    eredex_steps_with unit_eta "unit eta".
  - compute_eq_compilation.
    reduce.
    step_backward cc_lang "clo_eta".
    by_reduction.
  - compute_eq_compilation.
    Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    repeat clo_eta_cong.
    eapply eq_term_trans.
    {
      term_cong;unfold Model.eq_term.
      - right; compute; reflexivity.
      - term_refl.
      - term_refl.
      - term_cong.
        + right; compute; reflexivity.
        + term_refl.
        + term_refl.
        + term_refl.
        + term_refl.
        + instantiate (1:= {{e #"hd" #"emp" (#"neg" #"nat") }}).
          unfold Model.eq_term.
          eapply eq_term_trans; cycle 1.
          {
            compute_eq_compilation.
            eredex_steps_with cc_lang "clo_eta".
          }
          compute_eq_compilation.
          term_cong.
          *term_refl.
          *term_refl.
          *term_refl.
          * unfold Model.eq_term.
            compute_eq_compilation.
            Matches.reduce.
            term_refl.
          * unfold Model.eq_term.
            compute_eq_compilation.
            Matches.reduce.
            term_refl.
      - term_refl.
    }
    Matches.by_reduction.
  - compute_eq_compilation.
    Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    repeat clo_eta_cong.
    unfold Model.eq_term.
    compute_eq_compilation.
    term_refl.
  - compute_eq_compilation.
    Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    repeat clo_eta_cong.
    term_refl.
    (*
  - compute_eq_compilation.
    Matches.reduce.
    admit Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    repeat clo_eta_cong.
    unfold Model.eq_term.
    compute_eq_compilation.
    hide_implicits.
    term_refl.*)
  - compute_eq_compilation.
    Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    repeat clo_eta_cong.
    term_refl.
  - compute_eq_compilation.
    Matches.reduce.
    unfold Model.eq_term.
    compute_eq_compilation.
    eapply eq_term_trans.
    {
      eredex_steps_with heap_cps_ops "eval get".
    }
    
    Matches.by_reduction.

    Unshelve.
    all: repeat Matches.t'.
Qed.
#[export] Hint Resolve ch8_cc_preserving : elab_pfs.


