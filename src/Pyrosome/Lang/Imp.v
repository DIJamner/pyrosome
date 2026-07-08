From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Lang.LinearSubst Lang.LinearSTLC
  Tools.Matches Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference
  Tools.EGraph.InjRuleGen
  Tools.EGraph.Automation.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVCC SimpleVFixCC
  SimpleVCPSHeap SimpleUnit SimpleVCCHeap SimpleVCPS NatHeap.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.


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

Definition ch8_injectivity :=
  [("assign", ["e"; "x"]); ("neq_0_r", ["n"]); ("value", ["n"]); ("1+", ["n"]);
   ("if0", ["nz"; "z"; "e"]); ("while", ["c"; "e"]); ("neq_1+", ["p"; "m"; "n"]);
   ("hvar", ["n"]); ("seq", ["cmd2"; "cmd1"]); ("neq", ["m"; "n"]); ("lookup", ["l"]);
   ("neq_0_l", ["n"])].

Definition ch8 :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 (heap++nat_lang) ch8_def.

Lemma ch8_wf : wf_lang_ext (heap++nat_lang) ch8.
Proof. compute_wf_lang. Qed.
#[local] Definition ch8_entry :=
  lang_entry ch8_wf.
#[export] Hint Resolve ch8_entry : wf_lang_db.

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

Definition ch8_config_injectivity :=
  [("neq", ["m"; "n"]); ("neq_1+", ["p"; "m"; "n"]); ("neq_0_l", ["n"]); ("hvar", ["n"]);
   ("if0", ["nz"; "z"; "e"]); ("1+", ["n"]); ("while", ["c"; "e"]); ("assign", ["e"; "x"]);
   ("value", ["n"]); ("neq_0_r", ["n"]); ("lookup", ["l"])].

Definition ch8_config :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 (ch8 ++ heap++nat_lang) ch8_config_def.

Lemma ch8_config_wf : wf_lang_ext (ch8 ++ heap++nat_lang) ch8_config.
Proof.  compute_wf_lang. Qed.
#[local] Definition ch8_config_entry :=
  lang_entry ch8_config_wf.
#[export] Hint Resolve ch8_config_entry : wf_lang_db.

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

Definition ch8_ectx_injectivity :=
  [("Eassign", ["E"; "x"]); ("lookup", ["l"]); ("Eplug", ["e"; "E"]); ("Eseq", ["c"; "C"]);
   ("neq_0_r", ["n"]); ("1+", ["n"]); ("Cplug", ["e"; "C"]); ("Eif0", ["nz"; "z"; "E"]);
   ("neq", ["m"; "n"]); ("neq_1+", ["p"; "m"; "n"]); ("value", ["n"]); ("if0", ["nz"; "z"; "e"]);
   ("neq_0_l", ["n"]); ("hvar", ["n"]); ("while", ["c"; "e"]); ("assign", ["e"; "x"])].

Definition ch8_ectx :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100 (ch8_config ++ ch8 ++ heap++nat_lang) ch8_ectx_def.

Lemma ch8_ectx_wf : wf_lang_ext (ch8_config ++ ch8 ++ heap++nat_lang) ch8_ectx.
Proof.  compute_wf_lang. Qed.
#[local] Definition ch8_ectx_entry :=
  lang_entry ch8_ectx_wf.
#[export] Hint Resolve ch8_ectx_entry : wf_lang_db.

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

Ltac clo_eta_cong :=
  eapply eq_term_trans;
  [ eapply eq_term_sym; now eredex_steps_with cc_lang "clo_eta"|];
  compute_eq_compilation;
  reduce_lhs;
  eapply eq_term_trans; cycle
(*Use: `hide_implicits` shows the pre-elaboration terms,
  and `wysiwyg` shows the actual goal again.
 *)
 1;
  [ now eredex_steps_with cc_lang "clo_eta"|];
  reduce_rhs;
  repeat (term_cong;
          unfold Model.eq_term;
          try term_refl;[]).

(* ============================================================================
   inj_rules-driven pre-pass for by_reduction.

   The generated injectivity/cancellation schemas ([gen_fundep_schemas]) DRIVE
   the decomposition: at each node [cong_subgoals_gen] consults the rules to
   decide whether (and on which args) the goal [f s1 = f s2] may be split; we
   realize the sanctioned split with [term_cong] (closing the required-equal
   args by [term_refl]) and recurse, so the e-graph is only ever built over the
   small leaves the rules cannot decompose.  (Not blind congruence: a node is
   peeled ONLY where the rules say [f] is injective/cancellable there.)
   ============================================================================ *)
Fixpoint select_recurse (c : list (string * Term.sort string)) (recurse : list string)
  (s1 s2 : list (Term.term string)) : option (list (Term.term string * Term.term string)) :=
  match recurse, c, s1, s2 with
  | [], [], _, _ => Some []
  | [], (_::_), _, _ => if eqb s1 s2 then Some [] else None
  | x::recurse', (x',_)::c', e1::s1', e2::s2' =>
      if eqb x x' then
        match select_recurse c' recurse' s1' s2' with
        | Some rest => Some ((e1,e2)::rest) | None => None end
      else if eqb e1 e2 then select_recurse c' recurse s1' s2' else None
  | _, _, _, _ => None
  end.

Definition gen_inj_rules := list (string * list (list string)).

Definition cong_subgoals_gen (l : list (string * Rule.rule string)) (rules : gen_inj_rules)
  (goal : Term.term string * Term.term string) : list (Term.term string * Term.term string) :=
  let '(e1,e2) := goal in
  match e1, e2 with
  | con n1 s1, con n2 s2 =>
      if eqb n1 n2 then
        match named_list_lookup_err rules n1, named_list_lookup_err l n1 with
        | Some alts, Some (term_rule c _ _) =>
            let fix try_alts alts :=
              match alts with
              | [] => [(e1,e2)]
              | recurse :: alts' =>
                  match select_recurse c recurse s1 s2 with
                  | Some sub => sub | None => try_alts alts' end
              end in try_alts alts
        | _, _ => [(e1,e2)] end
      else [(e1,e2)]
  | _, _ => [(e1,e2)]
  end.

Fixpoint group_concls (fds : list (string * (list string * list string))) : gen_inj_rules :=
  match fds with
  | [] => []
  | (n,(_sh,concl)) :: rest =>
      let g := group_concls rest in
      match concl with
      | [] => g
      | _ => let fix ins g :=
               match g with
               | [] => [(n,[concl])]
               | (n',alts)::g' =>
                   if eqb n n' then (n', if existsb (eqb concl) alts then alts else alts ++ [concl]) :: g'
                   else (n',alts) :: ins g'
               end in ins g
      end
  end.

(* small pre-reduced fragment carrying the goal-spine ops' contexts; used for
   the [cong_subgoals_gen] lookup so we never vm_compute over the huge
   [target_lang] at each node.  (The ops have the same contexts here as in
   [target_lang], so the decomposition is identical.) *)
Definition ch8_cover : list (string * Rule.rule string) :=
  Eval vm_compute in
    (cc_lang ++ prod_cc ++ cps_prod_lang ++ unit_lang ++ block_subst ++ value_subst).

(* generated from that fragment *)
Definition ch8_inj_rules : gen_inj_rules :=
  Eval vm_compute in group_concls (gen_fundep_schemas 3 ch8_cover).

(* rule-driven: peel a node ONLY when the rules sanction the decomposition AND
   it stays linear (exactly one nontrivial child), so branching nodes are left
   compact for by_reduction instead of being fragmented into separately-hard
   sub-equations.  The rules' value is refusing to peel a non-injective
   single-child node (e.g. .1 x = .1 y, where .1 is not injective in the value)
   that blind congruence peeling would wrongly split. *)
Ltac inj_prepass rules :=
  try (unfold Model.eq_term);
  lazymatch goal with
  | |- eq_term _ _ _ ?E1 ?E2 =>
      let d := eval vm_compute in (cong_subgoals_gen ch8_cover rules (E1,E2)) in
      lazymatch d with
      | cons (pair E1 E2) nil => idtac              (* rules do not decompose: leave *)
      | _ =>
          let nt := eval vm_compute in
            (List.length (filter (fun p => negb (eqb (fst p) (snd p))) d)) in
          lazymatch nt with
          | 1%nat => term_cong; try term_refl; [> inj_prepass rules ..]  (* linear: peel *)
          | _ => idtac                               (* branching: keep compact *)
          end
      end
  | |- _ => idtac
  end.

Ltac by_reduction_prepass rules :=
  compute_eq_compilation;
  Matches.reduce;
  inj_prepass rules;
  Automation.by_reduction; Matches.t'.

Derive ch8_cc
       in (elab_preserving_compiler
                   []
                   target_lang
                   ch8_cc_def
                   ch8_cc
                   (ch8_ectx++ch8_config++ch8++heap++nat_lang))
       as ch8_cc_preserving.
Proof.
  (*Note: Automation.auto_elab_compiler doesn't work because the goals take too long to fail. *)
  ElabCompilers.auto_elab_compiler.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.    
  - (*TODO: this case takes at least a while w/ by_reduction.
      probably wants inj congruence.
      TODO: more specifically, probably wants something intelligent.
      The current proof uses this reasoning:
      <e>[/s/] = <e>[/s'/] iff s = s' for metavariable <e>.
      How should I express that?
      *)
    compute_eq_compilation.
    Matches.reduce.
    repeat (term_cong; try term_refl;[]).
    clo_eta_cong.
    (*
    UnElab.hide_implicits.
    TODO: injectivity doesn't deal well w/ closures!.
    not very injective.
    Need the following injectivity pattern:
      <\xy.e, c> = <\xy.e', c> <-> e = e'.
    if c is the same, then e, e' injective. requires more complicated pattern than I have
                           
    
Definition cc_injectivity :=
  [("jmp", ["G"]); ("cont", ["e";"A"; "G"]); ("neg", ["A"])].

  TODO: clo_eta is expensive
     *)
    clo_eta_cong.
    Automation.by_reduction;Matches.t'.
  - (* metavariable-substitution congruence: the generated inj_rules drive the
       decomposition (cong_subgoals_gen) BEFORE saturation. *)
    by_reduction_prepass ch8_inj_rules.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.
  - Automation.by_reduction; Matches.t'.
  Unshelve.
  all: repeat Matches.t'.
Qed.
#[local] Definition ch8_cc_entry :=
  cmp_entry (elab_compiler_implies_preserving ch8_cc_preserving).
#[export] Hint Resolve ch8_cc_entry : wf_lang_db.


