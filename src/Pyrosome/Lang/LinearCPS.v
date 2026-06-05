Set Implicit Arguments.

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
  Tools.EGraph.Automation.

Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.

Local Notation compiler := (compiler string).

Definition linear_cps_lang_def : lang :=
  {[l/lin_subst (* [linear_blk_subst ++ linear_value_subst] *)
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
  [:| "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (ext "G" "A")
      -----------------------------------------------
      #"cont" "A" "e" : #"val" "G" (#"neg" "A")
   ];
   [:| "G" : #"env", "H" : #"env",
       "A" : #"ty",
       "v1" : #"val" "G" (#"neg" "A"),
       "v2" : #"val" "H" "A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" (#"conc" "G" "H")
   ];
  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "e" : #"blk" (ext "G" "A"),
      "v" : #"val" "H" "A"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"cont" "A" "e") "v"
      = #"blk_subst" (#"csub" (#"id" "G") (#"vsub" "v")) "e"
      : #"blk" (#"conc" "G" "H")
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" (#"neg" "A")
      ----------------------------------------------- ("cont_eta")
      #"cont" "A" (#"jmp" "v" (#"hd" "A")) = "v"
      : #"val" "G" (#"neg" "A")
  ]
  ]}.

(*TODO: move to LinearSubst *)
Definition linear_value_subst_injectivity :=
  [("exch", ["H";"G"]);("vsub",["v";"A"; "G"]);("hd", ["A"]);
   ("only", ["A"]); ("emp", []); ("val_subst", ["A"; "G"]); ("val", ["A"; "G"]);
   ("cmp", ["G3"; "G1"]); ("id", ["G"]); ("sub", ["G'"; "G"]); ("env", []); ("ty", [])].

(*TODO: move to LinearSubst *)
Definition linear_block_subst_injectivity :=
  [("blk_subst", ["G"]); ("blk", ["G"])].

Definition linear_cps_injectivity :=
  [("cont", ["e";"A"; "G"]); ("neg", ["A"])].

(* TODO: doesn't know that ext is injective, so jump beta doesn't infer
Definition linear_cps_lang :=
  Eval vm_compute in
    (infer_lang_ext_simple
       (linear_block_subst ++ linear_value_subst)
       linear_cps_lang_def
       (linear_cps_injectivity
          ++linear_block_subst_injectivity
          ++linear_value_subst_injectivity)).
*)

Derive linear_cps_lang
       in (elab_lang_ext (linear_block_subst ++ linear_value_subst)
                               linear_cps_lang_def
                               linear_cps_lang)
       as cps_lang_wf.
Proof.
  auto_elab.
Qed.
#[local] Definition linear_cps_entry :=
  lang_entry (elab_lang_implies_wf cps_lang_wf).
#[export] Hint Resolve linear_cps_entry : wf_lang_db.

Definition linear_cps_subst_def : compiler :=
  match # from (linear_exp_subst ++ linear_value_subst) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (ext "G" (#"neg" "A")) }}
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"csub" "g" (#"id" (#"only" (#"neg" "A")))) "e"}}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"blk_subst" (#"exch" "G" (#"only" (#"neg" "A"))) (#"jmp" (#"hd" (#"neg" "A")) "v")}}
  end.

Derive linear_cps_subst
       in (elab_preserving_compiler []
                                          (linear_cps_lang
                                             ++ linear_block_subst
                                             ++ linear_value_subst)
                                          linear_cps_subst_def
                                          linear_cps_subst
                                          (linear_exp_subst ++ linear_value_subst))
       as linear_cps_subst_preserving.
Proof.
  auto_elab_compiler.
Qed.
#[local] Definition linear_cps_cmp_entry :=
  cmp_entry (elab_compiler_implies_preserving linear_cps_subst_preserving).
#[export] Hint Resolve linear_cps_cmp_entry : preserving_db.

(*TODO: separate file?*)
Definition linear_cps_prod_lang_def : lang :=
{[l/lin_subst

  [:| "A" : #"ty", "B": #"ty"
      -----------------------------------------------
      #"prod" "A" "B" : #"ty"
  ];

  [:| "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e1" : #"val" "G" "A",
      "e2" : #"val" "H" "B"
      -----------------------------------------------
      #"pair" "e1" "e2" : #"val" (#"conc" "G" "H") (#"prod" "A" "B")
  ];

  [:| "G" : #"env", "H" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v" : #"val" "H" (#"prod" "A" "B"),
      "e" : #"blk" (ext (ext "G" "A") "B")
      -----------------------------------------------
      #"pm_pair" "v" "e" : #"blk" (#"conc" "G" "H")
  ];

  [:= "G" : #"env", "H" : #"env", "K" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "H" "B",
      "e" : #"blk" (ext (ext "K" "A") "B")
      ----------------------------------------------- ("eval pm_pair")
      #"pm_pair" (#"pair" "v1" "v2") "e"
      = #"blk_subst" (#"csub" (#"id" "K") (#"csub" (#"vsub" "v1") (#"vsub" "v2"))) "e"
      : #"blk" (#"conc" "K" (#"conc" "G" "H"))
  ];
  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty", "B" : #"ty",
      "v" : #"val" "H" (#"prod" "A" "B"),
      "e" : #"blk" (ext "G" (#"prod" "A" "B"))
      ----------------------------------------------- ("prod_eta")
      #"pm_pair" "v" (#"blk_subst" (#"csub" (#"id" "G") (#"vsub" (#"pair" (#"hd" "A") (#"hd" "B")))) "e")
      = #"blk_subst" (#"csub" (#"id" "G") (#"vsub" "v")) "e"
      : #"blk" (#"conc" "G" "H")
  ] ]}.

Derive linear_cps_prod_lang
       in (elab_lang_ext (linear_block_subst ++ linear_value_subst) linear_cps_prod_lang_def linear_cps_prod_lang)
       as linear_cps_prod_wf.
Proof. auto_elab. Qed.
#[local] Definition linear_cps_prod_entry :=
  lang_entry (elab_lang_implies_wf linear_cps_prod_wf).
#[export] Hint Resolve linear_cps_prod_entry : wf_lang_db.

(* e: blk G; {~A}
   k: blk H; {A} *)
Definition bind e G A k :=
  {{e #"blk_subst" (#"csub" (#"id" {G})
      (#"vsub" (#"cont" {A} {k}))) {e} }}.
(* bind: blk G; H *)
Arguments bind e G A k/.

Definition linear_cps_def : compiler :=
  match # from (linear_stlc) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (ext "G" (#"neg" "A")) }}
  | {{e #"lolli" "A" "B"}} =>
    {{e #"neg" (#"prod" "A" (#"neg" "B")) }}
  | {{e #"linear_lambda" "G" "A" "B" "e"}} =>
    {{e #"cont" (#"prod" "A" (#"neg" "B"))
      (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e")}}
  | {{e #"linear_app" "G" "H" "A" "B" "e" "e'"}} =>
    (* blk G; H; {~B} *)
    bind (var "e") (var "G") {{e #"neg" (#"prod" "A" (#"neg" "B"))}}
    ( (* blk H; {~B}; {~(A * ~B)} *)
      bind (var "e'") (var "H") (var "A")
      ( (* blk {~B}; {~(A * ~B)}; {A} *)
        {{e #"blk_subst"
          (#"csub" (#"exch" (#"only" (#"neg" "B")) (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))))
                   (#"id" (#"only" "A")))
          (* blk {~(A * ~B)}; {~B}; {A} *)
          (#"jmp" (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
            (* val {~B}; {A} (A * ~B) *)
            (#"val_subst" (#"exch" (#"only" (#"neg" "B")) (#"only" "A"))
              (* val {A}; {~B} (A * ~B) *)
              (#"pair" (#"hd" "A") (#"hd" (#"neg" "B")))))
        }}
      )
    )
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"csub" "g" (#"id" (#"only" (#"neg" "A")))) "e"}}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"blk_subst" (#"exch" "G" (#"only" (#"neg" "A"))) (#"jmp" (#"hd" (#"neg" "A")) "v")}}
  end.


From Pyrosome.Tools Require Import UnElab.
From Pyrosome.Proof Require Import TreeProofs.
Ltac by_reduction := Matches.by_reduction.
Ltac reduce_by l r :=
  eapply eq_term_trans;
  [> eredex_steps_with l r | ..].

Ltac normalize_env_step :=
  compute_eq_compilation;
  match goal with
  | |- eq_term _ _ {{s #"env"}} {{e #"conc" #"emp" {_} }} _ =>
    reduce_by linear_value_subst "conc_emp_l"
  | |- eq_term _ _ {{s #"env"}} {{e #"conc" {_} #"emp" }} _ =>
    reduce_by linear_value_subst "conc_emp_r"
  | |- eq_term _ _ {{s #"env"}} {{e #"conc" (#"conc" {_} {_}) {_} }} _ =>
    reduce_by linear_value_subst "conc_assoc"
  | |- eq_term _ _ {{s #"env"}} {{e #"conc" {_} {_} }} _ => term_cong
  | _ => term_refl
  end.

Ltac normalize_env :=
  eapply eq_term_trans;
  [> repeat normalize_env_step; term_refl | .. ].


Ltac solve_wf_term := first [eapply wf_term_by';
  [> solve_in | solve_wf_args | first [left; reflexivity | right; solve_sort] ]
  | eapply wf_term_var; solve_in]
with solve_wf_args :=
  first [apply wf_args_nil | constructor; [> solve_wf_term | solve_wf_args ]]
with env_eq :=
  compute_eq_compilation;
  normalize_env;
  eapply eq_term_sym;
  normalize_env;
  apply eq_term_refl;
  solve_wf_term
with solve_sort := sort_cong; [> env_eq .. ].

Ltac solve_wf_subst :=
  repeat (eapply wf_subst_cons; [> .. | solve_wf_term ]);
  eapply wf_subst_nil.

Ltac blk_cmp :=
  eapply eq_term_trans;
  [> lazymatch goal with
    | [|- eq_term _ _ _ {{e #"blk_subst" {_} {_}
      (#"cmp" {?G1} {?G2} {?G3} {?g1} {?g2})
      {?e} }} _ ] =>
      instantiate (1:=
        {{e #"blk_subst" {G1} {G2} {g1}
            (#"blk_subst" {G2} {G3} {g2} {e})}});
      apply eq_term_sym;
      eapply eq_term_conv;
      [> eredex_steps_with linear_block_subst "blk_subst_cmp";
        solve_wf_subst
      | solve_sort]
    end
  | .. ].

 Ltac s :=
   match goal with
  | [|- fresh _ _ ]=> compute_fresh
  | [|- sublist _ _ ]=> compute_sublist
   (* TODO: if this works, use this pattern for other typeclass occurances *)
  | [|- In _ _ ]=> solve_in
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => (repeat eapply elab_args_cons_ex') || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_by' || eapply elab_term_var
  | [|-wf_term _ _ _ _] => solve_wf_term || shelve
  | [|-elab_rule _ _ _] => econstructor
  (* | [|- ?eq \/ ?seq ] => tryif (has_evar ?Goal) then shelve else (left; reflexivity) || shelve *)
  | [|- _ = _] => compute; reflexivity
 end.

Ltac reduce_to e :=
  eapply eq_term_trans;
  [> instantiate (1:=e); try by_reduction | .. ].

Ltac break_cmp :=
  term_cong; cycle 1;
  [> term_refl | term_refl | term_refl |
      compute_eq_compilation | compute_eq_compilation |
      left; solve_sort ].

Ltac normalize_perm :=
  lazymatch goal with
  | [|- eq_term _ _ {{s #"sub" {?s1} {?s2} }} ?e _ ] =>
    lazymatch e with
    | {{e #"cmp" {_} {_} {_} {_} {_} }} =>
      eapply eq_term_trans;
      [> break_cmp;
        [> normalize_perm | term_refl ] |
        compute_eq_compilation ]
    | _ => term_refl
    end
  end.

Ltac csub_join G G' H H' g h :=
  match h with
  | {{e #"csub" {?H1} {?H1'} {?H2} {?H2'} {?h1} {?h2} }} =>
    csub_join
      {{e #"conc" {G} {H1} }} {{e #"conc" {G'} {H1'} }} H2 H2'
      {{e #"csub" {g} {h1} }} h2
  | _ => constr:({{e #"csub" {G} {G'} {H} {H'} {g} {h} }})
  end.

Ltac csub_normalize cs :=
  match cs with
  | {{e #"csub" {?G} {?G'} {?H} {?H'} {?g} {?h} }} =>
    let g' := csub_normalize g in
    let h' := csub_normalize h in
    csub_join G G' H H' g' h'
  | {{e #"id" (#"conc" {?G} {?H}) }} =>
    csub_normalize {{e #"csub" {G} {G} {H} {H} (#"id" {G}) (#"id" {H}) }}
  | _ => cs
  end.

Ltac exch_invert :=
  compute_eq_compilation;
  eapply eq_term_conv;
  [> eapply eq_term_trans;
    [> term_cong; [> .. | term_refl ] |
      compute_eq_compilation;
      eredex_steps_with linear_value_subst "exch_cmp" ] |
    solve_sort ];
  [> env_eq .. | solve_wf_subst ].

Ltac unapply l r :=
  eapply eq_term_sym;
  eredex_steps_with l r.

Ltac trans t :=
  eapply eq_term_trans;
  [> t | .. ].

Ltac eredex_general l r :=
  eapply eq_term_conv;
      [>
        eapply eq_term_trans;
        [> term_cong | .. ];
        [> .. | eredex_steps_with l r ] |
        .. ].

(* Defer every side-condition goal (the term metavariables left after
   [solve_wf_term]); keep only the equational [eq_term] goals in focus.
   Applied as [all: try shelve_if_not_eqterm], this is a position-independent
   replacement for the old [N: shelve] selectors. *)
Ltac shelve_if_not_eqterm :=
  lazymatch goal with
  | |- eq_term _ _ _ _ _ => fail
  | |- _ => shelve
  end.

(* left-assoc cmp of three subs -> split into two cmps *)
Ltac reassoc_cmp4 :=
  lazymatch goal with
  | [|- eq_term _ _ _ {{e #"cmp" {?G1} {?G4} {?G5}
        (#"cmp" {?G1} {?G3} {?G4} (#"cmp" {?G1} {?G2} {?G3} {?c1} {?c2}) {?c3})
        {?c4} }} _ ] =>
      reduce_to {{e #"cmp" {G1} {G3} {G5}
        (#"cmp" {G1} {G2} {G3} {c1} {c2}) (#"cmp" {G3} {G4} {G5} {c3} {c4}) }}
  end.

(* cmp (cmp p cs) e -> cmp p (cmp cs e) *)
Ltac reassoc_cmp3 :=
  lazymatch goal with
  | [|- eq_term _ _ _ {{e #"cmp" {?G1} {?G3} {?G4}
        (#"cmp" {?G1} {?G2} {?G3} {?p} {?cs}) {?e} }} _ ] =>
      reduce_to {{e #"cmp" {G1} {G2} {G4} {p} (#"cmp" {G2} {G3} {G4} {cs} {e}) }}
  end.

(* shared prefix of the two "csub_id dances" *)
Ltac csub_id_dance :=
  trans ltac:(unapply linear_value_subst "csub_id");
  compute_eq_compilation;
  trans ltac:(term_cong; cycle 1;
    [> term_refl .. |
       unapply linear_value_subst "id_left" |
       unapply linear_value_subst "exch_inv" |
       right; reflexivity ]).

Derive linear_cps
       in (elab_preserving_compiler linear_cps_subst
                                          (linear_cps_prod_lang
                                             ++ linear_cps_lang
                                             ++ linear_block_subst
                                             ++ linear_value_subst)
                                          linear_cps_def
                                          linear_cps
                                          linear_stlc)
       as linear_cps_preserving.
Proof.
  setup_elab_compiler.
  { repeat t. }
  { repeat t. }
  { by_reduction; now t'. }
  {
    (*TODO: figure out what t does wrong here,
      or use e-graph inference machinery.
     *)
    repeat s.
    24:instantiate (1 := {{e ext (ext (#"only" (#"neg" "B"))
                                   (#"neg" (#"prod" "A" (#"neg" "B"))))
                             "A" }}).
    30:instantiate (1 := {{e ext "H" (#"neg" "B")}}).
    all: first [left; vm_compute; reflexivity
               | right; sort_cong; by_reduction; now t'].
  }
  { by_reduction; now t'. }
  (* ===== obligation 6 (Linear-STLC-beta): reduce + verified explicit proof ===== *)
  reduce. compute_eq_compilation.
  (* ===== dance 1 ===== *)
  match goal with
  | [|- eq_term _ _ _ {{e #"blk_subst" {_} {_} (#"cmp" {_} {_} {_} (#"exch" {?G} {?H}) (#"csub" {?H} {?H'} {?G} {?G'} {?h} {?g})) (#"jmp" {?H'} {?G'} {?A} {?b} {?a})}} _ ] =>
    reduce_to {{e #"blk_subst" (#"conc" {G} {H}) (#"conc" {H} {G}) (#"exch" {G} {H}) (#"blk_subst" (#"conc" {H} {G}) (#"conc" {H'} {G'}) (#"csub" {H} {H'} {G} {G'} {h} {g}) (#"jmp" {H'} {G'} {A} {b} {a}))}}
  end.
  match goal with
  | [|- eq_term _ _ _ {{e #"blk_subst" {?Ga} {?Gb} (#"exch" {?G} {?H}) (#"blk_subst" {_} {_} (#"csub" {?H2} {?H'} {?G2} {?G'} {?h} {?g}) (#"jmp" {?H'} {?G'} {?A} {?b} {?a}))}} _ ] =>
    eapply eq_term_trans; [ instantiate (1 := {{e #"blk_subst" {Ga} {Gb} (#"exch" {G} {H}) (#"jmp" {H} {G} {A} (#"val_subst" {H2} {H'} {h} (#"neg" {A}) {b}) (#"val_subst" {G2} {G'} {g} {A} {a}))}}) | ]
  end.
  1:term_cong.
  1:(left; solve_sort). 1:term_refl. 1:term_refl. 1:term_refl.
  1:(compute_eq_compilation; eredex_steps_with linear_cps_lang "jmp-subst").
  reduce.
  lazymatch goal with
  | [|- eq_term _ _ _ {{e #"blk_subst" {?G1} {?G5} (#"cmp" {?G1} {?G4} {?G5} (#"cmp" {?G1} {?G3} {?G4} (#"cmp" {?G1} {?G2} {?G3} {?a} {?b}) {?c}) {?d}) {?j} }} _ ] =>
    reduce_to {{e #"blk_subst" {G1} {G3} (#"cmp" {G1} {G2} {G3} {a} {b}) (#"blk_subst" {G3} {G5} (#"cmp" {G3} {G4} {G5} {c} {d}) {j}) }}
  end.
  (* ===== dance 2 ===== *)
  hide_implicits. eapply eq_term_trans.
  1:term_cong.
  1:(left; solve_sort). 1:term_refl. 1:term_refl. 1:term_refl.
  1:(compute_eq_compilation; match goal with | [|- eq_term _ _ _ {{e #"blk_subst" {_} {_} (#"cmp" {_} {_} {_} (#"exch" {?G} {?H}) (#"csub" {?H} {?H'} {?G} {?G'} {?h} {?g})) (#"jmp" {?H'} {?G'} {?A} {?b} {?a})}} _ ] => reduce_to {{e #"blk_subst" (#"conc" {G} {H}) (#"conc" {H} {G}) (#"exch" {G} {H}) (#"blk_subst" (#"conc" {H} {G}) (#"conc" {H'} {G'}) (#"csub" {H} {H'} {G} {G'} {h} {g}) (#"jmp" {H'} {G'} {A} {b} {a}))}} end).
  1:(match goal with | [|- eq_term _ _ _ {{e #"blk_subst" {?Ga} {?Gb} (#"exch" {?G} {?H}) (#"blk_subst" {_} {_} (#"csub" {?H2} {?H'} {?G2} {?G'} {?h} {?g}) (#"jmp" {?H'} {?G'} {?A} {?b} {?a}))}} _ ] => eapply eq_term_trans; [ instantiate (1 := {{e #"blk_subst" {Ga} {Gb} (#"exch" {G} {H}) (#"jmp" {H} {G} {A} (#"val_subst" {H2} {H'} {h} (#"neg" {A}) {b}) (#"val_subst" {G2} {G'} {g} {A} {a}))}}) | ] end).
  1:term_cong.
  1:term_refl. 1:term_refl. 1:term_refl.
  1:(compute_eq_compilation; eredex_steps_with linear_cps_lang "jmp-subst").
  1:term_refl.
  (* ===== push jmp ===== *)
  reduce.
  lazymatch goal with
  | [|- eq_term _ _ _ {{e #"blk_subst" {?H1} {?H2} {?c} (#"jmp" {?G1} {?G2} {?A} (#"hd" {?B}) (#"val_subst" {?G2} {?G3} {?s} {?A} {?p})) }} _ ] =>
    reduce_to {{e #"blk_subst" {H1} {H2} {c} (#"blk_subst" {H2} (#"conc" {G1} {G3}) (#"csub" {G1} {G1} {G2} {G3} (#"id" (#"only" {B})) {s}) (#"jmp" {G1} {G3} {A} (#"hd" {B}) {p})) }};
    reduce_to {{e #"blk_subst" {H1} (#"conc" {G1} {G3}) (#"cmp" {H1} {H2} (#"conc" {G1} {G3}) {c} (#"csub" {G1} {G1} {G2} {G3} (#"id" (#"only" {B})) {s})) (#"jmp" {G1} {G3} {A} (#"hd" {B}) {p}) }}
  end.
  (* ===== continuation ===== *)
  {
    eapply eq_term_sym.
    blk_cmp.
    term_refl.
  }

  Unshelve.
  all: try solve_wf_term.
  Unshelve.
  all: try solve_wf_term.

  Optimize Proof.
  Optimize Heap.

  hide_implicits.

  eapply eq_term_trans.

  {
    term_cong; cycle 1.
    1, 2, 4: term_refl.
    2: left; solve_sort.

    compute_eq_compilation.

    normalize_perm.
    Unshelve.
    all: try solve_wf_term.
    Unshelve.
    all: try solve_wf_term.

    Optimize Proof.
    Optimize Heap.

    { term_refl. }
    {
      lazymatch goal with
      | [|- eq_term _ _ _ {{e #"cmp"
          {?G1} {?G3} {?G4}
          (#"cmp" {?G1} {?G2} {?G3} {?p} {?cs} )
          {?e}
        }} _ ] =>
          let cs' := csub_normalize cs in
          reduce_to {{e #"cmp" {G1} {G2} {G4} {p} (#"cmp" {G2} {G3} {G4} {cs'} {e}) }};
          eapply eq_term_trans; [>
          break_cmp;
          [> term_refl | .. ];
          eapply eq_term_trans;
          [> break_cmp;
            [> eredex_steps_with linear_value_subst "csub_assoc" |  term_refl ]
            | exch_invert ]
          | .. ];
          compute_eq_compilation;
          reduce_lhs;
          break_cmp;
          [> .. | term_refl ]
      end.

      lazymatch goal with
      | [|- eq_term _ _ _ {{e #"cmp"
          {?G1} {?G2} {?G3}
          {?g1} {?g2}
        }} _ ] => reduce_to {{e
          #"cmp" {G1} {G2} {G3}
          (#"cmp" {G1} {G2} {G2}
            {g1} (#"id" {G2}))
          {g2}
        }}
      end.

      trans break_cmp.
      2: term_refl.
      1: {
        trans break_cmp.
        1: term_refl.
        {
          csub_id_dance.
          trans ltac:(unapply linear_value_subst "cmp_csub").
          compute_eq_compilation.
          term_refl.

          Unshelve.
          all: try solve_wf_term.
          Unshelve.
          all: try solve_wf_term.
          all: shelve.
        }

        eredex_steps_with linear_value_subst "cmp_assoc".
        all: try (lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end).

        Unshelve.
        all: try solve_wf_term.
        all: try shelve_if_not_eqterm.
      }

      compute_eq_compilation.

      reassoc_cmp4.

      trans break_cmp.

      {
        trans break_cmp.
        1: term_refl.
        1: unapply linear_value_subst "exch_triple".
        compute_eq_compilation.
        reduce_lhs.
        trans break_cmp.
        2: term_refl.
        1: reduce_to {{e #"cmp" (#"conc" "G" (ext "H" (#"neg" "B"))) (
                   #"conc" (ext "H" (#"neg" "B")) "G") (
                   #"conc" "G" (ext "H" (#"neg" "B"))) (
                   #"exch" "G" (ext "H" (#"neg" "B"))) (
                   #"exch" (ext "H" (#"neg" "B")) "G")}};
          eredex_steps_with linear_value_subst "exch_inv".

        Unshelve.
        all: try solve_wf_term.
        Unshelve.
        all: try solve_wf_term.

        (* Optimize Proof. *) (* this doesn't work *)
        Optimize Heap.

        all: try shelve_if_not_eqterm.

        reduce_lhs.

        lazymatch goal with
        | [|- eq_term _ _ {{s #"sub" {?X} {?Y} }} ?e _ ] =>
          reduce_to {{e #"cmp" {X} {X} {Y} (#"id" {X}) {e} }}
        end.

        trans break_cmp.

        Unshelve.
        all: try solve_wf_term.
        all: try shelve_if_not_eqterm.
        2: term_refl.
        {
          csub_id_dance.
          compute_eq_compilation.
          trans ltac:(unapply linear_value_subst "cmp_csub").
          compute_eq_compilation.
          break_cmp.
          1: term_refl.
          unapply linear_value_subst "exch_triple".

          Unshelve.
          all: try solve_wf_term.
          Unshelve.
          all: try solve_wf_term.
          all: shelve.
        }

        compute_eq_compilation.

        reduce_lhs.
        reassoc_cmp4.

        trans break_cmp.
        1: term_refl.
        {
          eredex_general linear_value_subst "cmp_csub".
          4-5: term_refl.
          1-3: try env_eq.
          all: try (lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end).
          solve_sort.

          Unshelve.
          all: try solve_wf_term.
          Unshelve.
          all: try solve_wf_term.
          all: shelve.
        }

        compute_eq_compilation.

        reduce_lhs.
        term_refl.

      }

      {
        trans ltac:(
          eredex_general linear_value_subst "exch_cmp";
          cycle 3;
          [> term_refl | term_refl |
             solve_wf_subst |
             solve_sort |
             try env_eq .. ]
        ).
        compute_eq_compilation.
        term_refl.

        Unshelve.
        all: try solve_wf_term.
        Unshelve.
        all: try solve_wf_term.
        all: try shelve_if_not_eqterm.
      }

      reduce_lhs.

      trans break_cmp.
      2: term_refl.
      {
        trans ltac:(unapply linear_value_subst "cmp_assoc").
        all: try (lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end).
        compute_eq_compilation.
        trans break_cmp.
        1: term_refl.
        {
          reduce_to {{e #"cmp"
            (#"conc" (ext "G" (#"neg" "B")) "H")
            (#"conc" "H" (ext "G" (#"neg" "B")))
            (#"conc" (ext "G" (#"neg" "B")) "H")
            (#"exch" (ext "G" (#"neg" "B")) "H")
            (#"exch" "H" (ext "G" (#"neg" "B")))}}.
          eapply eq_term_conv.
          1: eredex_steps_with linear_value_subst "exch_inv".
          solve_sort.

          Unshelve.
          all: try solve_wf_term.
          Unshelve.
          all: try solve_wf_term.
          all: shelve.
        }
        reduce_lhs.
        unapply linear_value_subst "exch_triple".
      }

      reduce_lhs.

      trans ltac:(unapply linear_value_subst "cmp_assoc").
      all: try (lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end).

      Unshelve.
      all: try solve_wf_term.
      all: try shelve_if_not_eqterm.

      compute_eq_compilation.

      trans break_cmp.
      Unshelve.
      all: try solve_wf_term.
      all: try shelve_if_not_eqterm.
      1: term_refl.
      {
        trans ltac:(
          eredex_general linear_value_subst "cmp_csub";
          cycle 3;
          [> term_refl | term_refl |
             solve_wf_subst |
             solve_sort |
             try env_eq .. ]
        ).
        Unshelve.
        all: try solve_wf_term.
        Unshelve.
        all: try solve_wf_term.
        all: try shelve_if_not_eqterm.
        reduce_lhs.
        term_refl.
      }

      reduce_lhs.
      term_refl.
    }
    {
      reassoc_cmp3.

      eapply eq_term_trans.
      {
        break_cmp; [> term_refl | .. ].

        eapply eq_term_trans.
        {
          break_cmp; [> .. | term_refl ].
          lazymatch goal with
            | [|- eq_term _ _ _ {{e
              #"csub" {?A} {?A'} {_} {_}
              {?a}
              (#"csub" {?B} {?B'} {?C} {?C'} {?b} {?c})
            }} _ ] =>
              instantiate (1:= {{e #"csub" (#"conc" {A} {B}) (#"conc" {A'} {B'}) {C} {C'}
                (#"csub" {A} {A'} {B} {B'} {a} {b}) {c} }}); by_reduction
            end.
        }

        eapply eq_term_trans.
        {
          eapply eq_term_conv;
          [>
            eapply eq_term_trans;
            [> term_cong | .. ];
            [> .. | eredex_steps_with linear_value_subst "cmp_csub" ] |
            .. ].

          all: try compute_eq_compilation.
          5: term_refl.
          4: term_refl.
          1-3: try env_eq.
          all: try (lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end).
          1: solve_sort.

          Unshelve.
          all: try solve_wf_term.
          Unshelve.
          all: try solve_wf_term.
          all: shelve.

          Optimize Proof.
          (* Optimize Heap. *) (* does not terminate in 10 minutes *)

        }

        reduce_lhs.
        term_refl.

      }

      term_refl.

      Unshelve.
      all: try solve_wf_term.
      Unshelve.
      all: try solve_wf_term.
    }
    {
      reassoc_cmp3.

      eapply eq_term_trans.
      {
        break_cmp; [> term_refl | .. ].
        eapply eq_term_trans.
        {
          break_cmp; [> .. | term_refl ].
          lazymatch goal with
            | [|- eq_term _ _ _ {{e
              #"csub" {?A} {?A'} {_} {_}
              {?a}
              (#"csub" {?B} {?B'} {?C} {?C'} {?b} {?c})
            }} _ ] =>
              instantiate (1:= {{e #"csub" (#"conc" {A} {B}) (#"conc" {A'} {B'}) {C} {C'}
                (#"csub" {A} {A'} {B} {B'} {a} {b}) {c} }}); by_reduction
            end.
        }

        Unshelve.
        all: try solve_wf_term.
        Unshelve.
        all: try solve_wf_term.

        all: try shelve_if_not_eqterm.

        trans ltac:(eredex_general linear_value_subst "cmp_csub").
        4-5: term_refl.
        1-3: try env_eq.
        all: try (lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end).
        1: solve_sort.

        Unshelve.
        all: try solve_wf_term.

        all: try shelve_if_not_eqterm.

        compute_eq_compilation.

        reduce_lhs.

        lazymatch goal with
          | [|- eq_term _ _ _ {{e
            #"csub" {?G1} {?G2} {?H1} {?H2}
            {?g} {?h}
          }} _ ] => reduce_to {{e
            #"csub" {G1} {G2} {H1} {H2}
            {g} (#"cmp" {H1} {H1} {H2} (#"id" {H1}) {h})
          }}
        end.

        trans ltac:(
          eapply eq_term_conv;
          [> unapply linear_value_subst "cmp_csub" |
             solve_sort ]
        ).

        Unshelve.
        all: try solve_wf_term.
        all: try shelve_if_not_eqterm.

        compute_eq_compilation.
        term_refl.

      }

      reduce_lhs.

      break_cmp.
      2: term_refl.
      Unshelve.
      all: try solve_wf_term.
      Unshelve.
      all: try solve_wf_term.
      all: try shelve_if_not_eqterm.

      eapply eq_term_trans.
      2: {
        instantiate (1:= {{e
          #"csub"
            "G" "G"
            (ext "H" (#"neg" "B")) (#"conc" (#"only" (#"neg" "B")) "H")
            (#"id" "G")
            (#"exch" "H" (#"only" (#"neg" "B")))
        }}).

        eredex_steps_with linear_value_subst "exch_triple".
      }

      by_reduction.
    }
    {
      trans ltac:(unapply linear_value_subst "cmp_assoc").
      reduce_lhs.
      term_refl.
    }
  }

  by_reduction.
  Unshelve.
  all: try solve_wf_term.

  Unshelve.
  all: repeat t'.
Qed.
#[local] Definition linear_cps_stlc_entry :=
  cmp_entry (elab_compiler_implies_preserving linear_cps_preserving).
#[export] Hint Resolve linear_cps_stlc_entry : preserving_db.
