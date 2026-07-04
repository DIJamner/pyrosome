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
  Tools.EGraph.InjRuleGen
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

(* The implicit env of [cont]/[jmp] must be recovered by inverting a [conc]:
   e.g. [jmp]'s result sort is [blk (conc ?G H)] and the rule declares it
   [blk (conc G H)], so the e-graph must conclude [?G = G] from [conc ?G H =
   conc G H].  We cannot do this by declaring [conc] injective, because [conc]
   genuinely is not injective ([conc emp G = G], [conc] is associative), so such
   a schema would be unsound.  But [conc] *is* cancellative -- environments form
   the free monoid on the [only A] generators -- and it is left-cancellation
   that fires here: the shared factor ends up as the *first* [conc] argument in
   the e-graph, so [conc Z A = conc Z B -> A = B] recovers the env.  (This is
   sound; the earlier attempt used right-cancellation, whose shared factor never
   appears, so it silently matched nothing and left [#"?"] holes -- which in turn
   made [compute_wf_lang] thrash on the junk constructors.) *)
Definition linear_ext_injectivity :=
  [left_cancellation_seq "conc"].

(*TODO: move to LinearSubst *)
Definition linear_block_subst_injectivity :=
  [("blk_subst", ["G"]); ("blk", ["G"])].

Definition linear_cps_injectivity :=
  [("cont", ["e";"A"; "G"]); ("neg", ["A"])].

Definition linear_cps_gen_schemas :=
  Eval vm_compute in
    gen_fundep_schemas 10 (linear_block_subst ++ linear_value_subst).

Definition linear_cps_lang :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100
       (linear_block_subst ++ linear_value_subst)
       linear_cps_lang_def.

Lemma cps_lang_wf
  : wf_lang_ext (linear_block_subst ++ linear_value_subst) linear_cps_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition linear_cps_entry := lang_entry cps_lang_wf.
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

Definition linear_cps_subst :=
  Eval vm_compute in
    (infer_compiler_simple_autoinj 10
       (linear_cps_lang
          ++ linear_block_subst
          ++ linear_value_subst)
       []
       linear_cps_subst_def
       (linear_exp_subst ++ linear_value_subst)).

Lemma linear_cps_subst_preserving
  : preserving_compiler_ext []
      (tgt_Model := core_model (linear_cps_lang
         ++ linear_block_subst
         ++ linear_value_subst))
      linear_cps_subst
      (linear_exp_subst ++ linear_value_subst).
Proof. compute_preserving_compiler (@nil (string*rule)). Qed.
#[local] Definition linear_cps_cmp_entry :=
  cmp_entry linear_cps_subst_preserving.
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

(* As in the cartesian [cps_prod_injectivity] (SimpleVCPS), [prod] (and [pair])
   are genuine free constructors and so are soundly injective; the implicit type
   args [A]/[B] of [pm_pair] in [prod_eta] are recovered from the sort
   [val H (prod A B)] of its scrutinee by inverting [prod]. *)
Definition linear_cps_prod_injectivity :=
  [("pair", ["e2"; "e1"; "B"; "A"; "H"; "G"]); ("prod", ["B"; "A"])].

Definition linear_cps_prod_lang :=
  Eval vm_compute in
    infer_lang_ext_simple_incr 10 100
        (linear_block_subst ++ linear_value_subst)
       linear_cps_prod_lang_def.

Lemma linear_cps_prod_wf
  : wf_lang_ext (linear_block_subst ++ linear_value_subst) linear_cps_prod_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition linear_cps_prod_entry := lang_entry linear_cps_prod_wf.
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


(* The infer-produced langs annotate some rule-ctx sorts with a different
   [conc]-nesting than the sort declared in the goal ctx (e.g. [pm_pair]'s
   block argument is expected at [blk (conc G (ext (only A) B))] while the
   ctx declares [blk (ext (ext G A) B)]), so a variable can occur at a sort
   that is only convertible-by-[conc_assoc] to its declared sort; the
   [wf_term_conv] fallback bridges the two by env normalization. *)
Ltac solve_wf_term := first [eapply wf_term_by';
  [> solve_in | solve_wf_args | first [left; reflexivity | right; solve_sort] ]
  | eapply wf_term_var; solve_in
  | eapply wf_term_conv; [> eapply wf_term_var; solve_in | solve_sort ] ]
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

(* shared prefix of the two "csub_id dances" *)
Ltac csub_id_dance :=
  trans ltac:(unapply linear_value_subst "csub_id");
  compute_eq_compilation;
  trans ltac:(term_cong; cycle 1;
    [> term_refl .. |
       unapply linear_value_subst "id_left" |
       unapply linear_value_subst "exch_inv" |
      right; reflexivity ]).

Definition linear_cps :=
  Eval vm_compute in
    (infer_compiler_simple_autoinj 4
       (linear_cps_prod_lang
          ++ linear_cps_lang
          ++ linear_block_subst
          ++ linear_value_subst)
       linear_cps_subst
       linear_cps_def
       linear_stlc).


(* Interactive breaker for [preserving_compiler_ext], the direct analogue of
   [setup_elab_compiler] (no elaboration detour).
   [preserving_compiler_cons_nth_tail] peels one source rule using
   [nth_error]/[nth_tail] (avoiding higher-order unification on [map fst c]);
   [setup_preserving_compiler] then leaves one wf/eq obligation per source rule.
   TODO: move next to [elab_compiler_cons_nth_tail] in Elab.ElabCompilers. *)
Section PreservingBreak.
  Context (target : lang).
  Local Notation cmplr := (@CompilerDefs.compiler string (@Term.term string) (@Term.sort string)).
  Context (cmp_pre : cmplr).
  Let model := core_model target.
  Existing Instance model.
  Existing Instance term_default.
  Existing Instance sort_default.
  Local Notation compileC cmp := (compile (cmp++cmp_pre)).
  Local Notation compileS cmp := (compile_sort (cmp++cmp_pre)).
  Local Notation compileX cmp := (compile_ctx (cmp++cmp_pre)).
  Lemma preserving_compiler_cons_nth_tail (cmp : cmplr) (src : lang) n m name r
    : nth_error src m = Some (name,r) ->
      match r with
      | sort_rule c _ =>
          exists t cmp',
          nth_error cmp n = Some (name, sort_case (map fst c) t) /\
          nth_tail n cmp = (name, sort_case (map fst c) t)::cmp' /\
          preserving_compiler_ext cmp_pre (nth_tail (S n) cmp) (nth_tail (S m) src) /\
          Model.wf_sort (compileX (nth_tail (S n) cmp) c) t
      | term_rule c _ t =>
          exists e cmp',
          nth_error cmp n = Some (name, term_case (map fst c) e) /\
          nth_tail n cmp = (name, term_case (map fst c) e)::cmp' /\
          preserving_compiler_ext cmp_pre (nth_tail (S n) cmp) (nth_tail (S m) src) /\
          Model.wf_term (compileX (nth_tail (S n) cmp) c) e (compileS (nth_tail (S n) cmp) t)
      | sort_eq_rule c t1 t2 =>
          preserving_compiler_ext cmp_pre (nth_tail n cmp) (nth_tail (S m) src) /\
          Model.eq_sort (compileX (nth_tail n cmp) c)
                  (compileS (nth_tail n cmp) t1) (compileS (nth_tail n cmp) t2)
      | term_eq_rule c e1 e2 t =>
          preserving_compiler_ext cmp_pre (nth_tail n cmp) (nth_tail (S m) src) /\
          Model.eq_term (compileX (nth_tail n cmp) c) (compileS (nth_tail n cmp) t)
                  (compileC (nth_tail n cmp) e1) (compileC (nth_tail n cmp) e2)
      end ->
      preserving_compiler_ext cmp_pre (nth_tail n cmp) (nth_tail m src).
  Proof.
    destruct r; intros; firstorder;
      repeat match goal with
             |[ H : nth_tail _ _ = _|-_] =>
              rewrite H; rewrite (nth_tail_equals_cons_res _ _ H); clear H
             |[ H : nth_error _ _ = _|-_] =>
              rewrite (nth_tail_to_cons _ _ H); clear H
             end; constructor; simpl; basic_utils_crush.
  Qed.
End PreservingBreak.

Ltac preserving_compiler_cons :=
  eapply preserving_compiler_cons_nth_tail;
  [ compute; reflexivity | cbn beta match; repeat (apply conj || safe_eexists) ].
Ltac break_preserving_ext :=
  (preserving_compiler_cons; try reflexivity; [ break_preserving_ext |..])
  || (compute; apply CompilerDefs.preserving_compiler_nil).
Ltac setup_preserving_compiler :=
  lazymatch goal with
  | |- preserving_compiler_ext ?cmp_pre ?cmp ?src =>
      rewrite (as_nth_tail cmp); rewrite (as_nth_tail src)
  end; break_preserving_ext.

(* The compiled Linear-STLC beta redex after one mechanical pass of
   [by_reduction]: the [jmp] of the compiled argument pair into [hd], under a
   single composite permutation substitution.  Written out explicitly so the
   proof below can reach it with one e-graph call; the remaining distance to
   the compiled RHS is the permutation reasoning done manually after it. *)
Definition linear_cps_beta_mid := {{e  #"blk_subst" (#"conc" "G" (ext "H" (#"neg" "B"))) (
                     #"conc" (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))) (
                             ext (#"only" "A") (#"neg" "B"))) (
                     #"cmp" (#"conc" "G" (ext "H" (#"neg" "B"))) (
                            #"conc" (#"only" (#"neg" 
                                              (#"prod" "A" (#"neg" "B")))) (
                                    ext (#"only" (#"neg" "B")) "A")) (
                            #"conc" (#"only" (#"neg" 
                                              (#"prod" "A" (#"neg" "B")))) (
                                    ext (#"only" "A") (
                                    #"neg" "B"))) (
                            #"cmp" (#"conc" "G" (ext "H" (#"neg" "B"))) (
                                   #"conc" (#"only" (#"neg" "B")) (
                                           ext (#"only" 
                                                (#"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))))
                                           "A")) (
                                   #"conc" (#"only" 
                                            (#"neg" 
                                             (#"prod" "A" (#"neg" "B")))) (
                                           ext (#"only" (#"neg" "B")) "A")) (
                                   #"cmp" (#"conc" "G" (ext "H" (#"neg" "B"))) (
                                          #"conc" 
                                          (#"only" (#"neg" "B")) (
                                          #"conc" 
                                          (#"only" 
                                           (#"neg" (#"prod" "A" (#"neg" "B")))) "H")) (
                                          #"conc" 
                                          (#"only" (#"neg" "B")) (
                                          ext (#"only" 
                                               (#"neg" 
                                                (#"prod" "A" (#"neg" "B"))))
                                          "A")) (#"cmp" 
                                                 (
                                                 #"conc" 
                                                 "G" (
                                                 ext "H" (#"neg" "B"))) (
                                                 #"conc" 
                                                 "H" (
                                                 ext (
                                                 #"only" (#"neg" "B"))
                                                 (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))))) (
                                                 #"conc" 
                                                 (
                                                 #"only" (#"neg" "B")) (
                                                 #"conc" 
                                                 (
                                                 #"only" 
                                                 (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B")))) "H")) (
                                                 #"cmp" 
                                                 (
                                                 #"conc" 
                                                 "G" (
                                                 ext "H" (#"neg" "B"))) (
                                                 #"conc" 
                                                 "H" (
                                                 #"conc" 
                                                 (
                                                 #"only" (#"neg" "B")) "G")) (
                                                 #"conc" 
                                                 "H" (
                                                 ext (
                                                 #"only" (#"neg" "B"))
                                                 (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))))) (
                                                 #"exch" 
                                                 "G" (
                                                 ext "H" (#"neg" "B"))) (
                                                 #"csub" 
                                                 (
                                                 ext "H" (#"neg" "B")) (
                                                 ext "H" (
                                                 #"neg" "B")) "G" (
                                                 #"only" 
                                                 (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B")))) (
                                                 #"id" 
                                                 (ext "H" (#"neg" "B"))) (
                                                 #"vsub" 
                                                 "G" (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))) (
                                                 #"cont" 
                                                 "G" (
                                                 #"prod" 
                                                 "A" (#"neg" "B")) (
                                                 #"pm_pair" 
                                                 "G" (
                                                 #"only" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))) "A" (
                                                 #"neg" 
                                                 "B") (
                                                 #"hd" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))) "e"))))) (
                                                 #"exch" 
                                                 "H" (
                                                 ext (
                                                 #"only" (#"neg" "B"))
                                                 (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B")))))) (
                                          #"csub" 
                                          (ext (#"only" (#"neg" "B"))
                                           (#"neg" (#"prod" "A" (#"neg" "B")))) (
                                          ext (#"only" (#"neg" "B"))
                                          (#"neg" (#"prod" "A" (#"neg" "B")))) "H" (
                                          #"only" 
                                          "A") (#"id" 
                                                (ext (
                                                 #"only" (#"neg" "B"))
                                                 (
                                                 #"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))))) (
                                          #"vsub" 
                                          "H" "A" "v"))) (
                                   #"csub" (ext (#"only" (#"neg" "B"))
                                            (#"neg" 
                                             (#"prod" "A" (#"neg" "B")))) (
                                           ext (#"only" 
                                                (#"neg" 
                                                 (
                                                 #"prod" "A" (#"neg" "B"))))
                                           (#"neg" "B")) (
                                           #"only" "A") (
                                           #"only" "A") (
                                           #"exch" 
                                           (#"only" (#"neg" "B")) (
                                           #"only" 
                                           (#"neg" (#"prod" "A" (#"neg" "B"))))) (
                                           #"id" (#"only" "A")))) (
                            #"csub" (#"only" (#"neg" 
                                              (#"prod" "A" (#"neg" "B")))) (
                                    #"only" (#"neg" 
                                             (#"prod" "A" (#"neg" "B")))) (
                                    ext (#"only" (#"neg" "B")) "A") (
                                    ext (#"only" "A") (
                                    #"neg" "B")) (
                                    #"id" (#"only" 
                                           (#"neg" (#"prod" "A" (#"neg" "B"))))) (
                                    #"exch" (#"only" (#"neg" "B")) (
                                            #"only" 
                                            "A")))) (
                     #"jmp" (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))) (
                            ext (#"only" "A") (#"neg" "B")) (
                            #"prod" "A" (#"neg" "B")) (
                            #"hd" (#"neg" (#"prod" "A" (#"neg" "B")))) (
                            #"pair" (#"only" "A") (
                                    #"only" (#"neg" "B")) "A" (
                                    #"neg" "B") (#"hd" "A") (
                                    #"hd" (#"neg" "B")))) }}.

Lemma linear_cps_preserving : preserving_compiler_ext linear_cps_subst
                                (tgt_Model:= core_model (linear_cps_prod_lang
                                                           ++ linear_cps_lang
                                                           ++ linear_block_subst
                                                           ++ linear_value_subst))
                                linear_cps
                                linear_stlc.
Proof.
  assert (wf_lang (linear_cps_prod_lang ++ linear_cps_lang
                   ++ linear_block_subst ++ linear_value_subst)) by prove_by_lang_db.
  setup_preserving_compiler.
  (* wf obligations: reflective; simple eq obligations: reduction *)
  1,2,4: compute_term_wf.
  1,2: solve [ Automation.by_reduction; now t' ].
  (* ===== remaining obligation (Linear-STLC-beta).
     A single [by_reduction] cannot check the whole equation (the e-graph
     diverges on the permutation reasoning), so the proof is staged: one
     [by_reduction] pushes the beta redex through the substitution calculus
     to the explicit intermediate [linear_cps_beta_mid]; the permutation
     kernel below rearranges the composite substitution by hand (this part
     is beyond the e-graph at any fuel); a final [by_reduction] closes the
     remaining gap, absorbing everything the kernel leaves oriented.  The
     [eq_term_conv] wrappers around [csub_assoc]/[exch_triple] bridge the
     left-nested sort annotations the inference-based elaboration gives
     those rules. ===== *)
  unfold Model.eq_term; cbn [core_model].
  compute_eq_compilation.
  eapply eq_term_trans;
    [ instantiate (1 := linear_cps_beta_mid); unfold linear_cps_beta_mid;
      Automation.by_reduction; repeat t' | ].
  compute_eq_compilation.

  eapply eq_term_trans.

  {
    term_cong; cycle 1.
    1, 2, 4: term_refl.
    2: unshelve (left; solve_sort); now repeat t'.

    compute_eq_compilation.
    normalize_perm.

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
          reduce_to {{e #"cmp" {G1} {G2} {G4} {p} (#"cmp" {G2} {G3} {G4} {cs'} {e}) }}
      end.

      eapply eq_term_trans.
      {
        break_cmp.
        { term_refl. }
        eapply eq_term_trans.
        { break_cmp;
          [ now (eapply eq_term_conv;
                 [ eredex_steps_with linear_value_subst "csub_assoc"
                 | solve_sort ])
          | term_refl ]. }
        { now exch_invert. }
      }
      reduce_lhs; break_cmp; [ | term_refl ].

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
      {
        trans break_cmp.
        1: term_refl.
        {
          csub_id_dance.
          unapply linear_value_subst "cmp_csub".
        }

        eredex_steps_with linear_value_subst "cmp_assoc".

        Unshelve.
        all: repeat t'; shelve.
      }
      { term_refl. }
      {
        compute_eq_compilation.
        reassoc_cmp4.

        trans break_cmp.
        {
          trans break_cmp.
          { term_refl. }
          { eapply eq_term_conv;
            [ unapply linear_value_subst "exch_triple" | solve_sort ]. }
          compute_eq_compilation.
          reduce_lhs.
          trans break_cmp.
          {
            reduce_to {{e #"cmp" (#"conc" "G" (ext "H" (#"neg" "B"))) (
                            #"conc" (ext "H" (#"neg" "B")) "G") (
                            #"conc" "G" (ext "H" (#"neg" "B"))) (
                            #"exch" "G" (ext "H" (#"neg" "B"))) (
                            #"exch" (ext "H" (#"neg" "B")) "G")}};
              eredex_steps_with linear_value_subst "exch_inv".
          }
          { term_refl. }

          Unshelve.
          all: repeat t';try shelve_if_not_eqterm.
          Optimize Heap.

          reduce_lhs.

          lazymatch goal with
          | [|- eq_term _ _ {{s #"sub" {?X} {?Y} }} ?e _ ] =>
              reduce_to {{e #"cmp" {X} {X} {Y} (#"id" {X}) {e} }}
          end.

          trans break_cmp.
          {
            csub_id_dance.
            compute_eq_compilation.
            trans ltac:(unapply linear_value_subst "cmp_csub").
            compute_eq_compilation.
            break_cmp.
            1: term_refl.
            eapply eq_term_conv;
            [ unapply linear_value_subst "exch_triple" | solve_sort ].

            Unshelve.
            all: repeat t'; shelve.
          }
          { term_refl. }
          {
            reduce_lhs.
            reassoc_cmp4.

            break_cmp.
            { term_refl. }
            {
              eredex_general linear_value_subst "cmp_csub".
              4-5: term_refl.
              1-3: try env_eq.
              {
                lazymatch goal with |- wf_subst _ _ _ => solve_wf_subst end.
              }
              { solve_sort. }
              Unshelve.
              all: repeat t'; shelve.
            }
          }
        }
        {
          unshelve (eredex_general linear_value_subst "exch_cmp";
                    cycle 3;
                    [> term_refl | term_refl |
                      solve_wf_subst |
                      solve_sort |
                      try env_eq .. ]);
            repeat t'; shelve.
        }
        {
          reduce_lhs.

          trans break_cmp.
          {
            trans ltac:(unapply linear_value_subst "cmp_assoc").
            compute_eq_compilation.
            trans break_cmp.
            { term_refl. }
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
              all: repeat t'; shelve.
            }
            reduce_lhs.
            eapply eq_term_conv;
            [ unapply linear_value_subst "exch_triple" | solve_sort ].
          }
          { term_refl. }
          {
            reduce_lhs.
            term_refl.
          }
        }
      }
    }
    {
      reduce_lhs.
      term_refl.
    }
    {
      reduce_lhs.
      term_refl.
    }
    term_refl.
  }
  Automation.by_reduction; repeat t'.
  Unshelve.
  all: repeat t'.
Qed.
#[local] Definition linear_cps_stlc_entry := cmp_entry linear_cps_preserving.
#[export] Hint Resolve linear_cps_stlc_entry : preserving_db.
