Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Lang.LinearSubst Lang.LinearSTLC Tools.Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.
Require Import Pyrosome.Tools.UnElab.

Local Notation compiler := (compiler string).

About eq_term_trans.

Notation "'only' e" := ({{e #"ext" #"emp" {e} }})(in custom term at level 40, e custom arg at level 0).

Definition linear_cps_lang_def : lang :=
  {[l/lin_subst (* [linear_blk_subst ++ linear_value_subst] *)
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
  [:| "G" : #"env",
      "A" : #"ty",
      "e" : #"blk" (#"ext" "G" "A")
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
      "e" : #"blk" (#"ext" "G" "A"),
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

Compute linear_cps_lang_def.

Derive linear_cps_lang
       SuchThat (elab_lang_ext (linear_block_subst ++ linear_value_subst)
                               linear_cps_lang_def
                               linear_cps_lang)
       As cps_lang_wf.
Proof.
  auto_elab;
  break_elab_rule;
  unfold Model.eq_term;
  by_reduction.
  Unshelve.
  all: cleanup_auto_elab.
Qed.

#[export] Hint Resolve cps_lang_wf : elab_pfs.

Definition linear_cps_subst_def : compiler :=
  match # from (linear_exp_subst ++ linear_value_subst) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" "G" (#"neg" "A")) }}
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"csub" "g" (#"id" (only (#"neg" "A")))) "e"}}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"blk_subst" (#"exch" #"emp" "G" (#"ext" #"emp" (#"neg" "A")) #"emp") (#"jmp" (#"hd" (#"neg" "A")) "v")}}
  end.

Axiom todo : forall (T : Type), T.
Ltac kill := apply todo.

(* Ltac eredex_steps_with lang name :=
  let mr := eval vm_compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- @eq_term ?V _ ?l ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_:subst V) in
          first [unify_var_names V s c | fail 2 "could not unify var names"];
          first [ replace (eq_term l c' t e1 e2)
                    with (@eq_term V _ l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [| f_equal; vm_compute; reflexivity (*TODO: is this general?*)]
                | fail 2 "could not replace with subst"];
          eapply (@eq_term_subst V _ l c' s s c);
          [eapply (@eq_term_by V _ l c name tp e1p e2p);
           try solve [cleanup_auto_elab]
          | eapply eq_subst_refl; try solve [cleanup_auto_elab]
          | try solve [cleanup_auto_elab]
          ]
        end
      | None =>
        fail 100 "rule not found in lang"
      end. *)


Derive linear_cps_subst
       SuchThat (elab_preserving_compiler []
                                          (linear_cps_lang
                                             ++ linear_block_subst
                                             ++ linear_value_subst)
                                          linear_cps_subst_def
                                          linear_cps_subst
                                          (linear_exp_subst ++ linear_value_subst))
       As linear_cps_subst_preserving.
Proof.
auto_elab_compiler; try compute_eq_compilation.
all: kill.
(*
- hide_implicits.
  eapply eq_term_trans; cycle 1.
  + eredex_steps_with linear_value_subst "exch_cmp".
  + compute_eq_compilation. term_refl.
- cbv. (* should generate eq_sort goal instead *) kill.
- hide_implicits.
  eapply eq_term_trans; cycle 1.
  { eredex_steps_with linear_block_subst "blk_subst_id". }
  compute_eq_compilation.
  replace {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) (
                   #"csub" "G" "G" (only (#"neg" "A")) (only (
                           #"neg" "A")) (#"id" "G") (#"id" (only (#"neg" "A")))) "e"}} with
          {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) "s" "e"}}
          [/[("s", {{e #"csub" "G" "G" (only (#"neg" "A")) (only (
                           #"neg" "A")) (#"id" "G") (#"id" (only (#"neg" "A")))}})] /]
          by reflexivity.
  replace {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) (
                   #"id" (#"ext" "G" (#"neg" "A"))) "e"}} with
          {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) "s" "e"}}
          [/[("s", {{e #"id" (#"ext" "G" (#"neg" "A"))}})] /]
          by reflexivity.
  replace {{s #"blk" (#"ext" "G" (#"neg" "A"))}} with
          {{s #"blk" (#"ext" "G" (#"neg" "A"))}}
          [/[("s", {{e #"id" (#"ext" "G" (#"neg" "A"))}})] /]
          by reflexivity.
  eapply eq_term_subst.
  + term_refl.
  + econstructor. { econstructor. }
    unfold Model.eq_term.
    instantiate (1 := {{s #"sub" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) }}).
    compute_eq_compilation.
    eapply eq_term_trans.
    Print eq_term_subst.
    { eredex_steps_with linear_value_subst "csub_id". }


  eapply eq_term_trans; cycle 1.
  { instantiate (1 := {{e #"blk_subst" (#"ext" (#"conc" "G" #"emp") (#"neg" "A")) (#"ext" (#"conc" "G" #"emp") (#"neg" "A")) (#"id" (#"ext" (#"conc" "G" #"emp") (#"neg" "A"))) "e"}}).
    compute_eq_compilation.
    (* eredex_steps_with linear_value_subst "conc_emp". *)
    replace {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) (
                   #"id" (#"ext" "G" (#"neg" "A"))) "e"}} with
            {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) (
                              #"id" (#"ext" "G" (#"neg" "A"))) "e"}}
            [/[("G", {{e "G"}})] /] by reflexivity.
    replace {{e #"blk_subst" (#"ext" (#"conc" "G" #"emp") (#"neg" "A")) (#"ext" (#"conc" "G" #"emp") (#"neg" "A"))
                  (#"id" (#"ext" (#"conc" "G" #"emp") (#"neg" "A"))) "e"}} with
            {{e #"blk_subst" (#"ext" "G" (#"neg" "A")) (#"ext" "G" (#"neg" "A")) (#"id" (#"ext" "G" (#"neg" "A"))) "e"}}
            [/[("G", {{e #"conc" "G" #"emp"}})] /] by reflexivity.
    replace {{s #"blk" (#"ext" "G" (#"neg" "A"))}} with
      {{s #"blk" (#"ext" "G" (#"neg" "A"))}} [/[("G", {{e "G"}})] /] by reflexivity.
    eapply eq_term_subst.
    - term_refl.
    - econstructor. { econstructor. }
      unfold Model.eq_term.
      instantiate (1 := {{s #"env"}}).
      compute_eq_compilation.
      replace {{s #"env"}} with {{s #"env"}} [/[("G", {{e "G"}})] /] by reflexivity.
      replace {{e #"conc" "G" #"emp"}} with {{e #"conc" "G" #"emp"}} [/[("G", {{e "G"}})] /] by reflexivity.
      replace {{e "G"}} with {{e "G"}} [/[("G", {{e "G"}})] /] by reflexivity.
      eapply eq_term_subst; cycle 1.
      + econstructor. { econstructor. }
        instantiate (1 := {{s #"env"}}).
        term_refl.
      + cleanup_auto_elab.
      + eredex_steps_with linear_value_subst "conc_emp".
    - cleanup_auto_elab. }

    eapply eq_term_trans; cycle 1.
    { eredex_steps_with linear_value_subst "conc_ext". }
- hide_implicits. kill.
- cbv. (* should generate eq_sort *) kill.
- hide_implicits. kill.
Unshelve.
all: cleanup_auto_elab.
*)
Qed.
#[export] Hint Resolve linear_cps_subst_preserving : elab_pfs.


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
      "e" : #"blk" (#"ext" (#"ext" "G" "A") "B")
      -----------------------------------------------
      #"pm_pair" "v" "e" : #"blk" (#"conc" "G" "H")
  ];
  [:= "G" : #"env", "H" : #"env", "K" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "v1" : #"val" "G" "A",
      "v2" : #"val" "H" "B",
      "e" : #"blk" (#"ext" (#"ext" "K" "A") "B")
      ----------------------------------------------- ("eval pm_pair")
      #"pm_pair" (#"pair" "v1" "v2") "e"
      = #"blk_subst" (#"csub" (#"id" "K") (#"csub" (#"vsub" "v1") (#"vsub" "v2"))) "e"
      : #"blk" (#"conc" "K" (#"conc" "G" "H"))
  ];
  [:= "G" : #"env", "H" : #"env",
      "A" : #"ty", "B" : #"ty",
      "v" : #"val" "H" (#"prod" "A" "B"),
      "e" : #"blk" (#"ext" "G" (#"prod" "A" "B"))
      ----------------------------------------------- ("prod_eta")
      #"pm_pair" "v" (#"blk_subst" (#"csub" (#"id" "G") (#"vsub" (#"pair" (#"hd" "A") (#"hd" "B")))) "e")
      = #"blk_subst" (#"csub" (#"id" "G") (#"vsub" "v")) "e"
      : #"blk" (#"conc" "G" "H")
  ] ]}.



Derive linear_cps_prod_lang
       SuchThat (elab_lang_ext (linear_block_subst ++ linear_value_subst) linear_cps_prod_lang_def linear_cps_prod_lang)
       As linear_cps_prod_wf.
Proof. auto_elab.
  break_elab_rule.
  all: unfold Model.eq_term; compute_eq_compilation;
  by_reduction.
  Unshelve.
  all: cleanup_auto_elab.
Qed.
#[export] Hint Resolve linear_cps_prod_wf : elab_pfs.

Print linear_cps_lang.

Definition under s :=
  {{e #"snoc" s #"hd"}}.

Definition bind e A k :=
  {{e #"blk_subst" (#"snoc" #"id" (#"cont" {A} {k})) {e} }}.
Arguments bind e A k/.


Definition linear_cps_def : compiler :=
  match # from (linear_stlc) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" "G" (#"neg" "A")) }}
  | {{e #"lolli" "A" "B"}} =>
    {{e #"neg" (#"prod" "A" (#"neg" "B")) }}
  | {{e #"linear_lambda" "G" "A" "B" "e"}} =>
    {{e #"cont" (#"prod" "A" (#"neg" "B")) (#"pm_pair" #"hd" "e")}}
  | {{e #"linear_app" "G" "H" "A" "B" "e" "e'"}} =>
    (* blk (G; H), ~B = blk G; (H, ~B) *)
    bind (var "e") {{e #"neg" (#"prod" "A" (#"neg" "B"))}}
    ( (* blk H, ~B, ~(A * ~B) = blk H; ({}, ~B, ~(A * ~B)) *)
      bind (var "e'") (var "A")
      ( (* blk {}, ~B, ~(A * ~B), A = blk {}; ({}, ~B); ({}, ~(A * ~B)); ({}, A) *)
        {{e #"blk_subst" (#"exch" #"emp"
                                  (#"ext" #"emp" (#"neg" "B"))
                                  (#"ext" #"emp" (#"neg" (#"prod" "A" (#"neg" "B"))))
                                  (#"ext" #"emp" "A"))
          (* blk {}; ({}, ~(A * ~B)); ({}, ~B); ({}, A) = blk ({}, ~(A * ~B)); ({}, ~B, A) *)
          (#"jmp" #"hd"
            (* val ({}, ~B, A) (A * ~B) = val {}; ({}, ~B); ({}, A); {} (A * ~B) *)
            (#"val_subst" (#"exch" #"emp"
                                   (#"ext" #"emp" (#"neg" "B"))
                                   (#"ext" #"emp" "A")
                                   #"emp")
              (#"pair" #"hd" #"hd")))
        }}
      )
    )
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" (#"snoc" "g" #"hd") "e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"blk_subst" (#"exch" #"emp" "G" (#"ext" #"emp" (#"neg" "A")) #"emp") (#"jmp" #"hd" "v")}}
  end.

Derive linear_cps
       SuchThat (elab_preserving_compiler linear_cps_subst
                                          (linear_cps_prod_lang
                                             ++ linear_cps_lang
                                             ++ linear_block_subst
                                             ++ linear_value_subst)
                                          linear_cps_def
                                          linear_cps
                                          linear_stlc)
       As linear_cps_preserving.
Proof. auto_elab_compiler; cycle 2.
all: kill.
(*
  - kill.
  - cbn. kill.
  - cbn. kill.
  - cbn. kill.
  - cbv. kill.
  - compute_eq_compilation. eapply eq_term_trans.
    { instantiate (1 := {{e #"cont" "G'" (#"prod" "A" (#"neg" "B")) (#"blk_subst" (#"conc" "G'" (#"ext" #"emp" (#"prod" "A" (#"neg" "B")))) (
                                      #"ext" "G" (#"prod" "A" (#"neg" "B"))) (
                                      #"snoc" "G'" "G" (
                                              #"ext" #"emp" (#"prod" "A" (#"neg" "B"))) (#"prod" "A" (#"neg" "B")) "g" (
                                              #"hd"
                                              (#"prod" "A" (#"neg" "B")))) (#"pm_pair"
                                                           "G" (#"ext"
                                                                #"emp" (
                                                                #"prod" "A" (#"neg" "B"))) "A" (
                                                           #"neg" "B") (
                                                           #"hd" (#"prod" "A" (#"neg" "B"))) "e"))}}).
      eredex_steps_with (linear_cps_prod_lang
                                             ++ linear_cps_lang
                                             ++ linear_block_subst
                                             ++ linear_value_subst) "cont-subst".
      constructor. 2: cleanup_auto_elab.
      constructor. 2: cleanup_auto_elab.
      constructor; cycle 1.
      { eapply wf_term_conv; cycle 1.
         { instantiate (1 := {{s #"blk" (#"conc" "G" (#"ext" #"emp" (#"prod" "A" (#"neg" "B"))))}}).
          compute_eq_compilation.
          eredex_steps_with
            (linear_cps_prod_lang ++ linear_cps_lang ++ linear_block_subst ++ linear_value_subst) "conc_ext_right". }  } }
*)
Qed.
#[export] Hint Resolve linear_cps_preserving : elab_pfs.
