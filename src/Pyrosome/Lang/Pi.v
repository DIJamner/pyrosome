Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core Elab.Elab
  Elab.PreRule
  Tools.Matches Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Interactive
  Lang.Subst
  Lang.SubstEqnGen.

Require Coq.derive.Derive.

Import Core.Notations.
Import PreRule.Notations.


Import Tools.ComputeWf.

(*TODO: generalize cbv*)
Ltac debug_term_wf :=
  let descend_wf :=
    try(
    eapply wf_term_by';[solve_in |  | try (left; reflexivity)];
    let x := numgoals in
    guard x=1;
    (repeat (apply wf_args_cons || apply wf_args_nil));
    debug_term_wf)
  in
  (compute_noconv_term_wf || descend_wf);
  cbv - [subst_lang].


Ltac debug_term_wf_cong_by_red :=
  eapply wf_term_by';[solve_in |  | right; sort_cong; by_reduction];
    let x := numgoals in
    guard x=1;
    (repeat (apply wf_args_cons || apply wf_args_nil));
    cbv - [subst_lang];
    try compute_noconv_term_wf.


Ltac debug_gen_subst :=
  lazymatch goal with
    |- wf_lang_ext ((?n,term_rule ?c _ ?t)::_) _ =>
      let mrule := eval vm_compute in
      (substable_constr n c t)
        in
        lazymatch mrule with
        | Some ?rule => push_rule_no_compute rule
        | None => fail "Failed to generate substitution rule. TODO: improve message"
        end
  end.


(* TODO: delcare interactively, register in DB *)
Definition pi_injectivity :=
  [("app", ["G"]); ("lambda", ["e";"B"; "A"; "G"]); ("Pi", ["B"; "A"; "G"])].

Derive pi
       SuchThat (wf_lang_ext subst_lang pi)
       As pi_wf.
Proof.
  setup_lang_interactive.

  elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A")
      -----------------------------------------------
      #"Pi" "A" "B" : #"ty" "G"
    ]}%prerule
    (pi_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" (#"ext" "G" "A") "B"
      -----------------------------------------------
      #"lambda" "A" "e" : #"exp" "G" (#"Pi" "A" "B")
  ]}%prerule
   (pi_injectivity++subst_injectivity).
  gen_subst.
  elab_rule {[r "G" : #"env",
          "A" : #"ty" "G",
          "B": #"ty" (#"ext" "G" "A"),
          (*TODO: why is this annotation needed? *)
          "e" : #"exp" "G" (#"Pi" ["G":="G"] "A" "B"), 
          "e'" : #"exp" "G" "A"
          -----------------------------------------------
          #"app" "e" "e'" : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e'") "B")
   ]}%prerule
    (pi_injectivity++subst_injectivity).
   gen_subst.
  elab_rule{[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" (#"ext" "G" "A") "B",
      "e'" : #"exp" "G" "A"
      ----------------------------------------------- ("Pi beta")
      #"app" (#"lambda" "A" "e") "e'"
      = #"exp_subst" (#"snoc" #"id" "e'") "e"
      : #"exp" "G" (#"ty_subst" (#"snoc" #"id" "e'") "B")
  ]}%prerule
    (pi_injectivity++subst_injectivity).
elab_rule {[r "G" : #"env",
      "A" : #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "e" : #"exp" "G" (#"Pi" ["G":="G"] "A" "B")
      ----------------------------------------------- ("Pi eta")
      #"lambda" "A" (#"app" ["B":= #"ty_subst" {inr (under' {{pe#"wkn"}}) } "B"]
                       (*TODO: check this type *)
                       (#"exp_subst" #"wkn" "e")
                        #"hd")
      = "e"
      : #"exp" "G" (#"Pi" "A" "B")
  ]}%prerule
  (pi_injectivity++subst_injectivity).
apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[export] Hint Resolve pi_wf : elab_pfs.

#[local] Definition Pi_inst_for_db := inst_for_db "Pi".
#[export] Hint Resolve Pi_inst_for_db : injective_con.
