Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core Elab.Elab
  Elab.PreRule
  Tools.ComputeWf
  Tools.Matches
  Tools.Resolution
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.EGraph.Automation
  Tools.Interactive.

Require Import Pyrosome.Compilers.Parameterizer.

From Pyrosome.Lang Require Import
  Subst SubstEqnGen
  Pi Sigma.

Require Coq.derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

Derive levels
       SuchThat (wf_lang (levels : lang))
       As levels_wf.
Proof.
  setup_lang_interactive.
  elab_rule {[r
      -----------------------------------------------
      #"lvl" srt
    ]}%prerule
    (@nil (string* list string)).  
  elab_rule {[r
      -----------------------------------------------
      #"l0" : #"lvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "l" : #"lvl"
      -----------------------------------------------
      #"lS" "l" : #"lvl"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r  "l1" : #"lvl",  "l2" : #"lvl"
      -----------------------------------------------
      #"<" "l1" "l2" srt
    ]}%prerule
    (@nil (string* list string)).  
  elab_rule {[r "l" : #"lvl"
      -----------------------------------------------
      #"<0" : #"<" #"l0" (#"lS" "l")
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "l" : #"lvl"
      -----------------------------------------------
      #"<S" : #"<" "l" (#"lS" "l")
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2"
      -----------------------------------------------
      #"<S_cong" "p" : #"<" (#"lS" "l1") (#"lS" "l2")
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "l1" : #"lvl",
          "l2" : #"lvl",
            "p1" : #"<" "l1" "l2",
          "l3" : #"lvl",
            "p2" : #"<" "l2" "l3"
      -----------------------------------------------
      #"<trans" "p1" "p2" : #"<" "l1" "l3"
    ]}%prerule
    (@nil (string* list string)).
  elab_rule {[r "l1" : #"lvl",
          "l2" : #"lvl",
            "p1" : #"<" "l1" "l2",
            "p2" : #"<" "l1" "l2"
      ----------------------------------------------- ("<irr")
      #"p1" = "p2" : #"<" "l1" "l3"
    ]}%prerule
    (@nil (string* list string)).
  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition levels_entry := lang_entry levels_wf.
#[export] Hint Resolve levels_entry : wf_lang_db.

Definition levels_injectivity :=
  [("<", ["l2"; "l1"]);("lS", ["l"]); ("l0", []);
   ("lvl", [])].

#[local] Definition subst_leveled' :=
    let ps := (elab_param "l" (subst_lang)
                 [(*("env", None);
                   ("sub", None);*)
                ("exp",Some 1);
                ("ty", Some 0)]) in
  parameterize_lang "l" {{s #"lvl"}}
    ps subst_lang.

Definition subst_leveled :=
  Eval vm_compute in subst_leveled'.

Lemma subst_leveled_wf
  : wf_lang_ext levels subst_leveled.
Proof. compute_wf_lang. Qed.
#[local] Definition subst_leveled_entry := lang_entry subst_leveled_wf.
#[export] Hint Resolve subst_leveled_entry : wf_lang_db.


(*TODO: parameterize subst injectivity programmatically?
  When should the parameter be injective? always?
 *)
Definition subst_injectivity :=
  [("hd", ["A"; "l"; "G"]); ("wkn", ["A"; "l"; "G"]);
   ("snoc", ["v"; "A"; "l"; "g"; "G'"; "G"]); ("ext", ["A"; "G"]);
   ("forget", ["G"]); ("emp", []); ("ty", ["l";"G"]); ("ty_subst", ["l";"G"]);
   ("exp_subst", ["l";"G"]); ("exp", ["A"; "l"; "G"]);
   ("cmp", ["G3"; "G1"]); ("id", ["G"]); ("sub", ["G'"; "G"]); ("env", [])].

#[local] Definition pi_leveled' :=
    let ps := (elab_param "l" (pi++subst_lang)
                 [(*("env", None);
                   ("sub", None);*)
                ("exp",Some 1);
                ("ty", Some 0)]) in
  parameterize_lang "l" {{s #"lvl"}}
    ps pi.

Definition pi_leveled :=
  Eval vm_compute in pi_leveled'.


Lemma pi_leveled_wf
  : wf_lang_ext (subst_leveled++levels) pi_leveled.
Proof. compute_wf_lang. Qed.
#[local] Definition pi_leveled_entry := lang_entry pi_leveled_wf.
#[export] Hint Resolve pi_leveled_entry : wf_lang_db.

(*
TODO: level promotion constructs
*)
