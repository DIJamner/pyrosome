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

(* Lift operation and equations from
   https://arxiv.org/abs/1902.08848 (Sterling, "Algebraic Type Theory and
   Universe Hierarchies"), Section 4.1.
 *)
Definition lift_inj := levels_injectivity ++ subst_injectivity.

Derive lift
       SuchThat (wf_lang_ext (subst_leveled ++ levels) (lift : lang))
       As lift_wf.
Proof.
  setup_lang_interactive.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env", "A" : #"ty" "G" "l1"
      -----------------------------------------------
      #"lift" "p" "A" : #"ty" "G" "l2"
    ]}%prerule
    lift_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
                "A" : #"ty" "G'" "l1"
      ----------------------------------------------- ("lift_subst")
      #"ty_subst" "g" (#"lift" "p" "A")
      = #"lift" "p" (#"ty_subst" "g" "A")
      : #"ty" "G" "l2"
    ]}%prerule
    lift_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "l3" : #"lvl",
                "p" : #"<" "l1" "l2", "q" : #"<" "l2" "l3",
                "G" : #"env", "A" : #"ty" "G" "l1"
      ----------------------------------------------- ("lift_cmp")
      #"lift" "q" (#"lift" "p" "A")
      = #"lift" (#"<trans" "p" "q") "A"
      : #"ty" "G" "l3"
    ]}%prerule
    lift_inj.
  (* The `( s ) e1 = e2 srt` notation conflicts with the term-equality
     `( s ) e1 = e2 : t` notation, so we construct the prerule manually. *)
  elab_rule
    ("lift_el"%string,
     presort_eq_rule
       [("A", {{ps #"ty" "G" "l1"}});
        ("G", {{ps #"env"}});
        ("p", {{ps #"<" "l1" "l2"}});
        ("l2", {{ps #"lvl"}});
        ("l1", {{ps #"lvl"}})]
       {{ps #"exp" "G" "l1" "A"}}
       {{ps #"exp" "G" "l2" (#"lift" "p" "A")}})
    lift_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env", "A" : #"ty" "G" "l1"
      ----------------------------------------------- ("lift_ext")
      #"ext" "G" "A" = #"ext" "G" (#"lift" "p" "A") : #"env"
    ]}%prerule
    lift_inj.
  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition lift_entry := lang_entry lift_wf.
#[export] Hint Resolve lift_entry : wf_lang_db.

(* Naturality rules describing how `lift` interacts with the constructs of
   `pi_leveled`.
 *)
Definition pi_leveled_injectivity :=
  [("app", ["l"; "G"]);
   ("lambda", ["e"; "B"; "A"; "l"; "G"]);
   ("Pi", ["B"; "A"; "l"; "G"])].

Definition lift_pi_inj :=
  levels_injectivity ++ pi_leveled_injectivity ++ subst_injectivity.

Derive lift_pi
       SuchThat (wf_lang_ext (lift ++ pi_leveled ++ subst_leveled ++ levels)
                             (lift_pi : lang))
       As lift_pi_wf.
Proof.
  setup_lang_interactive.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "B" : #"ty" (#"ext" "G" "A") "l1"
      ----------------------------------------------- ("lift_Pi")
      #"lift" "p" (#"Pi" "A" "B")
      = #"Pi" (#"lift" "p" "A") (#"lift" "p" "B")
      : #"ty" "G" "l2"
    ]}%prerule
    lift_pi_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "B" : #"ty" (#"ext" "G" "A") "l1",
                "e" : #"exp" (#"ext" "G" "A") "l1" "B"
      ----------------------------------------------- ("lift_lambda")
      #"lambda" "A" "e"
      = #"lambda" (#"lift" "p" "A") "e"
      : #"exp" "G" "l2" (#"Pi" (#"lift" "p" "A") (#"lift" "p" "B"))
    ]}%prerule
    lift_pi_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "B" : #"ty" (#"ext" "G" "A") "l1",
                "e" : #"exp" "G" "l1" (#"Pi" "A" "B"),
                "e'" : #"exp" "G" "l1" "A"
      ----------------------------------------------- ("lift_app")
      #"app" ["A" := #"lift" "p" "A"] ["B" := #"lift" "p" "B"] "e" "e'"
      = #"app" "e" "e'"
      : #"exp" "G" "l2" (#"ty_subst" (#"snoc" #"id" "e'") (#"lift" "p" "B"))
    ]}%prerule
    lift_pi_inj.
  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition lift_pi_entry := lang_entry lift_pi_wf.
#[export] Hint Resolve lift_pi_entry : wf_lang_db.

#[local] Definition sigma_leveled' :=
    let ps := (elab_param "l" (sigma++subst_lang)
                 [(*("env", None);
                   ("sub", None);*)
                ("exp",Some 1);
                ("ty", Some 0)]) in
  parameterize_lang "l" {{s #"lvl"}}
    ps sigma.

Definition sigma_leveled :=
  Eval vm_compute in sigma_leveled'.

Lemma sigma_leveled_wf
  : wf_lang_ext (subst_leveled++levels) sigma_leveled.
Proof. compute_wf_lang. Qed.
#[local] Definition sigma_leveled_entry := lang_entry sigma_leveled_wf.
#[export] Hint Resolve sigma_leveled_entry : wf_lang_db.

(* Naturality rules describing how `lift` interacts with the constructs of
   `sigma_leveled`.
 *)
Definition sigma_leveled_injectivity :=
  [("proj2", ["l"; "G"]);
   ("proj1", ["A"; "l"; "G"]);
   ("ex", ["e2"; "B"; "e1"; "A"; "l"; "G"]);
   ("Sig", ["B"; "A"; "l"; "G"])].

Definition lift_sigma_inj :=
  levels_injectivity ++ sigma_leveled_injectivity ++ subst_injectivity.

Derive lift_sigma
       SuchThat (wf_lang_ext (lift ++ sigma_leveled ++ subst_leveled ++ levels)
                             (lift_sigma : lang))
       As lift_sigma_wf.
Proof.
  setup_lang_interactive.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "B" : #"ty" (#"ext" "G" "A") "l1"
      ----------------------------------------------- ("lift_Sig")
      #"lift" "p" (#"Sig" "A" "B")
      = #"Sig" (#"lift" "p" "A") (#"lift" "p" "B")
      : #"ty" "G" "l2"
    ]}%prerule
    lift_sigma_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "e1" : #"exp" "G" "l1" "A",
                "B" : #"ty" (#"ext" "G" "A") "l1",
                "e2" : #"exp" "G" "l1" (#"ty_subst" (#"snoc" #"id" "e1") "B")
      ----------------------------------------------- ("lift_ex")
      #"ex" "e1" "e2"
      = #"ex" "e1" "e2"
      : #"exp" "G" "l2" (#"Sig" (#"lift" "p" "A") (#"lift" "p" "B"))
    ]}%prerule
    lift_sigma_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "B" : #"ty" (#"ext" "G" "A") "l1",
                "e" : #"exp" "G" "l1" (#"Sig" "A" "B")
      ----------------------------------------------- ("lift_proj1")
      #"proj1" ["A" := #"lift" "p" "A"] ["B" := #"lift" "p" "B"] "e"
      = #"proj1" "e"
      : #"exp" "G" "l2" (#"lift" "p" "A")
    ]}%prerule
    lift_sigma_inj.
  elab_rule {[r "l1" : #"lvl", "l2" : #"lvl", "p" : #"<" "l1" "l2",
                "G" : #"env",
                "A" : #"ty" "G" "l1",
                "B" : #"ty" (#"ext" "G" "A") "l1",
                "e" : #"exp" "G" "l1" (#"Sig" "A" "B")
      ----------------------------------------------- ("lift_proj2")
      #"proj2" ["A" := #"lift" "p" "A"] ["B" := #"lift" "p" "B"] "e"
      = #"proj2" "e"
      : #"exp" "G" "l2"
            (#"ty_subst" (#"snoc" #"id" (#"proj1" "e")) (#"lift" "p" "B"))
    ]}%prerule
    lift_sigma_inj.
  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition lift_sigma_entry := lang_entry lift_sigma_wf.
#[export] Hint Resolve lift_sigma_entry : wf_lang_db.
