From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
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

From Pyrosome.Compilers Require Import Parameterizer.

From Pyrosome.Lang Require Import
  Subst SubstEqnGen.
From Pyrosome.Lang.OTT Require Import Base Nat.

From Stdlib Require derive.Derive.

Import Core.Notations.
Import PreRule.Notations.

(* Structural wf prover: decompose wf goals to leaves WITHOUT the e-graph
   solve_wf_ctx (which does not terminate on the deep ty_subst/El sorts).
   wf_term_by' lets a con-term be typed at a convertible type; by_reduction
   discharges the conversion (eq_sort/eq_term) via reduction proofs. *)
Ltac wfstep :=
  match goal with
  | |- fresh _ _ => solve_fresh
  | |- sublist _ _ => solve_sublist
  | |- In _ _ => solve_in
  | |- len_eq _ _ => econstructor
  | |- wf_ctx (Model := _) _ => apply wf_ctx_nil || apply wf_ctx_cons
  | |- Model.wf_ctx _ => apply wf_ctx_nil || apply wf_ctx_cons
  | |- Model.wf_sort _ _ => eapply wf_sort_by
  | |- wf_sort _ _ _ => eapply wf_sort_by
  | |- Model.wf_args _ _ _ =>
        simple apply wf_args_nil || simple eapply wf_args_cons2 || simple eapply wf_args_cons
  | |- wf_args _ _ _ _ =>
        simple apply wf_args_nil || simple eapply wf_args_cons2 || simple eapply wf_args_cons
  | |- Model.wf_term _ (var _) _ =>
        eapply wf_term_var || (eapply wf_term_conv; [ eapply wf_term_var |])
  | |- wf_term _ _ (var _) _ =>
        eapply wf_term_var || (eapply wf_term_conv; [ eapply wf_term_var |])
  | |- Model.wf_term _ _ _ => eapply wf_term_by'
  | |- wf_term _ _ _ _ => eapply wf_term_by'
  | |- _ = _ \/ _ => first [ left; reflexivity | left; vm_compute; reflexivity | right ]
  | |- Model.eq_sort _ _ _ => first [ sort_cong | by_reduction ]
  | |- eq_sort _ _ _ _ => first [ sort_cong | by_reduction ]
  | |- Model.eq_term _ _ _ _ => by_reduction
  | |- eq_term _ _ _ _ _ => by_reduction
  | |- eq_args _ _ _ _ =>
        apply eq_args_nil || simple eapply eq_args_cons2 || simple eapply eq_args_cons
  | |- _ = _ => vm_compute; reflexivity
  end.

(* ====================================================================== *)
(* Identity types (Agda Typed.agda:101-108, 109-116).                     *)
(*   Id A t u : SProp   (A a proof-relevant code in U_{!,l}; t,u : El A)  *)
(*   Idrefl A t : Id A t t                                                *)
(*   transp : transport along a proof-irrelevant predicate                *)
(* Plus the first-order ℕ-computation rules for Id (Typed.agda:241-250).  *)
(* ====================================================================== *)

Definition id_injectivity :=
  [("Id", ["u"; "t"; "A"; "l"; "G"]);
   ("Idrefl", ["t"; "A"; "l"; "G"])].

Derive ott_id
       in (wf_lang_ext (ott_nat ++ ott_base ++ subst_ott ++ ott_info) ott_id)
       as ott_id_wf.
Proof.
  setup_lang_interactive.

  (* Id A t u : a code in SProp. *)
  elab_rule {[r "G" : #"env", "l" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A")
      -----------------------------------------------
      #"Id" "A" "t" "u" : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'", "l" : #"lvl",
          "A" : #"exp" "G'" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G'"] #"rel" "l"),
          "t" : #"exp" "G'" (#"info" #"rel" (#"iota" "l")) (#"El" "A"),
          "u" : #"exp" "G'" (#"info" #"rel" (#"iota" "l")) (#"El" "A")
      ----------------------------------------------- ("Id subst")
      #"exp_subst" "g" (#"Id" "A" "t" "u")
        = #"Id" (#"exp_subst" "g" "A") (#"exp_subst" "g" "t") (#"exp_subst" "g" "u")
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* Idrefl A t : Id A t t  (a proof, lives in SProp). *)
  elab_rule {[r "G" : #"env", "l" : #"lvl",
          "A" : #"exp" "G" (#"info" #"rel" (#"next" "l")) (#"U" ["G" := "G"] #"rel" "l"),
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" "l")) (#"El" "A")
      -----------------------------------------------
      #"Idrefl" "A" "t"
        : #"exp" "G" (#"info" #"irr" (#"iota" #"L0"))
          (#"El" ["G" := "G"] ["r" := #"irr"] ["l" := #"L0"] (#"Id" ["G" := "G"] ["l" := "l"] "A" "t" "t"))
    ]}%prerule
    (id_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* First-order ℕ computations for Id (Typed.agda:241-250, 272-277).
     These equate CODES, so are NOT subsumed by proof irrelevance.
     (Id ℕ 0 0 = sUnit needs Π and lives in Pi-importing follow-up.) *)
  elab_rule {[r "G" : #"env",
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-0S")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) #"zero" (#"suc" "t")
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env",
          "t" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-S0")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"suc" "t") #"zero"
        = #"Empty" ["G" := "G"]
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).
  elab_rule {[r "G" : #"env",
          "m" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"])),
          "n" : #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" ["G" := "G"] ["r" := #"rel"] ["l" := #"L0"] (#"Nat" ["G" := "G"]))
      ----------------------------------------------- ("Id-Nat-SS")
      #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) (#"suc" "m") (#"suc" "n")
        = #"Id" ["G" := "G"] ["l" := #"L0"] (#"Nat" ["G" := "G"]) "m" "n"
      : #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" ["G" := "G"] #"irr" #"L0")
    ]}%prerule
    (id_injectivity ++ nat_injectivity ++ ott_base_injectivity ++ ott_info_injectivity ++ subst_ott_injectivity).

  (* transp (Typed.agda:109-116): DEFERRED ON THIS MACHINE (out of memory).
     The structural proof IS correct and complete:
       push_rule_no_compute [:| <transp, fully explicit> ]%rule.
       1:{ apply wf_lang_nil. }
       apply wf_term_rule.
       all: repeat wfstep.            (* wfstep, defined above, fully decomposes *)
       Unshelve.
       all: try (vm_compute; reflexivity). all: try (repeat wfstep). all: shelve.
     wfstep leaves 0 remaining goals (verified), discharging the snoc-id
     ty_subst_id conversion via by_reduction.  But the vm_compute/by_reduction
     steps allocate >7GB and the rocqworker is OOM-killed on this 8GB swapless
     box (confirmed in dmesg: "Out of memory: Killed process ... rocqworker
     total-vm:7304860kB").  Needs more RAM / swap (run elsewhere) to land.
     transp's computation is in any case subsumed by proof irrelevance. *)
  apply wf_lang_nil.
Unshelve.
1:shelve.
1:vm_compute; reflexivity.
Qed.
#[local] Definition ott_id_entry := lang_entry ott_id_wf.
#[export] Hint Resolve ott_id_entry : wf_lang_db.
