(* Does min-sorts actually engage for the fix_cps target language, and what
   does fix_beta's compiled query look like? *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.SyntacticSorts
  Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Tools.Matches Tools.EGraph.Automation Tools.EGraph.TypeInference Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS.
Import Core.Notations.

Definition Ltgt :=
  fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst.

(* (1) Is the syntactic-sort-equality gate ON for the target? *)
Definition gate := syntactic_sort_eq_langb Ltgt.
Eval vm_compute in gate.

(* (2) The index heads R, and per-conjunct breakdown of the gate. *)
Eval vm_compute in (index_heads_b Ltgt).
Eval vm_compute in (forallb (fun p => negb (is_sort_eq_ruleb (snd p))) Ltgt).
Eval vm_compute in (inclb (close_index_step Ltgt (index_heads_b Ltgt)) (index_heads_b Ltgt)).
Eval vm_compute in
  (forallb (fun p => match snd p with
                     | term_eq_rule _ _ _ t => negb (inb (sort_head t) (index_heads_b Ltgt))
                     | _ => true end) Ltgt).

(* (3) The fix_beta rule itself, and fv of its LHS vs its ctx. *)
Definition fixbeta := named_list_lookup_err Ltgt "fix_beta".
Eval vm_compute in fixbeta.

(* (4) Does fix_beta fire on its OWN statement? (sort-free query => should be
   a one-step refl match.) Probe Is_Success at small fuel. *)
Ltac probe_res sf rf :=
  apply (egraph_sound 100 sf 100 rf filter_rules
           (fun _ : string * Rule.rule string => true) empty_inj_rules);
  [ prove_by_lang_db | shelve | shelve | shelve |
    lazymatch goal with
    | |- ?G => let r := eval vm_compute in G in idtac "  fix_beta-self RESULT (True=fires):" r
    end ].

Goal eq_term Ltgt
  [("v", {{s #"val" "G" "A"}});
   ("e", {{s #"blk" (#"ext" (#"ext" "G" (#"neg" "A")) "A")}});
   ("A", {{s #"ty"}}); ("G", {{s #"env"}})]
  {{s #"blk" "G"}}
  {{e #"jmp" "G" "A" (#"fix" "G" "A" "e") "v"}}
  {{e #"blk_subst" "G" (#"ext" (#"ext" "G" (#"neg" "A")) "A")
        (#"snoc" "G" (#"ext" "G" (#"neg" "A"))
            (#"snoc" "G" "G" (#"id" "G") (#"neg" "A") (#"fix" "G" "A" "e"))
            "A" "v") "e"}}.
Proof. idtac "===== fix_beta self-test ====="; probe_res 20 4. Abort.
