Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleEvalCtx SimpleVCPS.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Notation compiler := (compiler string).

(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Definition Ectx_cps_def : compiler :=
  match # from eval_ctx with
  | {{s #"Ectx" "G" "A" "B" }} =>
    {{s #"blk" (#"ext" (#"ext" "G" (#"neg" "B")) "A") }}
  | {{e #"[ ]" "G" "A"}} =>
    {{e #"jmp" {ovar 1} {ovar 0} }}
  | {{e #"plug" "G" "A" "B" "E" "e"}} =>
    bind_k 1 (var "e") (var "A") (var "E")
  end.

Derive Ectx_cps
       SuchThat (elab_preserving_compiler cps_subst
                                          (cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          Ectx_cps_def
                                          Ectx_cps
                                          eval_ctx)
       As Ectx_cps_preserving.
Proof. auto_elab_compiler. Qed.
#[local] Definition Ectx_cps_entry :=
  cmp_entry (elab_compiler_implies_preserving Ectx_cps_preserving).
#[export] Hint Resolve Ectx_cps_entry : preserving_db.
