(* ============================================================================
   Cluster II of trie #4: depth-uniformity of the [build_tries] output and the
   [variable_flags] bookkeeping facts.

   These discharge the [Hfd]/[H9] obligations of
   [FullPosTrieConv.fpt_spaced_intersect_inputs_hit] for the positive
   e-graph instantiation, so that H9/H10 at Automation.v can be closed and
   [egraph_sound] becomes axiom-free.  See WIP/trie4_P2_build_tries_depth_design.md.
   ============================================================================ *)
From Stdlib Require Import Lists.List Uint63.
Import ListNotations.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils Monad Default.
From Utils Require Import EGraph.Defs.

Section VariableFlags.
  Context {idx : Type} {Eqb_idx : Eqb idx} {Eqb_idx_ok : Eqb_ok Eqb_idx}.

  (* [variable_flags] returns one flag per query variable. *)
  Lemma variable_flags_length (qvs cvs : list idx) :
    length (variable_flags idx Eqb_idx qvs cvs) = length qvs.
  Proof.
    revert cvs. induction qvs as [|qx qvs' IH]; intros cvs; cbn [variable_flags length].
    - reflexivity.
    - destruct cvs as [|cx cvs'].
      + cbn [length]. rewrite IH. reflexivity.
      + destruct (eqb qx cx); cbn [length]; rewrite IH; reflexivity.
  Qed.

  (* The number of selected (true) flags equals the number of clause variables,
     when the clause variables are exactly a value-predicate filtering of the
     query variables -- which is how [compile_query_clause] builds
     [clause_vars := sort_by_position_in (out::args) qvs = filter _ qvs]. *)
  Lemma variable_flags_filter_id_len (p : idx -> bool) (qv : list idx) :
    length (filter id (variable_flags idx Eqb_idx qv (filter p qv))) = length (filter p qv).
  Proof.
    induction qv as [|qx qv' IH]; cbn [filter variable_flags].
    - reflexivity.
    - destruct (p qx) eqn:Hpqx.
      + cbn [variable_flags]. rewrite eqb_refl_true by exact Eqb_idx_ok.
        cbn [filter id length]. rewrite IH. reflexivity.
      + destruct (filter p qv') as [|cx cv''] eqn:Hcv'.
        * cbn [variable_flags filter id]. rewrite IH. reflexivity.
        * assert (Hpcx : p cx = true).
          { assert (Hin : In cx (filter p qv')) by (rewrite Hcv'; left; reflexivity).
            apply filter_In in Hin. apply Hin. }
          cbn [variable_flags].
          replace (eqb qx cx) with false.
          2:{ symmetry. apply eqb_ineq_false;
                [ exact Eqb_idx_ok
                | left; intros ->; rewrite Hpcx in Hpqx; discriminate ]. }
          cbn [filter id]. exact IH.
  Qed.

End VariableFlags.
