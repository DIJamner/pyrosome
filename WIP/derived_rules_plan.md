# Derived rules via the e-graph — plan and verified mechanism

## The mechanism (working prototype: `WIP/GluingDerived.v`, verified axiom-free)

A **derived rule** is an `eq_term stlc_unit c _ _ _` stated over OBJECT-LEVEL
variables (`var "D"`, `var "G"`, …) in a concrete context `c`, proved by one
e-graph call. It is then instantiated at meta-level terms by a tactic that
infers the substitution, exactly as `eredex_steps_with` does for a primitive
rule. Three pieces:

```coq
(* 1. prove a derived rule *)
Ltac egraph_eq :=
  pose proof stlc_unit_wf;
  apply (egraph_sound 100 100 100 100 filter_rules
           (fun _ : string * Rule.rule string => true) empty_inj_rules);
  [ exact stlc_unit_wf | solve_wf_ctx | compute_term_wf | compute_term_wf
  | flagged_exact I ].

(* 2. instantiate it, inferring the substitution *)
Ltac dstep lem :=
  let ty := type of lem in
  lazymatch ty with
  | @eq_term ?V _ ?l ?cr ?tp ?e1p ?e2p =>
      lazymatch goal with
      | [|- @eq_term ?V' _ ?l' ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_ : @NamedList.named_list V (Term.term V)) in
          first [ unify_var_names V s cr | fail 2 "could not unify var names" ];
          first [ replace (@eq_term V' _ l' c' t e1 e2)
                    with (@eq_term V _ l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [ | f_equal; vm_compute; reflexivity ]
                | fail 2 "could not replace with subst" ];
          eapply (@eq_term_subst V _ l c' s s cr);
          [ exact lem
          | apply eq_subst_refl; try unfold cr; wf_subst_solve'
          | ]
      end
  end.
(* leaves one goal: wf_ctx cr -- discharge with a stored lemma proved by solve_wf_ctx *)
```

Gotchas found empirically (all already handled above):

- `egraph_eq` needs `wf_lang stlc_unit` in the local context: `solve_wf_ctx` and
  `compute_term_wf` both start with `assumption`. Hence the leading `pose proof`.
- `open_constr:(_ : subst V)` does not parse in these files (`subst`'s variable
  is already fixed); use `@NamedList.named_list V (Term.term V)`.
- The `wf_subst` goal mentions the context CONSTANT, so `wf_subst_solve'` needs
  `try unfold cr` first.
- `flagged_exact I` uses `vm_cast_no_check`, so the e-graph run happens at `Qed`,
  not at tactic time. A failing `egraph_eq` looks like it succeeded until `Qed`.
  Measure cost with `Print Assumptions`, not with tactic timing.

Cost: about **6 s per derived rule** (three e-graph runs: the equation, the
context, and the two subject terms).

## Targets

Pure equational chains — the whole statement is an `eq_term` between concrete
syntax, so the entire lemma becomes one derived rule:

| current lemma | file | hand steps |
|---|---|---|
| `lift_cmp_wkn` | StlcNormalForms | 3 |
| `eq_beta_lift` / `eq_lift_inst` | StlcModelCong / StlcModelEq (duplicated) | 4 |
| `eq_lam_beta` / `eq_beta_lift` | StlcModelCong / StlcModelEq (duplicated) | 4 |

Pure equational TAILS inside larger lemmas — extract the tail as a derived rule
and leave the surrounding induction/reducibility reasoning alone:

| host lemma | extractable tail |
|---|---|
| `by_cmp_assoc` | `eq_cmp_assoc; eq_cmp_assoc` (4-fold reassociation) |
| `by_val_subst_cmp` | `eq_val_subst_cmp; eq_val_subst_cmp` |
| `by_exp_subst_cmp` | `eq_exp_subst_cmp; eq_exp_subst_cmp` |
| `by_cmp_snoc` | `eq_cmp_assoc; eq_cmp_snoc` |
| `by_exp_subst_ret` | `eq_exp_subst_cmp; eq_exp_subst_ret` |
| `by_exp_subst_app` | `eq_exp_subst_cmp; eq_exp_subst_app` |
| `by_cmp_forget` | `eq_cmp_assoc; eq_cmp_forget` |
| `by_snoc_wkn_hd` | `cong_Cmp + eq_snoc_wkn_hd + eq_id_right` |
| `by_stlc_beta` | `eq_exp_subst_app; cong_App(eq_exp_subst_ret ×2); eq_beta_lift` |
| `RSub_id` | `eq_id_right; eq_id_right` |

NOT candidates — the chain consumes a hypothesis equation or an induction
hypothesis, so there is no closed derived rule to state: `Wk_cmp`, `VarT_wk`,
`NfT_wk`, `RSub_wk`, `RSub_proj`, `RSub_hd`, `RV_wk`, `RE_wk`, `RV_lam`,
`RV_lam_sub`, `term_trans_obligation`, `RSub_eq'`.

## Rule

Only convert where the derived rule actually shortens the proof. A two-step
chain that is already `eapply eq_term_trans; [apply eq_X; wfa | apply eq_Y; wfa]`
costs 2 lines; a derived rule costs a context definition, a `wf_ctx` lemma, the
rule itself, and 6 s of build time. Convert the three pure chains and the
`by_stlc_beta` tail for certain; measure the rest and report the build-time
delta before committing to them.
