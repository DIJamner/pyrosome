| Paper | File | Name |
|---|---|---|
| §1, two-pass STLC compiler (CPS + closure conversion) | `src/Pyrosome/Lang/CombinedThm.v` | `full_compiler_preserving`, `full_compiler_semantic` |
| §2, CPS pass ⟦λ(x:A).e⟧, ⟦e v⟧ | `src/Pyrosome/Lang/SimpleVCPS.v` | `cps_def` |
| §2, §4, `egraph_equal` | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_equal` |
| §4 footnote 1, `egraph_reducing_equal'` | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_reducing_equal'` |
| §4, e-graph ⟨D, U, PA, E, W, A⟩ | `src/Utils/EGraph/Defs.v` | `instance` |
| §4, database tables (epoch and analysis metadata) | `src/Utils/EGraph/Defs.v` | `db_entry` |
| §4, atom f(x⃗) → y | `src/Utils/EGraph/Defs.v` | `atom` |
| §4, `analysis` typeclass | `src/Utils/EGraph/Defs.v` | `analysis` |
| Fig. 2, `run1iter` | `src/Utils/EGraph/Defs.v` | `run1iter` |
| Fig. 2, `saturate_until'` | `src/Utils/EGraph/Defs.v` | `saturate_until'` |
| Fig. 2, `saturate_until` | `src/Utils/EGraph/Defs.v` | `saturate_until` |
| §4 footnote 2, `scheduled_saturate_until` | `src/Pyrosome/Tools/EGraph/Defs.v` | `scheduled_saturate_until` |
| Fig. 3, `repair_union` | `src/Utils/EGraph/Defs.v` | `repair_union` |
| Fig. 3, `repair` | `src/Utils/EGraph/Defs.v` | `repair` |
| Fig. 3, `rebuild` | `src/Utils/EGraph/Defs.v` | `rebuild` |
| §4, union-find `find`, `union` | `src/Utils/UnionFind.v` | `find`, `union` |
| Fig. 4, logic-program IR (clause, sequent) | `src/Utils/EGraph/Semantics.v` | `clause`, `sequent` |
| §4.2, trie_DB (per-clause index) | `src/Utils/EGraph/Defs.v` | `trie_of_clause`, `build_tries` |
| §4.2, n-way trie intersection with skipped-variable flags | `src/Utils/EGraph/Defs.v` | `intersection_keys` |
| §4.2 footnote 3, `pt_spaced_intersect` | `src/Utils/PosListMap.v` | `pt_spaced_intersect` |
| §4.2, correctness of `pt_spaced_intersect` | `src/Utils/PosListMapIntersectSpec.v` | `pt_spaced_intersect_correct` |
| §4.2, semi-naive tries T^full, T^old, T^new | `src/Utils/EGraph/Defs.v` | `build_tries_for_symbol` |
| §4.2, semi-naive query T^old ∩ … ∩ T^new ∩ … ∩ T^full | `src/Utils/EGraph/Defs.v` | `process_erule'_sn`, `process_erule` |
| Fig. 6, executable format ⟨Q, R⃗, C⃗⟩ | `src/Utils/EGraph/Defs.v` | `rule_set`, `erule`, `const_rule` |
| §4.3, compilation of IR rules to executable rules | `src/Utils/EGraph/QueryOpt.v` | `compile_rule`, `build_rule_set` |
| §4.4, Pyrosome rule to sequent | `src/Pyrosome/Tools/EGraph/Defs.v` | `rule_to_log_rule`, `rule_set_from_lang` |
| §4.4, rule optimization via e-graph | `src/Utils/EGraph/QueryOpt.v` | `optimize_sequent` |
| §4.5, sort-clause exclusion criterion | `src/Pyrosome/Theory/PatternRigidity.v` | `rigid_term_skip`, `rigid_sort_skip` |
| §4.6, cost analysis | `src/Pyrosome/Tools/EGraph/Defs.v` | `weighted_size_analysis` |
| Fig. 8, `optimal_nodes` | `src/Pyrosome/Tools/EGraph/Defs.v` | `select_optimal_nodes` |
| Fig. 8, `extract` | `src/Pyrosome/Tools/EGraph/Defs.v` | `extract_weighted` |
| §4.7, rule scheduling (epoch window) | `src/Pyrosome/Tools/EGraph/Defs.v` | `scheduled_saturate_until` |
| §4.7, eager reduction | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_reducing_equal_step` |
| §4.7, opportunistic congruence | `src/Pyrosome/Tools/EGraph/Defs.v` | `cong_subgoals`, `saturate_cong_subgoals`, `egraph_reducing_cong` |
| §4.7, congruence-candidate generation | `src/Pyrosome/Tools/EGraph/InjRuleGen.v` | `gen_reduce_inj_rules` |
| §4.8, compiler correctness by computation | `src/Pyrosome/Tools/EGraph/ComputeWf.v` | `compute_preserving_compiler`, `compute_preserving_compiler_sound` |
| §4.8, well-formedness by computation | `src/Pyrosome/Tools/EGraph/ComputeWf.v` | `compute_wf_lang`, `compute_wf_lang_sound` |
| §5, type inference | `src/Pyrosome/Tools/EGraph/TypeInference.v` | `infer_rule`, `infer_lang_ext`, `infer_compiler_simple` |
| §5, injectivity sequents | `src/Pyrosome/Tools/EGraph/TypeInference.v` | `injection_rule_from_name_and_rule`, `build_injection_rule` |
| Theorem 6.1 | `src/Pyrosome/Tools/EGraph/Automation.v` | `egraph_sound` |
| Theorem 6.1 (renamed-language core) | `src/Pyrosome/Tools/EGraph/Automation.v` | `egraph_reducing_equal_sound` |
| §6, models of logic programs ⟨D, ∼, I⟩ | `src/Utils/EGraph/Semantics.v` | `model`, `model_ok`, `model_satisfies_rule` |
| §6, term model | `src/Pyrosome/Tools/EGraph/Theorems.v` | `lang_model` |
| §6, e-graph interpretations e ⊨ₘ i | `src/Utils/EGraph/Semantics.v` | `egraph_sound_for_interpretation` |
| §6, c {R} | `src/Utils/VC.v` | `vc` |
| Theorem 6.2 | `src/Utils/EGraph/Semantics.v` | `rebuild_sound` |
| Lemma 6.3 | `src/Utils/VC.v` | `vc_bind` |
| Theorem 6.4 | `src/Utils/EGraph/SemanticsSaturate.v` | `saturate_until_sound` |
| Theorem 6.4 (scheduled variant) | `src/Pyrosome/Tools/EGraph/SchedSat.v` | `scheduled_saturate_until_sound` |
| Theorem 6.5, `add_open_term` | `src/Pyrosome/Tools/EGraph/Defs.v` | `add_open_term` |
| Theorem 6.5 | `src/Pyrosome/Tools/EGraph/Theorems.v` | `add_open_term_sound` |
| §6.1, rule-translation soundness | `src/Utils/EGraph/QueryOptSound.v` | `compile_rule_inl_erule_sound`, `compile_rule_inr_const_sound`, `optimize_sequent_forward_atoms` |
| §6.2, union-find invariants (1)–(5) | `src/Utils/UnionFind.v` | `union_find_ok` |
| §6.2, `find` and `union` preserve the invariants | `src/Utils/UnionFind.v` | `find_spec`, `union_spec` |
| §6.2, `alloc` preserves the invariants | `src/Utils/EGraph/Semantics.v` | `alloc_sound`, `alloc_egraph_ok` |
| §6.2, `egraph_ok` | `src/Utils/EGraph/Semantics.v` | `egraph_ok` |
| Fig. 9, STLC CPS | `src/Pyrosome/Lang/SimpleVCPS.v` | `cps_def`, `cps_preserving` |
| Fig. 9, STLC CC | `src/Pyrosome/Lang/SimpleVCC.v` | `cc_def`, `cc` |
| Fig. 9, Fix CPS | `src/Pyrosome/Lang/SimpleVFixCPS.v` | `fix_cps_def`, `fix_cps` |
| Fig. 9, Fix CC | `src/Pyrosome/Lang/SimpleVFixCC.v` | `fix_cc_def`, `fix_cc` |
| Fig. 9, Ref CPS | `src/Pyrosome/Lang/SimpleVCPSHeap.v` | `heap_cps_def`, `heap_cps`, `heap_ctx_cps_def`, `heap_ctx_cps` |
| Fig. 9, Ref CC | `src/Pyrosome/Lang/SimpleVCCHeap.v` | `heap_cc_def`, `heap_cc` |
| Fig. 9, Poly CPS | `src/Pyrosome/Lang/PolyCompilersCPS.v` | `poly_cps_def`, `poly_cps` |
| Fig. 9, Ex CPS | `src/Pyrosome/Lang/PolyCompilersCPS.v` | `exists_cps_def`, `exists_cps` |
| Fig. 9, Ex CC | `src/Pyrosome/Lang/PolyCompilers.v` | `exists_cc_def`, `exists_cc` |
| Fig. 9, Imp | `src/Pyrosome/Lang/Imp.v` | `ch8_cc_def`, `ch8_cc` |
| Fig. 9, LinearCPS | `src/Pyrosome/Lang/LinearCPS.v` | `linear_cps_def`, `linear_cps_preserving` |
