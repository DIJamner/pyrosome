| Paper | Line | File | Name |
|---|---|---|---|
| §1, two-pass STLC compiler (CPS + closure conversion) | 121–123 | `src/Pyrosome/Lang/CombinedThm.v` | `full_compiler_preserving`, `full_compiler_semantic` |
| §2, CPS pass ⟦λ(x:A).e⟧, ⟦e v⟧ | 131–134 | `src/Pyrosome/Lang/SimpleVCPS.v` | `cps_def` |
| §2, §4, `egraph_equal` | 170, 318 | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_equal` |
| §4 footnote 1, `egraph_reducing_equal'` | 340 | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_reducing_equal'` |
| §4, e-graph ⟨D, U, PA, E, W, A⟩ | 282–284 | `src/Utils/EGraph/Defs.v` | `instance` |
| §4, `analysis` typeclass | 309–313 | `src/Utils/EGraph/Defs.v` | `analysis` |
| Fig. 2, `run1iter` | 346 | `src/Utils/EGraph/Defs.v` | `run1iter` |
| Fig. 2, `saturate_until'` | 352 | `src/Utils/EGraph/Defs.v` | `saturate_until'` |
| Fig. 2, `saturate_until` | 362 | `src/Utils/EGraph/Defs.v` | `saturate_until` |
| §4 footnote 2, `scheduled_saturate_until` | 342 | `src/Pyrosome/Tools/EGraph/Defs.v` | `scheduled_saturate_until` |
| Fig. 3, `repair_union` | 393 | `src/Utils/EGraph/Defs.v` | `repair_union` |
| Fig. 3, `repair` | 407 | `src/Utils/EGraph/Defs.v` | `repair` |
| Fig. 3, `rebuild` | 416 | `src/Utils/EGraph/Defs.v` | `rebuild` |
| Fig. 4, logic-program IR (clause, sequent) | 442 | `src/Utils/EGraph/Semantics.v` | `clause`, `sequent` |
| §4.2 footnote 3, `pt_spaced_intersect` | 585–587 | `src/Utils/PosListMap.v` | `pt_spaced_intersect` |
| §4.2, correctness of `pt_spaced_intersect` | 585–587 | `src/Utils/PosListMapIntersectSpec.v` | `pt_spaced_intersect_correct` |
| §4.2, semi-naive tries T^full, T^old, T^new | 580–583 | `src/Utils/EGraph/Defs.v` | `build_tries_for_symbol` |
| §4.2, semi-naive query T^old ∩ … ∩ T^new ∩ … ∩ T^full | 589–591 | `src/Utils/EGraph/Defs.v` | `process_erule'_sn`, `process_erule` |
| Fig. 6, executable format ⟨Q, R⃗, C⃗⟩ | 638 | `src/Utils/EGraph/Defs.v` | `rule_set`, `erule`, `const_rule` |
| §4.3, compilation of IR rules to executable rules | 633–636 | `src/Utils/EGraph/QueryOpt.v` | `compile_rule`, `build_rule_set` |
| §4.4, Pyrosome rule to sequent | 667 | `src/Pyrosome/Tools/EGraph/Defs.v` | `rule_to_log_rule`, `rule_set_from_lang` |
| §4.4, rule optimization via e-graph | 679 | `src/Utils/EGraph/QueryOpt.v` | `optimize_sequent` |
| §4.5, sort-clause exclusion criterion | 729–733 | `src/Pyrosome/Theory/PatternRigidity.v` | `rigid_term_skip`, `rigid_sort_skip` |
| Fig. 8, `optimal_nodes` | 785 | `src/Pyrosome/Tools/EGraph/Defs.v` | `select_optimal_nodes` |
| Fig. 8, `extract` | 793 | `src/Pyrosome/Tools/EGraph/Defs.v` | `extract_weighted` |
| §4.7, eager reduction | 838–846 | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_reducing_equal_step` |
| §4.7, opportunistic congruence | 847–853 | `src/Pyrosome/Tools/EGraph/Defs.v` | `egraph_reducing_cong` |
| §4.7, congruence-candidate generation | 856–861 | `src/Pyrosome/Tools/EGraph/InjRuleGen.v` | `gen_reduce_inj_rules` |
| §4.8, compiler correctness by computation | 871–876 | `src/Pyrosome/Tools/EGraph/ComputeWf.v` | `compute_preserving_compiler`, `compute_preserving_compiler_sound` |
| §5, type inference | 885–892 | `src/Pyrosome/Tools/EGraph/TypeInference.v` | `infer_rule`, `infer_lang_ext`, `infer_compiler_simple` |
| §5, injectivity sequents | 901 | `src/Pyrosome/Tools/EGraph/TypeInference.v` | `build_injection_rule` |
| Theorem 6.1 | 932–933 | `src/Pyrosome/Tools/EGraph/Automation.v` | `egraph_sound` |
| §6, models of logic programs ⟨D, ∼, I⟩ | 941–954 | `src/Utils/EGraph/Semantics.v` | `model`, `model_ok`|
| §6, term model | 955–962 | `src/Pyrosome/Tools/EGraph/Theorems.v` | `lang_model` |
| §6, e-graph interpretations e ⊨ₘ i | 963–970 | `src/Utils/EGraph/Semantics.v` | `egraph_sound_for_interpretation` |
| §6, c {R} | 975 | `src/Utils/VC.v` | `vc` |
| Theorem 6.2 | 981–983 | `src/Utils/EGraph/Semantics.v` | `rebuild_sound` |
| Lemma 6.3 | 998–1001 | `src/Utils/VC.v` | `vc_bind` |
| Theorem 6.4 | 1009–1015 | `src/Utils/EGraph/SemanticsSaturate.v` | `saturate_until_sound` |
| Theorem 6.4 (scheduled variant) | 1009–1015 | `src/Pyrosome/Tools/EGraph/SchedSat.v` | `scheduled_saturate_until_sound` |
| Theorem 6.5, `add_open_term` | 1040–1046 | `src/Pyrosome/Tools/EGraph/Defs.v` | `add_open_term` |
| Theorem 6.5 | 1040–1046 | `src/Pyrosome/Tools/EGraph/Theorems.v` | `add_open_term_sound` |
| §6.2, union-find invariants (1)–(5) | 1073–1078, 1095–1096 | `src/Utils/UnionFind.v` | `union_find_ok` |
| §6.2, `find` and `union` preserve the invariants | 1071–1072 | `src/Utils/UnionFind.v` | `find_spec`, `union_spec` |
| §6.2, `alloc` preserves the invariants | 1071–1072 | `src/Utils/EGraph/Semantics.v` | `alloc_sound`, `alloc_egraph_ok` |
| §6.2, `egraph_ok` | 1097–1103 | `src/Utils/EGraph/Semantics.v` | `egraph_ok` |
| Fig. 9, STLC CPS | 1080 | `src/Pyrosome/Lang/SimpleVCPS.v` | `cps_def`, `cps_preserving` |
| Fig. 9, STLC CC | 1081 | `src/Pyrosome/Lang/SimpleVCC.v` | `cc_def`, `cc_preserving` |
| Fig. 9, Fix CPS | 1082 | `src/Pyrosome/Lang/SimpleVFixCPS.v` | `fix_cps_def`, `fix_cps_preserving` |
| Fig. 9, Fix CC | 1083 | `src/Pyrosome/Lang/SimpleVFixCC.v` | `fix_cc_def`, `fix_cc_preserving` |
| Fig. 9, Ref CPS | 1084 | `src/Pyrosome/Lang/SimpleVCPSHeap.v` | `heap_cps_def`, `heap_cps_preserving`, `heap_ctx_cps_def`, `heap_ctx_cps_preserving` |
| Fig. 9, Ref CC | 1085 | `src/Pyrosome/Lang/SimpleVCCHeap.v` | `heap_cc_def`, `heap_cc_preserving` |
| Fig. 9, Poly CPS | 1086 | `src/Pyrosome/Lang/PolyCompilersCPS.v` | `poly_cps_def`, `poly_cps_preserving` |
| Fig. 9, Ex CPS | 1087 | `src/Pyrosome/Lang/PolyCompilersCPS.v` | `exists_cps_def`, `exists_cps_preserving` |
| Fig. 9, Ex CC | 1088 | `src/Pyrosome/Lang/PolyCompilers.v` | `exists_cc_def`, `exists_cc_preserving` |
| Fig. 9, Imp | 1089 | `src/Pyrosome/Lang/Imp.v` | `ch8_cc_def`, `ch8_cc_preserving` |
| Fig. 9, LinearCPS | 1090 | `src/Pyrosome/Lang/LinearCPS.v` | `linear_cps_def`, `linear_cps_preserving` |
