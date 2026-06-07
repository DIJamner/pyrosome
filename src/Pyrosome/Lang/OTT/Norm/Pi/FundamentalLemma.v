(* ====================================================================== *)
(* OTT pivot, file 4/5 (see WIP/NEXT_SESSION.md UPDATE-v).                  *)
(*                                                                        *)
(* The FUNDAMENTAL LEMMA for the reduction-on-syntax logical relation:      *)
(* every well-typed OTT type/term is reducible.  This is also where the     *)
(* DEFERRED correctness of the LogicalRelation.v Kripke builders            *)
(* (act_code/cod_at/ounder/mapp) gets exercised against the real OTT typing *)
(* and the OTT substitution equations.                                     *)
(*                                                                        *)
(* FOUNDATION (this commit): assemble the concrete OTT language             *)
(*   ott := ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info         *)
(* and prove `wf_lang ott`, so the generic LR (over `wf_lang l`) can be     *)
(* instantiated at `l := ott`.  The fundamental lemma itself is TODO.       *)
(* ====================================================================== *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Theory Require CutElim.
From Pyrosome.Tools Require Import Matches.
From Pyrosome.Lang.OTT Require Import Base Nat Pi.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral LogicalRelation.
Import Core.Notations.

(* The concrete cut-free OTT language with proof-relevant Π, ℕ/Empty, the
   substitution calculus and the static info layer.  (No Id/Cast/Σ — those are
   not needed for the Π normalization payoff.)  The Π β/η computation rules live
   inside `ott_pi` itself, so this is exactly the language the reduction relation
   orients. *)
Definition ott : lang string :=
  (ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info)%list.

(* NB: `ott_wf` inherits the project-wide `Automation.egraph_sound` axiom from the
   imported OTT language wf proofs (`ott_pi_wf`/`ott_nat_wf`/`ott_base_wf`/...),
   which are established via the e-graph wf checker.  The LR machinery itself
   (Reduction/Neutral/LogicalRelation) is axiom-free; only the concrete OTT lang
   instantiation carries `egraph_sound`. *)
Lemma ott_wf : wf_lang ott.
Proof.
  unfold ott.
  (* lower stack, bottom-up via wf_lang_concat. *)
  pose proof ott_info_wf as H0.
  pose proof (wf_lang_concat H0 subst_ott_wf) as H1.
  pose proof (wf_lang_concat H1 ott_base_wf) as H2.
  pose proof (wf_lang_concat H2 ott_nat_wf) as H3.
  (* ott_pi is ext over (ott_base ++ ..), weaken it over (ott_nat ++ ott_base ++ ..). *)
  assert (Hpi : wf_lang_ext (ott_nat ++ ott_base ++ subst_ott ++ ott_info)%list ott_pi).
  { eapply lang_ext_monotonicity.
    - exact ott_pi_wf.
    - apply incl_appr, incl_refl.
    - compute_all_fresh. }
  exact (wf_lang_concat H3 Hpi).
Qed.

(* ====================================================================== *)
(* WELL-TYPEDNESS OF THE LogicalRelation.v KRIPKE BUILDERS (subgoal (a)).    *)
(*                                                                        *)
(* The reducibility relation's Pi case carries Kripke operations            *)
(* (`act_code`, `extc`, `cod_at`, `mapp`, ...) that push the domain /        *)
(* codomain codes and the member along an object substitution.  Their        *)
(* DEFINITIONS landed in LogicalRelation.v with correctness DEFERRED here     *)
(* (UPDATE-v): until `wf_lang ott` and the OTT substitution equations are in  *)
(* scope, one cannot check that the inlined `exp_subst`/`under'` annotations  *)
(* actually type.  This section discharges those obligations one builder at   *)
(* a time, against the real `ott` typing rules.                              *)
(* ====================================================================== *)

(* The standard "build a `wf_term`/`wf_args` derivation by hand" driver,      *)
(* specialised to `ott`: peel `wf_args`, expose the model's `wf_term`,        *)
(* compute the `with_names_from` substitution in each subject's sort, close   *)
(* variable leaves by assumption and constructor leaves by `wf_term_by'`      *)
(* (which keeps the conclusion type flexible, so the `with_names_from`        *)
(* unification is deferred to a reflexivity/conversion side-goal).            *)
Ltac ott_wf_args :=
  repeat first
    [ simple apply wf_args_nil
    | simple eapply wf_args_cons2
    | simple eapply wf_args_cons
    | progress cbn [Model.wf_term core_model]
    | progress compute_wf_subjects
    | eassumption
    | (eapply Elab.wf_term_by';
         [ apply named_list_lookup_err_in; compute; reflexivity
         |
         | left; compute; reflexivity ]) ].

(* The "U subst" computation rule instantiated by an EXPLICIT (variable-only)
   substitution, packaged so its `wf_subst` side-goal is discharged from the
   variable hypotheses by `assumption` rather than the computational wf checker
   (which cannot evaluate the free env/level/sub variables).  This is the bare
   convertibility `ty_subst g (U rF lF G) = U rF lF D` the builder typings need. *)
Lemma U_subst_eq rF lF g G D
  (HG : wf_term ott [] G (scon "env" []))
  (HD : wf_term ott [] D (scon "env" []))
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (scon "sub" [G; D]))
  : eq_term ott [] (scon "ty" [code_info lF; D])
      (con "ty_subst" [oU rF lF G; code_info lF; g; G; D]) (oU rF lF D).
Proof.
  pose proof ott_wf as Hwf.
  pose (s := [("l", lF); ("r", rF); ("g", g); ("G'", G); ("G", D)] : subst string).
  (* recast the explicit conclusion as the "U subst" rule's t/e1/e2 under s,
     so `eq_term_subst` applies without inverting the substitution. *)
  change (eq_term ott []
    ({{s #"ty" "G" (#"info" #"rel" (#"next" "l")) }} [/s/])
    ({{e #"ty_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "l")) (#"U" "G'" "r" "l") }} [/s/])
    ({{e #"U" "G" "r" "l" }} [/s/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "U subst").
    apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s.
    repeat first
      [ simple apply wf_subst_nil | simple eapply wf_subst_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | eassumption ].
  - eapply rule_in_ctx_wf with (name := "U subst").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* `act_code rF lF g G D F` pushes the domain code `F : exp G (U rF lF)`      *)
(* along an object substitution `g : sub D G`, landing a code in env `D`.     *)
(* The naive result type `exp D _ (ty_subst g (U rF lF G))` is converted to   *)
(* `exp D _ (U rF lF D)` via the "U subst" computation rule, so downstream    *)
(* `extc`/`cod_at` see a bare `U`-code. *)
Lemma act_code_wf rF lF g G D F
  (HG : wf_term ott [] G (scon "env" []))
  (HD : wf_term ott [] D (scon "env" []))
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (scon "sub" [G; D]))
  (HF : wf_term ott [] F (scon "exp" [oU rF lF G; code_info lF; G]))
  : wf_term ott [] (act_code rF lF g G D F)
                   (scon "exp" [oU rF lF D; code_info lF; D]).
Proof.
  pose proof ott_wf as Hwf.
  unfold act_code, oexp_subst.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + ott_wf_args.
  - (* the naive `exp_subst` result type `exp D _ (ty_subst g (U rF lF G))`
       converts to the target `exp D _ (U rF lF D)`: reduce the substitution
       into the result sort, split by congruence, and the only non-reflexive
       component is the "U subst" computation rule. *)
    cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: first
      [ solve [ eapply eq_term_refl; ott_wf_args ]
      | solve [ match goal with
                | |- eq_term ?l ?c ?t ?lhs ?rhs =>
                    let t2 := eval vm_compute in t in
                    let lhs2 := eval vm_compute in lhs in
                    change (eq_term l c t2 lhs2 rhs)
                end;
                apply U_subst_eq; assumption ] ].
Qed.

(* `extc rF lF g G D F` = `ext D (El (act_code …))` is the env `D` extended by
   the (decoded) pushed domain code; the Kripke codomain lives over it.  It is
   well-formed as an env: the `ext` rule needs `El (act_code …) : ty D (info rF
   (iota lF))`, whose code argument is exactly `act_code_wf`'s conclusion.  Same
   checker-free driver as `act_code_wf`, extended with an `act_code_wf` leaf. *)
Lemma extc_wf rF lF g G D F
  (HG : wf_term ott [] G (scon "env" []))
  (HD : wf_term ott [] D (scon "env" []))
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (scon "sub" [G; D]))
  (HF : wf_term ott [] F (scon "exp" [oU rF lF G; code_info lF; G]))
  : wf_term ott [] (extc rF lF g G D F) (scon "env" []).
Proof.
  pose proof ott_wf as Hwf.
  unfold extc, oext.
  repeat first
    [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
    | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
    | (apply act_code_wf; eassumption)
    | eassumption
    | (eapply Elab.wf_term_by';
         [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
Qed.

(* ====================================================================== *)
(* THE under'-LIFT CLUSTER (NEXT_SESSION UPDATE-w).                         *)
(*                                                                        *)
(* The Kripke codomain code (`act_cod`/`cod_at`) is pushed along the       *)
(* under'-lift `ounder = snoc (cmp g wkn) hd : sub (extc ..) (ext G (El F))`.*)
(* Typing `ounder` is the genuinely fiddly obligation: its `hd` leaf lands  *)
(* at `ty_subst wkn (El (act_code))`, but the `snoc` rule demands it at     *)
(* `ty_subst (cmp g wkn) (El F)`.  Those agree only via the OTT             *)
(* "ty_subst_cmp" + "El subst" computation rules (`ty_subst_g0_El_eq`).     *)
(* This section discharges that chain, then `ounder_wf`.                    *)
(* ====================================================================== *)

(* Sort abbreviations: `s_sub tgt src` is the rule's `sub tgt src` (tgt the
   target env, src the source env); `s_exp G i A` / `s_ty G i` likewise. *)
Definition s_env : osort := scon "env" [].
Definition s_sub (tgt src : tm) : osort := scon "sub" [src; tgt].
Definition s_exp (G i A : tm) : osort := scon "exp" [A; i; G].
Definition s_ty (G i : tm) : osort := scon "ty" [i; G].

(* `El (act_code ..) : ty D (term_info rF lF)` — the decoded pushed domain
   code, used as the extension type of `extc` and the `A` of `wkn`/`hd`. *)
Lemma El_act_code_ty rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : wf_term ott [] (oEl rF lF D (act_code rF lF g G D F))
                   (s_ty D (term_info rF lF)).
Proof.
  pose proof ott_wf as Hwf.
  unfold oEl, s_ty, term_info.
  eapply Elab.wf_term_by'.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - cbn [Model.wf_term core_model].
    repeat first
      [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | (apply act_code_wf; eassumption)
      | eassumption
      | (eapply Elab.wf_term_by';
           [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - left; compute; reflexivity.
Qed.

(* `wkn : sub (extc ..) D` — weaken out of the domain-extended env. *)
Lemma wkn_extc_wf rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : wf_term ott []
      (owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
      (s_sub (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D) D).
Proof.
  pose proof ott_wf as Hwf.
  unfold owkn, oext, s_sub.
  eapply Elab.wf_term_by'.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - cbn [Model.wf_term core_model].
    repeat first
      [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | (apply El_act_code_ty; eassumption)
      | eassumption
      | (eapply Elab.wf_term_by';
           [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - left; compute; reflexivity.
Qed.

(* `g0 = cmp g wkn : sub (extc ..) G` — the under'-lift's underlying subst. *)
Lemma cmp_g0_wf rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : wf_term ott []
      (ocmp g (owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
            G D (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D))
      (s_sub (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D) G).
Proof.
  pose proof ott_wf as Hwf.
  unfold ocmp, oext, s_sub.
  eapply Elab.wf_term_by'.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - cbn [Model.wf_term core_model].
    repeat first
      [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | (apply wkn_extc_wf; eassumption)
      | (apply El_act_code_ty; eassumption)
      | eassumption
      | (eapply Elab.wf_term_by';
           [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - left; compute; reflexivity.
Qed.

(* The "El subst" computation rule under an explicit variable substitution:
   `ty_subst g (El F) = El (exp_subst g F) = El (act_code ..)`.  Same
   checker-free packaging as `U_subst_eq` (the `wf_subst` side-goal is closed
   from the variable hypotheses, not the computational wf checker). *)
Lemma El_subst_eq rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : eq_term ott [] (s_ty D (term_info rF lF))
      (con "ty_subst" [oEl rF lF G F; term_info rF lF; g; G; D])
      (oEl rF lF D (act_code rF lF g G D F)).
Proof.
  pose proof ott_wf as Hwf.
  pose (s := [("e", F); ("l", lF); ("r", rF); ("g", g); ("G'", G); ("G", D)] : subst string).
  change (eq_term ott []
    ({{s #"ty" "G" (#"info" "r" (#"iota" "l")) }} [/s/])
    ({{e #"ty_subst" "G" "G'" "g" (#"info" "r" (#"iota" "l")) (#"El" "G'" "r" "l" "e") }} [/s/])
    ({{e #"El" "G" "r" "l" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "l")) (#"U" "G'" "r" "l") "e") }} [/s/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "El subst").
    apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s.
    repeat first
      [ simple apply wf_subst_nil | simple eapply wf_subst_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | eassumption ].
  - eapply rule_in_ctx_wf with (name := "El subst").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* The checker-free "hand-build a wf_term/wf_subst/wf_args over open OTT terms"
   driver, extended with the cluster's already-typed builders as leaves. *)
Ltac ott_build :=
  repeat first
    [ simple apply wf_subst_nil | simple eapply wf_subst_cons
    | simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
    | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
    | (apply act_code_wf; eassumption)
    | (apply El_act_code_ty; eassumption)
    | (apply wkn_extc_wf; eassumption)
    | (apply cmp_g0_wf; eassumption)
    | eassumption
    | (eapply Elab.wf_term_by';
         [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].

(* THE CRUX: the under'-lift's `hd` leaf type-mismatch resolves to this single
   convertibility.  `ty_subst (cmp g wkn) (El F) = ty_subst wkn (El (act_code))`
   via "ty_subst_cmp" (split the composite subst) then "El subst" (push g into
   the code) under a `ty_subst wkn` congruence (`term_con_congruence`). *)
Lemma ty_subst_g0_El_eq rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : eq_term ott []
      (s_ty (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D) (term_info rF lF))
      (con "ty_subst"
         [oEl rF lF G F; term_info rF lF;
          ocmp g (owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
               G D (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D);
          G; oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D])
      (con "ty_subst"
         [oEl rF lF D (act_code rF lF g G D F); term_info rF lF;
          owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D;
          D; oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D]).
Proof.
  pose proof ott_wf as Hwf.
  eapply eq_term_trans with
    (e12 := con "ty_subst"
       [con "ty_subst" [oEl rF lF G F; term_info rF lF; g; G; D];
        term_info rF lF;
        owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D;
        D; oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D]).
  - eapply eq_term_sym.
    pose (s := [("A", oEl rF lF G F); ("i", term_info rF lF); ("g", g);
                ("f", owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D);
                ("G3", G); ("G2", D);
                ("G1", oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)] : subst string).
    change (eq_term ott []
      ({{s #"ty" "G1" "i" }} [/s/])
      ({{e #"ty_subst" "G1" "G2" "f" "i" (#"ty_subst" "G2" "G3" "g" "i" "A") }} [/s/])
      ({{e #"ty_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "i" "A" }} [/s/])).
    eapply eq_term_subst.
    + eapply eq_term_by with (name := "ty_subst_cmp").
      apply named_list_lookup_err_in; compute; reflexivity.
    + apply eq_subst_refl. unfold s. ott_build.
    + eapply rule_in_ctx_wf with (name := "ty_subst_cmp").
      * exact Hwf.
      * apply named_list_lookup_err_in; compute; reflexivity.
      * compute; reflexivity.
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right; compute; reflexivity.
    + exact Hwf.
    + do 5 (simple eapply eq_args_cons;
            [ | try (apply El_subst_eq; eassumption);
                try (eapply eq_term_refl; ott_build) ]);
      apply eq_args_nil.
Qed.

(* `hd : exp (extc ..) (term_info rF lF) (ty_subst (cmp g wkn) (El F))` — the
   `snoc` rule's `v` leaf for `ounder`, i.e. `hd` converted (via the crux above)
   from its native `ty_subst wkn (El (act_code))` type to the `cmp`-form `snoc`
   demands. *)
Lemma hd_extc_wf rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : wf_term ott []
      (ohd (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
      (s_exp (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
             (term_info rF lF)
             (con "ty_subst"
                [oEl rF lF G F; term_info rF lF;
                 ocmp g (owkn (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
                      G D (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D);
                 G; oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D])).
Proof.
  pose proof ott_wf as Hwf.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + ott_build.
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    unfold s_exp.
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: first
      [ solve [ eapply eq_term_refl; ott_build ]
      | solve [ eapply eq_term_sym; apply ty_subst_g0_El_eq; assumption ]
      | solve [ apply ty_subst_g0_El_eq; assumption ] ].
Qed.

(* `ounder rF lF g G D F : sub (extc ..) (ext G (El F))` — the under'-lift of
   `g` over the domain binder, well-typed.  This is the fiddliest builder
   typing; it composes `cmp_g0_wf` (the `snoc`'s subst) with `hd_extc_wf` (the
   converted `hd` leaf). *)
Lemma ounder_wf rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : wf_term ott [] (ounder rF lF g G D F)
      (s_sub (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
             (oext (oEl rF lF G F) (term_info rF lF) G)).
Proof.
  pose proof ott_wf as Hwf.
  unfold ounder, dom_info, s_sub.
  eapply Elab.wf_term_by'.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - cbn [Model.wf_term core_model].
    repeat first
      [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | (apply hd_extc_wf; eassumption)
      | (apply cmp_g0_wf; eassumption)
      | (apply El_act_code_ty; eassumption)
      | (apply act_code_wf; eassumption)
      | eassumption
      | (eapply Elab.wf_term_by';
           [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - left; compute; reflexivity.
Qed.

(* `act_cod rF lF lG g G D F C : exp (extc ..) (code_info lG) (U ! lG (extc ..))`
   — the codomain code `C` pushed along the under'-lift `ounder`, landing as a
   code over the extended target env `extc`.  Structurally `act_code_wf` over
   `ounder` instead of `g`: `exp_subst` then a "U subst" conversion, whose only
   non-reflexive component reuses `U_subst_eq` instantiated at `ounder`. *)
Lemma act_cod_wf rF lF lG g G D F C
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  : wf_term ott [] (act_cod rF lF lG g G D F C)
      (s_exp (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
             (code_info lG)
             (oU orel lG (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D))).
Proof.
  pose proof ott_wf as Hwf.
  unfold act_cod, dom_info, extc, oexp_subst, s_exp.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply ounder_wf; eassumption)
        | (apply El_act_code_ty; eassumption)
        | (apply act_code_wf; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    change (eq_term ott []
      (s_ty (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D) (code_info lG))
      (con "ty_subst"
         [oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G); code_info lG;
          ounder rF lF g G D F;
          oext (oEl rF lF G F) (term_info rF lF) G;
          oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D])
      (oU orel lG (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D))).
    apply U_subst_eq;
      first [ (apply ounder_wf; eassumption) | eassumption | ott_build ].
Qed.

(* The "ty_subst_id" computation rule on the pushed domain code, under an
   explicit substitution: `ty_subst (id D) (El (act_code)) = El (act_code)`.
   Needed to type the `snoc a id` instantiation substitution `snoc_a`. *)
Lemma ty_subst_id_El_eq rF lF g G D F
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : eq_term ott [] (s_ty D (term_info rF lF))
      (con "ty_subst" [oEl rF lF D (act_code rF lF g G D F); term_info rF lF; oid D; D; D])
      (oEl rF lF D (act_code rF lF g G D F)).
Proof.
  pose proof ott_wf as Hwf.
  pose (s := [("A", oEl rF lF D (act_code rF lF g G D F)); ("i", term_info rF lF); ("G", D)] : subst string).
  change (eq_term ott []
    ({{s #"ty" "G" "i" }} [/s/])
    ({{e #"ty_subst" "G" "G" (#"id" "G") "i" "A" }} [/s/])
    ({{e "A" }} [/s/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "ty_subst_id").
    apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s. ott_build.
  - eapply rule_in_ctx_wf with (name := "ty_subst_id").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* `snoc_a = snoc a id : sub D (extc ..)` — the substitution that instantiates
   the domain binder at the argument `a`.  Its `v`-leaf is `a`, which lands at
   `El (act_code)` but `snoc` demands `ty_subst (id D) (El (act_code))`; the two
   agree via `ty_subst_id_El_eq`. *)
Lemma snoc_a_wf rF lF g G D F a
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  : wf_term ott []
      (osnoc a (oid D) (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D D)
      (s_sub D (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)).
Proof.
  pose proof ott_wf as Hwf.
  unfold osnoc, oext, s_sub.
  eapply Elab.wf_term_by'.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - cbn [Model.wf_term core_model].
    simple eapply wf_args_cons2.
    + ott_build.
    + eapply wf_term_conv.
      * unfold s_exp in Ha. apply Ha.
      * cbn [with_names_from sort_subst apply_subst substable_sort
             Substable.apply_subst0 term_substable].
        sort_cong.
        all: cbn [Model.eq_term core_model].
        all: try solve [ eapply eq_term_refl; ott_build ].
        eapply eq_term_sym; apply ty_subst_id_El_eq; assumption.
    + ott_build.
  - left; compute; reflexivity.
Qed.

(* `cod_at rF lF lG g G D F C a : exp D (code_info lG) (U ! lG D)` — the pushed
   codomain code `act_cod` instantiated at the argument `a` (i.e. pulled back
   along `snoc_a` to env `D`).  `act_cod_wf`-over-`snoc_a` plus a "U subst"
   conversion (`U_subst_eq` at `snoc_a`/`extc`/`D`). *)
Lemma cod_at_wf rF lF lG g G D F C a
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  : wf_term ott [] (cod_at rF lF lG g G D F C a)
      (s_exp D (code_info lG) (oU orel lG D)).
Proof.
  pose proof ott_wf as Hwf.
  unfold cod_at, dom_info, extc, oexp_subst, s_exp.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply act_cod_wf; eassumption)
        | (apply snoc_a_wf; eassumption)
        | (apply El_act_code_ty; eassumption)
        | (apply act_code_wf; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    change (eq_term ott []
      (s_ty D (code_info lG))
      (con "ty_subst"
         [oU orel lG (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D); code_info lG;
          osnoc a (oid D) (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D D;
          oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D;
          D])
      (oU orel lG D)).
    apply U_subst_eq;
      first [ (apply snoc_a_wf; eassumption) | eassumption | ott_build ].
Qed.

(* The "Pi_rel subst" computation rule under an explicit substitution:
   `exp_subst g (Pi_rel rF lF lG F C G) = Pi_rel rF lF lG (act_code)(act_cod) D`.
   This is the OTT rule whose codomain push is exactly the `ounder` under'-lift;
   the (large) RHS reuses `act_code`/`act_cod` definitionally.  Packaged
   checker-free like `U_subst_eq`. *)
Lemma Pi_rel_subst_eq rF lF lG g G D F C
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  : eq_term ott [] (s_exp D (code_info lG) (oU orel lG D))
      (con "exp_subst" [oPi_rel rF lF lG F C G; oU orel lG G; code_info lG; g; G; D])
      (oPi_rel rF lF lG (act_code rF lF g G D F) (act_cod rF lF lG g G D F C) D).
Proof.
  pose proof ott_wf as Hwf.
  pose (s := [("B", C); ("F", F); ("lG", lG); ("lF", lF); ("rF", rF);
              ("g", g); ("G'", G); ("G", D)] : subst string).
  change (eq_term ott []
    ({{s #"exp" "G" (#"info" #"rel" (#"next" "lG")) (#"U" "G" #"rel" "lG") }} [/s/])
    ({{e #"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lG")) (#"U" "G'" #"rel" "lG")
            (#"Pi_rel" "G'" "rF" "lF" "lG" "F" "B") }} [/s/])
    ({{e #"Pi_rel" "G" "rF" "lF" "lG"
            (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lF")) (#"U" "G'" "rF" "lF") "F")
            (#"exp_subst"
               (#"ext" "G" (#"info" "rF" (#"iota" "lF"))
                  (#"El" "G" "rF" "lF" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lF")) (#"U" "G'" "rF" "lF") "F")))
               (#"ext" "G'" (#"info" "rF" (#"iota" "lF")) (#"El" "G'" "rF" "lF" "F"))
               (#"snoc"
                  (#"ext" "G" (#"info" "rF" (#"iota" "lF"))
                     (#"El" "G" "rF" "lF" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lF")) (#"U" "G'" "rF" "lF") "F")))
                  "G'" (#"info" "rF" (#"iota" "lF")) (#"El" "G'" "rF" "lF" "F")
                  (#"cmp"
                     (#"ext" "G" (#"info" "rF" (#"iota" "lF"))
                        (#"El" "G" "rF" "lF" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lF")) (#"U" "G'" "rF" "lF") "F")))
                     "G" "G'"
                     (#"wkn" "G" (#"info" "rF" (#"iota" "lF"))
                        (#"El" "G" "rF" "lF" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lF")) (#"U" "G'" "rF" "lF") "F")))
                     "g")
                  (#"hd" "G" (#"info" "rF" (#"iota" "lF"))
                     (#"El" "G" "rF" "lF" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "lF")) (#"U" "G'" "rF" "lF") "F"))))
               (#"info" #"rel" (#"next" "lG"))
               (#"U" (#"ext" "G'" (#"info" "rF" (#"iota" "lF")) (#"El" "G'" "rF" "lF" "F")) #"rel" "lG")
               "B") }} [/s/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "Pi_rel subst").
    apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s. ott_build.
  - eapply rule_in_ctx_wf with (name := "Pi_rel subst").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* `ty_subst g (El (Pi_rel .. G)) = El (Pi_rel .. D)` — push a Π-code under an
   object substitution.  Composes "El subst" (outer) with `Pi_rel_subst_eq`
   (under an `El` congruence).  This is the conversion `act_member` needs. *)
Lemma El_Pi_subst_eq rF lF lG g G D F C
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  : eq_term ott [] (s_ty D (term_info orel lG))
      (con "ty_subst" [oEl orel lG G (oPi_rel rF lF lG F C G); term_info orel lG; g; G; D])
      (oEl orel lG D (oPi_rel rF lF lG (act_code rF lF g G D F) (act_cod rF lF lG g G D F C) D)).
Proof.
  pose proof ott_wf as Hwf.
  eapply eq_term_trans with
    (e12 := oEl orel lG D
              (con "exp_subst" [oPi_rel rF lF lG F C G; oU orel lG G; code_info lG; g; G; D])).
  - pose (s := [("e", oPi_rel rF lF lG F C G); ("l", lG); ("r", orel);
                ("g", g); ("G'", G); ("G", D)] : subst string).
    change (eq_term ott []
      ({{s #"ty" "G" (#"info" "r" (#"iota" "l")) }} [/s/])
      ({{e #"ty_subst" "G" "G'" "g" (#"info" "r" (#"iota" "l")) (#"El" "G'" "r" "l" "e") }} [/s/])
      ({{e #"El" "G" "r" "l" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "l")) (#"U" "G'" "r" "l") "e") }} [/s/])).
    eapply eq_term_subst.
    + eapply eq_term_by with (name := "El subst").
      apply named_list_lookup_err_in; compute; reflexivity.
    + apply eq_subst_refl. unfold s. ott_build.
    + eapply rule_in_ctx_wf with (name := "El subst").
      * exact Hwf.
      * apply named_list_lookup_err_in; compute; reflexivity.
      * compute; reflexivity.
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right; compute; reflexivity.
    + exact Hwf.
    + do 4 (simple eapply eq_args_cons;
            [ | try (apply Pi_rel_subst_eq; eassumption);
                try (eapply eq_term_refl; ott_build) ]);
      apply eq_args_nil.
Qed.

(* `act_member rF lF lG g G D F C f : exp D (term_info ! lG) (El (Pi_rel .. D))`
   — the function member `f` pushed along `g`, then re-typed (via El_Pi_subst_eq)
   from its naive `ty_subst g (El (Pi_rel .. G))` type to the `act_code`/`act_cod`
   Π over `D` that `mapp`'s `app_rel` consumes. *)
Lemma act_member_wf rF lF lG g G D F C f
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hf : wf_term ott [] f (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  : wf_term ott [] (act_member rF lF lG g G D F C f)
      (s_exp D (term_info orel lG)
             (oEl orel lG D (oPi_rel rF lF lG (act_code rF lF g G D F) (act_cod rF lF lG g G D F C) D))).
Proof.
  pose proof ott_wf as Hwf.
  unfold act_member, oexp_subst, s_exp.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply El_act_code_ty; eassumption)
        | (apply act_code_wf; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    change (eq_term ott []
      (s_ty D (term_info orel lG))
      (con "ty_subst" [oEl orel lG G (oPi_rel rF lF lG F C G); term_info orel lG; g; G; D])
      (oEl orel lG D (oPi_rel rF lF lG (act_code rF lF g G D F) (act_cod rF lF lG g G D F C) D))).
    apply El_Pi_subst_eq; assumption.
Qed.

(* `ty_subst (snoc a id) (El (act_cod)) = El (cod_at)` — instantiating the pushed
   codomain code's decode at the argument is exactly the `cod_at` build (an "El
   subst" with `g := snoc_a`). *)
Lemma El_act_cod_subst_eq rF lF lG g G D F C a
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  : eq_term ott [] (s_ty D (term_info orel lG))
      (con "ty_subst"
         [oEl orel lG (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
              (act_cod rF lF lG g G D F C);
          term_info orel lG;
          osnoc a (oid D) (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D D;
          oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D;
          D])
      (oEl orel lG D (cod_at rF lF lG g G D F C a)).
Proof.
  pose proof ott_wf as Hwf.
  pose (s := [("e", act_cod rF lF lG g G D F C); ("l", lG); ("r", orel);
              ("g", osnoc a (oid D) (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D D);
              ("G'", oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D);
              ("G", D)] : subst string).
  change (eq_term ott []
    ({{s #"ty" "G" (#"info" "r" (#"iota" "l")) }} [/s/])
    ({{e #"ty_subst" "G" "G'" "g" (#"info" "r" (#"iota" "l")) (#"El" "G'" "r" "l" "e") }} [/s/])
    ({{e #"El" "G" "r" "l" (#"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "l")) (#"U" "G'" "r" "l") "e") }} [/s/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "El subst").
    apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s.
    repeat first
      [ simple apply wf_subst_nil | simple eapply wf_subst_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | (apply act_cod_wf; eassumption)
      | (apply snoc_a_wf; eassumption)
      | eassumption
      | ott_build ].
  - eapply rule_in_ctx_wf with (name := "El subst").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* `mapp rF lF lG g G D F C f a : exp D (term_info ! lG) (El (cod_at .. a))` — the
   pushed member `act_member` applied to the argument `a` via `app_rel`, re-typed
   (El_act_cod_subst_eq) to the instantiated codomain type the RedAtPi member
   relation consumes.  THE LAST under'-lift builder; closes the cluster. *)
Lemma mapp_wf rF lF lG g G D F C f a
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hf : wf_term ott [] f (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  : wf_term ott [] (mapp rF lF lG g G D F C f a)
      (s_exp D (term_info orel lG) (oEl orel lG D (cod_at rF lF lG g G D F C a))).
Proof.
  pose proof ott_wf as Hwf.
  unfold mapp, oapp_rel, s_exp.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply act_member_wf; eassumption)
        | (apply act_cod_wf; eassumption)
        | (apply act_code_wf; eassumption)
        | (apply El_act_code_ty; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    change (eq_term ott []
      (s_ty D (term_info orel lG))
      (con "ty_subst"
         [oEl orel lG (oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D)
              (act_cod rF lF lG g G D F C);
          term_info orel lG;
          osnoc a (oid D) (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D D;
          oext (oEl rF lF D (act_code rF lF g G D F)) (term_info rF lF) D;
          D])
      (oEl orel lG D (cod_at rF lF lG g G D F C a))).
    apply El_act_cod_subst_eq; assumption.
Qed.

(* Member-application congruence in the ARGUMENT: applying the (fixed) pushed
   member `f` to declaratively equal arguments `a ~ a'` yields equal member
   applications `mapp .. f a ~ mapp .. f a'`, at the codomain type instantiated
   at the RHS argument `a'`.  This is the app_rel congruence the reflect-at-Pi
   case consumes: a neutral function maps a related pair of domain members to a
   related pair of codomain members (then `mapp_neutral` puts both reducts in
   the codomain's neutral fiber).  Reuses `mapp_wf`'s eq_args/conversion
   machinery; only the head `a`-position is non-reflexive (`Heqa`), the rest
   close by `eq_args_refl` over the shared builder `wf_args`. *)
Lemma mapp_cong rF lF lG g G D F C f a a'
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hf : wf_term ott [] f (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  (Ha' : wf_term ott [] a' (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  (Heqa : eq_term ott [] (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))) a a')
  : eq_term ott [] (s_exp D (term_info orel lG) (oEl orel lG D (cod_at rF lF lG g G D F C a')))
      (mapp rF lF lG g G D F C f a) (mapp rF lF lG g G D F C f a').
Proof.
  pose proof ott_wf as Hwf.
  unfold mapp, oapp_rel, s_exp.
  eapply eq_term_conv.
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right. cbn [with_names_from]. reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons.
      2: exact Heqa.
      eapply eq_args_refl.
      1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
      repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply act_member_wf; eassumption)
        | (apply act_cod_wf; eassumption)
        | (apply act_code_wf; eassumption)
        | (apply El_act_code_ty; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    apply El_act_cod_subst_eq; assumption.
Qed.

(* The reflect-at-Pi bridge: a NEUTRAL function `n` (well typed at the Π type)
   sends a declaratively-equal pair of domain arguments `a ~ a'` to a pair of
   member applications that are `ne_eq` at the instantiated codomain type --
   i.e. both are neutral (`mapp_neutral`, since `n` is) and declaratively equal
   (`mapp_cong`).  This is exactly the input the recursive (codomain) reflect
   call consumes, so it is the key combinator for discharging the eta crux's
   member-relation obligation. *)
Lemma mapp_ne_eq rF lF lG g G D F C n a a'
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hn : wf_term ott [] n (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Hnn : neutral ott_pa n)
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  (Ha' : wf_term ott [] a' (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  (Heqa : eq_term ott [] (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))) a a')
  : ne_eq string ott ott_pa
      (s_exp D (term_info orel lG) (oEl orel lG D (cod_at rF lF lG g G D F C a')))
      (mapp rF lF lG g G D F C n a) (mapp rF lF lG g G D F C n a').
Proof.
  unfold ne_eq; repeat split.
  - apply mapp_neutral; exact Hnn.
  - apply mapp_neutral; exact Hnn.
  - apply mapp_cong; eassumption.
Qed.

(* Member-push congruence in the FUNCTION: declaratively equal Π members `f ~ f'`
   push to equal pushed members `act_member f ~ act_member f'` (an `exp_subst`
   congruence; conversion `El_Pi_subst_eq`).  With `mapp_cong` (argument side)
   this gives the GENERAL two-sided application congruence by transitivity:
   `mapp f a ~ mapp f a' ~ mapp f' a'` -- needed for reflecting a pair of
   DISTINCT neutral functions (the PER side, where the two neutrals differ). *)
Lemma act_member_cong rF lF lG g G D F C f f'
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hf : wf_term ott [] f (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Hf' : wf_term ott [] f' (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Heqf : eq_term ott [] (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))) f f')
  : eq_term ott []
      (s_exp D (term_info orel lG)
             (oEl orel lG D (oPi_rel rF lF lG (act_code rF lF g G D F) (act_cod rF lF lG g G D F C) D)))
      (act_member rF lF lG g G D F C f) (act_member rF lF lG g G D F C f').
Proof.
  pose proof ott_wf as Hwf.
  unfold act_member, oexp_subst, s_exp.
  eapply eq_term_conv.
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right. cbn [with_names_from]. reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons.
      2: exact Heqf.
      eapply eq_args_refl.
      1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
      repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply El_act_code_ty; eassumption)
        | (apply act_code_wf; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    apply El_Pi_subst_eq; assumption.
Qed.

(* App congruence in the FUNCTION position (argument fixed): `f ~ f'` ⇒
   `mapp f a ~ mapp f' a` at `El(cod_at C a)`.  The function-position arg is the
   pushed member, handled by `act_member_cong`; the head `a` is reflexive.
   Composing with `mapp_cong` (argument side) by `eq_term_trans` gives the full
   two-sided application congruence
   `mapp f a ~ mapp f a' ~ mapp f' a'`. *)
Lemma mapp_cong_fun rF lF lG g G D F C f f' a
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hf : wf_term ott [] f (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Hf' : wf_term ott [] f' (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Heqf : eq_term ott [] (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))) f f')
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  : eq_term ott [] (s_exp D (term_info orel lG) (oEl orel lG D (cod_at rF lF lG g G D F C a)))
      (mapp rF lF lG g G D F C f a) (mapp rF lF lG g G D F C f' a).
Proof.
  pose proof ott_wf as Hwf.
  unfold mapp, oapp_rel, s_exp.
  eapply eq_term_conv.
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right. cbn [with_names_from]. reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons.
      2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons.
      2:{ apply act_member_cong; eassumption. }
      eapply eq_args_refl.
      1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
      repeat first
        [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
        | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (apply act_cod_wf; eassumption)
        | (apply act_code_wf; eassumption)
        | (apply El_act_code_ty; eassumption)
        | eassumption
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
  - cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: try solve [ eapply eq_term_refl; ott_build ].
    apply El_act_cod_subst_eq; assumption.
Qed.

(* The GENERAL two-sided reflect-at-Pi bridge: a pair of DISTINCT neutral
   functions `na ~ nb` sends a related argument pair `a ~ a'` to an `ne_eq`
   pair of member applications `mapp na a ~ mapp nb a'`, at the instantiated
   codomain type.  Both reducts are neutral (`mapp_neutral`); the equation is
   `mapp na a ~ mapp na a' ~ mapp nb a'` by `mapp_cong` then `mapp_cong_fun`.
   This is the input the codomain reflect call consumes on the PER (eq_term)
   side, where the two neutrals genuinely differ; `mapp_ne_eq` is the `na = nb`
   special case used by the fundamental lemma's reflexive reflect leaves. *)
Lemma mapp_ne_eq2 rF lF lG g G D F C na nb a a'
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Hna : wf_term ott [] na (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Hnb : wf_term ott [] nb (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Heqf : eq_term ott [] (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))) na nb)
  (Hnna : neutral ott_pa na)
  (Hnnb : neutral ott_pa nb)
  (Ha : wf_term ott [] a (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  (Ha' : wf_term ott [] a' (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))))
  (Heqa : eq_term ott [] (s_exp D (term_info rF lF) (oEl rF lF D (act_code rF lF g G D F))) a a')
  : ne_eq string ott ott_pa
      (s_exp D (term_info orel lG) (oEl orel lG D (cod_at rF lF lG g G D F C a')))
      (mapp rF lF lG g G D F C na a) (mapp rF lF lG g G D F C nb a').
Proof.
  unfold ne_eq; repeat split.
  - apply mapp_neutral; exact Hnna.
  - apply mapp_neutral; exact Hnnb.
  - eapply eq_term_trans.
    + apply mapp_cong; eassumption.
    + apply mapp_cong_fun; eassumption.
Qed.

(* ====================================================================== *)
(* LR ESCAPE (soundness) at the CONCRETE language `l := ott`.               *)
(*                                                                        *)
(* The abstract-`l` neutral-fiber escape `RedNe_sound` lives in            *)
(* LogicalRelation.v.  The Nat-fiber escape recurses through `rnm_suc`,    *)
(* so its sub-member typing must be re-derived by subject reduction        *)
(* (`reds_wf`) + inversion of the CONCRETE `suc` rule -- hence it lands     *)
(* here, where `ott` is in scope.                                          *)
(* ====================================================================== *)

(* Invert a well-typed `suc`: the argument is a Nat element in the same env,
   and the env itself is well-formed.  The `suc` rule is pinned out of the
   abstract `In` via `all_fresh` uniqueness against the computed lookup. *)
Lemma suc_inv G x
  : wf_term ott [] (osuc G x) (nat_sort G) ->
    wf_term ott [] x (nat_sort G) /\ wf_term ott [] G (scon "env" []).
Proof.
  intro Hwf.
  apply WfCutElim.invert_wf_term_con in Hwf as (c' & cargs & t' & Hin & Hwfargs & Hsort).
  assert (Hall : all_fresh ott) by exact (wf_lang_ext_all_fresh ott_wf).
  assert (Hin2 : In ("suc",
     term_rule
       [("n", {{s #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" "G" #"rel" #"L0" (#"Nat" "G")) }});
        ("G", {{s #"env"}})]
       ["n"]
       {{s #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" "G" #"rel" #"L0" (#"Nat" "G")) }}) ott)
    by (apply named_list_lookup_err_in; vm_compute; reflexivity).
  pose proof (in_all_fresh_same _ _ _ _ Hall Hin Hin2) as Heq; safe_invert Heq.
  safe_invert Hwfargs.
  safe_invert H5.
  split; assumption.
Qed.

(* Nat-fiber escape: a reducible Nat pair, given both members well typed,
   escapes to declarative `eq_term`.  zero/ne are leaf (reds_sound + the
   ne-fiber conversion); the suc case recurses via the IH after re-typing the
   predecessors with `suc_inv`, then re-assembles by `suc` congruence. *)
Lemma RedNatMem_sound G a b
  : RedNatMem ott G a b ->
    wf_term ott [] a (nat_sort G) ->
    wf_term ott [] b (nat_sort G) ->
    eq_term ott [] (nat_sort G) a b.
Proof.
  intros HM; induction HM; intros Hwfa Hwfb.
  - (* zero *)
    pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ Hwfa r) as H1.
    pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ Hwfb r0) as H2.
    eapply eq_term_trans; [ exact H1 | eapply eq_term_sym; exact H2 ].
  - (* suc *)
    pose proof (@reds_wf string _ _ _ ott ott_wf ott_pa _ _ _ Hwfa r) as Hwa.
    pose proof (@reds_wf string _ _ _ ott ott_wf ott_pa _ _ _ Hwfb r0) as Hwb.
    destruct (suc_inv _ _ Hwa) as [Hwa' HwG].
    destruct (suc_inv _ _ Hwb) as [Hwb' _].
    pose proof (IHHM Hwa' Hwb') as Hab'.
    pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ Hwfa r) as Hra.
    pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ Hwfb r0) as Hrb.
    eapply eq_term_trans; [ exact Hra | ].
    eapply eq_term_trans; [ | eapply eq_term_sym; exact Hrb ].
    (* eq_term (osuc G a') (osuc G b') by `suc` congruence on a' ~ b' *)
    assert (HinS : In ("suc",
       term_rule
         [("n", {{s #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" "G" #"rel" #"L0" (#"Nat" "G")) }});
          ("G", {{s #"env"}})]
         ["n"]
         {{s #"exp" "G" (#"info" #"rel" (#"iota" #"L0")) (#"El" "G" #"rel" #"L0" (#"Nat" "G")) }}) ott)
      by (apply named_list_lookup_err_in; vm_compute; reflexivity).
    unfold osuc.
    eapply term_con_congruence; [ exact HinS | | exact ott_wf | ].
    + right. vm_compute. reflexivity.
    + constructor.
      * constructor; [ constructor | eapply eq_term_refl; exact HwG ].
      * exact Hab'.
  - (* ne *)
    pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ Hwfa r) as H1.
    pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ Hwfb r0) as H2.
    eapply eq_term_trans; [ exact H1 | ].
    eapply eq_term_trans; [ | eapply eq_term_sym; exact H2 ].
    exact (proj2 (proj2 n)).
Qed.

(* ====================================================================== *)
(* TYPE-LEVEL ESCAPE, LEAF CASES (the non-recursive constructors of         *)
(* `RedTy_tot`).  Reducibility of a type-code pair `A`/`B`, given both codes *)
(* well typed at a common code-sort `S`, escapes to declarative `eq_term S A *)
(* B`.  These are the nat/empty/neutral cases of the eventual total          *)
(* `RedTy_sound`; the `rtt_pi` case is the Kripke/eta crux (it needs the     *)
(* fundamental lemma's reflect adequacy at the domain to instantiate the     *)
(* codomain at a fresh variable) and is NOT a leaf, so the total statement   *)
(* must wait on Π.  Each leaf is `reds_sound` on both sides + transitivity;  *)
(* the neutral case additionally bridges the `ne_eq` sort `t` to the typing  *)
(* sort `S` via `term_sorts_eq` (the reduct `na` is well typed at both).     *)
(* ====================================================================== *)

(* The empty Pyrosome context is well formed under `ott` (used by the
   presupposition / sort-uniqueness lemmas below). *)
Lemma wf_ctx_ott_nil : wf_ctx (Model := core_model ott) [].
Proof. constructor. Qed.

(* Nat code: A,B both weak-head reduce to `Nat G`, so each is `eq_term`-equal
   to `Nat G` at whatever code-sort it is typed at. *)
Lemma RedTy_Nat_sound G A B S
  : RNat ott G A -> RNat ott G B ->
    wf_term ott [] A S -> wf_term ott [] B S ->
    eq_term ott [] S A B.
Proof.
  intros Ha Hb HwfA HwfB.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HwfA Ha) as H1.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HwfB Hb) as H2.
  eapply eq_term_trans; [ exact H1 | eapply eq_term_sym; exact H2 ].
Qed.

(* Empty code: identical to Nat, with `Empty G` the common reduct. *)
Lemma RedTy_Empty_sound G A B S
  : REmpty ott G A -> REmpty ott G B ->
    wf_term ott [] A S -> wf_term ott [] B S ->
    eq_term ott [] S A B.
Proof.
  intros Ha Hb HwfA HwfB.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HwfA Ha) as H1.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HwfB Hb) as H2.
  eapply eq_term_trans; [ exact H1 | eapply eq_term_sym; exact H2 ].
Qed.

(* Neutral code: like `RedNe_sound`, but the codes may be typed at a sort `S`
   DIFFERENT from the sort `t` carried by the `ne_eq` (the type-level `rtt_ne`
   carries an arbitrary `t`).  The two are bridged by `term_sorts_eq`: the
   common reduct `na` is well typed at `t` (presupposition of the `ne_eq`'s
   `eq_term`) and at `S` (subject reduction from `A : S`), hence `eq_sort t S`,
   so the neutral equation transports to `S` by `eq_term_conv`. *)
Lemma RedNe_sound_at (t S : osort) a b
  : RedNe ott t a b ->
    wf_term ott [] a S -> wf_term ott [] b S ->
    eq_term ott [] S a b.
Proof.
  intros [na nb ra rb h] HwfA HwfB.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HwfA ra) as H1.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HwfB rb) as H2.
  destruct h as (Hna & Hnb & Heq).
  pose proof (@reds_wf string _ _ _ ott ott_wf ott_pa _ _ _ HwfA ra) as HwfNaS.
  pose proof (eq_term_wf_l ott_wf wf_ctx_ott_nil Heq) as HnaT.
  pose proof (term_sorts_eq ott_wf wf_ctx_ott_nil HnaT HwfNaS) as Hsorts.
  pose proof (eq_term_conv Heq Hsorts) as HeqS.
  eapply eq_term_trans; [ exact H1 | ].
  eapply eq_term_trans; [ exact HeqS | eapply eq_term_sym; exact H2 ].
Qed.


(* ====================================================================== *)
(* Escape-at-Pi prerequisite: the id/var-collapse substitution identity.    *)
(* cmp (ounder wkn) (snoc hd (id extG)) = id  at sort sub extG extG          *)
(* (extG := ext G (El F)).  Feeds cod_at(wkn,hd) = C, the Pi-codomain        *)
(* instantiation at the bound variable used by escape-at-Pi.                *)
(* ====================================================================== *)
Lemma sub_collapse rF lF G F
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HD : wf_term ott [] (oext (oEl rF lF G F) (term_info rF lF) G) s_env)
  (Hwkn : wf_term ott [] (owkn (oEl rF lF G F) (term_info rF lF) G)
            (s_sub (oext (oEl rF lF G F) (term_info rF lF) G) G))
  (Hhd : wf_term ott [] (ohd (oEl rF lF G F) (term_info rF lF) G)
            (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (term_info rF lF)
               (oEl rF lF (oext (oEl rF lF G F) (term_info rF lF) G)
                  (act_code rF lF (owkn (oEl rF lF G F) (term_info rF lF) G)
                     G (oext (oEl rF lF G F) (term_info rF lF) G) F))))
  : let extG := oext (oEl rF lF G F) (term_info rF lF) G in
    let wkn  := owkn (oEl rF lF G F) (term_info rF lF) G in
    let hd   := ohd (oEl rF lF G F) (term_info rF lF) G in
    eq_term ott [] (s_sub extG extG)
      (ocmp (ounder rF lF wkn G extG F)
            (osnoc hd (oid extG)
               (oEl rF lF extG (act_code rF lF wkn G extG F))
               (term_info rF lF) extG extG)
            extG
            (oext (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG)
            extG)
      (oid extG).
Proof.
  pose proof ott_wf as Hwf.
  intros extG wkn hd. unfold ounder, act_code, dom_info.
  pose (ElaF := oEl rF lF extG (oexp_subst F (oU rF lF G) (code_info lF) wkn G extG)).
  pose (iF := term_info rF lF).
  pose (extc := oext ElaF iF extG).
  pose (wknD := owkn ElaF iF extG).
  pose (hdD := ohd ElaF iF extG).
  pose (g0 := ocmp wkn wknD G extG extc).
  pose (snoc_a := osnoc hd (oid extG) ElaF iF extG extG).
  (* ----- g-equality: cmp snoc_a g0 = wkn (cmp_assoc; wkn_snoc; id_left).
     VALIDATED interactively (axiom-free). ----- *)
  assert (Hgeq : eq_term ott [] (s_sub extG G) (ocmp g0 snoc_a G extc extG) wkn).
  { pose (sa := [("h", wkn); ("g", wknD); ("f", snoc_a); ("G4", G); ("G3", extG); ("G2", extc); ("G1", extG)] : subst string).
    eapply eq_term_trans with (e12 := ({{e #"cmp" "G1" "G3" "G4" (#"cmp" "G1" "G2" "G3" "f" "g") "h"}})[/sa/]).
    { change (eq_term ott []
        (({{s #"sub" "G1" "G4"}})[/sa/])
        (({{e #"cmp" "G1" "G2" "G4" "f" (#"cmp" "G2" "G3" "G4" "g" "h")}})[/sa/])
        (({{e #"cmp" "G1" "G3" "G4" (#"cmp" "G1" "G2" "G3" "f" "g") "h"}})[/sa/])).
      eapply eq_term_subst.
      - eapply eq_term_by with (name := "cmp_assoc"). apply named_list_lookup_err_in; compute; reflexivity.
      - apply eq_subst_refl. unfold sa.
        repeat first
          [ progress ott_build
          | (apply El_act_code_ty; eassumption)
          | (apply act_code_wf; eassumption)
          | (simple apply snoc_a_wf; eassumption)
          | eassumption
          | (eapply Elab.wf_term_by'; [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ])
          | (eapply wf_term_conv;
               [ exact Hhd
               | unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
                 try solve [ eapply eq_term_refl; ott_build ];
                 eapply eq_term_sym; apply ty_subst_id_El_eq; eassumption ]) ].
      - eapply rule_in_ctx_wf with (name := "cmp_assoc").
        + exact Hwf.
        + apply named_list_lookup_err_in; compute; reflexivity.
        + compute; reflexivity. }
    eapply eq_term_trans with (e12 := ocmp wkn (oid extG) G extG extG).
    - eapply term_con_congruence.
      + apply named_list_lookup_err_in; compute; reflexivity.
      + right. cbn [with_names_from]. reflexivity.
      + exact ott_wf.
      + cbn [with_names_from].
        eapply eq_args_cons.
        2:{ eapply eq_term_refl. eassumption. }
        eapply eq_args_cons.
        2:{ pose (sw := [("v", hd); ("A", oEl rF lF extG (act_code rF lF wkn G extG F)); ("i", iF); ("g", oid extG); ("G'", extG); ("G", extG)] : subst string).
            change (eq_term ott []
              (({{s #"sub" "G" "G'"}})[/sw/])
              (({{e #"cmp" "G" (#"ext" "G'" "i" "A") "G'" (#"snoc" "G" "G'" "i" "A" "g" "v") (#"wkn" "G'" "i" "A")}})[/sw/])
              (({{e "g"}})[/sw/])).
            eapply eq_term_subst.
            * eapply eq_term_by with (name := "wkn_snoc"). apply named_list_lookup_err_in; compute; reflexivity.
            * apply eq_subst_refl. unfold sw.
              repeat first
                [ progress ott_build | (apply El_act_code_ty; eassumption) | (apply act_code_wf; eassumption) | eassumption
                | (eapply wf_term_conv;
                     [ exact Hhd
                     | unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
                       try solve [ eapply eq_term_refl; ott_build ];
                       eapply eq_term_sym; apply ty_subst_id_El_eq; eassumption ]) ].
            * eapply rule_in_ctx_wf with (name := "wkn_snoc").
              -- exact Hwf.
              -- apply named_list_lookup_err_in; compute; reflexivity.
              -- compute; reflexivity. }
        eapply eq_args_refl.
        1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
        repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | eassumption ].
    - pose (sl := [("f", wkn); ("G'", G); ("G", extG)] : subst string).
      change (eq_term ott []
        (({{s #"sub" "G" "G'"}})[/sl/])
        (({{e #"cmp" "G" "G" "G'" (#"id" "G") "f"}})[/sl/])
        (({{e "f"}})[/sl/])).
      eapply eq_term_subst.
      + eapply eq_term_by with (name := "id_left"). apply named_list_lookup_err_in; compute; reflexivity.
      + apply eq_subst_refl. unfold sl. repeat first [ progress ott_build | eassumption ].
      + eapply rule_in_ctx_wf with (name := "id_left").
        * exact Hwf.
        * apply named_list_lookup_err_in; compute; reflexivity.
        * compute; reflexivity. }
  (* ----- annotation equality: ty_subst g0 (El F) = ty_subst wknD (El act_code).
     Brings the cmp_snoc-produced exp_subst annotation to snoc_hd's form. ----- *)
  assert (annot_eq : eq_term ott [] (s_ty extc iF)
            (con "ty_subst" [oEl rF lF G F; iF; g0; G; extc])
            (con "ty_subst" [oEl rF lF extG (act_code rF lF wkn G extG F); iF; wknD; extG; extc])).
  { eapply eq_term_trans with (e12 := con "ty_subst" [con "ty_subst" [oEl rF lF G F; iF; wkn; G; extG]; iF; wknD; extG; extc]).
    - eapply eq_term_sym.
      pose (sc := [("A", oEl rF lF G F); ("i", iF); ("g", wkn); ("f", wknD); ("G3", G); ("G2", extG); ("G1", extc)] : subst string).
      change (eq_term ott []
        (({{s #"ty" "G1" "i"}})[/sc/])
        (({{e #"ty_subst" "G1" "G2" "f" "i" (#"ty_subst" "G2" "G3" "g" "i" "A")}})[/sc/])
        (({{e #"ty_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "i" "A"}})[/sc/])).
      eapply eq_term_subst.
      + eapply eq_term_by with (name := "ty_subst_cmp"). apply named_list_lookup_err_in; compute; reflexivity.
      + apply eq_subst_refl. unfold sc.
        repeat first
          [ progress ott_build | (apply El_act_code_ty; eassumption) | (apply act_code_wf; eassumption) | eassumption
          | (eapply Elab.wf_term_by'; [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ].
      + eapply rule_in_ctx_wf with (name := "ty_subst_cmp").
        * exact Hwf.
        * apply named_list_lookup_err_in; compute; reflexivity.
        * compute; reflexivity.
    - eapply term_con_congruence.
      + apply named_list_lookup_err_in; compute; reflexivity.
      + right. cbn [with_names_from]. reflexivity.
      + exact ott_wf.
      + cbn [with_names_from].
        eapply eq_args_cons.
        2:{ apply El_subst_eq; eassumption. }
        eapply eq_args_refl.
        1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
        repeat first
          [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
          | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
          | progress ott_build | (apply El_act_code_ty; eassumption) | (apply act_code_wf; eassumption) | eassumption
          | (eapply Elab.wf_term_by'; [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ]) ]. }
  (* ----- main chain: cmp ounder snoc_a = id ----- *)
  pose (s := [("v", hdD); ("A", oEl rF lF G F); ("i", iF); ("g", g0); ("f", snoc_a); ("G3", G); ("G2", extc); ("G1", extG)] : subst string).
  (* Step 1 (cmp_snoc) -- VALIDATED. *)
  eapply eq_term_trans with (e12 := ({{e #"snoc" "G1" "G3" "i" "A" (#"cmp" "G1" "G2" "G3" "f" "g") (#"exp_subst" "G1" "G2" "f" "i" (#"ty_subst" "G2" "G3" "g" "i" "A") "v")}}) [/s/]).
  { change (eq_term ott []
      (({{s #"sub" "G1" (#"ext" "G3" "i" "A")}})[/s/])
      (({{e #"cmp" "G1" "G2" (#"ext" "G3" "i" "A") "f" (#"snoc" "G2" "G3" "i" "A" "g" "v")}})[/s/])
      (({{e #"snoc" "G1" "G3" "i" "A" (#"cmp" "G1" "G2" "G3" "f" "g") (#"exp_subst" "G1" "G2" "f" "i" (#"ty_subst" "G2" "G3" "g" "i" "A") "v")}})[/s/])).
    eapply eq_term_subst.
    - eapply eq_term_by with (name := "cmp_snoc"). apply named_list_lookup_err_in; compute; reflexivity.
    - apply eq_subst_refl. unfold s.
      repeat first
        [ progress ott_build
        | (apply hd_extc_wf; eassumption)
        | (apply cmp_g0_wf; eassumption)
        | (simple apply snoc_a_wf; eassumption)
        | (apply El_act_code_ty; eassumption)
        | (apply act_code_wf; eassumption)
        | eassumption
        | (eapply wf_term_conv;
             [ exact Hhd
             | unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
               try solve [ eapply eq_term_refl; ott_build ];
               eapply eq_term_sym; apply ty_subst_id_El_eq; eassumption ]) ].
    - eapply rule_in_ctx_wf with (name := "cmp_snoc").
      + exact Hwf.
      + apply named_list_lookup_err_in; compute; reflexivity.
      + compute; reflexivity. }
  (* Step 2: snoc (cmp snoc_a g0) (exp_subst snoc_a hdD) = snoc wkn hd = id.
     congruence (g-position = Hgeq; v-position = snoc_hd, TODO) then snoc_wkn_hd. *)
  eapply eq_term_trans with (e12 := osnoc hd wkn (oEl rF lF G F) iF G extG).
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right. cbn [with_names_from]. reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons.
      2:{ (* v-position: exp_subst snoc_a hdD = hd.  Proved REVERSED (hd = e1) so the
             congruence's s2 = e1 carries the natural annotation ANNOT1. *)
          eapply eq_term_sym.
          eapply eq_term_trans with (e12 := oexp_subst hdD (con "ty_subst" [oEl rF lF extG (act_code rF lF wkn G extG F); iF; wknD; extG; extc]) iF snoc_a extc extG).
          - (* hd = e1' : sym snoc_hd, conv SORT_id -> SORT_wkn *)
            eapply eq_term_sym.
            eapply eq_term_conv with (t := scon "exp" [con "ty_subst" [oEl rF lF extG (act_code rF lF wkn G extG F); iF; oid extG; extG; extG]; iF; extG]).
            + pose (s3 := [("v", hd); ("A", oEl rF lF extG (act_code rF lF wkn G extG F)); ("i", iF); ("g", oid extG); ("G'", extG); ("G", extG)] : subst string).
              change (eq_term ott []
                (({{s #"exp" "G" "i" (#"ty_subst" "G" "G'" "g" "i" "A")}})[/s3/])
                (({{e #"exp_subst" "G" (#"ext" "G'" "i" "A") (#"snoc" "G" "G'" "i" "A" "g" "v") "i" (#"ty_subst" (#"ext" "G'" "i" "A") "G'" (#"wkn" "G'" "i" "A") "i" "A") (#"hd" "G'" "i" "A")}})[/s3/])
                (({{e "v"}})[/s3/])).
              eapply eq_term_subst.
              * eapply eq_term_by with (name := "snoc_hd"). apply named_list_lookup_err_in; compute; reflexivity.
              * apply eq_subst_refl. unfold s3.
                repeat first
                  [ progress ott_build | (apply act_code_wf; eassumption) | (apply El_act_code_ty; eassumption) | eassumption
                  | (eapply wf_term_conv; [ exact Hhd | unfold s_exp; sort_cong; cbn [Model.eq_term core_model]; try solve [ eapply eq_term_refl; ott_build ]; eapply eq_term_sym; apply ty_subst_id_El_eq; eassumption ]) ].
              * eapply rule_in_ctx_wf with (name := "snoc_hd").
                -- exact Hwf.
                -- apply named_list_lookup_err_in; compute; reflexivity.
                -- compute; reflexivity.
            + unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
              try solve [ eapply eq_term_refl; ott_build ];
              eapply eq_term_trans; [ apply ty_subst_id_El_eq; eassumption | eapply eq_term_sym; apply El_subst_eq; eassumption ].
          - (* e1' = e1 : annotation congruence (s2 = e1, ANNOT1), conv SORT_out -> SORT_wkn via ty_subst_cmp + Hgeq *)
            eapply eq_term_conv.
            + eapply term_con_congruence.
              * apply named_list_lookup_err_in; compute; reflexivity.
              * right. cbn [with_names_from]. reflexivity.
              * exact ott_wf.
              * cbn [with_names_from].
                eapply eq_args_cons.
                2:{ eapply eq_term_refl. apply hd_extc_wf; eassumption. }
                eapply eq_args_cons.
                2:{ eapply eq_term_sym; exact annot_eq. }
                eapply eq_args_refl.
                1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
                repeat first
                  [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons
                  | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
                  | (simple apply snoc_a_wf; eassumption) | (apply El_act_code_ty; eassumption) | (apply act_code_wf; eassumption)
                  | progress ott_build | eassumption
                  | (eapply wf_term_conv; [ exact Hhd | unfold s_exp; sort_cong; cbn [Model.eq_term core_model]; try solve [ eapply eq_term_refl; ott_build ]; eapply eq_term_sym; apply ty_subst_id_El_eq; eassumption ]) ].
            + unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
              try solve [ eapply eq_term_refl; ott_build ];
              eapply eq_term_trans with (e12 := con "ty_subst" [oEl rF lF G F; iF; ocmp g0 snoc_a G extc extG; G; extG]).
              * pose (sk := [("A", oEl rF lF G F); ("i", iF); ("g", g0); ("f", snoc_a); ("G3", G); ("G2", extc); ("G1", extG)] : subst string).
                change (eq_term ott []
                  (({{s #"ty" "G1" "i"}})[/sk/])
                  (({{e #"ty_subst" "G1" "G2" "f" "i" (#"ty_subst" "G2" "G3" "g" "i" "A")}})[/sk/])
                  (({{e #"ty_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "i" "A"}})[/sk/])).
                eapply eq_term_subst.
                -- eapply eq_term_by with (name := "ty_subst_cmp"). apply named_list_lookup_err_in; compute; reflexivity.
                -- apply eq_subst_refl. unfold sk.
                   repeat first
                     [ progress ott_build | (apply cmp_g0_wf; eassumption) | (simple apply snoc_a_wf; eassumption) | (apply El_act_code_ty; eassumption) | (apply act_code_wf; eassumption) | eassumption
                     | (eapply wf_term_conv; [ exact Hhd | unfold s_exp; sort_cong; cbn [Model.eq_term core_model]; try solve [ eapply eq_term_refl; ott_build ]; eapply eq_term_sym; apply ty_subst_id_El_eq; eassumption ]) ].
                -- eapply rule_in_ctx_wf with (name := "ty_subst_cmp").
                   ++ exact Hwf.
                   ++ apply named_list_lookup_err_in; compute; reflexivity.
                   ++ compute; reflexivity.
              * eapply term_con_congruence.
                -- apply named_list_lookup_err_in; compute; reflexivity.
                -- right. cbn [with_names_from]. reflexivity.
                -- exact ott_wf.
                -- cbn [with_names_from].
                   eapply eq_args_cons.
                   2:{ eapply eq_term_refl. eapply Elab.wf_term_by';
                         [ apply named_list_lookup_err_in; compute; reflexivity
                         | cbn [Model.wf_term core_model]; repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress compute_wf_subjects | eassumption ]
                         | left; compute; reflexivity ]. }
                   eapply eq_args_cons.
                   2:{ eapply eq_term_refl. ott_build. }
                   eapply eq_args_cons.
                   2:{ exact Hgeq. }
                   eapply eq_args_refl.
                   1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
                   repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ]. }
      eapply eq_args_cons.
      2:{ exact Hgeq. }
      eapply eq_args_refl.
      1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
      repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
        | (eapply Elab.wf_term_by'; [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ])
        | progress ott_build | eassumption ].
  - (* snoc wkn hd = id (snoc_wkn_hd) -- VALIDATED. *)
    pose (s2 := [("A", oEl rF lF G F); ("i", iF); ("G", G)] : subst string).
    change (eq_term ott []
      (({{s #"sub" (#"ext" "G" "i" "A") (#"ext" "G" "i" "A")}})[/s2/])
      (({{e #"snoc" (#"ext" "G" "i" "A") "G" "i" "A" (#"wkn" "G" "i" "A") (#"hd" "G" "i" "A")}})[/s2/])
      (({{e #"id" (#"ext" "G" "i" "A")}})[/s2/])).
    eapply eq_term_subst.
    + eapply eq_term_by with (name := "snoc_wkn_hd"). apply named_list_lookup_err_in; compute; reflexivity.
    + apply eq_subst_refl. unfold s2.
      repeat first
        [ progress ott_build
        | (eapply Elab.wf_term_by';
             [ apply named_list_lookup_err_in; compute; reflexivity | | left; compute; reflexivity ])
        | eassumption ].
    + eapply rule_in_ctx_wf with (name := "snoc_wkn_hd").
      * exact Hwf.
      * apply named_list_lookup_err_in; compute; reflexivity.
      * compute; reflexivity.
Qed.

(* ====================================================================== *)
(* cod_at_wkn_hd_eq: the id/var-collapse for the CODOMAIN code.  At the    *)
(* escape-at-Pi instantiation (g := wkn, D := ext G (El F), a := hd) the   *)
(* pushed-and-instantiated codomain collapses back to C:                   *)
(*   cod_at(wkn, hd) = exp_subst snoc_a (exp_subst ounder C) = C           *)
(* via exp_subst_cmp (compose the two pushes), sub_collapse (the composite *)
(* sub is the identity), then exp_subst_id.                                *)
(* ====================================================================== *)
Lemma cod_at_wkn_hd_eq rF lF lG G F C
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  : let extG := oext (oEl rF lF G F) (term_info rF lF) G in
    let wkn  := owkn (oEl rF lF G F) (term_info rF lF) G in
    let hd   := ohd (oEl rF lF G F) (term_info rF lF) G in
    eq_term ott [] (s_exp extG (code_info lG) (oU orel lG extG))
      (cod_at rF lF lG wkn G extG F C hd)
      C.
Proof.
  pose proof ott_wf as Hwf.
  intros extG wkn hd.
  (* ----- wf prerequisites for the bound-variable instantiation ----- *)
  assert (HElF : wf_term ott [] (oEl rF lF G F) (s_ty G (term_info rF lF))).
  { unfold s_ty, oEl, term_info. ott_build. }
  assert (HD : wf_term ott [] extG s_env).
  { unfold extG. ott_build. }
  assert (Hwkn : wf_term ott [] wkn (s_sub extG G)).
  { unfold wkn, extG. ott_build. }
  assert (Hhd : wf_term ott [] hd
            (s_exp extG (term_info rF lF) (oEl rF lF extG (act_code rF lF wkn G extG F)))).
  { unfold hd. eapply wf_term_conv.
    - eapply Elab.wf_term_by';
        [ apply named_list_lookup_err_in; compute; reflexivity
        | cbn [Model.wf_term core_model]; unfold extG; ott_build
        | left; compute; reflexivity ].
    - unfold s_exp, extG; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ];
      apply El_subst_eq; eassumption. }
  unfold cod_at, act_cod, dom_info, extc.
  pose proof (sub_collapse rF lF G F HG HrF HlF HF HD Hwkn Hhd) as Hsc; cbv zeta in Hsc.
  (* ----- the substitution-calculus wf and "U subst" leaves ----- *)
  assert (Horel : wf_term ott [] orel (scon "relevance" [])).
  { unfold orel. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  assert (Hounder : wf_term ott [] (ounder rF lF wkn G extG F)
            (s_sub (oext (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG) extG)).
  { apply ounder_wf; eassumption. }
  assert (HextD : wf_term ott []
            (oext (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG) s_env).
  { unfold s_env. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  assert (Hsnoc_a : wf_term ott []
            (osnoc hd (oid extG) (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG extG)
            (s_sub extG (oext (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG))).
  { apply (snoc_a_wf rF lF wkn G extG F hd); eassumption. }
  unfold dom_info.
  pose proof (U_subst_eq orel lG (ounder rF lF wkn G extG F) extG
                (oext (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG)
                HD HextD Horel HlG Hounder) as HUcW.
  pose proof (U_subst_eq orel lG
                (osnoc hd (oid extG) (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG extG)
                (oext (oEl rF lF extG (act_code rF lF wkn G extG F)) (term_info rF lF) extG) extG
                HextD HD Horel HlG Hsnoc_a) as HUcS.
  (* ----- fold the big subterms for readability ----- *)
  set (iF := term_info rF lF) in *.
  set (iG := code_info lG) in *.
  set (ElaF := oEl rF lF extG (act_code rF lF wkn G extG F)) in *.
  set (extD := oext ElaF iF extG) in *.
  set (ounderW := ounder rF lF wkn G extG F) in *.
  set (snoc_a := osnoc hd (oid extG) ElaF iF extG extG) in *.
  set (Uext := oU orel lG extG) in *.
  set (UextD := oU orel lG extD) in *.
  fold extG; fold Uext.
  (* ----- more "U subst" leaves (at the composite sub and the identity) ----- *)
  pose proof (eq_term_wf_l Hwf wf_ctx_ott_nil Hsc) as Hcmpwf.
  assert (Hidwf : wf_term ott [] (oid extG) (s_sub extG extG)).
  { unfold oid, s_sub. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  pose proof (U_subst_eq orel lG (ocmp ounderW snoc_a extG extD extG) extG extG
                HD HD Horel HlG Hcmpwf) as HUcCmp.
  pose proof (U_subst_eq orel lG (oid extG) extG extG HD HD Horel HlG Hidwf) as HUid.
  fold iG in HUcCmp, HUid; fold Uext in HUcCmp, HUid.
  (* the doubly-nested type-level collapse, for link1's sort obligation. *)
  assert (Hty2 : eq_term ott [] (s_ty extG iG)
    (con "ty_subst" [con "ty_subst" [Uext; iG; ounderW; extG; extD]; iG; snoc_a; extD; extG]) Uext).
  { eapply eq_term_trans with (e12 := con "ty_subst" [UextD; iG; snoc_a; extD; extG]).
    - eapply term_con_congruence.
      + apply named_list_lookup_err_in; compute; reflexivity.
      + right; cbn [with_names_from]; reflexivity.
      + exact ott_wf.
      + cbn [with_names_from].
        eapply eq_args_cons.
        2:{ exact HUcW. }
        eapply eq_args_refl.
        1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
        repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ].
    - exact HUcS. }
  (* wf of the inner pushed codomain (act_cod), at its natural ty_subst-annotated sort. *)
  pose proof (act_cod_wf rF lF lG wkn G extG F C HG HD HrF HlF HlG Hwkn HF HC) as Hactcod.
  cbv zeta in Hactcod. unfold act_cod, dom_info, extc in Hactcod.
  fold iF iG extG ElaF extD ounderW Uext in Hactcod.
  unfold dom_info in Hactcod. fold iF in Hactcod. fold extD in Hactcod. fold UextD in Hactcod.
  assert (Hactcod_nat : wf_term ott [] (oexp_subst C Uext iG ounderW extG extD)
            (s_exp extD iG (con "ty_subst" [Uext; iG; ounderW; extG; extD]))).
  { eapply wf_term_conv; [ exact Hactcod | unfold s_exp; sort_cong; cbn [Model.eq_term core_model]; try solve [ eapply eq_term_refl; ott_build ]; eapply eq_term_sym; exact HUcW ]. }
  (* =================== the collapse chain =================== *)
  (* LHS = exp_subst snoc_a (exp_subst ounder C) at sort (exp extG iG Uext). *)
  (* link1: bridge the OUTER annotation UextD ~> ty_subst ounder Uext. *)
  eapply eq_term_trans with (e12 := oexp_subst (oexp_subst C Uext iG ounderW extG extD)
                                      (con "ty_subst" [Uext; iG; ounderW; extG; extD]) iG snoc_a extD extG).
  { eapply term_con_congruence.
    - apply named_list_lookup_err_in; compute; reflexivity.
    - left. cbn [with_names_from].
      unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ];
      eapply eq_term_sym; exact Hty2.
    - exact ott_wf.
    - cbn [with_names_from].
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. exact Hactcod_nat. }
      eapply eq_args_cons.
      2:{ eapply eq_term_sym; exact HUcW. }
      eapply eq_args_refl.
      1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
      repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ]. }
  (* link2: exp_subst_cmp -- compose the two pushes into one. *)
  eapply eq_term_trans with (e12 := oexp_subst C Uext iG (ocmp ounderW snoc_a extG extD extG) extG extG).
  { eapply eq_term_conv with (t := s_exp extG iG (con "ty_subst" [Uext; iG; ocmp ounderW snoc_a extG extD extG; extG; extG])).
    - pose (s := [("v", C); ("A", Uext); ("i", iG); ("g", ounderW); ("f", snoc_a); ("G3", extG); ("G2", extD); ("G1", extG)] : subst string).
      change (eq_term ott []
        (({{s #"exp" "G1" "i" (#"ty_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "i" "A")}})[/s/])
        (({{e #"exp_subst" "G1" "G2" "f" "i" (#"ty_subst" "G2" "G3" "g" "i" "A") (#"exp_subst" "G2" "G3" "g" "i" "A" "v")}})[/s/])
        (({{e #"exp_subst" "G1" "G3" (#"cmp" "G1" "G2" "G3" "f" "g") "i" "A" "v"}})[/s/])).
      eapply eq_term_subst.
      + eapply eq_term_by with (name := "exp_subst_cmp"). apply named_list_lookup_err_in; compute; reflexivity.
      + apply eq_subst_refl. unfold s. ott_build.
      + eapply rule_in_ctx_wf with (name := "exp_subst_cmp").
        * exact Hwf.
        * apply named_list_lookup_err_in; compute; reflexivity.
        * compute; reflexivity.
    - unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ];
      exact HUcCmp. }
  (* link3: sub_collapse -- the composite sub is the identity. *)
  eapply eq_term_trans with (e12 := oexp_subst C Uext iG (oid extG) extG extG).
  { eapply term_con_congruence.
    - apply named_list_lookup_err_in; compute; reflexivity.
    - left. cbn [with_names_from].
      unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ];
      eapply eq_term_sym; exact HUid.
    - exact ott_wf.
    - cbn [with_names_from].
      eapply eq_args_cons. 2:{ eapply eq_term_refl; exact HC. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ exact Hsc. }
      eapply eq_args_refl.
      1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
      repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ]. }
  (* link4: exp_subst_id -- substituting the identity is a no-op. *)
  pose (s4 := [("v", C); ("A", Uext); ("i", iG); ("G", extG)] : subst string).
  change (eq_term ott []
    (({{s #"exp" "G" "i" "A"}})[/s4/])
    (({{e #"exp_subst" "G" "G" (#"id" "G") "i" "A" "v"}})[/s4/])
    (({{e "v"}})[/s4/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "exp_subst_id"). apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s4. ott_build.
  - eapply rule_in_ctx_wf with (name := "exp_subst_id").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* ====================================================================== *)
(* act_code_id_eq: the id-collapse for the DOMAIN code.  At the            *)
(* escape-at-Pi instantiation of DomRed at (D := G, g := id G) the pushed  *)
(* domain code collapses back to F:                                        *)
(*   act_code(id G) = exp_subst (id G) F = F                               *)
(* directly by exp_subst_id (a single push along the identity).  This is   *)
(* the domain analogue of cod_at_wkn_hd_eq, and feeds F ~ F' in the Pi     *)
(* type-escape congruence. *)
(* ====================================================================== *)
Lemma act_code_id_eq rF lF G F
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G))
      (act_code rF lF (oid G) G G F) F.
Proof.
  pose proof ott_wf as Hwf.
  unfold act_code.
  pose (s4 := [("v", F); ("A", oU rF lF G); ("i", code_info lF); ("G", G)] : subst string).
  change (eq_term ott []
    (({{s #"exp" "G" "i" "A"}})[/s4/])
    (({{e #"exp_subst" "G" "G" (#"id" "G") "i" "A" "v"}})[/s4/])
    (({{e "v"}})[/s4/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "exp_subst_id"). apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s4. ott_build.
  - eapply rule_in_ctx_wf with (name := "exp_subst_id").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* ====================================================================== *)
(* El_cong / ext_cong: congruence of code-decoding and env-extension.      *)
(* These reconcile the two codomain environments in the escape-at-Pi       *)
(* Pi_rel congruence: from F ~ F' we get El F ~ El F', hence               *)
(* ext G (El F) ~ ext G (El F') (as envs), so the codomain codes C, C'     *)
(* (which live over these distinct envs) can be compared. *)
(* ====================================================================== *)
Lemma El_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : eq_term ott [] (s_ty G (term_info rF lF)) (oEl rF lF G F) (oEl rF lF G F').
Proof.
  pose proof ott_wf as Hwf.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons.
    2:{ exact HFF'. }
    eapply eq_args_refl.
    1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
    repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ].
Qed.

Lemma ext_cong rF lF G A A'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HAA' : eq_term ott [] (s_ty G (term_info rF lF)) A A')
  : eq_term ott [] s_env (oext A (term_info rF lF) G) (oext A' (term_info rF lF) G).
Proof.
  pose proof ott_wf as Hwf.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons.
    2:{ exact HAA'. }
    eapply eq_args_refl.
    1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
    repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ].
Qed.

(* ====================================================================== *)
(* MACHINERY-CONGRUENCE LEAVES for cod_at_machinery_cong.  In the          *)
(* escape-at-Pi codomain IH the SECOND code is the MIXED instantiation     *)
(*   cod_at (machinery built over El F) F' C' (hd over El F)               *)
(* whose substitution machinery (wkn/hd/ext/act_code) is built from F but  *)
(* whose pushed code is F'/C'.  cod_at_wkn_hd_eq needs machinery AND code   *)
(* to be the SAME X, so it does not collapse this directly.  The fix is to  *)
(* SWAP the machinery F -> F' (legitimate because El F ~ El F'), then       *)
(* cod_at_wkn_hd_eq at F' collapses to C'.  These leaves are the per-former *)
(* congruences (driven by F ~ F') the swap is assembled from. *)
(* ====================================================================== *)

(* weakening is congruent in its decoded-code argument: El F ~ El F' =>     *)
(* wkn (El F) ~ wkn (El F').                                                *)
Lemma wkn_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : eq_term ott [] (s_sub (oext (oEl rF lF G F') (term_info rF lF) G) G)
      (owkn (oEl rF lF G F) (term_info rF lF) G)
      (owkn (oEl rF lF G F') (term_info rF lF) G).
Proof.
  pose proof ott_wf as Hwf.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons.
    2:{ exact HElFF'. }
    eapply eq_args_refl.
    1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
    repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ].
Qed.

(* the bound variable is congruent in its decoded-code argument.  Its       *)
(* natural sort is the WEAKENED domain (ty_subst wkn (El F')), not the      *)
(* El(act_code) form. *)
Lemma hd_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : eq_term ott []
      (s_exp (oext (oEl rF lF G F') (term_info rF lF) G) (term_info rF lF)
        (con "ty_subst" [oEl rF lF G F'; term_info rF lF;
            owkn (oEl rF lF G F') (term_info rF lF) G; G;
            oext (oEl rF lF G F') (term_info rF lF) G]))
      (ohd (oEl rF lF G F) (term_info rF lF) G)
      (ohd (oEl rF lF G F') (term_info rF lF) G).
Proof.
  pose proof ott_wf as Hwf.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons.
    2:{ exact HElFF'. }
    eapply eq_args_refl.
    1: apply (@ModelImpls.core_model_ok string _); [ typeclasses eauto | exact ott_wf ].
    repeat first [ simple apply wf_args_nil | simple eapply wf_args_cons2 | simple eapply wf_args_cons | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects | progress ott_build | eassumption ].
Qed.

(* act_code with the F-machinery (g := wkn over El F, target := ext G (El F)) *)
(* but pushing the OTHER code F' is congruent to act_code with the matching  *)
(* F'-machinery (lands at the clean U-code sort via "U subst"). *)
Lemma act_code_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    eq_term ott [] (s_exp extGF' (code_info lF) (oU rF lF extGF'))
      (act_code rF lF wknF G extGF F')
      (act_code rF lF wknF' G extGF' F').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  pose proof (wkn_cong rF lF G F F' HG HrF HlF HF HF' HFF') as HwknFF'.
  assert (HextGF' : wf_term ott [] extGF' s_env).
  { unfold extGF', iF. ott_build. }
  assert (HwknF'wf : wf_term ott [] wknF' (s_sub extGF' G)).
  { unfold wknF', extGF', iF. ott_build. }
  unfold act_code.
  eapply eq_term_conv with
    (t := s_exp extGF' (code_info lF)
            (con "ty_subst" [oU rF lF G; code_info lF; wknF'; G; extGF'])).
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right; cbn [with_names_from]; reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons. 2:{ eapply eq_term_refl; exact HF'. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ exact HwknFF'. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ exact HextGG'. }
      eapply eq_args_nil.
  - unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ].
    apply U_subst_eq; try eassumption.
Qed.

(* id is congruent in its env argument. *)
Lemma id_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    eq_term ott [] (s_sub extGF' extGF') (oid extGF) (oid extGF').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_nil.
Qed.

(* El of the pushed domain code (over the extended env) is congruent:        *)
(* swapping the F-machinery to F' (env extG and act_code both move). *)
Lemma ElaF_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    eq_term ott [] (s_ty extGF' (term_info rF lF))
      (oEl rF lF extGF (act_code rF lF wknF G extGF F'))
      (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')).
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  pose proof (act_code_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hac.
  cbv zeta in Hac.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ exact Hac. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_nil.
Qed.

(* the doubly-extended env extc is congruent under the F->F' machinery swap. *)
Lemma extc_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    eq_term ott [] s_env
      (extc rF lF wknF G extGF F')
      (extc rF lF wknF' G extGF' F').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  pose proof (ElaF_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hel.
  cbv zeta in Hel.
  unfold extc, dom_info.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ exact Hel. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_nil.
Qed.

(* U over the extc env is congruent (the U-code annotation of act_cod). *)
Lemma U_env_cong rF lF lG G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    eq_term ott [] (s_ty (extc rF lF wknF' G extGF' F') (code_info lG))
      (oU orel lG (extc rF lF wknF G extGF F'))
      (oU orel lG (extc rF lF wknF' G extGF' F')).
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF'.
  pose proof (extc_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hextc.
  cbv zeta in Hextc.
  assert (Horel : wf_term ott [] orel (scon "relevance" [])).
  { unfold orel. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ eapply eq_term_refl; eassumption. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; eassumption. }
    eapply eq_args_cons. 2:{ exact Hextc. }
    eapply eq_args_nil.
Qed.

(* weakening over the doubly-extended env (the under'-lift inner wkn). *)
Lemma wknD_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    let ElaF := oEl rF lF extGF (act_code rF lF wknF G extGF F') in
    let ElaF' := oEl rF lF extGF' (act_code rF lF wknF' G extGF' F') in
    eq_term ott [] (s_sub (oext ElaF' iF extGF') extGF')
      (owkn ElaF iF extGF) (owkn ElaF' iF extGF').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF' ElaF ElaF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  pose proof (ElaF_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hel.
  cbv zeta in Hel.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ exact Hel. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_nil.
Qed.

(* the bound variable over the doubly-extended env (the under'-lift hd). *)
Lemma hdD_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    let ElaF := oEl rF lF extGF (act_code rF lF wknF G extGF F') in
    let ElaF' := oEl rF lF extGF' (act_code rF lF wknF' G extGF' F') in
    eq_term ott []
      (s_exp (oext ElaF' iF extGF') iF
        (con "ty_subst" [ElaF'; iF; owkn ElaF' iF extGF'; extGF'; oext ElaF' iF extGF']))
      (ohd ElaF iF extGF) (ohd ElaF' iF extGF').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF' ElaF ElaF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  pose proof (ElaF_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hel.
  cbv zeta in Hel.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ exact Hel. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_nil.
Qed.

(* the cmp inside ounder's g-component (g0 = cmp g wkn) is congruent. *)
Lemma cmp_g0_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    let ElaF := oEl rF lF extGF (act_code rF lF wknF G extGF F') in
    let ElaF' := oEl rF lF extGF' (act_code rF lF wknF' G extGF' F') in
    eq_term ott [] (s_sub (oext ElaF' iF extGF') G)
      (ocmp wknF (owkn ElaF iF extGF) G extGF (oext ElaF iF extGF))
      (ocmp wknF' (owkn ElaF' iF extGF') G extGF' (oext ElaF' iF extGF')).
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF' ElaF ElaF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  pose proof (wkn_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hwkn.
  pose proof (wknD_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as HwknD.
  cbv zeta in HwknD.
  pose proof (extc_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hextc.
  cbv zeta in Hextc. unfold extc, dom_info in Hextc.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ exact Hwkn. }
    eapply eq_args_cons. 2:{ exact HwknD. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_cons. 2:{ exact Hextc. }
    eapply eq_args_nil.
Qed.

(* the under'-lift ounder is congruent under the F->F' machinery swap.  Its    *)
(* v-leaf (hdD) lands at the wkn-form sort but snoc demands the cmp(g0)-form,   *)
(* bridged by ty_subst_g0_El_eq (THE under'-lift crux). *)
Lemma ounder_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    let ElaF' := oEl rF lF extGF' (act_code rF lF wknF' G extGF' F') in
    eq_term ott [] (s_sub (oext ElaF' iF extGF') extGF')
      (ounder rF lF wknF G extGF F')
      (ounder rF lF wknF' G extGF' F').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF' ElaF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  assert (HextGF' : wf_term ott [] extGF' s_env).
  { unfold extGF', iF. ott_build. }
  assert (HwknF'wf : wf_term ott [] wknF' (s_sub extGF' G)).
  { unfold wknF', extGF', iF. ott_build. }
  pose proof (hdD_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hhd. cbv zeta in Hhd.
  pose proof (cmp_g0_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hg0. cbv zeta in Hg0.
  pose proof (extc_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hextc.
  cbv zeta in Hextc. unfold extc, dom_info in Hextc.
  pose proof (ty_subst_g0_El_eq rF lF wknF' G extGF' F' HG HextGF' HrF HlF HwknF'wf HF') as Hcrux.
  unfold ounder, dom_info. cbv zeta.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons.
    2:{ eapply eq_term_conv; [ exact Hhd | ].
        unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
        try solve [ eapply eq_term_refl; ott_build ].
        eapply eq_term_sym. exact Hcrux. }
    eapply eq_args_cons. 2:{ exact Hg0. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact Hextc. }
    eapply eq_args_nil.
Qed.

(* snoc_a (the snoc a id that instantiates the binder at the argument) is       *)
(* congruent.  Its v-leaf (the SIMPLE bound var hd over El F) lands at the El   *)
(* (act_code) sort but snoc demands ty_subst id (El act_code); bridged by       *)
(* El_subst_eq then ty_subst_id_El_eq. *)
Lemma snoc_a_mach_cong rF lF G F F'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    let ElaF := oEl rF lF extGF (act_code rF lF wknF G extGF F') in
    let ElaF' := oEl rF lF extGF' (act_code rF lF wknF' G extGF' F') in
    eq_term ott [] (s_sub extGF' (oext ElaF' iF extGF'))
      (osnoc (ohd (oEl rF lF G F) iF G) (oid extGF) ElaF iF extGF extGF)
      (osnoc (ohd (oEl rF lF G F') iF G) (oid extGF') ElaF' iF extGF' extGF').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF' ElaF ElaF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  assert (HextGF' : wf_term ott [] extGF' s_env).
  { unfold extGF', iF. ott_build. }
  assert (HwknF'wf : wf_term ott [] wknF' (s_sub extGF' G)).
  { unfold wknF', extGF', iF. ott_build. }
  pose proof (hd_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hhd.
  pose proof (id_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hid. cbv zeta in Hid.
  pose proof (ElaF_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hel. cbv zeta in Hel.
  pose proof (El_subst_eq rF lF wknF' G extGF' F' HG HextGF' HrF HlF HwknF'wf HF') as Hels.
  pose proof (ty_subst_id_El_eq rF lF wknF' G extGF' F' HG HextGF' HrF HlF HwknF'wf HF') as Hidel.
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons.
    2:{ eapply eq_term_conv; [ exact Hhd | ].
        unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
        try solve [ eapply eq_term_refl; ott_build ].
        eapply eq_term_trans; [ exact Hels | eapply eq_term_sym; exact Hidel ]. }
    eapply eq_args_cons. 2:{ exact Hid. }
    eapply eq_args_cons. 2:{ exact Hel. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_cons. 2:{ exact HextGG'. }
    eapply eq_args_nil.
Qed.

(* U is congruent in its env argument (generic). *)
Lemma U_cong lG E E'
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HEE' : eq_term ott [] s_env E E')
  : eq_term ott [] (s_ty E' (code_info lG)) (oU orel lG E) (oU orel lG E').
Proof.
  pose proof ott_wf as Hwf.
  assert (Horel : wf_term ott [] orel (scon "relevance" [])).
  { unfold orel. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  eapply term_con_congruence.
  - apply named_list_lookup_err_in; compute; reflexivity.
  - right; cbn [with_names_from]; reflexivity.
  - exact ott_wf.
  - cbn [with_names_from].
    eapply eq_args_cons. 2:{ eapply eq_term_refl; eassumption. }
    eapply eq_args_cons. 2:{ eapply eq_term_refl; eassumption. }
    eapply eq_args_cons. 2:{ exact HEE'. }
    eapply eq_args_nil.
Qed.

(* the pushed codomain code act_cod is congruent under the F->F' machinery       *)
(* swap (code F'/C' fixed).  NB act_cod's home env extG is built from its         *)
(* F-ARGUMENT (= F'), so the A/G' positions are reflexive; only the under'-lift   *)
(* (g) and target env (extc) move.  Lands at the clean U-code sort via U_subst_eq.*)
Lemma act_cod_mach_cong rF lF lG G F F' C'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  (HC' : wf_term ott [] C'
           (s_exp (oext (oEl rF lF G F') (term_info rF lF) G) (code_info lG)
                  (oU orel lG (oext (oEl rF lF G F') (term_info rF lF) G))))
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    eq_term ott [] (s_exp (extc rF lF wknF' G extGF' F') (code_info lG)
                          (oU orel lG (extc rF lF wknF' G extGF' F')))
      (act_cod rF lF lG wknF G extGF F' C')
      (act_cod rF lF lG wknF' G extGF' F' C').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  assert (HextGF' : wf_term ott [] extGF' s_env).
  { unfold extGF', iF. ott_build. }
  assert (HwknF'wf : wf_term ott [] wknF' (s_sub extGF' G)).
  { unfold wknF', extGF', iF. ott_build. }
  pose proof (ounder_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hou. cbv zeta in Hou.
  pose proof (extc_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hextc.
  cbv zeta in Hextc. unfold extc, dom_info in Hextc.
  assert (Horel : wf_term ott [] orel (scon "relevance" [])).
  { unfold orel. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  pose proof (ounder_wf rF lF wknF' G extGF' F' HG HextGF' HrF HlF HwknF'wf HF') as Hou'.
  cbv zeta in Hou'.
  pose proof (extc_wf rF lF wknF' G extGF' F' HG HextGF' HrF HlF HwknF'wf HF') as HextD'.
  pose proof (U_subst_eq orel lG (ounder rF lF wknF' G extGF' F') extGF'
                (extc rF lF wknF' G extGF' F') HextGF' HextD' Horel HlG Hou') as HUs.
  unfold act_cod, dom_info, extc. cbv zeta.
  eapply eq_term_conv with
    (t := s_exp (oext (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')) iF extGF')
            (code_info lG)
            (con "ty_subst" [oU orel lG extGF'; code_info lG;
                ounder rF lF wknF' G extGF' F'; extGF';
                oext (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')) iF extGF'])).
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right; cbn [with_names_from]; reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons. 2:{ eapply eq_term_refl; exact HC'. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ exact Hou. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ unfold extc, dom_info in Hextc; exact Hextc. }
      eapply eq_args_nil.
  - unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ].
    unfold extc, dom_info in HUs; exact HUs.
Qed.

(* ====================================================================== *)
(* cod_at_machinery_cong -- THE machinery swap.  In the escape-at-Pi        *)
(* codomain IH the second code is the MIXED cod_at (machinery over El F but  *)
(* code F'/C', a = hd over El F); this swaps the WHOLE machinery to F',      *)
(* yielding the clean F'-form cod_at to which cod_at_wkn_hd_eq (at F')       *)
(* applies, collapsing it to C'.  Assembles act_cod_mach_cong (the v-leaf,  *)
(* itself the under'-lift swap), U_cong (the annotation), snoc_a_mach_cong   *)
(* (the binder-instantiation), extc_mach_cong/ext_cong (the envs); lands at  *)
(* the clean U-code sort via U_subst_eq at snoc_a'. *)
(* ====================================================================== *)
Lemma cod_at_machinery_cong rF lF lG G F F' C'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  (HC' : wf_term ott [] C'
           (s_exp (oext (oEl rF lF G F') (term_info rF lF) G) (code_info lG)
                  (oU orel lG (oext (oEl rF lF G F') (term_info rF lF) G))))
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let wknF' := owkn (oEl rF lF G F') iF G in
    let hdF := ohd (oEl rF lF G F) iF G in
    let hdF' := ohd (oEl rF lF G F') iF G in
    eq_term ott [] (s_exp extGF' (code_info lG) (oU orel lG extGF'))
      (cod_at rF lF lG wknF G extGF F' C' hdF)
      (cod_at rF lF lG wknF' G extGF' F' C' hdF').
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF wknF' hdF hdF'.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  assert (HextGF' : wf_term ott [] extGF' s_env).
  { unfold extGF', iF. ott_build. }
  assert (HwknF'wf : wf_term ott [] wknF' (s_sub extGF' G)).
  { unfold wknF', extGF', iF. ott_build. }
  pose proof (act_cod_mach_cong rF lF lG G F F' C' HG HrF HlF HlG HF HF' HFF' HC') as Hac.
  cbv zeta in Hac.
  pose proof (U_cong lG (extc rF lF wknF G extGF F') (extc rF lF wknF' G extGF' F') HlG
                (extc_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF')) as HU.
  cbv zeta in HU.
  pose proof (snoc_a_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hsnoc. cbv zeta in Hsnoc.
  pose proof (extc_mach_cong rF lF G F F' HG HrF HlF HF HF' HFF') as Hextc.
  cbv zeta in Hextc. unfold extc, dom_info in Hextc.
  assert (Horel : wf_term ott [] orel (scon "relevance" [])).
  { unfold orel. eapply Elab.wf_term_by';
      [ apply named_list_lookup_err_in; compute; reflexivity
      | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity ]. }
  (* hd_F' at the El(act_code) sort, for snoc_a' wf *)
  assert (Hhd' : wf_term ott [] hdF'
            (s_exp extGF' iF (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')))).
  { unfold hdF'. eapply wf_term_conv.
    - eapply Elab.wf_term_by';
        [ apply named_list_lookup_err_in; compute; reflexivity
        | cbn [Model.wf_term core_model]; unfold extGF', iF; ott_build
        | left; compute; reflexivity ].
    - unfold s_exp, extGF', iF; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ];
      apply El_subst_eq; eassumption. }
  pose proof (snoc_a_wf rF lF wknF' G extGF' F' hdF' HG HextGF' HrF HlF HwknF'wf HF' Hhd') as Hsa'.
  pose proof (extc_wf rF lF wknF' G extGF' F' HG HextGF' HrF HlF HwknF'wf HF') as HextD'.
  pose proof (U_subst_eq orel lG
                (osnoc hdF' (oid extGF') (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')) iF extGF' extGF')
                (extc rF lF wknF' G extGF' F') extGF' HextD' HextGF' Horel HlG Hsa') as HUs.
  unfold cod_at, dom_info, extc. cbv zeta.
  eapply eq_term_conv with
    (t := s_exp extGF' (code_info lG)
            (con "ty_subst"
               [oU orel lG (oext (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')) iF extGF');
                code_info lG;
                osnoc hdF' (oid extGF') (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')) iF extGF' extGF';
                oext (oEl rF lF extGF' (act_code rF lF wknF' G extGF' F')) iF extGF';
                extGF'])).
  - eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right; cbn [with_names_from]; reflexivity.
    + exact ott_wf.
    + cbn [with_names_from].
      eapply eq_args_cons. 2:{ unfold extc, dom_info in Hac; exact Hac. }
      eapply eq_args_cons. 2:{ unfold extc, dom_info in HU; exact HU. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ unfold dom_info in Hsnoc; exact Hsnoc. }
      eapply eq_args_cons. 2:{ unfold extc, dom_info in Hextc; exact Hextc. }
      eapply eq_args_cons. 2:{ exact HextGG'. }
      eapply eq_args_nil.
  - unfold s_exp; sort_cong; cbn [Model.eq_term core_model];
      try solve [ eapply eq_term_refl; ott_build ].
    unfold extc, dom_info in HUs; exact HUs.
Qed.

(* ====================================================================== *)
(* cod_collapse_both -- assemble C ~ C' from the codomain escape at the    *)
(* bound variable (HCodEsc) plus the domain code equality (HFF').  The     *)
(* escape gives cod_at(wknF,hdF,F,C) ~ cod_at(wknF,hdF,F',C') at the F-env *)
(* sort Sf; the LHS collapses to C (cod_at_wkn_hd_eq at F, env extGF), the *)
(* RHS is MIXED (F-machinery + F'/C' code) and collapses to C' via the     *)
(* machinery swap (cod_at_machinery_cong, F->F') THEN cod_at_wkn_hd_eq at  *)
(* F', both at the F'-env sort Sf'.  The two envs reconcile by             *)
(* ext_cong/El_cong + U_cong giving eq_sort Sf Sf'; the chain lands at the *)
(* Sf' sort demanded by the Pi_rel congruence's C-position.               *)
(* ====================================================================== *)
Lemma cod_collapse_both rF lF lG G F C F' C'
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (HC' : wf_term ott [] C' (s_exp (oext (oEl rF lF G F') (term_info rF lF) G) (code_info lG)
                                  (oU orel lG (oext (oEl rF lF G F') (term_info rF lF) G))))
  : let iF := term_info rF lF in
    let extGF := oext (oEl rF lF G F) iF G in
    let extGF' := oext (oEl rF lF G F') iF G in
    let wknF := owkn (oEl rF lF G F) iF G in
    let hdF := ohd (oEl rF lF G F) iF G in
    eq_term ott [] (s_exp extGF (code_info lG) (oU orel lG extGF))
      (cod_at rF lF lG wknF G extGF F C hdF)
      (cod_at rF lF lG wknF G extGF F' C' hdF) ->
    eq_term ott [] (s_exp extGF' (code_info lG) (oU orel lG extGF'))
      C C'.
Proof.
  pose proof ott_wf as Hwf.
  intros iF extGF extGF' wknF hdF HCodEsc.
  pose proof (cod_at_wkn_hd_eq rF lF lG G F C HG HrF HlF HlG HF HC) as HL. cbv zeta in HL.
  pose proof (cod_at_wkn_hd_eq rF lF lG G F' C' HG HrF HlF HlG HF' HC') as HR. cbv zeta in HR.
  pose proof (cod_at_machinery_cong rF lF lG G F F' C' HG HrF HlF HlG HF HF' HFF' HC') as HMach.
  cbv zeta in HMach.
  pose proof (El_cong rF lF G F F' HG HrF HlF HFF') as HElFF'.
  pose proof (ext_cong rF lF G (oEl rF lF G F) (oEl rF lF G F') HG HrF HlF HElFF') as HextGG'.
  assert (HSS' : eq_sort ott []
            (s_exp extGF (code_info lG) (oU orel lG extGF))
            (s_exp extGF' (code_info lG) (oU orel lG extGF'))).
  { unfold extGF, extGF', s_exp. sort_cong.
    - cbn [Model.eq_term core_model]. exact HextGG'.
    - cbn [Model.eq_term core_model]. eapply eq_term_refl. ott_build.
    - cbn [Model.eq_term core_model].
      apply (U_cong lG (oext (oEl rF lF G F) iF G) (oext (oEl rF lF G F') iF G) HlG HextGG'). }
  exact (eq_term_trans (eq_term_conv (eq_term_trans (eq_term_sym HL) HCodEsc) HSS')
           (eq_term_trans HMach HR)).
Qed.

(* ====================================================================== *)
(* RedTy_Pi_sound -- escape_ty at Pi.  Given the domain code equality       *)
(* HFF' (F~F') and the codomain code equality HCC' (C~C', from             *)
(* cod_collapse_both), plus both type-codes A,B reducing to the respective  *)
(* Pi codes and well typed at a common sort S, escape to eq_term S A B.     *)
(* A reds Pi F C G ~ Pi F' C' G reds B: the middle step is the Pi_rel       *)
(* con-congruence (eq_args = HCC' for C, HFF' for F, refl elsewhere) at the *)
(* natural Pi code sort Snat, transported to S via term_sorts_eq (Pi F C G  *)
(* is well typed at both Snat and S = subject reduction from A).            *)
(* ====================================================================== *)
Lemma RedTy_Pi_sound rF lF lG G F C F' C' A B S
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HF' : wf_term ott [] F' (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (HC' : wf_term ott [] C' (s_exp (oext (oEl rF lF G F') (term_info rF lF) G) (code_info lG)
                                  (oU orel lG (oext (oEl rF lF G F') (term_info rF lF) G))))
  (HFF' : eq_term ott [] (s_exp G (code_info lF) (oU rF lF G)) F F')
  (HCC' : eq_term ott []
            (s_exp (oext (oEl rF lF G F') (term_info rF lF) G) (code_info lG)
                   (oU orel lG (oext (oEl rF lF G F') (term_info rF lF) G)))
            C C')
  (HrdA : reds string ott ott_pa A (oPi_rel rF lF lG F C G))
  (HrdB : reds string ott ott_pa B (oPi_rel rF lF lG F' C' G))
  (HA : wf_term ott [] A S)
  (HB : wf_term ott [] B S)
  : eq_term ott [] S A B.
Proof.
  pose proof ott_wf as Hwf.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HA HrdA) as HrA.
  pose proof (@reds_sound string _ _ _ ott ott_wf ott_pa _ _ _ HB HrdB) as HrB.
  pose proof (@reds_wf string _ _ _ ott ott_wf ott_pa _ _ _ HA HrdA) as HPiS.
  assert (HPiCong : eq_term ott [] (s_exp G (code_info lG) (oU orel lG G))
            (oPi_rel rF lF lG F C G) (oPi_rel rF lF lG F' C' G)).
  { unfold oPi_rel, s_exp.
    eapply term_con_congruence.
    - apply named_list_lookup_err_in; compute; reflexivity.
    - right; cbn [with_names_from]; reflexivity.
    - exact ott_wf.
    - cbn [with_names_from].
      eapply eq_args_cons. 2:{ exact HCC'. }
      eapply eq_args_cons. 2:{ exact HFF'. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_nil. }
  pose proof (eq_term_wf_l ott_wf wf_ctx_ott_nil HPiCong) as HPiSnat.
  pose proof (term_sorts_eq ott_wf wf_ctx_ott_nil HPiSnat HPiS) as Hss.
  pose proof (eq_term_conv HPiCong Hss) as HPiCong_S.
  exact (eq_term_trans HrA (eq_term_trans HPiCong_S (eq_term_sym HrB))).
Qed.

(* ====================================================================== *)
(* RedTm_Pi_eta_sound -- escape_tm at Pi (the eta law).  Two functions t,u  *)
(* that agree on the bound variable (Hbody : mapp t hd ~ mapp u hd) are     *)
(* eq_term.  The "Pi_rel eta" rule body is SYNTACTICALLY mapp at the bound  *)
(* var (g:=wkn, a:=hd), so eta@t gives t ~ lam_rel(mapp t hd); lam_rel      *)
(* con-congruence on the bodies (Hbody, after reconciling the El(cod_at) vs *)
(* El C body sort via cod_at_wkn_hd_eq) gives lam(mapp t hd) ~ lam(mapp u   *)
(* hd); eta@u closes.                                                       *)
(* ====================================================================== *)
Lemma RedTm_Pi_eta_sound rF lF lG G F C t u
  (HG : wf_term ott [] G s_env)
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (HlG : wf_term ott [] lG (scon "lvl" []))
  (HF : wf_term ott [] F (s_exp G (code_info lF) (oU rF lF G)))
  (HC : wf_term ott [] C (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (code_info lG)
                                (oU orel lG (oext (oEl rF lF G F) (term_info rF lF) G))))
  (Ht : wf_term ott [] t (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Hu : wf_term ott [] u (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))))
  (Hbody : eq_term ott []
             (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (term_info orel lG)
                (oEl orel lG (oext (oEl rF lF G F) (term_info rF lF) G)
                   (cod_at rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
                      (oext (oEl rF lF G F) (term_info rF lF) G) F C
                      (ohd (oEl rF lF G F) (term_info rF lF) G))))
             (mapp rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
                (oext (oEl rF lF G F) (term_info rF lF) G) F C t
                (ohd (oEl rF lF G F) (term_info rF lF) G))
             (mapp rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
                (oext (oEl rF lF G F) (term_info rF lF) G) F C u
                (ohd (oEl rF lF G F) (term_info rF lF) G)))
  : eq_term ott [] (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))) t u.
Proof.
  pose proof ott_wf as Hwf.
  pose (etac := [("f", {{s #"exp" "G" (#"info" #"rel" (#"iota" "lG")) (#"El" "G" #"rel" "lG" (#"Pi_rel" "G" "rF" "lF" "lG" "F" "B"))}});
    ("B", {{s #"exp" (#"ext" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "G" "rF" "lF" "F")) (#"info" #"rel" (#"next" "lG")) (#"U" (#"ext" "G" (#"info" "rF" (#"iota" "lF")) (#"El" "G" "rF" "lF" "F")) #"rel" "lG")}});
    ("F", {{s #"exp" "G" (#"info" #"rel" (#"next" "lF")) (#"U" "G" "rF" "lF")}});
    ("lG", {{s #"lvl"}}); ("lF", {{s #"lvl"}}); ("rF", {{s #"relevance"}}); ("G", {{s #"env"}})] : ctx string).
  assert (Hin : In ("Pi_rel eta", _) ott) by (apply named_list_lookup_err_in; compute; reflexivity).
  assert (Hwfc : wf_ctx (Model:=core_model ott) etac).
  { use_rule_in_wf. rewrite invert_wf_term_eq_rule in H. destruct H as [Hc _]. exact Hc. }
  (* parametric eta: lam_rel(mapp f0 hd) ~ f0 for any well-typed function f0 *)
  assert (Heta : forall f0,
     wf_term ott [] f0 (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))) ->
     eq_term ott [] (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G)))
       (con "lam_rel" [mapp rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
            (oext (oEl rF lF G F) (term_info rF lF) G) F C f0 (ohd (oEl rF lF G F) (term_info rF lF) G);
          C; F; lG; lF; rF; G]) f0).
  { intros f0 Hf0.
    pose (s0 := [("f",f0);("B",C);("F",F);("lG",lG);("lF",lF);("rF",rF);("G",G)] : subst string).
    assert (Hws0 : wf_subst (Model:=core_model ott) [] s0 etac) by
      (unfold s0, etac; repeat first [ simple apply wf_subst_nil | simple apply wf_subst_cons ];
       first [ exact HG | exact HrF | exact HlF | exact HlG | exact HF | exact HC | exact Hf0 ]).
    eassert (Hrule : eq_term ott _ _ _ _) by (eapply eq_term_by; exact Hin).
    exact (eq_term_subst Hrule (eq_subst_refl Hws0) Hwfc). }
  pose proof (Heta t Ht) as Heta_t.
  pose proof (Heta u Hu) as Heta_u.
  (* reconcile the lam-body sort El(cod_at) with El C via cod_at_wkn_hd_eq *)
  pose proof (cod_at_wkn_hd_eq rF lF lG G F C HG HrF HlF HlG HF HC) as Hcweq. cbv zeta in Hcweq.
  assert (Horel : wf_term ott [] orel (scon "relevance" [])) by
    (unfold orel; eapply Elab.wf_term_by';
       [apply named_list_lookup_err_in; compute; reflexivity
       | cbn [Model.wf_term core_model]; ott_build | left; compute; reflexivity]).
  assert (HgextWf : wf_term ott [] (oext (oEl rF lF G F) (term_info rF lF) G) s_env) by ott_build.
  pose proof (El_cong orel lG (oext (oEl rF lF G F) (term_info rF lF) G)
     (cod_at rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
        (oext (oEl rF lF G F) (term_info rF lF) G) F C (ohd (oEl rF lF G F) (term_info rF lF) G))
     C HgextWf Horel HlG Hcweq) as HElcw.
  assert (Hsb : eq_sort ott []
     (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (term_info orel lG)
        (oEl orel lG (oext (oEl rF lF G F) (term_info rF lF) G)
           (cod_at rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
              (oext (oEl rF lF G F) (term_info rF lF) G) F C (ohd (oEl rF lF G F) (term_info rF lF) G))))
     (s_exp (oext (oEl rF lF G F) (term_info rF lF) G) (term_info orel lG)
        (oEl orel lG (oext (oEl rF lF G F) (term_info rF lF) G) C))).
  { unfold s_exp. sort_cong.
    - cbn [Model.eq_term core_model]. eapply eq_term_refl. exact HgextWf.
    - cbn [Model.eq_term core_model]. eapply eq_term_refl. ott_build.
    - cbn [Model.eq_term core_model]. exact HElcw. }
  pose proof (eq_term_conv Hbody Hsb) as Hbody'.
  (* lam_rel congruence on the bodies *)
  assert (Hlamcong : eq_term ott [] (s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G)))
     (con "lam_rel" [mapp rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
          (oext (oEl rF lF G F) (term_info rF lF) G) F C t (ohd (oEl rF lF G F) (term_info rF lF) G); C; F; lG; lF; rF; G])
     (con "lam_rel" [mapp rF lF lG (owkn (oEl rF lF G F) (term_info rF lF) G) G
          (oext (oEl rF lF G F) (term_info rF lF) G) F C u (ohd (oEl rF lF G F) (term_info rF lF) G); C; F; lG; lF; rF; G])).
  { eapply term_con_congruence.
    - apply named_list_lookup_err_in; compute; reflexivity.
    - right; cbn [with_names_from]; reflexivity.
    - exact ott_wf.
    - cbn [with_names_from].
      eapply eq_args_cons. 2:{ exact Hbody'. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_cons. 2:{ eapply eq_term_refl; ott_build. }
      eapply eq_args_nil. }
  exact (eq_term_trans (eq_term_sym Heta_t) (eq_term_trans Hlamcong Heta_u)).
Qed.

(* ====================================================================== *)
(* CLOSED-TERM CANONICITY for the finite info-layer sorts (#"relevance",   *)
(* #"lvl"), and the SORT-DISTINCTNESS foundation it rests on.              *)
(*                                                                        *)
(* These discharge step (1)/(2) of plan (A) (NEXT_SESSION z9): the Pi      *)
(* REFLECT case (typing-induction fundamental lemma) must rule out the     *)
(* bad relevance/level (oirr / L1) of a Nat/Empty-domain binder.  Because  *)
(* #"relevance" / #"lvl" are RIGID inductive sorts with exactly two        *)
(* nullary constructors and NO equational rules, a closed well-typed term  *)
(* of either sort is canonical — a FINITE enumeration, NOT normalization.  *)
(*                                                                        *)
(* The whole development is SYNTACTIC and model-free.  Its engine is       *)
(* `eq_sort_ott_same_name`: `ott` contains no `sort_eq_rule` (checked by    *)
(* computation), so `Core.eq_sort` over `ott` can never change the head    *)
(* constructor of a sort (the `eq_sort_by` constructor is vacuous, and     *)
(* `eq_sort_subst` preserves the head).  This is exactly the sort          *)
(* DISTINCTNESS the wall needs (e.g. `scon "lvl" _ ~/~ scon "relevance" _`).*)
(* ====================================================================== *)

(* `ott` has NO sort-equality rules. *)
Lemma ott_no_sort_eq_rule : forall name c t1 t2,
  ~ In (name, sort_eq_rule c t1 t2) ott.
Proof.
  assert (Hall : List.forallb
            (fun p => match snd p with sort_eq_rule _ _ _ => false | _ => true end)
            ott = true)
    by (vm_compute; reflexivity).
  rewrite List.forallb_forall in Hall.
  intros name c t1 t2 Hin.
  apply Hall in Hin. cbn in Hin. discriminate.
Qed.

(* The head constructor name of a sort. *)
Definition sort_name (s : osort) : string := match s with scon n _ => n end.

(* SORT DISTINCTNESS: eq_sort over `ott` never changes a sort's head. *)
Lemma eq_sort_ott_same_name : forall c t1 t2,
  eq_sort ott c t1 t2 -> sort_name t1 = sort_name t2.
Proof.
  intros c t1 t2 H.
  induction H.
  - (* eq_sort_by: vacuous, ott has no sort_eq_rule *)
    exfalso. eapply ott_no_sort_eq_rule; eassumption.
  - (* eq_sort_subst: substitution preserves the head *)
    destruct t1', t2'; cbn in *; congruence.
  - (* eq_sort_refl *) reflexivity.
  - (* eq_sort_trans *) congruence.
  - (* eq_sort_sym *) congruence.
Qed.

(* No closed `var` is well typed (the empty context has no variables).
   Stated via `remember`+`induction` so the wf_term CONV rule is handled by
   the IH — naive `inversion` loops through CONV. *)
Lemma no_wf_var_nil : forall n t, wf_term ott [] (var n) t -> False.
Proof.
  intros n t Hwf.
  remember (var n) as e eqn:He; remember (@nil (string*osort)) as cc eqn:Hcc.
  revert n He.
  induction Hwf; intros m He; try discriminate.
  - (* conv *) eapply IHHwf; eauto.
  - (* var *) subst. inversion H.
Qed.

(* RELEVANCE CANONICITY: a closed well-typed term of sort #"relevance" is
   #"rel" or #"irr".  No `inversion` on the typing (CONV loops); instead
   `WfCutElim.invert_wf_term_con` (the term is a `con`, not a `var`, by
   `no_wf_var_nil`) hands the rule, whose conclusion-sort head must be
   "relevance" (by `eq_sort_ott_same_name` for the eq-sort disjunct, or
   directly for the syntactic one), and a `filter` enumerates the only two
   such rules. *)
Lemma relevance_canon : forall r,
  wf_term ott [] r (scon "relevance" []) ->
  r = con "rel" [] \/ r = con "irr" [].
Proof.
  intros r Hwf.
  destruct r as [n | n s].
  - exfalso. eapply no_wf_var_nil; eassumption.
  - apply WfCutElim.invert_wf_term_con in Hwf
      as (c' & args & t' & Hin & Hwfargs & Hsort).
    assert (Hhead : sort_name t' = "relevance").
    { destruct t' as [tn ts]. destruct Hsort as [Heq | Heq].
      - apply eq_sort_ott_same_name in Heq. cbn in Heq. exact Heq.
      - cbn in Heq |- *. congruence. }
    clear Hsort.
    pose (f := fun p : string * rule string =>
      match snd p with
      | term_rule _ _ t' => String.eqb (sort_name t') "relevance"
      | _ => false end).
    assert (Hfin : In (n, term_rule c' args t') (filter f ott)).
    { apply filter_In. split; [exact Hin|]. subst f; cbn. rewrite Hhead. reflexivity. }
    vm_compute in Hfin.
    destruct Hfin as [He | [He | []]]; inversion He; subst.
    + inversion Hwfargs; subst s. right. reflexivity.
    + inversion Hwfargs; subst s. left. reflexivity.
Qed.

(* LEVEL CANONICITY: a closed well-typed term of sort #"lvl" is #"L0" or
   #"L1".  Identical structure to `relevance_canon`. *)
Lemma lvl_canon : forall r,
  wf_term ott [] r (scon "lvl" []) ->
  r = con "L0" [] \/ r = con "L1" [].
Proof.
  intros r Hwf.
  destruct r as [n | n s].
  - exfalso. eapply no_wf_var_nil; eassumption.
  - apply WfCutElim.invert_wf_term_con in Hwf
      as (c' & args & t' & Hin & Hwfargs & Hsort).
    assert (Hhead : sort_name t' = "lvl").
    { destruct t' as [tn ts]. destruct Hsort as [Heq | Heq].
      - apply eq_sort_ott_same_name in Heq. cbn in Heq. exact Heq.
      - cbn in Heq |- *. congruence. }
    clear Hsort.
    pose (f := fun p : string * rule string =>
      match snd p with
      | term_rule _ _ t' => String.eqb (sort_name t') "lvl"
      | _ => false end).
    assert (Hfin : In (n, term_rule c' args t') (filter f ott)).
    { apply filter_In. split; [exact Hin|]. subst f; cbn. rewrite Hhead. reflexivity. }
    vm_compute in Hfin.
    destruct Hfin as [He | [He | []]]; inversion He; subst.
    + inversion Hwfargs; subst s. right. reflexivity.
    + inversion Hwfargs; subst s. left. reflexivity.
Qed.

(* ====================================================================== *)
(* RELEVANCE / LEVEL DISTINCTNESS under eq_term (plan (A) step 2).         *)
(*                                                                        *)
(* The Pi REFLECT case must rule out the *bad* relevance/level of a        *)
(* relevant (Nat/Empty) binder: #"rel" /= #"irr" and #"L0" /= #"L1" as     *)
(* closed terms, even up to declarative `eq_term`.  Like the canonicity    *)
(* above, this is SYNTACTIC and model-free — `ott` contains NO             *)
(* `term_eq_rule` whose conclusion sort is #"relevance" or #"lvl"          *)
(* (`ott_no_term_eq_rule_rl`, by computation), so a closed `eq_term` at     *)
(* either sort never changes a term's head constructor.                    *)
(*                                                                        *)
(* The argument runs over the CUT-FREE judgments (CutElim): the cut-free   *)
(* `eq_term` has no `eq_term_subst` constructor (it is admissible), so a    *)
(* head-invariance induction goes through (the open-variable subst case    *)
(* that breaks the direct `Core.eq_term` induction simply does not arise). *)
(* We bridge back via `CutElim.core_implies_cut`.                          *)
(* ====================================================================== *)

(* Cut-free eq_sort over `ott` preserves the head name (no sort_eq_rule). *)
Lemma cut_eq_sort_ott_same_name : forall c t1 t2,
  @CutElim.eq_sort string _ ott c t1 t2 -> sort_name t1 = sort_name t2.
Proof.
  intros c t1 t2 H.
  induction H.
  - exfalso. eapply ott_no_sort_eq_rule; eassumption.
  - reflexivity.
  - congruence.
  - congruence.
Qed.

(* `ott` has NO term-equality rule with conclusion sort #"relevance"/#"lvl". *)
Lemma ott_no_term_eq_rule_rl : forall name c e1 e2 t,
  In (name, term_eq_rule c e1 e2 t) ott ->
  sort_name t <> "relevance" /\ sort_name t <> "lvl".
Proof.
  assert (Hall : List.forallb
    (fun p => match snd p with
       | term_eq_rule _ _ _ t =>
           negb (orb (String.eqb (sort_name t) "relevance")
                     (String.eqb (sort_name t) "lvl"))
       | _ => true end) ott = true)
    by (vm_compute; reflexivity).
  rewrite List.forallb_forall in Hall.
  intros name c e1 e2 t Hin.
  apply Hall in Hin. cbn in Hin.
  apply Bool.negb_true_iff, Bool.orb_false_iff in Hin.
  destruct Hin as [H1 H2].
  split; intro Hc; rewrite Hc in *; cbn in *; discriminate.
Qed.

(* The head constructor of a term (None for a var). *)
Definition tm_head (e : tm) : option string :=
  match e with con n _ => Some n | var _ => None end.

(* Cut-free eq_term at sort #"relevance"/#"lvl" preserves the term head. *)
Lemma cut_eq_term_ott_same_head : forall c t a b,
  @CutElim.eq_term string _ ott c t a b ->
  (sort_name t = "relevance" \/ sort_name t = "lvl") ->
  tm_head a = tm_head b.
Proof.
  intros c t a b H.
  induction H; intro Hs.
  - (* eq_term_by: vacuous (no such term_eq_rule) *)
    exfalso.
    destruct (ott_no_term_eq_rule_rl _ _ _ _ _ H) as [Hr Hl].
    destruct t as [tn ts]. cbn in Hs.
    destruct Hs as [Hs|Hs]; [apply Hr|apply Hl]; exact Hs.
  - (* eq_term_cong: same head con *) reflexivity.
  - (* eq_term_var *) reflexivity.
  - (* eq_term_trans *)
    rewrite IHeq_term1 by assumption. apply IHeq_term2; assumption.
  - (* eq_term_sym *) symmetry. apply IHeq_term; assumption.
  - (* eq_term_conv: sort head preserved by cut_eq_sort_ott_same_name *)
    apply IHeq_term.
    apply cut_eq_sort_ott_same_name in H0. rewrite H0. exact Hs.
Qed.

(* Bridge back to declarative `Core.eq_term` at the empty context. *)
Lemma core_eq_term_ott_same_head : forall t a b,
  eq_term ott [] t a b ->
  (sort_name t = "relevance" \/ sort_name t = "lvl") ->
  tm_head a = tm_head b.
Proof.
  intros t a b Hcore Hs.
  assert (Hcut : CutElim.wf_lang _ ott).
  { apply CutElim.wf_lang_iff_cut; [ typeclasses eauto | typeclasses eauto | exact ott_wf ]. }
  pose proof (CutElim.core_implies_cut _ ott Hcut) as Himpl.
  destruct Himpl as [_ [Hterm _]].
  apply Hterm in Hcore.
  eapply cut_eq_term_ott_same_head; eassumption.
Qed.

(* RELEVANCE DISTINCTNESS: #"rel" and #"irr" are NOT eq_term-equal. *)
Lemma rel_neq_irr :
  ~ eq_term ott [] (scon "relevance" []) (con "rel" []) (con "irr" []).
Proof.
  intro H.
  apply core_eq_term_ott_same_head in H; [ cbn in H; discriminate | left; reflexivity ].
Qed.

(* LEVEL DISTINCTNESS: #"L0" and #"L1" are NOT eq_term-equal. *)
Lemma L0_neq_L1 :
  ~ eq_term ott [] (scon "lvl" []) (con "L0" []) (con "L1" []).
Proof.
  intro H.
  apply core_eq_term_ott_same_head in H; [ cbn in H; discriminate | right; reflexivity ].
Qed.

(* ====================================================================== *)
(* SYNTACTIC UNIQUENESS at #"relevance"/#"lvl" (z13, Dustin's directive).   *)
(*                                                                        *)
(* STRENGTHENING of `core_eq_term_ott_same_head`: at the rigid info-layer   *)
(* sorts #"relevance"/#"lvl", declarative `eq_term` forces FULL syntactic   *)
(* equality (the whole term, not just the head constructor).  This is the   *)
(* trans-stable leaf the Pi bound-var distinctness obligation bottoms out   *)
(* at: those sorts admit NO `term_eq_rule` (`ott_no_term_eq_rule_rl`), so a  *)
(* closed `eq_term` at them can never relate two distinct terms, and the     *)
(* claim is trans/sym/conv-stable because it is itself a syntactic equality. *)
(* Runs over the CUT-FREE judgments (no `eq_term_subst` ctor) and bridges    *)
(* back via `CutElim.core_implies_cut`, exactly like the z10 head version.   *)
(* ====================================================================== *)

(* Cut-free `eq_term` at #"relevance"/#"lvl" forces syntactic equality. *)
Lemma cut_eq_term_ott_rl_syntactic : forall c t a b,
  @CutElim.eq_term string _ ott c t a b ->
  (sort_name t = "relevance" \/ sort_name t = "lvl") ->
  a = b.
Proof.
  intros c t a b H.
  induction H using CutElim.eq_term_ind'
    with (P := fun (_ _ : osort) => True)
         (P1 := fun (_ : ctx string) (_ _ : subst string) => True)
         (P2 := fun (_ : ctx string) (_ _ : list tm) => True);
    try (exact I); intros Hs.
  - (* eq_term_by: vacuous (no term_eq_rule at relevance/lvl) *)
    exfalso.
    destruct (ott_no_term_eq_rule_rl _ _ _ _ _ H) as [Hr Hl].
    destruct t as [tn ts]. cbn in Hs.
    destruct Hs as [Hs|Hs]; [apply Hr|apply Hl]; cbn; exact Hs.
  - (* eq_term_cong: the rule is one of rel/irr/L0/L1, all with empty ctx,
       so the argument lists are nil and `con name [] = con name []`. *)
    destruct t as [tn ts]. cbn in Hs.
    pose (f := fun p : string * rule string =>
      match snd p with
      | term_rule _ _ t' => orb (String.eqb (sort_name t') "relevance")
                                (String.eqb (sort_name t') "lvl")
      | _ => false end).
    assert (Hfin : In (name, term_rule c' args (scon tn ts)) (filter f ott)).
    { apply filter_In. split; [exact H|]. subst f; cbn.
      destruct Hs as [Hs|Hs]; rewrite Hs; cbn; reflexivity. }
    vm_compute in Hfin.
    repeat (destruct Hfin as [He | Hfin]; [ inversion He; subst; clear He |]);
      try (exfalso; exact Hfin);
      inversion H0; subst; reflexivity.
  - (* eq_term_var *) reflexivity.
  - (* eq_term_trans: trans of two syntactic equalities *)
    rewrite IHeq_term1 by assumption. apply IHeq_term2; assumption.
  - (* eq_term_sym *) symmetry. apply IHeq_term; assumption.
  - (* eq_term_conv: sort head preserved, so condition transports *)
    apply IHeq_term. apply cut_eq_sort_ott_same_name in H0. rewrite H0. exact Hs.
Qed.

(* Bridge to declarative `Core.eq_term`: FULL syntactic equality at rel/lvl. *)
Lemma core_eq_term_ott_rl_syntactic : forall t a b,
  eq_term ott [] t a b ->
  (sort_name t = "relevance" \/ sort_name t = "lvl") ->
  a = b.
Proof.
  intros t a b Hcore Hs.
  assert (Hcut : CutElim.wf_lang _ ott).
  { apply CutElim.wf_lang_iff_cut; [ typeclasses eauto | typeclasses eauto | exact ott_wf ]. }
  pose proof (CutElim.core_implies_cut _ ott Hcut) as Himpl.
  destruct Himpl as [_ [Hterm _]].
  apply Hterm in Hcore.
  eapply cut_eq_term_ott_rl_syntactic; eassumption.
Qed.

(* ====================================================================== *)
(* R1 — RELEVANCE-PRESERVATION METATHEOREM on the #"ty"/#"exp" sub-language *)
(* (NEXT_SESSION z14; Dustin's chosen route — NO model, NO target lang D).  *)
(*                                                                        *)
(* The Pi bound-var distinctness obligation is a BARE `eq_sort` between two *)
(* code sorts                                                              *)
(*   eq_sort ott extG (code_sort oirr lF G) (code_sort orel oL0 G) -> False *)
(* i.e. between `scon "exp" [oU oirr lF G; ..]` and `scon "exp" [oU orel    *)
(* oL0 G; ..]`.  A naive cong descent fails on `eq_sort_trans` (the         *)
(* intermediate #"exp" sort's type-component need not be `U`-headed).  The  *)
(* fix is a TRANS-STABLE invariant: a `code_rel` READING that extracts the  *)
(* relevance constant a ty-term denotes, LOOKING THROUGH `ty_subst`/`El`,   *)
(* and is preserved by every #"ty"/#"exp" rule + congruence + conv.  The    *)
(* load-bearing empirical fact (verified by enumerating the rules):  NO     *)
(* ty/exp rule alters a relevance constant — U subst / El subst /           *)
(* ty_subst_cmp / ty_subst_id all keep the buried relevance, and the        *)
(* congruences relate the relevance argument at sort #"relevance", which is  *)
(* SYNTACTIC by `core_eq_term_ott_rl_syntactic`.  Bottoming out there gives  *)
(* `oirr = orel`, contradiction (`rel_neq_irr` syntactically).              *)
(* ====================================================================== *)

(* The relevance reading on a ty-term: the `r` in its U/El head, seen
   through `ty_subst` (which never changes it).  `None` off the ty layer. *)
Fixpoint code_rel (A : tm) : option tm :=
  match A with
  | con n args =>
      if String.eqb n "U"
      then match args with _ :: r :: _ => Some r | _ => None end
      else if String.eqb n "El"
      then match args with _ :: _ :: r :: _ => Some r | _ => None end
      else if String.eqb n "ty_subst"
      then match args with A' :: _ => code_rel A' | _ => None end
      else None
  | var _ => None
  end.

(* The relevance reading lifted to a sort: the type-component of an #"exp". *)
Definition sort_rel (t : osort) : option tm :=
  match t with
  | scon n (A :: _) => if String.eqb n "exp" then code_rel A else None
  | _ => None
  end.

(* The LEVEL reading on a ty-term: the `l` in its U/El head, same recursion
   through `ty_subst`.  (U stores [l;r;G], so l is the head arg; El stores
   [e;l;r;G], so l is the 2nd arg.)  No ty/exp rule alters a level constant. *)
Fixpoint code_lvl (A : tm) : option tm :=
  match A with
  | con n args =>
      if String.eqb n "U"
      then match args with l :: _ => Some l | _ => None end
      else if String.eqb n "El"
      then match args with _ :: l :: _ => Some l | _ => None end
      else if String.eqb n "ty_subst"
      then match args with A' :: _ => code_lvl A' | _ => None end
      else None
  | var _ => None
  end.

Definition sort_lvl (t : osort) : option tm :=
  match t with
  | scon n (A :: _) => if String.eqb n "exp" then code_lvl A else None
  | _ => None
  end.

(* `all_fresh ott` (fast; the e-graph `compute_all_fresh` decision proc). *)
Lemma ott_all_fresh : all_fresh ott.
Proof. apply use_compute_all_fresh; vm_compute; reflexivity. Qed.

(* The unique `exp` sort rule of ott, pinned by membership. *)
Lemma exp_in_ott :
  In ("exp", sort_rule [("A", {{s #"ty" "G" "i"}}); ("i", {{s #"tyinfo"}});
                        ("G", {{s #"env"}})] ["A"; "i"; "G"]) ott.
Proof. vm_compute. tauto. Qed.

(* THE INVARIANT (mutual over the four cut-free judgments):                  *)
(*  - sort: `sort_rel` is preserved by `eq_sort` at #"exp" (cong descends to  *)
(*    the type-component; trans/sym free because it's an equality of options); *)
(*  - term: `code_rel` is preserved by `eq_term` at #"ty" — the eq_term_by     *)
(*    cases (U/El subst, ty_subst_cmp/id) keep the buried relevance/ty-reading; *)
(*    cong reads the U/El relevance arg at #"relevance" (SYNTACTIC by           *)
(*    `core_eq_term_ott_rl_syntactic`) or the ty_subst A-arg (recursively);    *)
(*  - subst/args: positional carriers feeding the eq_term_by/cong cases (the   *)
(*    relevance positions become syntactically equal, the ty positions equal   *)
(*    under `code_rel`).  No ty/exp rule alters a relevance constant, which is  *)
(*    what makes the reading TRANS-STABLE (the z11/z13 wall). *)
Lemma cut_code_rel_invariant (c : ctx string) :
  (forall (t1 t2 : osort),
     @CutElim.eq_sort string _ ott c t1 t2 -> sort_rel t1 = sort_rel t2)
  /\ (forall (t : osort) (a b : tm),
     @CutElim.eq_term string _ ott c t a b ->
     sort_name t = "ty" -> code_rel a = code_rel b)
  /\ (forall (c' : ctx string) (s1 s2 : subst string),
     @CutElim.eq_subst string _ ott c c' s1 s2 ->
     forall x t, named_list_lookup_err c' x = Some t ->
       (sort_name t = "relevance" -> subst_lookup s1 x = subst_lookup s2 x)
       /\ (sort_name t = "ty" ->
           code_rel (subst_lookup s1 x) = code_rel (subst_lookup s2 x)))
  /\ (forall (c' : ctx string) (s1 s2 : list tm),
     @CutElim.eq_args string _ ott c c' s1 s2 ->
     forall n name t a b, nth_error c' n = Some (name,t) ->
       nth_error s1 n = Some a -> nth_error s2 n = Some b ->
       (sort_name t = "relevance" -> a = b)
       /\ (sort_name t = "ty" -> code_rel a = code_rel b)).
Proof.
  pose proof ott_all_fresh as Hfresh.
  apply CutElim.cut_ind.
  (* sort eq_by: vacuous *)
  1:{ intros name c' t1 t2 s1 s2 Hin _ _. exfalso. eapply ott_no_sort_eq_rule; eassumption. }
  (* sort cong: at #"exp", descend to the type-component (position 0) *)
  1:{ intros name c' args s1 s2 Hin Hargs IHargs.
      unfold sort_rel.
      destruct (String.eqb name "exp") eqn:Hn.
      2:{ destruct s1; destruct s2; reflexivity. }
      apply String.eqb_eq in Hn. subst name.
      pose proof exp_in_ott as Hexp.
      pose proof (in_all_fresh_same _ _ _ _ Hfresh Hin Hexp) as Heq.
      inversion Heq; subst c' args; clear Heq Hexp Hin.
      inversion Hargs; subst.
      destruct (IHargs 0 "A" {{s #"ty" "G" "i"}} e1 e2 eq_refl eq_refl eq_refl) as [_ Hty0].
      apply (Hty0 eq_refl). }
  (* sort trans / sym *)
  1:{ intros t1 t12 t2 _ H1 _ H2. congruence. }
  1:{ intros t1 t2 _ H. congruence. }
  (* term eq_by: the four #"ty" rewrite rules all preserve `code_rel` *)
  1:{ intros name c' t e1 e2 s1 s2 Hin Hsub IHsub Hty.
      assert (Htyt : sort_name t = "ty") by (destruct t; cbn in Hty |- *; exact Hty).
      pose (f := fun p : string * rule string =>
        match snd p with
        | term_eq_rule _ _ _ t' => String.eqb (sort_name t') "ty"
        | _ => false end).
      assert (Hfin : In (name, term_eq_rule c' e1 e2 t) (filter f ott)).
      { apply filter_In. split; [exact Hin|]. subst f; cbn. rewrite Htyt. reflexivity. }
      vm_compute in Hfin.
      destruct Hfin as [He|[He|[He|[He|[]]]]]; inversion He; subst name c' e1 e2 t; clear He.
      - (* El subst: relevance arg "r" *)
        cbn -[subst_lookup]. f_equal.
        change (term_subst_lookup s1 "r") with (subst_lookup s1 "r").
        change (term_subst_lookup s2 "r") with (subst_lookup s2 "r").
        destruct (IHsub "r" {{s #"relevance"}} eq_refl) as [Hrel _].
        apply Hrel. reflexivity.
      - (* U subst: relevance arg "r" *)
        cbn -[subst_lookup]. f_equal.
        change (term_subst_lookup s1 "r") with (subst_lookup s1 "r").
        change (term_subst_lookup s2 "r") with (subst_lookup s2 "r").
        destruct (IHsub "r" {{s #"relevance"}} eq_refl) as [Hrel _].
        apply Hrel. reflexivity.
      - (* ty_subst_cmp: look through both ty_subst to the ty arg "A" *)
        cbn -[subst_lookup].
        change (term_subst_lookup s1 "A") with (subst_lookup s1 "A").
        change (term_subst_lookup s2 "A") with (subst_lookup s2 "A").
        destruct (IHsub "A" {{s #"ty" "G3" "i"}} eq_refl) as [_ Hty0].
        apply Hty0. reflexivity.
      - (* ty_subst_id: look through ty_subst to the ty arg "A" *)
        cbn -[subst_lookup].
        change (term_subst_lookup s1 "A") with (subst_lookup s1 "A").
        change (term_subst_lookup s2 "A") with (subst_lookup s2 "A").
        destruct (IHsub "A" {{s #"ty" "G" "i"}} eq_refl) as [_ Hty0].
        apply Hty0. reflexivity. }
  (* term cong: at #"ty" the rule is U/El/ty_subst; read the relevance/A arg *)
  1:{ intros name c' args t s1 s2 Hin Hargs IHargs Hty.
      assert (Htyt : sort_name t = "ty") by (destruct t; cbn in Hty |- *; exact Hty).
      pose (f := fun p : string * rule string =>
        match snd p with
        | term_rule _ _ t' => String.eqb (sort_name t') "ty"
        | _ => false end).
      assert (Hfin : In (name, term_rule c' args t) (filter f ott)).
      { apply filter_In. split; [exact Hin|]. subst f; cbn. rewrite Htyt. reflexivity. }
      vm_compute in Hfin.
      destruct Hfin as [He|[He|[He|[]]]]; inversion He; subst name c' args t; clear He;
        repeat (match goal with
                | H : CutElim.eq_args _ _ _ (_ :: _) _ _ |- _ => inversion H; subst; clear H
                end);
        cbn [code_rel].
      - (* El: relevance arg via the syntactic leaf *)
        match goal with
        | H : CutElim.eq_term _ _ _ {{s #"relevance"}} [/_/] ?a ?b |- _ =>
            assert (Hr : a = b) by
              (eapply cut_eq_term_ott_rl_syntactic; [ exact H | left; reflexivity ]); rewrite Hr
        end. reflexivity.
      - (* U: relevance arg *)
        match goal with
        | H : CutElim.eq_term _ _ _ {{s #"relevance"}} [/_/] ?a ?b |- _ =>
            assert (Hr : a = b) by
              (eapply cut_eq_term_ott_rl_syntactic; [ exact H | left; reflexivity ]); rewrite Hr
        end. reflexivity.
      - (* ty_subst: A arg via the args-IH ty-clause at position 0 *)
        destruct (IHargs 0 "A" {{s #"ty" "G'" "i"}} e1 e2 eq_refl eq_refl eq_refl) as [_ Hty0].
        rewrite (Hty0 eq_refl). reflexivity. }
  (* term var: both sides are `code_rel (var n)` *)
  1:{ intros n t Hin Hty. reflexivity. }
  (* term trans / sym *)
  1:{ intros t e1 e12 e2 _ H1 _ H2 Hty. rewrite H1 by assumption. apply H2; assumption. }
  1:{ intros t e1 e2 _ H Hty. symmetry. apply H; assumption. }
  (* term conv: eq_sort preserves the sort head, so #"ty" transports *)
  1:{ intros e1 e2 t t' _ IH Hsort _ Hty'.
      apply IH. apply cut_eq_sort_ott_same_name in Hsort.
      destruct t as [tn ts], t' as [tn' ts']. cbn [sort_name] in *. congruence. }
  (* subst nil *)
  1:{ intros x t Hl. cbn in Hl. discriminate. }
  (* subst cons *)
  1:{ intros c' s1 s2 Hsub IHsub name t e1 e2 Hhead IHhead.
      intros x t0 Hl. cbn in Hl.
      destruct (eqb x name) eqn:Hx.
      - inversion Hl; subst t0; clear Hl.
        unfold subst_lookup. cbn [named_list_lookup]. rewrite Hx.
        assert (Hsn : sort_name (t [/s2/]) = sort_name t) by (destruct t; reflexivity).
        split; intro Hs.
        + eapply cut_eq_term_ott_rl_syntactic; [exact Hhead | rewrite Hsn; left; exact Hs].
        + apply IHhead. rewrite Hsn. exact Hs.
      - unfold subst_lookup. cbn [named_list_lookup]. rewrite Hx.
        fold (subst_lookup s1 x). fold (subst_lookup s2 x).
        eapply IHsub; eassumption. }
  (* args nil *)
  1:{ intros n name t a b Hc. destruct n; cbn in Hc; discriminate. }
  (* args cons *)
  1:{ intros c' es1 es2 Hargs IHargs name t e1 e2 Hhead IHhead.
      intros n nm t0 a b Hc Ha Hb.
      destruct n.
      - cbn in Hc, Ha, Hb. inversion Hc; subst nm t0; clear Hc.
        inversion Ha; subst a; clear Ha. inversion Hb; subst b; clear Hb.
        assert (Hsn : sort_name (t [/with_names_from c' es2/]) = sort_name t)
          by (destruct t; reflexivity).
        split; intro Hs.
        + eapply cut_eq_term_ott_rl_syntactic; [exact Hhead | rewrite Hsn; left; exact Hs].
        + apply IHhead. rewrite Hsn. exact Hs.
      - cbn in Hc, Ha, Hb. eapply IHargs; eassumption. }
Qed.

(* Bridge to declarative `Core.eq_sort`: `sort_rel` is an eq_sort invariant. *)
Lemma core_sort_rel_invariant : forall c t1 t2,
  eq_sort ott c t1 t2 -> sort_rel t1 = sort_rel t2.
Proof.
  intros c t1 t2 Hcore.
  assert (Hcut : CutElim.wf_lang _ ott).
  { apply CutElim.wf_lang_iff_cut; [ typeclasses eauto | typeclasses eauto | exact ott_wf ]. }
  pose proof (CutElim.core_implies_cut _ ott Hcut) as Himpl.
  destruct Himpl as [Hsort _].
  apply Hsort in Hcore.
  destruct (cut_code_rel_invariant c) as [Hinv _].
  apply Hinv. exact Hcore.
Qed.

(* THE DISCHARGED OBLIGATION (relevance side).  Two code sorts whose buried
   relevances are the (syntactically distinct) constants oirr / orel are NOT
   eq_sort-related — this is the bound-var distinctness fact the z11/z13 wall
   needed, now proven WITHOUT a model or a target language.  `code_sort r l G`
   reads its relevance via `sort_rel` as `Some r`, so the invariant forces
   `oirr = orel`, contradiction. *)
Lemma code_sort_rel_neq_irr : forall c lF lG G G',
  ~ eq_sort ott c (code_sort oirr lF G) (code_sort orel lG G').
Proof.
  intros c lF lG G G' H.
  apply core_sort_rel_invariant in H.
  unfold code_sort, sort_rel, oU, code_rel, oirr, orel in H.
  cbn in H. discriminate.
Qed.

(* ---- LEVEL analogue (identical structure, reading the buried level) ---- *)
Lemma cut_code_lvl_invariant (c : ctx string) :
  (forall (t1 t2 : osort),
     @CutElim.eq_sort string _ ott c t1 t2 -> sort_lvl t1 = sort_lvl t2)
  /\ (forall (t : osort) (a b : tm),
     @CutElim.eq_term string _ ott c t a b ->
     sort_name t = "ty" -> code_lvl a = code_lvl b)
  /\ (forall (c' : ctx string) (s1 s2 : subst string),
     @CutElim.eq_subst string _ ott c c' s1 s2 ->
     forall x t, named_list_lookup_err c' x = Some t ->
       (sort_name t = "lvl" -> subst_lookup s1 x = subst_lookup s2 x)
       /\ (sort_name t = "ty" ->
           code_lvl (subst_lookup s1 x) = code_lvl (subst_lookup s2 x)))
  /\ (forall (c' : ctx string) (s1 s2 : list tm),
     @CutElim.eq_args string _ ott c c' s1 s2 ->
     forall n name t a b, nth_error c' n = Some (name,t) ->
       nth_error s1 n = Some a -> nth_error s2 n = Some b ->
       (sort_name t = "lvl" -> a = b)
       /\ (sort_name t = "ty" -> code_lvl a = code_lvl b)).
Proof.
  pose proof ott_all_fresh as Hfresh.
  apply CutElim.cut_ind.
  1:{ intros name c' t1 t2 s1 s2 Hin _ _. exfalso. eapply ott_no_sort_eq_rule; eassumption. }
  1:{ intros name c' args s1 s2 Hin Hargs IHargs.
      unfold sort_lvl.
      destruct (String.eqb name "exp") eqn:Hn.
      2:{ destruct s1; destruct s2; reflexivity. }
      apply String.eqb_eq in Hn. subst name.
      pose proof exp_in_ott as Hexp.
      pose proof (in_all_fresh_same _ _ _ _ Hfresh Hin Hexp) as Heq.
      inversion Heq; subst c' args; clear Heq Hexp Hin.
      inversion Hargs; subst.
      destruct (IHargs 0 "A" {{s #"ty" "G" "i"}} e1 e2 eq_refl eq_refl eq_refl) as [_ Hty0].
      apply (Hty0 eq_refl). }
  1:{ intros t1 t12 t2 _ H1 _ H2. congruence. }
  1:{ intros t1 t2 _ H. congruence. }
  1:{ intros name c' t e1 e2 s1 s2 Hin Hsub IHsub Hty.
      assert (Htyt : sort_name t = "ty") by (destruct t; cbn in Hty |- *; exact Hty).
      pose (f := fun p : string * rule string =>
        match snd p with
        | term_eq_rule _ _ _ t' => String.eqb (sort_name t') "ty"
        | _ => false end).
      assert (Hfin : In (name, term_eq_rule c' e1 e2 t) (filter f ott)).
      { apply filter_In. split; [exact Hin|]. subst f; cbn. rewrite Htyt. reflexivity. }
      vm_compute in Hfin.
      destruct Hfin as [He|[He|[He|[He|[]]]]]; inversion He; subst name c' e1 e2 t; clear He.
      - cbn -[subst_lookup]. f_equal.
        change (term_subst_lookup s1 "l") with (subst_lookup s1 "l").
        change (term_subst_lookup s2 "l") with (subst_lookup s2 "l").
        destruct (IHsub "l" {{s #"lvl"}} eq_refl) as [Hlvl _].
        apply Hlvl. reflexivity.
      - cbn -[subst_lookup]. f_equal.
        change (term_subst_lookup s1 "l") with (subst_lookup s1 "l").
        change (term_subst_lookup s2 "l") with (subst_lookup s2 "l").
        destruct (IHsub "l" {{s #"lvl"}} eq_refl) as [Hlvl _].
        apply Hlvl. reflexivity.
      - cbn -[subst_lookup].
        change (term_subst_lookup s1 "A") with (subst_lookup s1 "A").
        change (term_subst_lookup s2 "A") with (subst_lookup s2 "A").
        destruct (IHsub "A" {{s #"ty" "G3" "i"}} eq_refl) as [_ Hty0].
        apply Hty0. reflexivity.
      - cbn -[subst_lookup].
        change (term_subst_lookup s1 "A") with (subst_lookup s1 "A").
        change (term_subst_lookup s2 "A") with (subst_lookup s2 "A").
        destruct (IHsub "A" {{s #"ty" "G" "i"}} eq_refl) as [_ Hty0].
        apply Hty0. reflexivity. }
  1:{ intros name c' args t s1 s2 Hin Hargs IHargs Hty.
      assert (Htyt : sort_name t = "ty") by (destruct t; cbn in Hty |- *; exact Hty).
      pose (f := fun p : string * rule string =>
        match snd p with
        | term_rule _ _ t' => String.eqb (sort_name t') "ty"
        | _ => false end).
      assert (Hfin : In (name, term_rule c' args t) (filter f ott)).
      { apply filter_In. split; [exact Hin|]. subst f; cbn. rewrite Htyt. reflexivity. }
      vm_compute in Hfin.
      destruct Hfin as [He|[He|[He|[]]]]; inversion He; subst name c' args t; clear He;
        repeat (match goal with
                | H : CutElim.eq_args _ _ _ (_ :: _) _ _ |- _ => inversion H; subst; clear H
                end);
        cbn [code_lvl].
      - match goal with
        | H : CutElim.eq_term _ _ _ {{s #"lvl"}} [/_/] ?a ?b |- _ =>
            assert (Hr : a = b) by
              (eapply cut_eq_term_ott_rl_syntactic; [ exact H | right; reflexivity ]); rewrite Hr
        end. reflexivity.
      - match goal with
        | H : CutElim.eq_term _ _ _ {{s #"lvl"}} [/_/] ?a ?b |- _ =>
            assert (Hr : a = b) by
              (eapply cut_eq_term_ott_rl_syntactic; [ exact H | right; reflexivity ]); rewrite Hr
        end. reflexivity.
      - destruct (IHargs 0 "A" {{s #"ty" "G'" "i"}} e1 e2 eq_refl eq_refl eq_refl) as [_ Hty0].
        rewrite (Hty0 eq_refl). reflexivity. }
  1:{ intros n t Hin Hty. reflexivity. }
  1:{ intros t e1 e12 e2 _ H1 _ H2 Hty. rewrite H1 by assumption. apply H2; assumption. }
  1:{ intros t e1 e2 _ H Hty. symmetry. apply H; assumption. }
  1:{ intros e1 e2 t t' _ IH Hsort _ Hty'.
      apply IH. apply cut_eq_sort_ott_same_name in Hsort.
      destruct t as [tn ts], t' as [tn' ts']. cbn [sort_name] in *. congruence. }
  1:{ intros x t Hl. cbn in Hl. discriminate. }
  1:{ intros c' s1 s2 Hsub IHsub name t e1 e2 Hhead IHhead.
      intros x t0 Hl. cbn in Hl.
      destruct (eqb x name) eqn:Hx.
      - inversion Hl; subst t0; clear Hl.
        unfold subst_lookup. cbn [named_list_lookup]. rewrite Hx.
        assert (Hsn : sort_name (t [/s2/]) = sort_name t) by (destruct t; reflexivity).
        split; intro Hs.
        + eapply cut_eq_term_ott_rl_syntactic; [exact Hhead | rewrite Hsn; right; exact Hs].
        + apply IHhead. rewrite Hsn. exact Hs.
      - unfold subst_lookup. cbn [named_list_lookup]. rewrite Hx.
        fold (subst_lookup s1 x). fold (subst_lookup s2 x).
        eapply IHsub; eassumption. }
  1:{ intros n name t a b Hc. destruct n; cbn in Hc; discriminate. }
  1:{ intros c' es1 es2 Hargs IHargs name t e1 e2 Hhead IHhead.
      intros n nm t0 a b Hc Ha Hb.
      destruct n.
      - cbn in Hc, Ha, Hb. inversion Hc; subst nm t0; clear Hc.
        inversion Ha; subst a; clear Ha. inversion Hb; subst b; clear Hb.
        assert (Hsn : sort_name (t [/with_names_from c' es2/]) = sort_name t)
          by (destruct t; reflexivity).
        split; intro Hs.
        + eapply cut_eq_term_ott_rl_syntactic; [exact Hhead | rewrite Hsn; right; exact Hs].
        + apply IHhead. rewrite Hsn. exact Hs.
      - cbn in Hc, Ha, Hb. eapply IHargs; eassumption. }
Qed.

Lemma core_sort_lvl_invariant : forall c t1 t2,
  eq_sort ott c t1 t2 -> sort_lvl t1 = sort_lvl t2.
Proof.
  intros c t1 t2 Hcore.
  assert (Hcut : CutElim.wf_lang _ ott).
  { apply CutElim.wf_lang_iff_cut; [ typeclasses eauto | typeclasses eauto | exact ott_wf ]. }
  pose proof (CutElim.core_implies_cut _ ott Hcut) as Himpl.
  destruct Himpl as [Hsort _].
  apply Hsort in Hcore.
  destruct (cut_code_lvl_invariant c) as [Hinv _].
  apply Hinv. exact Hcore.
Qed.

(* THE DISCHARGED OBLIGATION (level side): two code sorts at the distinct
   level constants oL1 / oL0 are NOT eq_sort-related. *)
Lemma code_sort_lvl_neq_L1_L0 : forall c rF rG G G',
  ~ eq_sort ott c (code_sort rF (con "L1" []) G) (code_sort rG oL0 G').
Proof.
  intros c rF rG G G' H.
  apply core_sort_lvl_invariant in H.
  unfold code_sort, sort_lvl, oU, code_lvl, oL0 in H.
  cbn in H. discriminate.
Qed.

(* ====================================================================== *)
(* STEP 3 (plan (A)): the mutual ESCAPE/REFLECT lemma + the VR layer.       *)
(*                                                                        *)
(* The motive `Pmot` (= esc_ty * esc_tm * reflect_at), validated in        *)
(* WIP/MutualFund.v, is ported here where `l := ott`.  `elt_sort` reads the *)
(* canonical MEMBER sort off the `RedTy_tot` constructor; esc_ty/esc_tm/   *)
(* reflect_at are stated at that sort.  The three non-Pi LEAVES are        *)
(* discharged by the standalone escape/reflect leaves above.  The Pi case  *)
(* of the mutual lemma is entangled with the bound-variable reflect (z9)   *)
(* and is built in the VR / typing-induction layer below.                  *)
(* ====================================================================== *)

(* The canonical element sort of a reducible type, read off the constructor.
   reflect / escape_tm are stated at this sort. *)
Definition elt_sort {G A B} (r : RedTy ott G A B) : osort :=
  match projT2 r with
  | rtt_nat _ G _ _ _ _ => nat_sort G
  | rtt_empty _ G _ _ _ _ => empty_sort G
  | rtt_ne _ G _ _ na _ rN lN _ _ _ => el_sort rN lN G na
  | rtt_pi _ G _ _ rF lF lG F C _ _ _ _ _ _ _ _ =>
      s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))
  end.

Lemma elt_sort_nat (G A B : tm) (ra : RNat ott G A) (rb : RNat ott G B)
  : elt_sort (RedTy_nat ott ra rb) = nat_sort G.
Proof. reflexivity. Qed.

Lemma elt_sort_empty (G A B : tm) (ra : REmpty ott G A) (rb : REmpty ott G B)
  : elt_sort (RedTy_empty ott ra rb) = empty_sort G.
Proof. reflexivity. Qed.

Lemma elt_sort_ne (G A B na nb rN lN : tm) (ra : reds string ott ott_pa A na)
  (rb : reds string ott ott_pa B nb)
  (h : ne_eq string ott ott_pa (code_sort rN lN G) na nb)
  : elt_sort (@RedTy_ne ott G A B na nb rN lN ra rb h) = el_sort rN lN G na.
Proof. reflexivity. Qed.

Lemma elt_sort_pi (G A B rF lF lG F C F' C' : tm)
  (hA : reds string ott ott_pa A (oPi_rel rF lF lG F C G))
  (hB : reds string ott ott_pa B (oPi_rel rF lF lG F' C' G))
  (DomRed : forall D g (os : osub ott G D g),
      RedTy ott D (act_code rF lF g G D F) (act_code rF lF g G D F'))
  (CodRed : forall D g (os : osub ott G D g) a a',
      RedTm ott (DomRed D g os) a a' ->
      RedTy ott D (cod_at rF lF lG g G D F C a) (cod_at rF lF lG g G D F' C' a'))
  : elt_sort (RedTy_pi ott hA hB DomRed CodRed)
    = s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G)).
Proof. reflexivity. Qed.

(* ---- the three components of the motive ---- *)
Definition esc_ty {G A B} (r : RedTy ott G A B) : Prop :=
  forall S, wf_term ott [] A S -> wf_term ott [] B S -> eq_term ott [] S A B.

Definition esc_tm {G A B} (r : RedTy ott G A B) : Prop :=
  forall a b, RedTy_R ott r a b ->
    wf_term ott [] a (elt_sort r) -> wf_term ott [] b (elt_sort r) ->
    eq_term ott [] (elt_sort r) a b.

Definition reflect_at {G A B} (r : RedTy ott G A B) : Type :=
  forall a b, neutral ott_pa a -> neutral ott_pa b ->
    wf_term ott [] a (elt_sort r) -> wf_term ott [] b (elt_sort r) ->
    eq_term ott [] (elt_sort r) a b -> RedTy_R ott r a b.

Definition Pmot (G A B : tm) (r : RedTy ott G A B) : Type :=
  (esc_ty r * esc_tm r * reflect_at r)%type.

(* ---- LEAF: Nat ---- *)
Lemma leaf_nat (G A B : tm) (ra : RNat ott G A) (rb : RNat ott G B)
  : Pmot G A B (RedTy_nat ott ra rb).
Proof.
  unfold Pmot, esc_ty, esc_tm, reflect_at; rewrite !elt_sort_nat.
  repeat split.
  - (* escape_ty *) intros S HA HB. eapply RedTy_Nat_sound; eassumption.
  - (* escape_tm *) intros a b Hm Ha Hb.
    change (RedTy_R ott (RedTy_nat ott ra rb) a b) with (RedNatMem ott G a b) in Hm.
    eapply RedNatMem_sound; eassumption.
  - (* reflect *) intros a b Hna Hnb Ha Hb Heq.
    change (RedTy_R ott (RedTy_nat ott ra rb) a b) with (RedNatMem ott G a b).
    apply RedNatMem_reflect; repeat split; eassumption.
Qed.

(* ---- LEAF: Empty ---- *)
Lemma leaf_empty (G A B : tm) (ra : REmpty ott G A) (rb : REmpty ott G B)
  : Pmot G A B (RedTy_empty ott ra rb).
Proof.
  unfold Pmot, esc_ty, esc_tm, reflect_at; rewrite !elt_sort_empty.
  repeat split.
  - intros S HA HB. eapply RedTy_Empty_sound; eassumption.
  - intros a b Hm Ha Hb.
    change (RedTy_R ott (RedTy_empty ott ra rb) a b) with (RedNe ott (empty_sort G) a b) in Hm.
    eapply RedNe_sound_at; eassumption.
  - intros a b Hna Hnb Ha Hb Heq.
    change (RedTy_R ott (RedTy_empty ott ra rb) a b) with (RedNe ott (empty_sort G) a b).
    apply RedNe_reflect; repeat split; eassumption.
Qed.

(* ---- LEAF: neutral code ---- *)
Lemma leaf_ne (G A B na nb rN lN : tm) (ra : reds string ott ott_pa A na)
  (rb : reds string ott ott_pa B nb)
  (h : ne_eq string ott ott_pa (code_sort rN lN G) na nb)
  : Pmot G A B (@RedTy_ne ott G A B na nb rN lN ra rb h).
Proof.
  unfold Pmot, esc_ty, esc_tm, reflect_at; rewrite !elt_sort_ne.
  repeat split.
  - (* escape_ty: type codes A,B reduce to ne_eq codes na,nb at the U code-sort *)
    intros S HA HB. eapply RedNe_sound_at with (t:=code_sort rN lN G);
      [ eapply red_ne; eassumption | eassumption | eassumption ].
  - (* escape_tm: members reduce to ne_eq neutrals at El na *)
    intros a b Hm Ha Hb.
    change (RedTy_R ott (@RedTy_ne ott G A B na nb rN lN ra rb h) a b)
      with (RedNe ott (el_sort rN lN G na) a b) in Hm.
    eapply RedNe_sound_at; eassumption.
  - (* reflect: a neutral pair at El na is a neutral member *)
    intros a b Hna Hnb Ha Hb Heq.
    change (RedTy_R ott (@RedTy_ne ott G A B na nb rN lN ra rb h) a b)
      with (RedNe ott (el_sort rN lN G na) a b).
    apply RedNe_reflect; repeat split; eassumption.
Qed.

(* ====================================================================== *)
(* VR-layer groundwork: reduction is a CONGRUENCE at the principal arg of   *)
(* `exp_subst` (index 0 = the substituted code/term).  This is the          *)
(* substrate of the Kripke ACTION soundness the Pi case needs: the          *)
(* `act_code`/`act_member` of a reduct is a reduct, so a domain/codomain    *)
(* code that reduces-to-whnf still reduces-to-whnf after being pushed along  *)
(* an object substitution `g`.  Generic over the tail args (the type/info/   *)
(* env annotations of `exp_subst`), so it applies to both `act_code`         *)
(* (code push) and `act_member` (member push).                              *)
(* ====================================================================== *)
Lemma whstep_exp_subst_cong A A' rest
  : OperationalBridge.star (whstep string ott ott_pa) A A' ->
    OperationalBridge.star (whstep string ott ott_pa)
      (con "exp_subst" (A :: rest)) (con "exp_subst" (A' :: rest)).
Proof.
  intro H. induction H.
  - constructor.
  - eapply OperationalBridge.star_step.
    + exact IHstar.
    + eapply (whstep_congr string ott ott_pa "exp_subst" (b :: rest) 0 b c).
      * reflexivity.
      * reflexivity.
      * exact H0.
Qed.

(* The Kripke push of a term that weak-head reduces to `w` weak-head reduces
   to the push of `w` (one `exp_subst`-congruence run).  `act_code`/`act_member`
   are both `oexp_subst _ _ _ g G' G` with the pushed term at index 0, so this
   covers both.  (whnf of the pushed `w` is supplied by the caller — a pushed
   whnf may itself be a redex, e.g. `exp_subst g (Nat) -> Nat`, so the caller
   chains one more `reds` step to the true whnf.) *)
Lemma star_act_code rF lF g G D A w
  : OperationalBridge.star (whstep string ott ott_pa) A w ->
    OperationalBridge.star (whstep string ott ott_pa)
      (act_code rF lF g G D A) (act_code rF lF g G D w).
Proof.
  intro H. unfold act_code, oexp_subst. apply whstep_exp_subst_cong. exact H.
Qed.

Lemma star_act_member rF lF lG g G D F C f w
  : OperationalBridge.star (whstep string ott ott_pa) f w ->
    OperationalBridge.star (whstep string ott ott_pa)
      (act_member rF lF lG g G D F C f) (act_member rF lF lG g G D F C w).
Proof.
  intro H. unfold act_member, oexp_subst. apply whstep_exp_subst_cong. exact H.
Qed.

(* ---- Kripke action soundness LEAVES: Nat / Empty domains ---- *)
(* A code that reduces to `Nat G` (resp. `Empty G`), pushed along an object
   substitution `g : sub G D`, reduces to `Nat D` (resp. `Empty D`).  The
   relevance/level of the `act_code` wrapper is forced to `orel/oL0` (resp.
   `oirr/oL0`) for the subst redex to fire — exactly the relevance/level of the
   Nat (resp. Empty) code.  These build the Pi case's `DomRed` field when the
   domain is Nat / Empty (the bound-var reflect then bridges the canonical sort
   to the Pi former's symbolic `rF/lF` via the distinctness lemmas above). *)
Lemma whstep_Nat_subst g G D
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (Hg : osub ott G D g)
  : whstep string ott ott_pa
      (act_code orel oL0 g G D (oNat G)) (oNat D).
Proof.
  apply whstep_redex.
  unfold redex.
  exists "Nat subst",
    [("g", {{s #"sub" "G" "G'"}}); ("G'", {{s #"env"}}); ("G", {{s #"env"}})],
    {{e #"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" #"L0")) (#"U" "G'" #"rel" #"L0") (#"Nat" "G'")}},
    {{e #"Nat" "G"}},
    {{s #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" "G" #"rel" #"L0")}},
    [("g", g); ("G'", G); ("G", D)].
  split; [| split; [| split]].
  - apply named_list_lookup_err_in; compute; reflexivity.
  - simple apply wf_subst_cons.
    + simple apply wf_subst_cons.
      * simple apply wf_subst_cons.
        -- simple apply wf_subst_nil.
        -- cbn [Model.wf_term core_model]. exact HD.
      * cbn [Model.wf_term core_model]. exact HG.
    + cbn [Model.wf_term core_model]. unfold osub in Hg. cbn. exact Hg.
  - vm_compute. unfold act_code, oexp_subst, oNat, oU, code_info, oinfo, onext, orel, oL0. reflexivity.
  - vm_compute. unfold oNat. reflexivity.
Qed.

Lemma RNat_act g G D A
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (Hg : osub ott G D g)
  : RNat ott G A -> RNat ott D (act_code orel oL0 g G D A).
Proof.
  intros [Hstar Hwhnf].
  unfold RNat, reds. split.
  - eapply star_trans.
    + eapply star_act_code. exact Hstar.
    + eapply OperationalBridge.star_step.
      * apply OperationalBridge.star_refl.
      * apply whstep_Nat_subst; assumption.
  - apply whnf_Nat.
Qed.

Lemma whstep_Empty_subst g G D
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (Hg : osub ott G D g)
  : whstep string ott ott_pa
      (act_code oirr oL0 g G D (oEmpty G)) (oEmpty D).
Proof.
  apply whstep_redex.
  unfold redex.
  exists "Empty subst",
    [("g", {{s #"sub" "G" "G'"}}); ("G'", {{s #"env"}}); ("G", {{s #"env"}})],
    {{e #"exp_subst" "G" "G'" "g" (#"info" #"rel" (#"next" #"L0")) (#"U" "G'" #"irr" #"L0") (#"Empty" "G'")}},
    {{e #"Empty" "G"}},
    {{s #"exp" "G" (#"info" #"rel" (#"next" #"L0")) (#"U" "G" #"irr" #"L0")}},
    [("g", g); ("G'", G); ("G", D)].
  split; [| split; [| split]].
  - apply named_list_lookup_err_in; compute; reflexivity.
  - simple apply wf_subst_cons.
    + simple apply wf_subst_cons.
      * simple apply wf_subst_cons.
        -- simple apply wf_subst_nil.
        -- cbn [Model.wf_term core_model]. exact HD.
      * cbn [Model.wf_term core_model]. exact HG.
    + cbn [Model.wf_term core_model]. unfold osub in Hg. cbn. exact Hg.
  - vm_compute. unfold act_code, oexp_subst, oEmpty, oU, code_info, oinfo, onext, orel, oirr, oL0. reflexivity.
  - vm_compute. unfold oEmpty. reflexivity.
Qed.

Lemma REmpty_act g G D A
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (Hg : osub ott G D g)
  : REmpty ott G A -> REmpty ott D (act_code oirr oL0 g G D A).
Proof.
  intros [Hstar Hwhnf].
  unfold REmpty, reds. split.
  - eapply star_trans.
    + eapply star_act_code. exact Hstar.
    + eapply OperationalBridge.star_step.
      * apply OperationalBridge.star_refl.
      * apply whstep_Empty_subst; assumption.
  - apply whnf_Empty.
Qed.

(* ---- Kripke action soundness LEAF: neutral type code ---- *)
(* A pushed neutral code stays neutral: `act_code` is `exp_subst` with the code
   at principal arg 0, so `neutral_elim i=0` preserves neutrality. *)
Lemma act_code_neutral rF lF g G D F
  : neutral ott_pa F -> neutral ott_pa (act_code rF lF g G D F).
Proof.
  intro HF; unfold act_code, oexp_subst.
  eapply neutral_elim with (i:=0); [ reflexivity | reflexivity | exact HF ].
Qed.

(* The neutral type-code conversion `ne_eq (code_sort rN lN G) na nb` is pushed
   along `g : sub G D`: the `exp_subst` term-former congruence on the two codes
   gives an `eq_term` at the `exp_subst` result sort, which converts to
   `code_sort rN lN D` via the "U subst" computation rule (`U_subst_eq`). *)
Lemma eq_term_act_code rN lN g G D na nb
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrN : wf_term ott [] rN (scon "relevance" []))
  (HlN : wf_term ott [] lN (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (Hna : wf_term ott [] na (code_sort rN lN G))
  (Hnb : wf_term ott [] nb (code_sort rN lN G))
  (Heq : eq_term ott [] (code_sort rN lN G) na nb)
  : eq_term ott [] (code_sort rN lN D)
      (act_code rN lN g G D na) (act_code rN lN g G D nb).
Proof.
  pose proof ott_wf as Hwf.
  unfold act_code, oexp_subst, code_sort.
  eapply eq_term_conv.
  - (* exp_subst term-former congruence; ctx order [v;A;i;g;G';G] *)
    eapply term_con_congruence.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + right. cbn [with_names_from]. reflexivity.
    + exact Hwf.
    + cbn [with_names_from].
      eapply eq_args_cons.
      2:{ exact Heq. }                                    (* v : the two codes *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. cbn [Model.wf_term core_model].
          unfold oU. ott_wf_args. }                       (* A : U rN lN G *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. cbn [Model.wf_term core_model].
          unfold code_info, oinfo, onext. ott_wf_args. }   (* i : code_info lN *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. exact Hg. }                  (* g : sub D G *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. exact HG. }                  (* G' : G *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. exact HD. }                  (* G : D *)
      eapply eq_args_nil.
  - (* result sort `exp D (code_info lN) (ty_subst D G g (code_info lN)(U rN lN G))`
       converts to `exp D (code_info lN) (U rN lN D)` via U_subst_eq.
       NB sort_con_congruence puts Eqb_ok FIRST. *)
    cbn [with_names_from].
    eapply sort_con_congruence.
    + typeclasses eauto.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + exact Hwf.
    + cbn [with_names_from].
      eapply eq_args_cons.
      2:{ apply U_subst_eq; assumption. }                  (* A : the ty_subst *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. cbn [Model.wf_term core_model].
          unfold code_info, oinfo, onext. ott_wf_args. }   (* i : code_info lN *)
      eapply eq_args_cons.
      2:{ eapply eq_term_refl. exact HD. }                  (* G : D *)
      eapply eq_args_nil.
Qed.

(* Kripke action soundness LEAF for the neutral type code: a code `A` that
   reduces to a neutral code `na` (ne_eq at the U code-sort) pushes along
   `g : sub G D` to a `RedTy D` between the two pushed codes.  No subst redex
   fires (the pushed neutral is itself whnf); the `ne_eq` is transported by
   `eq_term_act_code`.  This is the Pi case's `DomRed` field when the domain is
   a neutral code. *)
Lemma RNe_act g G D A B na nb rN lN
  (HG : wf_term ott [] G s_env)
  (HD : wf_term ott [] D s_env)
  (HrN : wf_term ott [] rN (scon "relevance" []))
  (HlN : wf_term ott [] lN (scon "lvl" []))
  (Hg : wf_term ott [] g (s_sub D G))
  (Hna : wf_term ott [] na (code_sort rN lN G))
  (Hnb : wf_term ott [] nb (code_sort rN lN G))
  (ra : reds string ott ott_pa A na)
  (rb : reds string ott ott_pa B nb)
  (h : ne_eq string ott ott_pa (code_sort rN lN G) na nb)
  : RedTy ott D (act_code rN lN g G D A) (act_code rN lN g G D B).
Proof.
  destruct h as (Hnna & Hnnb & Hconv).
  eapply (@RedTy_ne ott D _ _
            (act_code rN lN g G D na) (act_code rN lN g G D nb) rN lN).
  - (* reds (act_code A) (act_code na) *)
    unfold reds. split.
    + eapply star_act_code. eapply reds_star. exact ra.
    + apply neutral_whnf. apply act_code_neutral. exact Hnna.
  - (* reds (act_code B) (act_code nb) *)
    unfold reds. split.
    + eapply star_act_code. eapply reds_star. exact rb.
    + apply neutral_whnf. apply act_code_neutral. exact Hnnb.
  - (* ne_eq (code_sort rN lN D) (act_code na) (act_code nb) *)
    unfold ne_eq. repeat split.
    + apply act_code_neutral. exact Hnna.
    + apply act_code_neutral. exact Hnnb.
    + apply eq_term_act_code; assumption.
Qed.

(* TODO (file 4 body, continued) — STEP 3 remaining (the typing-induction
   fundamental lemma):
   - The mutual ESCAPE/REFLECT lemma (Pmot) Pi case + the hard direction
     (typing-derivation induction producing RedTy/RedTm), structured by
     `wf_judge_ind` with a substitution-generalized motive keyed on the
     sort's object env (P [] e (code_sort r l G') := forall D g, osub G' D g ->
     RedTy D e[g] e[g]).  The Pi case builds DomRed/CodRed from the args-IH on
     F / C; the bound-var reflect consumes relevance_canon / lvl_canon +
     code_sort_rel_neq_irr / code_sort_lvl_neq_L1_L0 to discharge rF=orel /
     lF=oL0 (or proof-irrelevance for an irrelevant domain).
   - Kripke action soundness for the Nat/Empty/Ne leaves uses
     star_act_code (above) + the per-former subst redex (Nat subst / Empty
     subst / exp_subst-of-neutral). *)
