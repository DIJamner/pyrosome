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

(* TODO (file 4 body, continued):
   - remaining under'-lift cluster: `cod_at` (instantiate `act_cod` at the
     argument via `snoc a id`, reusing `act_cod_wf` + a "ty_subst_id"
     conversion), then `act_member` (naive `exp_subst` type converted via a
     "Pi_rel subst" analogue) and `mapp` (`app_rel` over the three).
   - then the fundamental lemma proper:
       wf_term ott [] e t -> reducible e   (and the eq_term -> RedTm PER side),
     by Pyrosome cut-elimination on canonical derivations; discharges the
     Pi reflect/reify eta crux. *)
