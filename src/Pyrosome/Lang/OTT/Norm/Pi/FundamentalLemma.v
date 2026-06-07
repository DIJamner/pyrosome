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

(* TODO (file 4 body, continued):
   - The full under'-lift Kripke-builder cluster is now TYPED
     (act_code/El_act_code/wkn/cmp/ounder/act_cod/cod_at/act_member/mapp), so the
     LogicalRelation.v RedTy_tot Pi case is fully discharged on the syntax side.
   - NEXT: the fundamental lemma proper:
       wf_term ott [] e t -> reducible e   (and the eq_term -> RedTm PER side),
     by Pyrosome cut-elimination on canonical derivations; discharges the
     Pi reflect/reify eta crux.
   - then the fundamental lemma proper:
       wf_term ott [] e t -> reducible e   (and the eq_term -> RedTm PER side),
     by Pyrosome cut-elimination on canonical derivations; discharges the
     Pi reflect/reify eta crux. *)
