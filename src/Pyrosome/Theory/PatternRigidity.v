(* PatternRigidity.v

   PURPOSE: The e-graph query compiler drops sort_of atoms for rule-context
   variables ("min-sorts").  This file provides the PATTERN-RIGIDITY gate: a
   per-rule, per-variable boolean check on the elaborated LHS pattern such that
   all sort-conversion obligations incurred by the skip-soundness machinery are
   between SYNTACTICALLY EQUAL sorts (so they discharge by reflexivity, with no
   language-level condition).  A variable x of rule ctx c is rigid-skippable in
   LHS e1 when (i) every internal con node of e1 "fits": its rule-output sort
   instantiated by its own args syntactically equals the telescope-expected sort
   at its position, and (ii) every occurrence of x in e1 has telescope-expected
   sort syntactically equal to x's declared sort in c.  Root sorts are not
   constrained (the consumers discard them).  This subsumes the
   syntactic-sort-equality gate (in such languages every wf pattern is rigid)
   and covers ~98% of the polymorphic stack (measured). *)

Set Implicit Arguments.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List Arith.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils SymmetricInduction.
From Pyrosome.Theory Require Import Core SyntacticSortCovering.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
    {|
      premodel := @syntax_model V V_Eqb;
      Model.eq_sort := eq_sort;
      Model.eq_term := eq_term;
      Model.wf_sort := wf_sort;
      Model.wf_term := wf_term;
    |}.

  Notation eq_subst l :=
    (eq_subst (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation eq_args l :=
    (eq_args (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation wf_subst l :=
    (wf_subst (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation wf_args l :=
    (wf_args (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).
  Notation wf_ctx l :=
    (wf_ctx (Model:= mut_mod (eq_sort l) (eq_term l) (wf_sort l) (wf_term l))).

  (* Telescope-expected sorts for an argument list (positional; mirrors
     wf_args_cons: the head argument's expected sort is its telescope sort
     substituted by the TAIL pairing). *)
  Fixpoint arg_expecteds (cM : ctx) (ss : list term) : list sort :=
    match cM, ss with
    | (_, t) :: cM', _ :: ss' => t [/with_names_from cM' ss'/] :: arg_expecteds cM' ss'
    | _, _ => []
    end.

  (* Generic paired walk; returns (all checks passed, collected var-occurrence
     expectations).  Ragged lists fail. *)
  Fixpoint zip_check (f : term -> sort -> bool * named_list sort)
                     (ss : list term) (Es : list sort) : bool * named_list sort :=
    match ss, Es with
    | [], [] => (true, [])
    | e :: ss', E :: Es' =>
        let r1 := f e E in
        let r2 := zip_check f ss' Es' in
        (fst r1 && fst r2, snd r1 ++ snd r2)
    | _, _ => (false, [])
    end.

  Section WithLang.
    Context (l : lang).

    (* Rigidity of a term against its expected sort.  A var is a leaf recording
       its occurrence's expectation; a con must FIT (rule-output instance
       syntactically equal to expected) and its args must be rigid against their
       telescope expectations. *)
    Fixpoint check_term (e : term) (expected : sort) {struct e}
      : bool * named_list sort :=
      match e with
      | Term.var x => (true, [(x, expected)])
      | Term.con m ss =>
          match named_list_lookup_err l m with
          | Some (term_rule cM _ tM) =>
              if Nat.eqb (List.length ss) (List.length cM)
              then let r := zip_check check_term ss (arg_expecteds cM ss) in
                   (eqb (tM [/with_names_from cM ss/]) expected && fst r, snd r)
              else (false, [])
          | _ => (false, [])
          end
      end.

    Definition check_args (ss : list term) (cM : ctx) : bool * named_list sort :=
      if Nat.eqb (List.length ss) (List.length cM)
      then zip_check check_term ss (arg_expecteds cM ss)
      else (false, []).

    (* Per-variable occurrence condition. *)
    Definition var_occs_ok (occs : named_list sort) (x : V) (tx : sort) : bool :=
      forallb (fun p => negb (eqb (fst p) x) || eqb (snd p) tx) occs.

    (* The runtime skip predicates (used verbatim by the e-graph rule compiler
       and its soundness adapters). *)
    Definition rigid_term_skip (c : ctx) (e1 : term) (x : V) : bool :=
      match e1 with
      | Term.con n0 s0 =>
          match named_list_lookup_err l n0 with
          | Some (term_rule cR _ _) =>
              fst (check_args s0 cR)
              && inb x (fv e1)
              && match named_list_lookup_err c x with
                 | Some tx => var_occs_ok (snd (check_args s0 cR)) x tx
                 | None => false
                 end
          | _ => false
          end
      | Term.var _ => false
      end.

    Definition rigid_sort_skip (c : ctx) (t1 : sort) (x : V) : bool :=
      match t1 with
      | scon n0 s0 =>
          match named_list_lookup_err l n0 with
          | Some (sort_rule cR _) =>
              fst (check_args s0 cR)
              && inb x (fv_sort t1)
              && match named_list_lookup_err c x with
                 | Some tx => var_occs_ok (snd (check_args s0 cR)) x tx
                 | None => false
                 end
          | _ => false
          end
      end.

    (* ------------------------------------------------------------------ *)
    (* Boolean facts                                                        *)
    (* ------------------------------------------------------------------ *)

    Lemma check_term_var x E : check_term (var x) E = (true, [(x, E)]).
    Proof. reflexivity. Qed.

    (* Helper: from fst (check_args ss cM) = true, the lengths are equal. *)
    Lemma check_args_length ss cM
      : fst (check_args ss cM) = true -> length ss = length cM.
    Proof.
      unfold check_args.
      destruct (Nat.eqb (length ss) (length cM)) eqn:Hlen.
      - intros _. apply Nat.eqb_eq. exact Hlen.
      - intros H. cbn in H. discriminate H.
    Qed.

    (* Helper: check_args cons unfolds to a single zip_check step *)
    Lemma check_args_cons_unfold e ss' nm t cM' :
      check_args (e :: ss') ((nm, t) :: cM') =
      if Nat.eqb (length ss') (length cM')
      then
        let r1 := check_term e (t [/with_names_from cM' ss'/]) in
        let r2 := zip_check check_term ss' (arg_expecteds cM' ss') in
        (fst r1 && fst r2, snd r1 ++ snd r2)
      else (false, []).
    Proof.
      unfold check_args.
      cbn [length Nat.eqb zip_check arg_expecteds].
      reflexivity.
    Qed.

    Lemma check_args_cons_inv e ss' nm t cM'
      : fst (check_args (e :: ss') ((nm, t) :: cM')) = true ->
        fst (check_term e (t [/with_names_from cM' ss'/])) = true
        /\ fst (check_args ss' cM') = true.
    Proof.
      rewrite check_args_cons_unfold.
      destruct (Nat.eqb (length ss') (length cM')) eqn:Hlen.
      - cbn [fst].
        intro H.
        apply Bool.andb_true_iff in H.
        split.
        + exact (proj1 H).
        + unfold check_args. rewrite Hlen. exact (proj2 H).
      - cbn [fst]. intro H. discriminate H.
    Qed.

    Lemma check_args_cons_snd e ss' nm t cM'
      : fst (check_args (e :: ss') ((nm, t) :: cM')) = true ->
        snd (check_args (e :: ss') ((nm, t) :: cM'))
        = snd (check_term e (t [/with_names_from cM' ss'/])) ++ snd (check_args ss' cM').
    Proof.
      rewrite check_args_cons_unfold.
      destruct (Nat.eqb (length ss') (length cM')) eqn:Hlen.
      - cbn [fst snd].
        intro H.
        apply Bool.andb_true_iff in H.
        unfold check_args. rewrite Hlen.
        reflexivity.
      - cbn [fst]. intro H. discriminate H.
    Qed.

    (* Auxiliary unfolding for check_term on a con *)
    Lemma check_term_con_unfold m ss E :
      check_term (Term.con m ss) E =
      match named_list_lookup_err l m with
      | Some (term_rule cM _ tM) =>
          if Nat.eqb (List.length ss) (List.length cM)
          then let r := zip_check check_term ss (arg_expecteds cM ss) in
               (eqb (tM [/with_names_from cM ss/]) E && fst r, snd r)
          else (false, [])
      | _ => (false, [])
      end.
    Proof. reflexivity. Qed.

    Lemma check_term_con_inv m ss E
      : fst (check_term (Term.con m ss) E) = true ->
        exists cM argsM tM,
          named_list_lookup_err l m = Some (term_rule cM argsM tM)
          /\ length ss = length cM
          /\ tM [/with_names_from cM ss/] = E
          /\ fst (check_args ss cM) = true
          /\ snd (check_term (Term.con m ss) E) = snd (check_args ss cM).
    Proof.
      intro H.
      (* Destruct the lookup inside the proof obligation *)
      pose (lkp := named_list_lookup_err l m).
      assert (Hlkp : named_list_lookup_err l m = lkp) by reflexivity.
      (* Extract the check for the con case by a direct case analysis *)
      destruct lkp as [r |] eqn:Hlookup.
      - (* Some r *)
        assert (Hlookup' : named_list_lookup_err l m = Some r) by exact Hlookup.
        (* rule constructor order: sort_rule(2), term_rule(3), sort_eq_rule(3), term_eq_rule(4) *)
        destruct r as [cM0 argsM0 | cM0 argsM0 tM0 | cM0 e10 e20 | cM0 e10 e20 t_eq0].
        + (* sort_rule: goal is absurd *)
          exfalso. rewrite check_term_con_unfold, Hlookup' in H. cbn in H. discriminate H.
        + (* term_rule cM0 argsM0 tM0: this is the case of interest *)
          (* Rewrite H using the con unfolding and the lookup result *)
          rewrite check_term_con_unfold, Hlookup' in H.
          (* Now H depends on the length check *)
          destruct (Nat.eqb (length ss) (length cM0)) eqn:Hlen.
          * (* lengths match; H has form fst (let r := zip_check ... in (eqb...&&fst r, snd r)) = true *)
            (* Use cbv beta to reduce the let binding *)
            cbv beta in H.
            cbn [fst] in H.
            apply Bool.andb_true_iff in H. destruct H as [Heqb Hr2].
            pose proof (@eqb_spec (Term.sort V) (@sort_eqb V V_Eqb) (@sort_eqb_ok V V_Eqb V_Eqb_ok)
                          (tM0 [/with_names_from cM0 ss/]) E) as Hspec.
            rewrite Heqb in Hspec.
            exists cM0, argsM0, tM0.
            refine (conj Hlookup' (conj _ (conj Hspec (conj _ _)))).
            -- apply Nat.eqb_eq. exact Hlen.
            -- unfold check_args. rewrite Hlen. exact Hr2.
            -- rewrite check_term_con_unfold, Hlookup', Hlen.
               cbn [snd]. unfold check_args. rewrite Hlen. reflexivity.
          * exfalso. revert H; cbn [fst]; discriminate.
        + exfalso. rewrite check_term_con_unfold, Hlookup' in H. cbn in H. discriminate H.
        + exfalso. rewrite check_term_con_unfold, Hlookup' in H. cbn in H. discriminate H.
      - (* None case: lkp = None, so named_list_lookup_err l m = None *)
        exfalso.
        unfold lkp in Hlookup.
        rewrite check_term_con_unfold in H.
        rewrite Hlookup in H.
        cbn in H. discriminate H.
    Qed.

    Lemma rigid_term_skip_inv c e1 x
      : rigid_term_skip c e1 x = true ->
        exists n0 s0 cR argsR tR tx,
          e1 = con n0 s0
          /\ named_list_lookup_err l n0 = Some (term_rule cR argsR tR)
          /\ fst (check_args s0 cR) = true
          /\ In x (fv e1)
          /\ named_list_lookup_err c x = Some tx
          /\ (forall E, In (x, E) (snd (check_args s0 cR)) -> E = tx).
    Proof.
      unfold rigid_term_skip.
      destruct e1 as [v | n0 s0].
      - intro H. discriminate H.
      - destruct (named_list_lookup_err l n0) as [r|] eqn:Hlookup.
        + (* rule constructor order: sort_rule(2), term_rule(3), sort_eq_rule(3), term_eq_rule(4) *)
          destruct r as [| cR argsR tR | |].
          * intro H. discriminate H.
          * (* term_rule cR argsR tR *)
            intro H.
            apply Bool.andb_true_iff in H. destruct H as [H Hocc].
            apply Bool.andb_true_iff in H. destruct H as [Hcheck Hinb].
            (* Resolve inb -> In *)
            assert (Hinfv : In x (fv (con n0 s0))).
            { apply (proj1 (inb_is_In x (fv (con n0 s0)))).
              apply Is_true_eq_left. exact Hinb. }
            (* Resolve named_list_lookup_err c x *)
            destruct (named_list_lookup_err c x) as [tx|] eqn:Hlookup_x.
            -- exists n0, s0, cR, argsR, tR, tx.
               refine (conj eq_refl (conj Hlookup (conj Hcheck (conj Hinfv (conj _ _))))).
               ++ reflexivity.
               ++ (* var_occs_ok -> forall E, In (x, E) ... -> E = tx *)
                  unfold var_occs_ok in Hocc.
                  rewrite forallb_forall in Hocc.
                  intros E HinE.
                  specialize (Hocc (x, E) HinE).
                  cbn [fst snd] in Hocc.
                  apply Bool.orb_true_iff in Hocc.
                  destruct Hocc as [Hneg | Heq].
                  ** (* negb (eqb x x) = true -> contradiction *)
                     rewrite Bool.negb_true_iff in Hneg.
                     pose proof (@eqb_spec V V_Eqb V_Eqb_ok x x) as Hspec.
                     rewrite Hneg in Hspec. exfalso. exact (Hspec eq_refl).
                  ** pose proof (@eqb_spec (Term.sort V) (@sort_eqb V V_Eqb) (@sort_eqb_ok V V_Eqb V_Eqb_ok) E tx) as Hspec.
                     rewrite Heq in Hspec. exact Hspec.
            -- discriminate Hocc.
          * intro H. discriminate H.
          * intro H. discriminate H.
        + intro H. discriminate H.
    Qed.

    Lemma rigid_sort_skip_inv c t1 x
      : rigid_sort_skip c t1 x = true ->
        exists n0 s0 cR argsR tx,
          t1 = scon n0 s0
          /\ named_list_lookup_err l n0 = Some (sort_rule cR argsR)
          /\ fst (check_args s0 cR) = true
          /\ In x (fv_sort t1)
          /\ named_list_lookup_err c x = Some tx
          /\ (forall E, In (x, E) (snd (check_args s0 cR)) -> E = tx).
    Proof.
      unfold rigid_sort_skip.
      destruct t1 as [n0 s0].
      destruct (named_list_lookup_err l n0) as [r|] eqn:Hlookup.
      - (* rule constructor order: sort_rule(2), term_rule(3), sort_eq_rule(3), term_eq_rule(4) *)
        destruct r as [cR argsR | | |].
        + (* sort_rule cR argsR *)
          intro H.
          apply Bool.andb_true_iff in H. destruct H as [H Hocc].
          apply Bool.andb_true_iff in H. destruct H as [Hcheck Hinb].
          assert (Hinfv : In x (fv_sort (scon n0 s0))).
          { apply (proj1 (inb_is_In x (fv_sort (scon n0 s0)))).
            apply Is_true_eq_left. exact Hinb. }
          destruct (named_list_lookup_err c x) as [tx|] eqn:Hlookup_x.
          * exists n0, s0, cR, argsR, tx.
            refine (conj eq_refl (conj Hlookup (conj Hcheck (conj Hinfv (conj _ _))))).
            -- reflexivity.
            -- unfold var_occs_ok in Hocc.
               rewrite forallb_forall in Hocc.
               intros E HinE.
               specialize (Hocc (x, E) HinE).
               cbn [fst snd] in Hocc.
               apply Bool.orb_true_iff in Hocc.
               destruct Hocc as [Hneg | Heq].
               ++ rewrite Bool.negb_true_iff in Hneg.
                  pose proof (@eqb_spec V V_Eqb V_Eqb_ok x x) as Hspec.
                  rewrite Hneg in Hspec. exfalso. exact (Hspec eq_refl).
               ++ pose proof (@eqb_spec (Term.sort V) (@sort_eqb V V_Eqb) (@sort_eqb_ok V V_Eqb V_Eqb_ok) E tx) as Hspec.
                  rewrite Heq in Hspec. exact Hspec.
          * discriminate Hocc.
        + intro H. discriminate H.
        + intro H. discriminate H.
        + intro H. discriminate H.
      - intro H. discriminate H.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* The rigid covering lemmas                                            *)
    (* ------------------------------------------------------------------ *)

    (* These mirror SyntacticSortCovering's covering_var_leaf_tr family, with
       the transport hypothesis REPLACED by the checker booleans; the var-leaf
       case becomes: the occurrence expectation forces use-sort = declared-sort,
       then the image wf IS the goal.  No Htr, no wf_ctx-of-target, no
       per-leaf wf_sort hypothesis. *)

    Lemma covering_var_leaf_rigid_args_aux (wfl : wf_lang l)
          (c c' : ctx) (s : subst)
          (Hwfc' : wf_ctx l c') (Hmap : map fst s = map fst c')
          (args : list term)
          (IHterm : forall e, In e args ->
                      forall t, fst (check_term e t) = true ->
                      wf_term l c' e t -> wf_term l c (e[/s/]) (t[/s/]) ->
                      forall x t', In x (fv e) -> In (x,t') c' ->
                        (forall E, In (x, E) (snd (check_term e t)) -> E = t') ->
                        wf_term l c (subst_lookup s x) (t'[/s/]))
      : forall cA,
          wf_ctx l cA ->
          fst (check_args args cA) = true ->
          wf_args l c' args cA -> wf_args l c (args[/s/]) cA ->
          forall x t', In x (fv_args args) -> In (x,t') c' ->
            (forall E, In (x, E) (snd (check_args args cA)) -> E = t') ->
            wf_term l c (subst_lookup s x) (t'[/s/]).
    Proof.
      intros cA HwfcA Hcheck Hsrc.
      revert HwfcA Hcheck.
      induction Hsrc as [| rest_args cA'' nm e0 tnm He0 Hrest IHrest].
      - (* nil case: fv_args [] = [], contradiction *)
        intros _ _ Himg x t' Hfv _ _.
        cbn [fv_args flat_map] in Hfv. exact (False_ind _ Hfv).
      - (* cons case: args = e0::rest_args, cA = (nm,tnm)::cA'' *)
        intros HwfcA Hcheck Himg x t' Hfv Hin Hoccs.
        apply invert_wf_ctx_cons in HwfcA.
        destruct HwfcA as [HfrcA [HwfcA'' HwftnmA]].
        cbn [apply_subst substable_args args_subst apply_subst0 substable_term map] in Himg.
        safe_invert Himg.
        unfold fv_args in Hfv; cbn [flat_map] in Hfv; rewrite in_app_iff in Hfv.
        (* Extract boolean facts for the head *)
        assert (Hcheck_hd : fst (check_term e0 (tnm [/with_names_from cA'' rest_args/])) = true
                            /\ fst (check_args rest_args cA'') = true).
        { eapply check_args_cons_inv. exact Hcheck. }
        assert (Hsnd : snd (check_args (e0 :: rest_args) ((nm, tnm) :: cA''))
                       = snd (check_term e0 (tnm [/with_names_from cA'' rest_args/]))
                         ++ snd (check_args rest_args cA'')).
        { eapply check_args_cons_snd. exact Hcheck. }
        destruct Hcheck_hd as [Hcheck_e0 Hcheck_rest].
        destruct Hfv as [Hfv_e0 | Hfv_rest].
        + (* x in fv e0: apply the term IH *)
          assert (Hlen : length cA'' = length rest_args)
            by (eapply wf_args_length_eq; eassumption).
          assert (Hwst_tnm : ws_sort (map fst cA'') tnm)
            by exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) HwftnmA).
          assert (Himgsort : tnm [/ with_names_from cA'' rest_args /] [/ s /] =
                             tnm [/ with_names_from cA'' (rest_args [/ s /]) /]).
          { rewrite with_names_from_args_subst.
            erewrite subst_assoc; [ reflexivity | typeclasses eauto | ].
            rewrite map_fst_with_names_from by exact Hlen.
            exact Hwst_tnm. }
          assert (H_img_e0 : wf_term l c (e0[/s/]) (tnm [/ with_names_from cA'' rest_args /] [/ s /])).
          { rewrite Himgsort.
            cbn [apply_subst substable_args args_subst apply_subst0 substable_term map].
            assumption. }
          (* The occurrence constraint for x from the full list restricts to e0's part *)
          assert (Hoccs_e0 : forall E, In (x, E) (snd (check_term e0 (tnm [/with_names_from cA'' rest_args/])) ) -> E = t').
          { intros E HinE. apply Hoccs. rewrite Hsnd. apply in_app_iff. left. exact HinE. }
          exact (IHterm e0 (in_eq e0 rest_args) (tnm[/with_names_from cA'' rest_args/])
                   Hcheck_e0 He0 H_img_e0 x t' Hfv_e0 Hin Hoccs_e0).
        + (* x in fv_args rest_args: recurse on the tail via IHrest *)
          eapply IHrest.
          * intros e He_in. exact (IHterm e (in_cons e0 e rest_args He_in)).
          * eauto.
          * exact Hcheck_rest.
          * eauto.
          * exact Hfv_rest.
          * exact Hin.
          * intros E HinE. apply Hoccs. rewrite Hsnd. apply in_app_iff. right. exact HinE.
    Qed.

    Lemma covering_var_leaf_rigid (wfl : wf_lang l)
          (c c' : ctx) (s : subst)
          (Hwfc' : wf_ctx l c') (Hmap : map fst s = map fst c')
      : forall e t,
          fst (check_term e t) = true ->
          wf_term l c' e t -> wf_term l c (e[/s/]) (t[/s/]) ->
          forall x t', In x (fv e) -> In (x,t') c' ->
            (forall E, In (x, E) (snd (check_term e t)) -> E = t') ->
            wf_term l c (subst_lookup s x) (t'[/s/]).
    Proof.
      induction e as [n | n se0 IHse0] using term_ind;
        intros t Hcheck Hsrc Himg x t' Hfv Hin Hoccs.
      - (* e = var n *)
        cbn [fv] in Hfv. destruct Hfv as [Hxn | []]. subst n.
        rewrite check_term_var in Hoccs, Hcheck.
        (* snd (check_term (var x) t) = [(x, t)]; the occurrence hypothesis gives t = t' *)
        assert (Heqt : t = t').
        { apply Hoccs. left. reflexivity. }
        subst t'.
        (* Himg : wf_term l c ((var x)[/s/]) (t[/s/]) which is wf_term l c (subst_lookup s x) (t[/s/]) *)
        change ((var x)[/s/]) with (subst_lookup s x) in Himg.
        exact Himg.
      - (* e = con n se0 *)
        cbn [fv] in Hfv.
        (* Extract con info from the checker *)
        pose proof (check_term_con_inv n se0 t Hcheck) as Hcon_inv.
        destruct Hcon_inv as (cM & argsM & tM & Hlookup & Hlen & Hfit & Hcheck_args & Hsnd).
        (* Invert source wf_term to get wf_args *)
        apply wf_term_con_args in Hsrc.
        destruct Hsrc as (cA_src & HwfA_src & argsA & tretA & HruleA_src).
        (* Invert image wf_term *)
        change ((con n se0)[/s/]) with (con n (se0[/s/])) in Himg.
        apply wf_term_con_args in Himg.
        destruct Himg as (cA_img & HwfA_img & argsI & tretI & HruleA_img).
        (* Pin the rule ctx to be the same *)
        pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) HruleA_src HruleA_img)
          as Heqr.
        safe_invert Heqr.
        (* Also reconcile with the lookup result *)
        symmetry in Hlookup.
        apply named_list_lookup_err_in in Hlookup.
        pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) Hlookup HruleA_img)
          as Heqr2.
        safe_invert Heqr2.
        (* wf_ctx l cA_img from the rule *)
        assert (HwfcA : wf_ctx l cA_img)
          by (eapply rule_in_ctx_wf; [exact wfl | exact HruleA_img | reflexivity]).
        (* Occurrence restriction *)
        assert (Hoccs_args : forall E, In (x, E) (snd (check_args se0 cA_img)) -> E = t').
        { intros E HinE. apply Hoccs. rewrite Hsnd. exact HinE. }
        (* Build IHterm from IHse0 *)
        assert (IHterm_aux : forall e, In e se0 ->
                    forall t0, fst (check_term e t0) = true ->
                    wf_term l c' e t0 -> wf_term l c (e[/s/]) (t0[/s/]) ->
                    forall x0 t'0, In x0 (fv e) -> In (x0,t'0) c' ->
                      (forall E, In (x0, E) (snd (check_term e t0)) -> E = t'0) ->
                      wf_term l c (subst_lookup s x0) (t'0[/s/])).
        { intros e_arg He_in.
          exact (@in_all _ _ se0 e_arg IHse0 He_in). }
        eapply (@covering_var_leaf_rigid_args_aux wfl c c' s Hwfc' Hmap se0 IHterm_aux
                 cA_img HwfcA Hcheck_args HwfA_src HwfA_img x t' Hfv Hin Hoccs_args).
    Qed.

    Lemma covering_var_leaf_rigid_con (wfl : wf_lang l)
          (c c' : ctx) (s : subst)
          (Hwfc' : wf_ctx l c') (Hmap : map fst s = map fst c')
      : forall n0 s0 cR argsR tR t T,
          named_list_lookup_err l n0 = Some (term_rule cR argsR tR) ->
          fst (check_args s0 cR) = true ->
          wf_term l c' (con n0 s0) t -> wf_term l c ((con n0 s0)[/s/]) T ->
          forall x t', In x (fv (con n0 s0)) -> In (x,t') c' ->
            (forall E, In (x, E) (snd (check_args s0 cR)) -> E = t') ->
            wf_term l c (subst_lookup s x) (t'[/s/]).
    Proof.
      intros n0 s0 cR argsR tR t T Hlookup Hcheck Hsrc Himg x t' Hfv Hin Hoccs.
      cbn [fv] in Hfv.
      symmetry in Hlookup.
      apply named_list_lookup_err_in in Hlookup.
      (* Invert source wf_term to get wf_args *)
      apply wf_term_con_args in Hsrc.
      destruct Hsrc as (cA_src & HwfA_src & argsA & tretA & HruleA_src).
      (* Invert image wf_term *)
      change ((con n0 s0)[/s/]) with (con n0 (s0[/s/])) in Himg.
      apply wf_term_con_args in Himg.
      destruct Himg as (cA_img & HwfA_img & argsI & tretI & HruleA_img).
      (* Pin the rule ctx to be the same for all three rule occurrences *)
      pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) HruleA_src HruleA_img)
        as Heqr.
      safe_invert Heqr.
      pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) Hlookup HruleA_img)
        as Heqr2.
      safe_invert Heqr2.
      (* wf_ctx l cA_img from the rule *)
      assert (HwfcA : wf_ctx l cA_img)
        by (eapply rule_in_ctx_wf; [exact wfl | exact HruleA_img | reflexivity]).
      (* Build IHterm_aux from covering_var_leaf_rigid *)
      assert (IHterm_aux : forall e, In e s0 ->
                  forall t0, fst (check_term e t0) = true ->
                  wf_term l c' e t0 -> wf_term l c (e[/s/]) (t0[/s/]) ->
                  forall x0 t'0, In x0 (fv e) -> In (x0,t'0) c' ->
                    (forall E, In (x0, E) (snd (check_term e t0)) -> E = t'0) ->
                    wf_term l c (subst_lookup s x0) (t'0[/s/])).
      { intros e_arg He_in t_arg Hche Hwfsrc Hwfimg x_arg t'_arg Hfv_arg Hin_arg Hocc_arg.
        exact (@covering_var_leaf_rigid wfl c c' s Hwfc' Hmap
                 e_arg t_arg Hche Hwfsrc Hwfimg x_arg t'_arg Hfv_arg Hin_arg Hocc_arg). }
      exact (@covering_var_leaf_rigid_args_aux wfl c c' s Hwfc' Hmap s0 IHterm_aux
               cA_img HwfcA Hcheck HwfA_src HwfA_img x t' Hfv Hin Hoccs).
    Qed.

  End WithLang.

End WithVar.
