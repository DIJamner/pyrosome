(* RigidRewrite.v

   A GENERIC, rule-driven, reflectively-validated rewriting engine.

   Given a language [l] and a list [ns] of names of term equations of [l], each
   of which passes the boolean check [rewrite_rule_ok], bottom-up rewriting with
   [matches] is SOUND: the result is [eq_term]-equal to the input, and therefore
   well-formed at the same sort.  See the comment block at the end of the file
   for an overview. *)

Set Implicit Arguments.

From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core SyntacticSortCovering PatternRigidity.
From Pyrosome.Theory Require WfCutElim.
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

  (* ------------------------------------------------------------------ *)
  (* A generic copy of Tools/Matches.matches.                             *)
  (* (Matches.v is specialized to [int]; we need it at an arbitrary [V].) *)
  (* ------------------------------------------------------------------ *)

  Fixpoint unordered_merge_unsafe {A} (l1 l2 : @NamedList.named_list V A)
    : @NamedList.named_list V A :=
    match l1 with
    | [] => l2
    | (n,e)::l1' =>
        (if freshb n l2 then [(n,e)] else [])
          ++ (unordered_merge_unsafe l1' l2)
    end.

  Section InnerLoop.
    Context (matches_unordered : forall (e pat : term), option subst).
    Fixpoint args_match_unordered (s pat : list term) : option subst :=
      match pat, s with
      | [],[] => Some []
      | pe::pat', e::s' =>
          match matches_unordered e pe with
          | Some res_e =>
              match args_match_unordered s' pat' with
              | Some res_s => Some (unordered_merge_unsafe res_e res_s)
              | None => None
              end
          | None => None
          end
      | _,_ => None
      end.
  End InnerLoop.

  Fixpoint matches_unordered (e pat : term) : option subst :=
    match pat, e with
    | Term.var px, _ => Some ([(px,e)])
    | Term.con pn ps, Term.con n s =>
        if eqb pn n then args_match_unordered matches_unordered s ps else None
    | _,_ => None
    end.

  Fixpoint order_subst' (s : subst) (args : list V) : option subst :=
    match args with
    | [] => Some []
    | x::args' =>
        match named_list_lookup_err s x with
        | Some e =>
            match order_subst' s args' with
            | Some s' => Some ((x,e)::s')
            | None => None
            end
        | None => None
        end
    end.

  Definition order_subst (s : subst) (args : list V) : option subst :=
    if Nat.eqb (length s) (length args) then order_subst' s args else None.

  (* Finds [s] with [map fst s = args] and [e = pat[/s/]], if one exists.
     The [eqb] post-check makes the result trustworthy regardless of how the
     unordered pass merged conflicting bindings. *)
  Definition matches (e pat : term) (args : list V) : option subst :=
    match matches_unordered e pat with
    | Some s =>
        match order_subst s args with
        | Some s' => if eqb e pat[/s'/] then Some s' else None
        | None => None
        end
    | None => None
    end.

  Lemma order_subst'_names : forall args s s',
      order_subst' s args = Some s' -> map fst s' = args.
  Proof.
    induction args as [|x args IH]; cbn [order_subst'].
    - intros s s' H. safe_invert H. reflexivity.
    - intros s s' H.
      destruct (named_list_lookup_err s x) as [e|]; [| discriminate H].
      destruct (order_subst' s args) as [s0|] eqn:Hs0; [| discriminate H].
      safe_invert H. cbn [map fst]. f_equal. apply (IH s s0 Hs0).
  Qed.

  Lemma matches_sound e pat args s
    : matches e pat args = Some s ->
      map fst s = args /\ e = pat[/s/].
  Proof.
    unfold matches, order_subst.
    destruct (matches_unordered e pat) as [s0|]; [| discriminate].
    destruct (Nat.eqb (length s0) (length args)); [| discriminate].
    destruct (order_subst' s0 args) as [s1|] eqn:Hord; [| discriminate].
    destruct (eqb e pat[/s1/]) eqn:Heqb; [| discriminate].
    intro H. safe_invert H.
    split.
    - exact (order_subst'_names _ _ Hord).
    - pose proof (@eqb_spec (Term.term V) (@term_eqb V V_Eqb)
                    (@term_eqb_ok V V_Eqb V_Eqb_ok) e pat[/s/]) as Hspec.
      rewrite Heqb in Hspec. exact Hspec.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Small generic helpers (would naturally live in Term.v / Core.v)      *)
  (* ------------------------------------------------------------------ *)

  Lemma ws_term_incl (args args' : list V)
    : incl args args' -> forall e, ws_term args e -> ws_term args' e.
  Proof.
    intros Hincl e.
    induction e using term_ind; cbn [ws_term].
    - apply Hincl.
    - intro Hall.
      revert H Hall.
      induction l as [|e0 l0 IH]; cbn [all]; [ tauto |].
      intros [He0 Hl0] [Hw Hws]. split; auto.
  Qed.

  Lemma ws_sort_incl (args args' : list V) (t : sort)
    : incl args args' -> ws_sort args t -> ws_sort args' t.
  Proof.
    destruct t as [n s]; cbn [ws_sort].
    intro Hincl.
    unfold ws_args.
    induction s as [|e s IH]; cbn [all]; [ tauto |].
    intros [He Hs]; split; [ eapply ws_term_incl; eassumption | auto ].
  Qed.

  Section WithLang.
    Context (l : lang).

    (* ---------------------------------------------------------------- *)
    (* The engine                                                        *)
    (* ---------------------------------------------------------------- *)

    (* A rule usable for rewriting: a term equation whose LHS is a [con]
       node that passes the rigidity check, whose stated sort is exactly the
       LHS head's output sort instantiated (root fit), and every ctx variable
       occurs in the LHS with only its declared sort as occurrence
       expectation. *)
    Definition rewrite_rule_ok (n : V) : bool :=
      match named_list_lookup_err l n with
      | Some (term_eq_rule c' (Term.con n0 s0) e2 t) =>
          match named_list_lookup_err l n0 with
          | Some (term_rule cR _ tR) =>
              fst (check_args l s0 cR)
              && eqb t (tR[/with_names_from cR s0/])
              && forallb (fun p => inb (fst p) (fv (Term.con n0 s0))
                                   && var_occs_ok (snd (check_args l s0 cR))
                                        (fst p) (snd p)) c'
          | _ => false
          end
      | _ => false
      end.

    Definition rewrite_with (n : V) (e : term) : option term :=
      match named_list_lookup_err l n with
      | Some (term_eq_rule c' e1 e2 t) =>
          match matches e e1 (map fst c') with
          | Some s => Some e2[/s/]
          | None => None
          end
      | _ => None
      end.

    (* the first rule in [ns] that applies *)
    Fixpoint first_rewrite (ns : list V) (e : term) : option term :=
      match ns with
      | [] => None
      | n::ns' =>
          match rewrite_with n e with
          | Some e' => Some e'
          | None => first_rewrite ns' e
          end
      end.

    (* one bottom-up pass: rewrite the children, then try the rules at the
       root once *)
    Fixpoint pass (ns : list V) (e : term) : term :=
      match e with
      | Term.var x => Term.var x
      | Term.con n s =>
          let e' := Term.con n (map (pass ns) s) in
          match first_rewrite ns e' with
          | Some e'' => e''
          | None => e'
          end
      end.

    (* iterate [pass] until a syntactic fixpoint or out of fuel *)
    Fixpoint rewrite_n (ns : list V) (fuel : nat) (e : term) : term :=
      match fuel with
      | 0 => e
      | S fuel' =>
          let e' := pass ns e in
          if eqb e' e then e else rewrite_n ns fuel' e'
      end.

    Lemma pass_con ns n s
      : pass ns (con n s)
        = match first_rewrite ns (con n (map (pass ns) s)) with
          | Some e'' => e''
          | None => con n (map (pass ns) s)
          end.
    Proof. reflexivity. Qed.

    (* ---------------------------------------------------------------- *)
    (* Soundness                                                         *)
    (* ---------------------------------------------------------------- *)

    Context (wfl : wf_lang l).

    (* Assemble a [wf_subst] from pointwise lookups. *)
    Lemma wf_subst_of_lookups (c : ctx)
      : forall (c' : ctx) (s : subst),
        wf_ctx l c' ->
        map fst s = map fst c' ->
        (forall x t', In (x,t') c' -> wf_term l c (subst_lookup s x) (t'[/s/])) ->
        wf_subst l c s c'.
    Proof.
      induction c' as [|[x tx] c' IH]; intros s Hwfc' Hmap Hpt.
      - destruct s as [|[y e] s]; [ constructor | cbn in Hmap; discriminate ].
      - destruct s as [|[y e] s]; [ cbn in Hmap; discriminate |].
        cbn [map fst] in Hmap. injection Hmap as Hy Hmap'. subst y.
        apply invert_wf_ctx_cons in Hwfc'.
        destruct Hwfc' as [Hfr [Hwfc' Hwfs]].
        assert (Hfrs : fresh x s).
        { unfold fresh in *. rewrite Hmap'. exact Hfr. }
        assert (Hwstx : ws_sort (map fst s) tx).
        { rewrite Hmap'. exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) Hwfs). }
        constructor.
        + apply IH; [ exact Hwfc' | exact Hmap' |].
          intros z tz Hin.
          assert (Hzy : z <> x).
          { intro; subst z. unfold fresh in Hfr. apply Hfr.
            change x with (fst (x,tz)). apply in_map. exact Hin. }
          pose proof (Hpt z tz (in_cons _ _ _ Hin)) as Hw.
          rewrite (@subst_lookup_tl V V_Eqb V_Eqb_ok x z e s Hzy) in Hw.
          assert (Hwfsz : Model.wf_sort (Model := mut_mod (eq_sort l) (eq_term l)
                                           (wf_sort l) (wf_term l)) c' tz)
            by (eapply in_ctx_wf; eauto).
          assert (Hwstz : ws_sort (map fst s) tz).
          { eapply ws_sort_incl;
              [ | exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) Hwfsz) ].
            rewrite Hmap'. apply incl_refl. }
          assert (Hstr : tz[/(x,e)::s/] = tz[/s/])
            by (apply sort_strengthen_subst; assumption).
          rewrite Hstr in Hw. exact Hw.
        + pose proof (Hpt x tx (in_eq _ _)) as Hw.
          rewrite (@subst_lookup_hd V V_Eqb V_Eqb_ok x e s) in Hw.
          assert (Hstr : tx[/(x,e)::s/] = tx[/s/])
            by (apply sort_strengthen_subst; assumption).
          rewrite Hstr in Hw. exact Hw.
    Qed.

    Theorem rewrite_with_sound (c : ctx) (wfc : wf_ctx l c) n e t e'
      : rewrite_rule_ok n = true ->
        wf_term l c e t ->
        rewrite_with n e = Some e' ->
        eq_term l c t e e'.
    Proof.
      unfold rewrite_rule_ok, rewrite_with.
      destruct (named_list_lookup_err l n) as [r|] eqn:Hn; [| discriminate].
      destruct r as [ | | | c' e1 e2 tq ]; try discriminate.
      destruct e1 as [ | n0 s0 ]; [ discriminate |].
      destruct (named_list_lookup_err l n0) as [r0|] eqn:Hn0; [| discriminate].
      destruct r0 as [ | cR argsR tR | | ]; try discriminate.
      intro Hok.
      apply Bool.andb_true_iff in Hok; destruct Hok as [Hok Hall].
      apply Bool.andb_true_iff in Hok; destruct Hok as [Hchk Hfit].
      intros Hwf Hrw.
      destruct (matches e (con n0 s0) (map fst c')) as [ s | ] eqn:Hm; [| discriminate].
      safe_invert Hrw.
      apply matches_sound in Hm. destruct Hm as [Hmap He]. subst e.
      (* rule facts *)
      assert (HinRule : In (n, term_eq_rule c' (con n0 s0) e2 tq) l)
        by (apply named_list_lookup_err_in; symmetry; exact Hn).
      assert (HinR : In (n0, term_rule cR argsR tR) l)
        by (apply named_list_lookup_err_in; symmetry; exact Hn0).
      pose proof (rule_in_wf _ _ wfl HinRule) as Hwr.
      rewrite app_nil_r in Hwr.
      inversion Hwr as [ | | | c'0 e10 e20 t0 Hwfc' Hwft1 Hwft2 Hwfsq Heqr ];
        subst; clear Hwr.
      pose proof (rule_in_wf _ _ wfl HinR) as HwrR.
      rewrite app_nil_r in HwrR.
      inversion HwrR as [ | cR0 argsR0 tR0 HwfcR HwfsR HsubR HeqrR | | ];
        subst; clear HwrR.
      (* root fit *)
      assert (Htq : tq = tR[/with_names_from cR s0/]).
      { pose proof (@eqb_spec (Term.sort V) (@sort_eqb V V_Eqb)
                      (@sort_eqb_ok V V_Eqb V_Eqb_ok) tq (tR[/with_names_from cR s0/]))
          as Hspec.
        rewrite Hfit in Hspec. exact Hspec. }
      (* the image term *)
      pose proof Hwf as Himg.
      (* pointwise wf of the substitution *)
      assert (Hpt : forall x t', In (x,t') c' ->
                      wf_term l c (subst_lookup s x) (t'[/s/])).
      { intros x t' Hin.
        rewrite forallb_forall in Hall.
        specialize (Hall (x,t') Hin). cbn [fst snd] in Hall.
        apply Bool.andb_true_iff in Hall. destruct Hall as [Hinb Hocc].
        assert (Hfv : In x (fv (con n0 s0))).
        { apply (proj1 (inb_is_In x (fv (con n0 s0)))).
          apply Is_true_eq_left. exact Hinb. }
        assert (Hoccs : forall E, In (x, E) (snd (check_args l s0 cR)) -> E = t').
        { unfold var_occs_ok in Hocc. rewrite forallb_forall in Hocc.
          intros E HinE. specialize (Hocc (x,E) HinE). cbn [fst snd] in Hocc.
          apply Bool.orb_true_iff in Hocc. destruct Hocc as [Hneg | Heq].
          - rewrite Bool.negb_true_iff in Hneg.
            pose proof (@eqb_spec V V_Eqb V_Eqb_ok x x) as Hspec.
            rewrite Hneg in Hspec. exfalso. exact (Hspec eq_refl).
          - pose proof (@eqb_spec (Term.sort V) (@sort_eqb V V_Eqb)
                          (@sort_eqb_ok V V_Eqb V_Eqb_ok) E t') as Hspec.
            rewrite Heq in Hspec. exact Hspec. }
        eapply (covering_var_leaf_rigid_con wfl (c:=c) (c':=c') (s:=s)
                  Hwfc' Hmap (n0:=n0) (s0:=s0) (cR:=cR) (argsR:=argsR) (tR:=tR)
                  (t:=tq) (T:=t) Hn0 Hchk Hwft2 Himg x Hfv Hin Hoccs). }
      assert (Hwfsub : wf_subst l c s c')
        by (eapply wf_subst_of_lookups; eauto).
      (* the equation, instantiated *)
      assert (Heqinst : eq_term l c (tq[/s/]) ((con n0 s0)[/s/]) (e2[/s/])).
      { eapply eq_term_subst;
          [ eapply eq_term_by; exact HinRule
          | apply eq_subst_refl; exact Hwfsub
          | exact Hwfc' ]. }
      (* substitution composition on the sort *)
      assert (Hlen : length s0 = length cR) by (apply (check_args_length _ _ _ Hchk)).
      assert (Hts : tq[/s/] = tR[/with_names_from cR (s0[/s/])/]).
      { rewrite Htq.
        rewrite with_names_from_args_subst.
        erewrite subst_assoc; [ reflexivity | typeclasses eauto | ].
        rewrite map_fst_with_names_from by (symmetry; exact Hlen).
        exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) HwfsR). }
      (* inversion of the image's wf to get the sort of the redex *)
      change ((con n0 s0)[/s/]) with (con n0 (s0[/s/])) in Himg.
      apply WfCutElim.invert_wf_term_con in Himg.
      destruct Himg as (c2 & args2 & t2 & Hin2 & Hwfargs2 & Hor).
      pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) HinR Hin2)
        as Heq2.
      safe_invert Heq2.
      change ((con n0 s0)[/s/]) with (con n0 (s0[/s/])) in Heqinst.
      destruct Hor as [Hor | Hor].
      - eapply eq_term_conv; [ | exact Hor ].
        rewrite <- Hts. exact Heqinst.
      - rewrite <- Hor, <- Hts. exact Heqinst.
    Qed.

    Theorem first_rewrite_sound (c : ctx) (wfc : wf_ctx l c) ns e t e'
      : forallb rewrite_rule_ok ns = true ->
        wf_term l c e t ->
        first_rewrite ns e = Some e' ->
        eq_term l c t e e'.
    Proof.
      induction ns as [|n ns IH]; cbn [first_rewrite forallb]; [ discriminate |].
      intro Hok. apply Bool.andb_true_iff in Hok. destruct Hok as [Hn Hns].
      intro Hwf.
      destruct (rewrite_with n e) as [e0|] eqn:Hrw.
      - intro H. safe_invert H.
        eapply rewrite_with_sound; eauto.
      - apply IH; assumption.
    Qed.

    Section PassSound.
      Context (ns : list V)
        (Hok : forallb rewrite_rule_ok ns = true)
        (c : ctx)
        (wfc : wf_ctx l c).

      Lemma eq_args_pass
        : forall (c' : ctx) (s : list term),
          WfCutElim.P_args V (fun e t => eq_term l c t e (pass ns e)) s c' ->
          eq_args l c c' (map (pass ns) s) s.
      Proof.
        induction c' as [|[nm tt] c' IH]; intros [|e s];
          cbn [WfCutElim.P_args map]; try tauto.
        - intros _. apply Model.eq_args_nil.
        - intros [Hp Hpe]. apply Model.eq_args_cons.
          + apply IH; exact Hp.
          + apply eq_term_sym. exact Hpe.
      Qed.

      Theorem pass_sound
        : forall (t : sort) (e : term),
          wf_term l c e t -> eq_term l c t e (pass ns e).
      Proof.
        induction 1 using WfCutElim.wf_term_cut_ind.
        - (* con *)
          rewrite pass_con.
          assert (Hargs : eq_args l c c' (map (pass ns) s) s)
            by (apply eq_args_pass; assumption).
          assert (Hcong : eq_term l c (t[/with_names_from c' s/])
                            (con name (map (pass ns) s)) (con name s))
            by (eapply term_con_congruence;
                [ eassumption | right; reflexivity | exact wfl | exact Hargs ]).
          assert (Hwf' : wf_term l c (con name (map (pass ns) s))
                           (t[/with_names_from c' s/]))
            by (eapply eq_term_wf_l; eauto).
          destruct (first_rewrite ns (con name (map (pass ns) s))) as [e''|] eqn:Hfr.
          + eapply eq_term_trans; [ apply eq_term_sym; exact Hcong |].
            eapply first_rewrite_sound; eauto.
          + apply eq_term_sym. exact Hcong.
        - (* var *)
          cbn [pass]. apply eq_term_refl. apply wf_term_var. assumption.
        - (* conv *)
          eapply eq_term_conv; eassumption.
      Qed.

      Theorem pass_wf
        : forall (t : sort) (e : term),
          wf_term l c e t -> wf_term l c (pass ns e) t.
      Proof.
        intros t e Hwf.
        eapply eq_term_wf_r; try typeclasses eauto;
          [ exact wfl | exact wfc | apply pass_sound; exact Hwf ].
      Qed.

      Theorem rewrite_n_sound
        : forall (fuel : nat) (t : sort) (e : term),
          wf_term l c e t -> eq_term l c t e (rewrite_n ns fuel e).
      Proof.
        induction fuel as [|fuel IH]; intros t e Hwf; cbn [rewrite_n].
        - apply eq_term_refl. exact Hwf.
        - destruct (eqb (pass ns e) e).
          + apply eq_term_refl. exact Hwf.
          + eapply eq_term_trans;
              [ apply pass_sound; exact Hwf
              | apply IH; apply pass_wf; exact Hwf ].
      Qed.

      Theorem rewrite_n_wf
        : forall (fuel : nat) (t : sort) (e : term),
          wf_term l c e t -> wf_term l c (rewrite_n ns fuel e) t.
      Proof.
        intros fuel t e Hwf.
        eapply eq_term_wf_r; try typeclasses eauto;
          [ exact wfl | exact wfc | apply rewrite_n_sound; exact Hwf ].
      Qed.

    End PassSound.

  End WithLang.

End WithVar.


(* ====================================================================
   HOW TO USE THIS ENGINE

   Fix a concrete language [l : lang] (e.g. [string]-named) with
   [wfl : wf_lang l], and a list [ns : list string] of names of TERM EQUATIONS
   of [l] to be used left-to-right as rewrite rules.

   1. Discharge the side condition reflectively:

        Lemma my_rules_ok : forallb (rewrite_rule_ok my_lang) my_rules = true.
        Proof. vm_compute. reflexivity. Qed.

      [rewrite_rule_ok l n] holds when [n] names a rule
      [term_eq_rule c' (con n0 s0) e2 t] such that
        (a) [con n0 s0] passes PatternRigidity's [check_args] against the ctx of
            the head constructor's rule (every internal node "fits": its
            declared output sort, instantiated by its own arguments, is
            SYNTACTICALLY equal to the telescope-expected sort at its
            position);
        (b) "root fit": [t] is syntactically [tR[/with_names_from cR s0/]];
        (c) every variable of [c'] occurs in the LHS, and all of its
            occurrence expectations are syntactically its declared sort.

   2. Then, for any [c] with [wf_ctx l c] (in particular [c := []]):

        rewrite_n_sound my_lang my_rules_ok wfc fuel Hwf
          : eq_term l c t e (rewrite_n l my_rules fuel e)
        rewrite_n_wf   ... : wf_term l c (rewrite_n l my_rules fuel e) t

   The engine itself:
     [pass l ns e]        - one bottom-up sweep: rewrite the children, then try
                            the rules once at the root ([first_rewrite]).
     [rewrite_n l ns k e] - iterate [pass] up to [k] times, stopping early at a
                            syntactic fixpoint.
   Neither is claimed to be COMPLETE or NORMALIZING; only sound.  Termination
   is bounded by [fuel], and the caller checks any completeness property of the
   result separately (that check is decidable on concrete terms).
   ==================================================================== *)
