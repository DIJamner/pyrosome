(* ============================================================== *)
(* Source-rule adapter — ctx readback / (I)-inversion core.       *)
(*                                                                *)
(* Carved out of Theorems.v (the [AddCtxInvert] section) to keep  *)
(* that file smaller.  Holds the eF-side ctx readback             *)
(* ([ctx_readback_eF]) plus its two driving lemmas                *)
(* ([ctx_readback_wf_subst], [ctx_readback_to_eF]), consumed by   *)
(* [add_ctx_inversion] in AddCtxInversion.v.                      *)
(*                                                                *)
(* This file Requires Theorems and re-exposes the section-closed  *)
(* constants the moved proofs reference (companion-section style,  *)
(* matching AddCtxInversion.v / the Semantics.v split).  No proof *)
(* bodies change.                                                 *)
(* ============================================================== *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsParents SemanticsAreUnified SemanticsSaturate SemanticsUnionSem SemanticsLSurvive SemanticsRebuildCanon SemanticsAnalysesCover SemanticsHashDb.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls SyntacticSortCovering PatternRigidity.
From Pyrosome.Theory Require WfCutElim.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph Require Import Theorems.


#[local] Hint Resolve Properties.map.extends_refl : utils.
#[local] Hint Rewrite combine_map_fst_snd : utils.


Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).


  Context
    (V_map : forall A, map.map V A)
      (V_map_plus : ExtraMaps.map_plus V_map)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A)
      (V_trie_ok : forall A, map.ok (V_trie A)).

  Notation instance := (instance V V V_map V_map V_trie).

  Notation atom := (atom V V).


  Context (succ : V -> V).

  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).

  Context (lt : V -> V -> Prop).

  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).

  (* --- re-exposed Theorems section-closed constants, applied to the
     ambient WithVar context, so the [AddCtxInvert] body below compiles
     verbatim.  All of these carry an explicit analysis arg [X] (and some
     an explicit [l]/[Hwf]/[Hsof]) AFTER the parameters fixed here, so the
     body's [<name> X ...] / [eapply <name>] call sites resolve unchanged. *)
  Local Notation lang_model := (@Theorems.lang_model V V_Eqb sort_of).
  Local Notation is_root := (@Theorems.is_root V V_map V_trie).
  Local Notation db_ctx_inv := (@Theorems.db_ctx_inv V V_map V_trie sort_of).
  Local Notation ctx_readback := (@Theorems.ctx_readback V V_Eqb V_default V_map V_trie sort_of).
  Local Notation ctx_readback_gen := (@Theorems.ctx_readback_gen V V_Eqb V_default V_map V_trie sort_of).
  Local Notation atom_tree_sort := (@Theorems.atom_tree_sort V V_Eqb V_default V_map V_trie).
  Local Notation represents_sort := (@Theorems.represents_sort V V_Eqb V_default V_map V_trie sort_of).
  Local Notation atom_tree_sort_to_represents_sort :=
    (@Theorems.atom_tree_sort_to_represents_sort V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of).
  Local Notation add_open_faithful_rep_sort :=
    (@Theorems.add_open_faithful_rep_sort V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of).
  Local Notation atom_tree_sort_survives :=
    (@Theorems.atom_tree_sort_survives V V_Eqb V_default V_map V_trie sort_of).

  (* ============================================================== *)
  (* P3 (I)-inversion assembly: ctx_readback_eF + ctx_readback_wf_subst. *)
  (* ============================================================== *)
  (* From an adversary [a] sound on the rebuilt assumption egraph     *)
  (* [eF]'s atoms, plus the F1c-discharged per-var readback in [eF]    *)
  (* ([ctx_readback_eF]: an [atom_tree_sort] witness for each ctx      *)
  (* var's sort at a sort id [xs], and the CANONICALISED               *)
  (* [sort_of([x']) -> xs] atom), reconstruct a wf substitution [sg]   *)
  (* of the ctx [c] agreeing with [a] on the companion ids.  This is   *)
  (* the (I)-inversion core of the source-rule soundness adapter; the  *)
  (* F1c gate is isolated to [ctx_readback_eF] (discharged at P5 from  *)
  (* [add_ctx_readback] + [atom_tree_sort_survives] + the [sort_of]    *)
  (* ret-canonicalisation fact).  See [[project-source-rule-adapter]]. *)
  Section AddCtxInvert.
    Context (X : Type) `{analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).

    Local Notation lang_model := (lang_model l).
    Local Notation interp := (V_map (lang_model.(domain _))).
    Local Notation ain a e := (@Semantics.atom_in_egraph V V V_map V_map V_trie X a e).
    Local Notation asnd a al := (@Semantics.atom_sound_for_model V V V_map lang_model a al).
    Local Notation lang_model_args_inl := (@Theorems.lang_model_args_inl V V_Eqb sort_of l).

    (* The eF-side readback: the F1c-discharged form of [ctx_readback].
       Per ctx var [(x,t)] with companion [x'], the rebuilt egraph [eF]
       carries (a) a structural [atom_tree_sort] for [t] at some sort id
       [xs], and (b) the CANONICALISED [sort_of([x']) -> xs] atom (same
       [xs]).  The (b) ret=[xs] coupling is exactly the [tx' -> xs]
       canonicalisation the F1c discharge supplies; [ctx_readback]
       (model-free) only had an existential [tx'].  This is what (I)
       consumes. *)
    Fixpoint ctx_readback_eF (eF : instance X) (sub : named_list V) (c0 : ctx)
      {struct c0} : Prop :=
      match c0, sub with
      | [], _ => True
      | (x,t)::c', (_, x')::sub' =>
          (exists xs, atom_tree_sort X eF sub' t xs
                   /\ ain (Build_atom sort_of [x'] xs) eF)
          /\ ctx_readback_eF eF sub' c'
      | _, _ => False
      end.

    Lemma ctx_readback_wf_subst (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      : forall c sub, wf_ctx l c ->
          map fst c = map fst sub ->
          ctx_readback_eF eF sub c ->
          exists sg, wf_subst l [] sg c
                  /\ map fst sg = map fst c
                  /\ (forall x, In x (map fst sub) ->
                        map.get a (named_list_lookup default sub x)
                          = Some (inl (named_list_lookup default sg x))).
    Proof.
      induction c as [|[x t] c' IH]; intros sub Hwfc Hdom Hrb.
      - exists []. split; [|split].
        + constructor.
        + reflexivity.
        + destruct sub as [|[? ?] ?]; cbn in Hdom; [|discriminate].
          intros x [].
      - destruct sub as [|[x0 x'] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hx Hdom'. subst x0.
        apply invert_wf_ctx_cons in Hwfc.
        destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
        cbn [ctx_readback_eF] in Hrb.
        destruct Hrb as [ [xs [Htree Hatom_sof] ] Hrb' ].
        specialize (IH sub' Hwfc' Hdom' Hrb').
        destruct IH as [sg' [Hwfsub' [Hdomsg' Hleaf'] ] ].
        assert (Hrep : represents_sort X l a eF sg' t xs).
        { eapply atom_tree_sort_to_represents_sort; eauto. }
        assert (Hfr : exists t', map.get a xs = Some (inr t')
                              /\ eq_sort l [] t' (t[/sg'/])).
        { eapply add_open_faithful_rep_sort; eauto. }
        destruct Hfr as [t' Hfr2]. destruct Hfr2 as [Hgxs Heqs].
        pose proof (Hsound _ Hatom_sof) as Hsnd.
        unfold Semantics.atom_sound_for_model, Is_Some_satisfying in Hsnd.
        cbn [atom_args atom_ret atom_fn Defs.atom_args Defs.atom_ret Defs.atom_fn
             list_Mmap] in Hsnd.
        destruct (map.get a x') as [dx|] eqn:Hgx'; cbn beta iota in Hsnd; [|contradiction].
        rewrite Hgxs in Hsnd.
        cbn beta iota in Hsnd.
        change (domain V lang_model) with (term + sort)%type in Hsnd.
        cbn [interprets_to lang_model] in Hsnd.
        cbn in Hsnd.
        (* Hsnd : interprets_to sort_of [dx] (inr t'); the [interprets_to_term]
           constructor is auto-eliminated (inl vs inr). *)
        inversion Hsnd as
          [ es t_es Hwt_es Hargdom Houtdom
          | f0 args0 t0 Heqs0 Hargdom Houtdom
          | f0 args0 e0 t0 Heqe0 Hargdom Houtdom ].
        + (* interprets_to_sort_of: Houtdom : inl es = dx; Hwt_es : wf_term l [] es t' *)
          exists ((x, es) :: sg').
          split; [|split].
          * econstructor; [exact Hwfsub' | eapply wf_term_conv; [exact Hwt_es | exact Heqs] ].
          * cbn [map fst]. rewrite Hdomsg'. reflexivity.
          * intros y Hy. cbn [map fst] in Hy. cbn [named_list_lookup].
            pose proof (eqb_spec y x) as Hsp.
            destruct (eqb y x) eqn:Hyx;
              [ rewrite Houtdom; exact Hgx'
              | apply Hleaf'; destruct Hy as [Heqyx | Hy];
                  [ exfalso; apply Hsp; symmetry; exact Heqyx | exact Hy ] ].
        + (* interprets_to_sort: f0 = sort_of, eq_sort scon -> fresh contradiction *)
          exfalso.
          apply eq_sort_wf_l in Heqs0; eauto with lang_core.
          safe_invert Heqs0.
          match goal with Hin : In (sort_of, _) l |- _ =>
            apply Hsof; eapply pair_fst_in; exact Hin end.
    Qed.

    (* Projection of [ctx_readback_eF]: given a companion pair [(nm,x')] in
       [sub], recover the ctx var [nm]'s sort [t], an [atom_tree_sort] for it
       over the FULL [sub] (the per-var tree is built over the suffix below
       [nm]; we weaken it up to the full sub via [atom_tree_sort_sub_cons_fresh],
       valid because each prepended later-bound name is fresh for [t]), and the
       canonical [sort_of([x']) -> xs] atom.  Consumed by [assum_ids_covered]'s
       sort_of branch (cover the companion's sort root [xs = x']'s sort_of-ret). *)
    Lemma ctx_readback_eF_lookup (eF : instance X)
      : forall c sub, wf_ctx l c ->
          map fst c = map fst sub ->
          ctx_readback_eF eF sub c ->
          forall nm x', In (nm, x') sub ->
            exists t xs, In (nm, t) c
                  /\ atom_tree_sort X eF sub t xs
                  /\ ain (Build_atom sort_of [x'] xs) eF.
    Proof.
      pose proof (wf_lang_implies_ws_noext Hwf) as Hwsl.
      induction c as [|[x tx] c' IH]; intros sub Hwfc Hdom Hrb nm x' Hin.
      - destruct sub as [|[? ?] ?]; cbn in Hdom; [|discriminate].
        cbn in Hin. contradiction.
      - destruct sub as [|[x0 x'x] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hx Hdom'. subst x0.
        apply invert_wf_ctx_cons in Hwfc.
        destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
        cbn [ctx_readback_eF] in Hrb.
        destruct Hrb as [ [xs [Htree Hatom_sof] ] Hrb' ].
        cbn [In] in Hin. destruct Hin as [Heq | Hin'].
        + injection Heq as Hnm Hx'eq. subst nm x'.
          destruct tx as [ntx stx].
          exists (scon ntx stx), xs.
          split; [left; reflexivity|].
          split; [| exact Hatom_sof].
          refine (@Theorems.atom_tree_sort_sub_cons_fresh V V_Eqb V_Eqb_ok V_default
                    V_map V_trie X eF sub' x x'x ntx stx xs _ Htree).
          eapply (@Theorems.ws_sort_fresh_not_fv V V_Eqb x (map fst c') ntx stx);
            [ exact Hfresh |].
          eapply wf_sort_implies_ws; eassumption.
        + specialize (IH sub' Hwfc' Hdom' Hrb' nm x' Hin').
          destruct IH as (t & xs0 & Hin_c' & Htree' & Hatom').
          destruct t as [nt st].
          exists (scon nt st), xs0.
          split; [right; exact Hin_c'|].
          split; [| exact Hatom'].
          refine (@Theorems.atom_tree_sort_sub_cons_fresh V V_Eqb V_Eqb_ok V_default
                    V_map V_trie X eF sub' x x'x nt st xs0 _ Htree').
          eapply (@Theorems.ws_sort_fresh_not_fv V V_Eqb x (map fst c') nt st);
            [ exact Hfresh |].
          assert (Hwf_t : wf_sort l c' (scon nt st)) by (eapply in_ctx_wf; eauto).
          eapply wf_sort_implies_ws; eassumption.
    Qed.

    (* ============================================================== *)
    (* P5 bridge: ctx_readback (pre-rebuild, model-free) -> ctx_readback_eF
       (post-rebuild eF).  The canonicalizing survival is taken as the
       single hypothesis [Hsurv] (mirroring [atom_tree_sort_survives]'
       verbatim Hsurv, but in the UP-TO-EQUIV / canonicalizing form so it
       also moves the demoted [sort_of([x']) -> tx'] atom to its canonical
       [sort_of([x']) -> xs]).  The assembly site (task 6) discharges
       [Hsurv] from the generalised [L_survive_canonical] (with [m :=
       lang_model] etc.), isolating the F1c gate there.  Keeps this lemma
       model-free and 0-axiom. *)
    Lemma ctx_readback_to_eF (e1 eF : instance X)
      (Hdbi : db_ctx_inv X e1)
      (Hsurv : forall a : atom,
          atom_in_egraph_up_to_equiv V V V_map V_map V_trie X a e1 ->
          all (is_root X e1) (atom_args a) ->
          is_root X e1 (atom_ret a) ->
          ain a eF)
      : forall c sub, wf_ctx l c ->
          all (fun p => is_root X e1 (snd p)) sub ->
          ctx_readback X e1 sub c ->
          ctx_readback_eF eF sub c.
    Proof.
      (* reflexivity of uf_rel_PER on a list of roots *)
      assert (Hrefl : forall xl,
                 all (is_root X e1) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e1)) xl xl).
      { induction xl as [|z xl IHxl]; cbn; [trivial|].
        intros [Hz Hxl]. split; [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]. }
      induction c as [|[x t] c' IH]; intros sub Hwfc Hroots Hrb.
      - cbn. exact I.
      - destruct sub as [|[x0 x'] sub'].
        + cbn in Hrb. contradiction.
        + apply invert_wf_ctx_cons in Hwfc.
          destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
          cbn in Hrb. destruct Hrb as [Hhead Hrb'].
          destruct Hhead as [xs [Hxs_root [Htree [tx' [Hatom_db Hper] ] ] ] ].
          cbn in Hroots. destruct Hroots as [Hx'_root Hroots'].
          cbn [ctx_readback_eF]. split.
          * exists xs. split.
            -- (* atom_tree_sort eF sub' t xs via survival (verbatim case of Hsurv) *)
               eapply atom_tree_sort_survives with (e:=e1) (c:=c');
                 [ exact Hsof | exact Hdbi | | exact Hwst | exact Htree ].
               intros a Ha_in Ha_args Ha_ret.
               apply Hsurv; [ | exact Ha_args | exact Ha_ret ].
               exists a. split; [| exact Ha_in].
               unfold atom_canonical_equiv. split; [reflexivity|]. split.
               ++ apply Hrefl; exact Ha_args.
               ++ apply Relations.PER_clo_base; exact Ha_ret.
            -- (* canonical sort_of atom in eF via Hsurv (canonicalizing case) *)
               apply Hsurv.
               ++ exists (Build_atom sort_of [x'] tx'). split.
                  ** unfold atom_canonical_equiv.
                     cbn [atom_fn atom_args atom_ret Defs.atom_fn Defs.atom_args Defs.atom_ret].
                     split; [reflexivity|]. split.
                     --- cbn. split; [apply Relations.PER_clo_base; exact Hx'_root | exact I].
                     --- apply Relations.PER_clo_sym; exact Hper.
                  ** exact Hatom_db.
               ++ cbn [atom_args Defs.atom_args]. split; [exact Hx'_root | exact I].
               ++ cbn [atom_ret Defs.atom_ret]. exact Hxs_root.
          * apply IH; [exact Hwfc' | exact Hroots' | exact Hrb'].
    Qed.


    (* ===== skip-sorts (_gen) variants for minimized eq-rule queries ===== *)
    (* [ctx_readback_eF_gen no_sort]: like [ctx_readback_eF] but a skipped  *)
    (* var ([no_sort x = true]) carries NO sort_of/atom_tree witness (its    *)
    (* sort is recovered downstream from the LHS image via                   *)
    (* [skip_decl_wf_from_image]); non-skipped vars keep the full witness.   *)
    Fixpoint ctx_readback_eF_gen (no_sort : V -> bool) (eF : instance X)
        (sub : named_list V) (c0 : ctx) {struct c0} : Prop :=
      match c0, sub with
      | [], _ => True
      | (x,t)::c', (_, x')::sub' =>
          (if no_sort x then True
           else (exists xs, atom_tree_sort X eF sub' t xs
                         /\ ain (Build_atom sort_of [x'] xs) eF))
          /\ ctx_readback_eF_gen no_sort eF sub' c'
      | _, _ => False
      end.

    (* [_gen] form of [ctx_readback_eF_lookup]: the looked-up var must be    *)
    (* NON-skipped ([no_sort nm = false]) so it carries the sort_of witness  *)
    (* (skip vars have no sort_of atom and are covered via the LHS tree      *)
    (* branch downstream, never through this lemma).  Skipped HEAD vars      *)
    (* contribute a trivial head clause; they only affect the [sub]-weaken   *)
    (* on the tail, which [atom_tree_sort_sub_cons_fresh] handles uniformly. *)
    Lemma ctx_readback_eF_lookup_gen (no_sort : V -> bool) (eF : instance X)
      : forall c sub, wf_ctx l c ->
          map fst c = map fst sub ->
          ctx_readback_eF_gen no_sort eF sub c ->
          forall nm x', In (nm, x') sub -> no_sort nm = false ->
            exists t xs, In (nm, t) c
                  /\ atom_tree_sort X eF sub t xs
                  /\ ain (Build_atom sort_of [x'] xs) eF.
    Proof.
      pose proof (wf_lang_implies_ws_noext Hwf) as Hwsl.
      induction c as [|[x tx] c' IH]; intros sub Hwfc Hdom Hrb nm x' Hin Hns.
      - destruct sub as [|[? ?] ?]; cbn in Hdom; [|discriminate].
        cbn in Hin. contradiction.
      - destruct sub as [|[x0 x'x] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hx Hdom'. subst x0.
        apply invert_wf_ctx_cons in Hwfc.
        destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
        cbn [ctx_readback_eF_gen] in Hrb.
        destruct Hrb as [Hhead Hrb'].
        cbn [In] in Hin. destruct Hin as [Heq | Hin'].
        + injection Heq as Hnm Hx'eq. subst nm x'.
          (* head var = looked-up var; non-skip, so the witness exists *)
          rewrite Hns in Hhead.
          destruct Hhead as [xs [Htree Hatom_sof] ].
          destruct tx as [ntx stx].
          exists (scon ntx stx), xs.
          split; [left; reflexivity|].
          split; [| exact Hatom_sof].
          refine (@Theorems.atom_tree_sort_sub_cons_fresh V V_Eqb V_Eqb_ok V_default
                    V_map V_trie X eF sub' x x'x ntx stx xs _ Htree).
          eapply (@Theorems.ws_sort_fresh_not_fv V V_Eqb x (map fst c') ntx stx);
            [ exact Hfresh |].
          eapply wf_sort_implies_ws; eassumption.
        + specialize (IH sub' Hwfc' Hdom' Hrb' nm x' Hin' Hns).
          destruct IH as (t & xs0 & Hin_c' & Htree' & Hatom').
          destruct t as [nt st].
          exists (scon nt st), xs0.
          split; [right; exact Hin_c'|].
          split; [| exact Hatom'].
          refine (@Theorems.atom_tree_sort_sub_cons_fresh V V_Eqb V_Eqb_ok V_default
                    V_map V_trie X eF sub' x x'x nt st xs0 _ Htree').
          eapply (@Theorems.ws_sort_fresh_not_fv V V_Eqb x (map fst c') nt st);
            [ exact Hfresh |].
          assert (Hwf_t : wf_sort l c' (scon nt st)) by (eapply in_ctx_wf; eauto).
          eapply wf_sort_implies_ws; eassumption.
    Qed.

    (* P5 bridge, _gen form: [ctx_readback_gen] (pre-rebuild) ->            *)
    (* [ctx_readback_eF_gen] (post-rebuild eF).  Mirrors [ctx_readback_to_eF]; *)
    (* the skipped-var head clause is trivial on both sides.                *)
    Lemma ctx_readback_to_eF_gen (no_sort : V -> bool) (e1 eF : instance X)
      (Hdbi : db_ctx_inv X e1)
      (Hsurv : forall a : atom,
          atom_in_egraph_up_to_equiv V V V_map V_map V_trie X a e1 ->
          all (is_root X e1) (atom_args a) ->
          is_root X e1 (atom_ret a) ->
          ain a eF)
      : forall c sub, wf_ctx l c ->
          all (fun p => is_root X e1 (snd p)) sub ->
          ctx_readback_gen X no_sort e1 sub c ->
          ctx_readback_eF_gen no_sort eF sub c.
    Proof.
      assert (Hrefl : forall xl,
                 all (is_root X e1) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e1)) xl xl).
      { induction xl as [|z xl IHxl]; cbn; [trivial|].
        intros [Hz Hxl]. split; [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]. }
      induction c as [|[x t] c' IH]; intros sub Hwfc Hroots Hrb.
      - cbn. exact I.
      - destruct sub as [|[x0 x'] sub'].
        + cbn in Hrb. contradiction.
        + apply invert_wf_ctx_cons in Hwfc.
          destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
          cbn in Hrb. destruct Hrb as [Hhead Hrb'].
          cbn in Hroots. destruct Hroots as [Hx'_root Hroots'].
          cbn [ctx_readback_eF_gen]. split.
          2:{ apply IH; [exact Hwfc' | exact Hroots' | exact Hrb']. }
          destruct (no_sort x).
          { exact I. }
          destruct Hhead as [xs [Hxs_root [Htree [tx' [Hatom_db Hper] ] ] ] ].
          exists xs. split.
          -- eapply atom_tree_sort_survives with (e:=e1) (c:=c');
               [ exact Hsof | exact Hdbi | | exact Hwst | exact Htree ].
             intros a Ha_in Ha_args Ha_ret.
             apply Hsurv; [ | exact Ha_args | exact Ha_ret ].
             exists a. split; [| exact Ha_in].
             unfold atom_canonical_equiv. split; [reflexivity|]. split.
             ++ apply Hrefl; exact Ha_args.
             ++ apply Relations.PER_clo_base; exact Ha_ret.
          -- apply Hsurv.
             ++ exists (Build_atom sort_of [x'] tx'). split.
                ** unfold atom_canonical_equiv.
                   cbn [atom_fn atom_args atom_ret Defs.atom_fn Defs.atom_args Defs.atom_ret].
                   split; [reflexivity|]. split.
                   --- cbn. split; [apply Relations.PER_clo_base; exact Hx'_root | exact I].
                   --- apply Relations.PER_clo_sym; exact Hper.
                ** exact Hatom_db.
             ++ cbn [atom_args Defs.atom_args]. split; [exact Hx'_root | exact I].
             ++ cbn [atom_ret Defs.atom_ret]. exact Hxs_root.
    Qed.

    (* ===== skip-sorts (_gen) reconstruction of the assignment ===== *)
    (* [ctx_readback_vals_gen]: the minimized-query analogue of               *)
    (* [ctx_readback_wf_subst], restricted to the VALUE map + leaf            *)
    (* correspondence (the non-circular part).  A skipped var                 *)
    (* ([no_sort x = true]) carries no [sort_of] atom, so its value is        *)
    (* supplied externally ([Hskip], discharged at the assembly from the LHS  *)
    (* image via [atom_tree_leaf_inl]); a non-skipped var's value is read off *)
    (* its [sort_of] atom (every sound atom resolves its args to terms,       *)
    (* [lang_model_args_inl]).  This yields the full value map [sg] and the   *)
    (* full companion leaf correspondence [Hfaith] -- WITHOUT building a       *)
    (* [wf_subst].  Recovering well-formedness at the declared (substituted)  *)
    (* sorts is the remaining obligation: it needs the skip vars' wf, which   *)
    (* in turn comes from the LHS image, so it cannot be done here (the       *)
    (* [wf_subst]-needs-[wf_subst] circularity).  [eq_ctx_inversion_gen]      *)
    (* closes it by feeding [sg]+[Hfaith] (plus the image) through            *)
    (* [skip_decl_wf_from_image] / [SyntacticSortCovering.covering_var_leaf_tr_con]. *)
    Lemma ctx_readback_vals_gen (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      : forall c sub, wf_ctx l c ->
          map fst c = map fst sub ->
          ctx_readback_eF_gen no_sort eF sub c ->
          (forall x, In x (map fst c) -> no_sort x = true ->
              exists es, map.get a (named_list_lookup default sub x) = Some (inl es)) ->
          exists sg, map fst sg = map fst c
                  /\ (forall x, In x (map fst sub) ->
                        map.get a (named_list_lookup default sub x)
                          = Some (inl (named_list_lookup default sg x))).
    Proof.
      induction c as [|[x t] c' IH]; intros sub Hwfc Hdom Hrb Hskip.
      - exists []. split; [reflexivity|].
        destruct sub as [|[? ?] ?]; cbn in Hdom; [|discriminate].
        intros x [].
      - destruct sub as [|[x0 x'] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hx Hdom'. subst x0.
        apply invert_wf_ctx_cons in Hwfc.
        destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
        cbn [ctx_readback_eF_gen] in Hrb.
        destruct Hrb as [Hhead Hrb'].
        (* tail [Hskip]: companion lookups of [sub'] agree with [sub] off [x] *)
        assert (Hskip' : forall y, In y (map fst c') -> no_sort y = true ->
                  exists es, map.get a (named_list_lookup default sub' y) = Some (inl es)).
        { intros y Hy Hyns.
          pose proof (eqb_spec y x) as Hsp.
          specialize (Hskip y (or_intror Hy) Hyns).
          cbn [named_list_lookup] in Hskip.
          destruct (eqb y x) eqn:Hyxb;
            [ subst y; contradiction | exact Hskip ]. }
        specialize (IH sub' Hwfc' Hdom' Hrb' Hskip').
        destruct IH as [sg' [Hdomsg' Hleaf'] ].
        (* head value [es] with [map.get a x' = Some (inl es)] *)
        assert (Hval : exists es, map.get a x' = Some (inl es)).
        { destruct (no_sort x) eqn:Hns.
          - (* skip: value from Hskip *)
            specialize (Hskip x (or_introl eq_refl) Hns).
            assert (Hlk_x : named_list_lookup default ((x,x')::sub') x = x').
            { cbn [named_list_lookup]. pose proof (eqb_spec x x) as Hs.
              destruct (eqb x x); [reflexivity | exfalso; apply Hs; reflexivity]. }
            rewrite Hlk_x in Hskip. exact Hskip.
          - (* non-skip: read the value off the [sort_of] atom *)
            destruct Hhead as [xs [Htree Hatom_sof] ].
            pose proof (Hsound _ Hatom_sof) as Hsnd.
            unfold Semantics.atom_sound_for_model, Is_Some_satisfying in Hsnd.
            cbn [atom_args atom_ret atom_fn Defs.atom_args Defs.atom_ret Defs.atom_fn
                 list_Mmap] in Hsnd.
            destruct (map.get a x') as [dx|] eqn:Hgx'; cbn beta iota in Hsnd; [|contradiction].
            destruct (map.get a xs) as [out|] eqn:Hgxs; cbn beta iota in Hsnd; [|contradiction].
            change (domain V lang_model) with (term + sort)%type in Hsnd.
            cbn [interprets_to lang_model] in Hsnd.
            apply lang_model_args_inl in Hsnd.
            destruct Hsnd as [ds Hds].
            destruct ds as [|d ds']; cbn [map] in Hds; [discriminate|].
            injection Hds as Hd _. subst dx.
            exists d. reflexivity. }
        destruct Hval as [es Hgx'].
        exists ((x, es) :: sg'). split.
        + cbn [map fst]. rewrite Hdomsg'. reflexivity.
        + intros y Hy. pose proof (eqb_spec y x) as Hsp.
          cbn [named_list_lookup].
          destruct (eqb y x) eqn:Hyx.
          * subst y. exact Hgx'.
          * apply Hleaf'. cbn [map fst] in Hy.
            destruct Hy as [Heqyx | Hy];
              [ exfalso; apply Hsp; symmetry; exact Heqyx | exact Hy ].
    Qed.

    (* ===== skip-sorts (_gen) IN-ORDER wf_subst reconstruction ===== *)
    (* [ctx_readback_wf_subst_gen]: the minimized-query analogue of            *)
    (* [ctx_readback_wf_subst].  Builds [wf_subst l [] sg c] by HEAD-FIRST     *)
    (* induction over [c] (Pyrosome ctx cons = most-dependent var first; the   *)
    (* tail [c'] is the strictly-earlier "prefix").  The IH supplies a         *)
    (* COMPLETE prefix [wf_subst l [] sg' c'] (the user's in-order unlock), so *)
    (* [t[/sg'/]] is the declared sort each head must hit.                     *)
    (*                                                                         *)
    (*  - NON-skip head [x]: value + declared-sort wf come from the var's      *)
    (*    [sort_of] atom (its model sort is [eq_sort] to [t[/sg'/]] via         *)
    (*    [add_open_faithful_rep_sort]; [sg'] is now a real wf_subst, so this   *)
    (*    applies -- exactly as in [ctx_readback_wf_subst]).                    *)
    (*  - SKIP head [x]: the value + [wf_term l [] es (t[/sg'/])] are supplied  *)
    (*    by [skip_decl_wf] (discharged at the assembly from the LHS image via   *)
    (*    [skip_decl_wf_from_image], i.e. [covering_var_leaf_rigid_con] fed by  *)
    (*    the wf_subst-free [Theorems.faithful_rep_rigid_root], gated on the    *)
    (*    per-variable pattern-rigidity check (Theory/PatternRigidity.v)).      *)
    (* The skip-var declared-sort witness, phrased against the INCREMENTAL
       prefix substitution [sg'] the induction produces (a genuine wf_subst
       over the prefix [c']).  At the assembly this is discharged from the LHS
       image by [skip_decl_wf_from_image] via [covering_var_leaf_rigid_con]
       (gated on per-variable pattern rigidity, [rigid_term_skip]/
       [rigid_sort_skip]; the transport-based [_tr] variants above remain
       for the general seam). *)
    Fixpoint skip_decl_wf (no_sort : V -> bool) (a : interp)
      (sub : named_list V) (c0 : ctx) {struct c0} : Prop :=
      match c0, sub with
      | [], _ => True
      | (x,t)::c', (_, x')::sub' =>
          (no_sort x = true ->
             forall sg', wf_subst l [] sg' c' ->
                map fst sg' = map fst c' ->
                (forall y, In y (map fst sub') ->
                   map.get a (named_list_lookup default sub' y)
                     = Some (inl (named_list_lookup default sg' y))) ->
                exists es, map.get a x' = Some (inl es)
                        /\ wf_term l [] es (t[/sg'/]))
          /\ skip_decl_wf no_sort a sub' c'
      | _, _ => True
      end.

    Lemma ctx_readback_wf_subst_gen (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      : forall c sub, wf_ctx l c ->
          map fst c = map fst sub ->
          ctx_readback_eF_gen no_sort eF sub c ->
          skip_decl_wf no_sort a sub c ->
          exists sg, wf_subst l [] sg c
                  /\ map fst sg = map fst c
                  /\ (forall x, In x (map fst sub) ->
                        map.get a (named_list_lookup default sub x)
                          = Some (inl (named_list_lookup default sg x))).
    Proof.
      induction c as [|[x t] c' IH]; intros sub Hwfc Hdom Hrb Hskip.
      - exists []. split; [|split].
        + constructor.
        + reflexivity.
        + destruct sub as [|[? ?] ?]; cbn in Hdom; [|discriminate].
          intros x [].
      - destruct sub as [|[x0 x'] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hx Hdom'. subst x0.
        apply invert_wf_ctx_cons in Hwfc.
        destruct Hwfc as [Hfresh [Hwfc' Hwst] ].
        cbn [ctx_readback_eF_gen] in Hrb.
        destruct Hrb as [Hhead Hrb'].
        cbn [skip_decl_wf] in Hskip.
        destruct Hskip as [Hskiphead Hskip'].
        specialize (IH sub' Hwfc' Hdom' Hrb' Hskip').
        destruct IH as [sg' [Hwfsub' [Hdomsg' Hleaf'] ] ].
        destruct (no_sort x) eqn:Hns.
        + (* SKIP head var: declared-sort wf from the external witness *)
          specialize (Hskiphead eq_refl sg' Hwfsub' Hdomsg' Hleaf').
          destruct Hskiphead as [es [Hgx' Hwfes] ].
          exists ((x, es) :: sg'). split; [|split].
          * econstructor; [exact Hwfsub' | exact Hwfes].
          * cbn [map fst]. rewrite Hdomsg'. reflexivity.
          * intros y Hy. cbn [map fst] in Hy. cbn [named_list_lookup].
            pose proof (eqb_spec y x) as Hsp.
            destruct (eqb y x) eqn:Hyx;
              [ subst y; exact Hgx'
              | apply Hleaf'; destruct Hy as [Heqyx | Hy];
                  [ exfalso; apply Hsp; symmetry; exact Heqyx | exact Hy ] ].
        + (* NON-skip head var: declared-sort wf from its [sort_of] atom,
             exactly as in [ctx_readback_wf_subst] (now [sg'] is a real
             wf_subst). *)
          cbn beta iota in Hhead.
          destruct Hhead as [xs [Htree Hatom_sof] ].
          assert (Hrep : represents_sort X l a eF sg' t xs).
          { eapply atom_tree_sort_to_represents_sort; eauto. }
          assert (Hfr : exists t', map.get a xs = Some (inr t')
                                /\ eq_sort l [] t' (t[/sg'/])).
          { eapply add_open_faithful_rep_sort; eauto. }
          destruct Hfr as [t' Hfr2]. destruct Hfr2 as [Hgxs Heqs].
          pose proof (Hsound _ Hatom_sof) as Hsnd.
          unfold Semantics.atom_sound_for_model, Is_Some_satisfying in Hsnd.
          cbn [atom_args atom_ret atom_fn Defs.atom_args Defs.atom_ret Defs.atom_fn
               list_Mmap] in Hsnd.
          destruct (map.get a x') as [dx|] eqn:Hgx'; cbn beta iota in Hsnd; [|contradiction].
          rewrite Hgxs in Hsnd.
          cbn beta iota in Hsnd.
          change (domain V lang_model) with (term + sort)%type in Hsnd.
          cbn [interprets_to lang_model] in Hsnd.
          cbn in Hsnd.
          inversion Hsnd as
            [ es t_es Hwt_es Hargdom Houtdom
            | f0 args0 t0 Heqs0 Hargdom Houtdom
            | f0 args0 e0 t0 Heqe0 Hargdom Houtdom ].
          * exists ((x, es) :: sg').
            split; [|split].
            -- econstructor; [exact Hwfsub' | eapply wf_term_conv; [exact Hwt_es | exact Heqs] ].
            -- cbn [map fst]. rewrite Hdomsg'. reflexivity.
            -- intros y Hy. cbn [map fst] in Hy. cbn [named_list_lookup].
               pose proof (eqb_spec y x) as Hsp.
               destruct (eqb y x) eqn:Hyx;
                 [ rewrite Houtdom; exact Hgx'
                 | apply Hleaf'; destruct Hy as [Heqyx | Hy];
                     [ exfalso; apply Hsp; symmetry; exact Heqyx | exact Hy ] ].
          * exfalso.
            apply eq_sort_wf_l in Heqs0; eauto with lang_core.
            safe_invert Heqs0.
            match goal with Hin : In (sort_of, _) l |- _ =>
              apply Hsof; eapply pair_fst_in; exact Hin end.
    Qed.

    (* Substitution extensionality: two substitutions that AGREE (by lookup)
       on every free variable of a term/sort give the same result.  This is the
       "generic strengthening" the in-order construction needs to replace the
       partial prefix substitution [sg'] by the full model value-map [sg]:
       the declared sort [t] is well-scoped over [x]'s prefix [c'] (= dom sg'),
       and [sg']/[sg] agree there ([Hagree]), so [t[/sg'/] = t[/sg/]]. *)
    Lemma term_var_map_ext (f g : V -> term) e
      : (forall y, In y (fv e) -> f y = g y) ->
        term_var_map f e = term_var_map g e.
    Proof.
      induction e as [x | n s IHs] using term_ind; intro Hag.
      - cbn [term_var_map fv] in *. apply Hag. left; reflexivity.
      - cbn [term_var_map fv] in *. f_equal.
        revert Hag; induction s as [|e0 s0 IH]; intro Hag; cbn [map]; [reflexivity|].
        cbn [all] in IHs. destruct IHs as [IHe0 IHs0].
        f_equal.
        + apply IHe0. intros y Hy. apply Hag.
          cbn [flat_map]. apply in_or_app. left. exact Hy.
        + apply IH; [exact IHs0|]. intros y Hy. apply Hag.
          cbn [flat_map]. apply in_or_app. right. exact Hy.
    Qed.

    Lemma term_subst_ext (sg1 sg2 : subst) e
      : (forall y, In y (fv e) ->
           named_list_lookup (var y) sg1 y = named_list_lookup (var y) sg2 y) ->
        e[/sg1/] = e[/sg2/].
    Proof.
      intro Hag.
      change (e[/?sg/]) with (term_subst sg e).
      unfold term_subst.
      apply term_var_map_ext. intros y Hy. cbn [term_subst_lookup].
      apply Hag; exact Hy.
    Qed.

    Lemma sort_subst_ext (sg1 sg2 : subst) (t : sort)
      : (forall y, In y (fv_sort t) ->
           named_list_lookup (var y) sg1 y = named_list_lookup (var y) sg2 y) ->
        t[/sg1/] = t[/sg2/].
    Proof.
      destruct t as [n s]. intro Hag.
      change ((scon n s)[/?sg/]) with (scon n (args_subst sg s)).
      f_equal.
      unfold fv_sort, fv_args in Hag.
      unfold args_subst.
      revert Hag; induction s as [|e0 s0 IH]; intro Hag; cbn [map]; [reflexivity|].
      f_equal.
      - change (apply_subst0 ?sg e0) with (e0[/sg/]).
        apply term_subst_ext. intros y Hy. apply Hag.
        cbn [flat_map]. apply in_or_app. left. exact Hy.
      - apply IH. intros y Hy. apply Hag.
        cbn [flat_map]. apply in_or_app. right. exact Hy.
    Qed.

    (* The declared sort [t] of [x] is well-scoped over its prefix [c'] (= dom
       sg'), on which [sg'] and the full value-map [sg] agree ([Hagree]); hence
       substituting [t] by [sg'] equals substituting by [sg].  This lets the
       skip-var checkpoint be discharged against the FULL substitution [sg]
       (where the engine value-wf and faithful representation live) and then
       transported back to the prefix form [t[/sg'/]] that [wf_subst] wants. *)
    Lemma term_fv_in_ws (args : list V) e
      : ws_term args e -> forall y, In y (fv e) -> In y args.
    Proof.
      induction e as [x | n s IHs] using term_ind; cbn [ws_term fv].
      - intros Hin y Hy. destruct Hy as [Hy | Hy]; [subst y; exact Hin | contradiction].
      - intros Hall y Hy.
        revert Hall; induction s as [|e0 s0 IH]; cbn [flat_map all] in *;
          [contradiction|].
        intros [Hwe0 Hall0]. destruct IHs as [IHe0 IHs0].
        apply in_app_or in Hy. destruct Hy as [Hy | Hy].
        + eapply IHe0; eauto.
        + eapply IH; eauto.
    Qed.

    Lemma sort_fv_in_ws (args : list V) (t : sort)
      : ws_sort args t -> forall y, In y (fv_sort t) -> In y args.
    Proof.
      destruct t as [n s]. cbn [ws_sort]. unfold fv_sort, fv_args.
      change (ws_args args s) with (all (ws_term args) s).
      induction s as [|e0 s0 IH]; cbn [flat_map all]; [contradiction|].
      intros [Hwe0 Hall0] y Hy.
      apply in_app_or in Hy. destruct Hy as [Hy | Hy].
      - eapply term_fv_in_ws; eauto.
      - eapply IH; eauto.
    Qed.

    (* A present key's lookup ignores the default. *)
    Lemma nll_default_indep (s : subst) y (d1 d2 : term)
      : In y (map fst s) ->
        named_list_lookup d1 s y = named_list_lookup d2 s y.
    Proof.
      induction s as [|[z v] s0 IH]; cbn [map fst named_list_lookup]; [contradiction|].
      intro Hin. eqb_case y z; [reflexivity|].
      destruct Hin as [Hzy | Hin]; [exfalso; congruence | apply IH; exact Hin].
    Qed.

    Lemma decl_sort_subst_prefix_eq (sg sg' : subst) (t : sort) (c' : ctx)
      (Hwst : wf_sort l c' t)
      (Hdomsg' : map fst sg' = map fst c')
      (Hdomsg : incl (map fst c') (map fst sg))
      (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y)
      : t[/sg'/] = t[/sg/].
    Proof.
      apply sort_subst_ext. intros y Hy.
      (* y in fv_sort t -> y in map fst c' (well-scopedness of t over c') *)
      assert (Hyc' : In y (map fst c')).
      { eapply sort_fv_in_ws; [ | exact Hy ].
        eapply wf_sort_implies_ws; eauto with lang_core. }
      assert (Hin' : In y (map fst sg')) by (rewrite Hdomsg'; exact Hyc').
      assert (Hin_sg : In y (map fst sg)) by (apply Hdomsg; exact Hyc').
      rewrite (nll_default_indep sg' y (var y) default Hin').
      rewrite (nll_default_indep sg y (var y) default Hin_sg).
      apply Hagree; exact Hyc'.
    Qed.
    (* ================================================================== *)
    (* THE SKIP-VARIABLE DISCHARGE (gated on [sort_transport_at l []]).    *)
    (*                                                                     *)
    (* Both the term-LHS ([skip_var_decl_sort_wf]) and sort-LHS            *)
    (* ([skip_var_decl_sort_wf_scon]) skip-variable obligations are        *)
    (* discharged by [covering_var_leaf_tr_con] (resp. its args helper),   *)
    (* which -- under [sort_transport_at l []] -- delivers, for every      *)
    (* var [x] occurring in a source-typed [e] whose IMAGE [e[/sg/]] is    *)
    (* wf, that [sg x] is wf at x's substituted DECLARED sort [t[/sg/]].  *)
    (* No [wf_subst l [] sg Cfull] is needed.  The single missing         *)
    (* ingredient is the wf_subst-free whole-LHS image wf, supplied by    *)
    (* [Theorems.faithful_rep_tr] (term) and                              *)
    (* [Theorems.faithful_rep_sort_args_tr] (sort).  The former           *)
    (* [skip_var_decl_sort_core] checkpoint (an [Admitted]                *)
    (* substitution-typing-reflection metatheorem) is hereby ELIMINATED.  *)
    (* [syntactic_sort_eq l] implies [sort_transport_at l []] via          *)
    (* [syntactic_sort_eq_transport_at], and the weakened poly checker     *)
    (* will discharge it once its soundness proof lands.                   *)

    Lemma skip_var_decl_sort_wf (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Htr : sort_transport_at l [])
      (Hsound : forall al, ain al eF -> asnd a al)
      (sg : subst) (n0 : V) (s0 : list term) (x1 : V)
      (Hrep : @Theorems.represents V V_Eqb V_default V_map V_trie sort_of X l a eF sg
                (con n0 s0) x1)
      (* the FULL rule ctx and the telescope position of [x]:
         [Cfull = pre ++ (x,t)::c'], so [t] is x's declared sort over its
         prefix [c'] and [c'] is x's strict prefix in the telescope. *)
      (Cfull pre : ctx) (t1 : sort)
      (Hwfcf : wf_ctx l Cfull) (Hwfe1f : wf_term l Cfull (con n0 s0) t1)
      (x : V) (t : sort) (c' : ctx) (sg' : subst)
      (Hcfull : Cfull = pre ++ (x,t)::c')
      (Hxfv : In x (fv (con n0 s0)))
      (Hwfsub' : wf_subst l [] sg' c')
      (Hdomsg' : map fst sg' = map fst c')
      (* the full model value-map [sg] covers the whole rule context, hence in
         particular [c'] (= x's dependencies). *)
      (Hdomsg : incl (map fst c') (map fst sg))
      (* [sg] domain spans the whole rule ctx (= [covering_var_leaf_tr_con]'s [Hmap]). *)
      (Hdomsgcf : map fst sg = map fst Cfull)
      (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y)
      : wf_term l [] (named_list_lookup default sg x) (t[/sg'/]).
    Proof.
      (* [t] is well-scoped over [x]'s prefix [c'] (the declared-sort position in
         the head-first context), so substituting by the prefix [sg'] or by the
         full value-map [sg] coincide -- "generic strengthening". *)
      assert (Hwst : wf_sort l c' t).
      { subst Cfull.
        clear -Hwfcf.
        induction pre as [|[pn pt] pre IH]; cbn [app] in Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply IH. apply Hwfcf. }
      assert (Hwfc' : wf_ctx l c').
      { subst Cfull.
        assert (Hgen : forall pre0 cc, wf_ctx l (pre0 ++ cc) -> wf_ctx l cc).
        { clear. intros pre0; induction pre0 as [|[pn pt] pre0 IHp]; intros cc Hw.
          - cbn in Hw. exact Hw.
          - cbn in Hw. apply invert_wf_ctx_cons in Hw.
            destruct Hw as [_ [Hw' _] ]. exact (IHp cc Hw'). }
        pose proof (Hgen pre ((x,t)::c') Hwfcf) as Hsuf.
        apply invert_wf_ctx_cons in Hsuf.
        destruct Hsuf as [_ [Hwfc'' _] ]. exact Hwfc''. }
      rewrite (decl_sort_subst_prefix_eq sg sg' t c' Hwst Hdomsg' Hdomsg Hagree).
      (* Goal is now [wf_term l [] (sg x) (t[/sg/])]. *)
      (* Derive [wf_sort l [] (t[/sg/])] for the trailing argument of
         [covering_var_leaf_tr_con].  First get [wf_sort l [] (t[/sg'/])] from
         [Hwst] and [Hwfsub'], then rewrite along
         [decl_sort_subst_prefix_eq]. *)
      assert (Hwfts : wf_sort l [] (t[/sg/])).
      { assert (Hwfts' : wf_sort l [] (t[/sg'/]))
          by (exact (wf_sort_subst_monotonicity Hwf Hwst Hwfc' Hwfsub')).
        rewrite <- (decl_sort_subst_prefix_eq sg sg' t c' Hwst Hdomsg' Hdomsg Hagree).
        exact Hwfts'. }
      (* whole-LHS image wf, wf_subst-free under [Htr]. *)
      assert (Hdom : incl (map fst Cfull) (map fst sg))
        by (rewrite Hdomsgcf; apply incl_refl).
      pose proof (@Theorems.faithful_rep_tr V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of
                    X l Hwf Hsof Htr a eF sg Hsound (con n0 s0) Cfull t1 Hwfcf Hwfe1f Hdom x1 Hrep)
        as Hfr.
      destruct Hfr as (e' & T & Hget & HeqT & _).
      assert (Himg : wf_term l [] ((con n0 s0)[/sg/]) T)
        by (exact (eq_term_wf_r Hwf ltac:(constructor) HeqT)).
      (* [x] is in [dom sg] (it is the head of the suffix of [Cfull]). *)
      assert (Hxin : In x (map fst sg)).
      { rewrite Hdomsgcf, Hcfull, map_app. apply in_or_app; right.
        cbn [map fst]. left; reflexivity. }
      assert (Hlk : named_list_lookup default sg x = subst_lookup sg x)
        by (apply (nll_default_indep sg x default (var x) Hxin)).
      rewrite Hlk.
      (* The covering metatheorem (under [Htr]) closes the leaf. *)
      exact (@covering_var_leaf_tr_con V V_Eqb V_Eqb_ok V_default l Hwf [] Cfull sg
               Htr ltac:(constructor) Hwfcf Hdomsgcf n0 s0 t1 T Hwfe1f Himg x t Hxfv
               ltac:(rewrite Hcfull; apply in_or_app; right; left; reflexivity)
               Hwfts).
    Qed.

    (* Rigid variant of [skip_var_decl_sort_wf]: the [sort_transport_at] gate
       is replaced by pattern-rigidity checker booleans from
       [PatternRigidity.check_args].  The rest of the statement is identical. *)
    Lemma skip_var_decl_sort_wf_rigid (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      (sg : subst) (n0 : V) (s0 : list term) (x1 : V)
      (Hrep : @Theorems.represents V V_Eqb V_default V_map V_trie sort_of X l a eF sg
                (con n0 s0) x1)
      (cR : ctx) (argsR : list V) (tR : sort)
      (Hrule : named_list_lookup_err l n0 = Some (term_rule cR argsR tR))
      (Hchk : fst (check_args l s0 cR) = true)
      (Cfull pre : ctx) (t1 : sort)
      (Hwfcf : wf_ctx l Cfull) (Hwfe1f : wf_term l Cfull (con n0 s0) t1)
      (x : V) (t : sort) (c' : ctx) (sg' : subst)
      (Hcfull : Cfull = pre ++ (x,t)::c')
      (Hxfv : In x (fv (con n0 s0)))
      (Hocc : forall E, In (x, E) (snd (check_args l s0 cR)) -> E = t)
      (Hwfsub' : wf_subst l [] sg' c')
      (Hdomsg' : map fst sg' = map fst c')
      (Hdomsg : incl (map fst c') (map fst sg))
      (Hdomsgcf : map fst sg = map fst Cfull)
      (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y)
      : wf_term l [] (named_list_lookup default sg x) (t[/sg'/]).
    Proof.
      assert (Hwst : wf_sort l c' t).
      { subst Cfull.
        clear -Hwfcf.
        induction pre as [|[pn pt] pre IH]; cbn [app] in Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply IH. apply Hwfcf. }
      rewrite (decl_sort_subst_prefix_eq sg sg' t c' Hwst Hdomsg' Hdomsg Hagree).
      assert (Hdom : incl (map fst Cfull) (map fst sg))
        by (rewrite Hdomsgcf; apply incl_refl).
      pose proof (@Theorems.faithful_rep_rigid_root V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of
                    X l Hwf Hsof a eF sg Hsound n0 s0 cR argsR tR Cfull t1 Hrule Hchk Hwfcf Hwfe1f Hdom x1 Hrep)
        as Hfr.
      destruct Hfr as (e' & T & Hget & HeqT & Himg).
      assert (Hxin : In x (map fst sg)).
      { rewrite Hdomsgcf, Hcfull, map_app. apply in_or_app; right.
        cbn [map fst]. left; reflexivity. }
      assert (Hlk : named_list_lookup default sg x = subst_lookup sg x)
        by (apply (nll_default_indep sg x default (var x) Hxin)).
      rewrite Hlk.
      assert (HinCfull : In (x, t) Cfull)
        by (rewrite Hcfull; apply in_or_app; right; left; reflexivity).
      eapply (@PatternRigidity.covering_var_leaf_rigid_con V V_Eqb V_Eqb_ok l Hwf
               [] Cfull sg Hwfcf Hdomsgcf n0 s0 cR argsR tR t1 T);
        [ exact Hrule | exact Hchk | exact Hwfe1f | exact Himg | exact Hxfv | exact HinCfull | exact Hocc ].
    Qed.

    (* =============================================================== *)
    (* Discharge of [skip_decl_wf] from the LHS image: assemble the     *)
    (* per-skip-var declared-sort witnesses (each from                  *)
    (* [skip_var_decl_sort_wf_rigid]) into the [skip_decl_wf] predicate  *)
    (* by induction over the ctx/sub telescope.  The gate is now the     *)
    (* per-variable pattern-rigidity boolean [rigid_term_skip]           *)
    (* (Theory/PatternRigidity.v); the transport-based                   *)
    (* [skip_var_decl_sort_wf] above remains for the general seam. *)
    Lemma skip_decl_wf_from_image (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      (sg : subst) (n0 : V) (s0 : list term) (x1 : V)
      (Hrep : @Theorems.represents V V_Eqb V_default V_map V_trie sort_of X l a eF sg
                (con n0 s0) x1)
      : forall c sub t1, wf_ctx l c -> wf_term l c (con n0 s0) t1 ->
          (forall x, no_sort x = true -> rigid_term_skip l c (con n0 s0) x = true) ->
          map fst c = map fst sub ->
          (* the full model value-map [sg] covers the whole rule context *)
          map fst sg = map fst c ->
          (forall x, no_sort x = true -> In x (fv (con n0 s0))) ->
          (forall x, In x (map fst sub) ->
                map.get a (named_list_lookup default sub x)
                  = Some (inl (named_list_lookup default sg x))) ->
          skip_decl_wf no_sort a sub c.
    Proof.
      intros Cfull sub t1 Hwfcf Hwfe1f Hrig Hdom Hdomsgc Hskipset Hvals.
      (* Track the prefix [pre] so that, at each head [(x,t)::c'], the FULL ctx
         is [Cfull = pre ++ (x,t)::c'].  This certifies [t] is x's declared sort
         over its strict prefix [c'] (the telescope link [skip_var_decl_sort_wf]
         needs).  We induct on a suffix [c] of [Cfull], keeping [Cfull]/[Hwfcf]/
         [Hwfe1f] fixed. *)
      (* generalize the suffix *)
      cut (forall (c : ctx) sub,
             (exists pre, Cfull = pre ++ c) ->
             map fst c = map fst sub ->
             (forall x, In x (map fst sub) ->
                map.get a (named_list_lookup default sub x)
                  = Some (inl (named_list_lookup default sg x))) ->
             skip_decl_wf no_sort a sub c).
      { intro Hcut. apply Hcut; [exists (@nil (V*sort)); reflexivity | exact Hdom | exact Hvals]. }
      clear Hdom Hvals sub.
      intro c. induction c as [|[x t] c' IH]; intros sub Hpre Hdom Hvals.
      - cbn. exact I.
      - destruct sub as [|[x0 x'] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hxx0 Hdom'. subst x0.
        (* wf_ctx of the suffix: it is a suffix of the wf full ctx *)
        assert (Hwfc_suf : wf_ctx l ((x,t)::c')).
        { destruct Hpre as [pre Hpre'].
          assert (Hgen : forall pre0 cc, wf_ctx l (pre0 ++ cc) -> wf_ctx l cc).
          { clear. intros pre0; induction pre0 as [|[pn pt] pre0 IHp]; intros cc Hw.
            - cbn in Hw. exact Hw.
            - cbn in Hw. apply invert_wf_ctx_cons in Hw.
              destruct Hw as [_ [Hw' _] ]. exact (IHp cc Hw'). }
          eapply Hgen. rewrite <- Hpre'. exact Hwfcf. }
        apply invert_wf_ctx_cons in Hwfc_suf.
        destruct Hwfc_suf as [Hfresh [Hwfc' Hwst] ].
        cbn [skip_decl_wf]. split.
        2:{ apply IH; [ | exact Hdom' | ].
            - (* tail prefix link: Cfull = (pre ++ [(x,t)]) ++ c' *)
              destruct Hpre as [pre Hpre']. exists (pre ++ [(x,t)]).
              rewrite <- app_assoc. cbn [app]. exact Hpre'.
            - intros y Hy. pose proof (Hvals y) as Hv. cbn beta in Hv.
              cbn [named_list_lookup map fst] in Hv.
              (* y is in sub', distinct from x (fresh), so lookup agrees *)
              assert (Hyx : y <> x).
              { intro; subst y. unfold fresh in Hfresh.
                rewrite Hdom' in Hfresh. apply Hfresh. exact Hy. }
              pose proof (eqb_spec y x) as Hsp.
              destruct (eqb y x) eqn:Hyxb; [exfalso; apply Hyx; exact Hsp|].
              apply Hv. cbn [map fst]. right. exact Hy. }
        (* head skip clause *)
        intros Hns sg' Hwfsub' Hdomsg' Hleaf'.
        (* the head value [es = sg x = a x'] *)
        assert (Hgx' : map.get a x' = Some (inl (named_list_lookup default sg x))).
        { pose proof (Hvals x (or_introl eq_refl)) as Hv.
          cbn [named_list_lookup] in Hv.
          pose proof (eqb_spec x x) as Hs.
          destruct (eqb x x); [exact Hv | exfalso; apply Hs; reflexivity]. }
        exists (named_list_lookup default sg x).
        split; [exact Hgx'|].
        (* x occurs in the LHS (skip), declared sort [t] over the prefix [c'],
           prefix [wf_subst l [] sg' c'] in hand.  Discharge via
           [skip_var_decl_sort_wf]. *)
        assert (Hxfv : In x (fv (con n0 s0))) by (apply Hskipset; exact Hns).
        (* prefix value-maps agree: both [sg'] and [sg] resolve [sub']'s
           companions to the same model values. *)
        assert (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y).
        { intros y Hy. rewrite Hdom' in Hy.
          (* companion id [sub' y] resolves to both [sg' y] and [sg y] *)
          pose proof (Hleaf' y Hy) as Hsg'y.
          pose proof (Hvals y) as Hsgy. cbn beta in Hsgy.
          assert (Hyx : y <> x).
          { intro; subst y. unfold fresh in Hfresh. rewrite Hdom' in Hfresh.
            apply Hfresh; exact Hy. }
          cbn [named_list_lookup map fst] in Hsgy.
          pose proof (eqb_spec y x) as Hsp.
          destruct (eqb y x) eqn:Hyxb; [exfalso; apply Hyx; exact Hsp|].
          specialize (Hsgy (or_intror Hy)).
          rewrite Hsg'y in Hsgy. injection Hsgy as Hsgy. exact Hsgy. }
        destruct Hpre as [pre Hpre'].
        (* [c'] is a suffix of [Cfull], whose domain is [map fst sg] ([Hdomsgc]) *)
        assert (Hincl : incl (map fst c') (map fst sg)).
        { rewrite Hdomsgc. rewrite Hpre'.
          rewrite map_app. cbn [map app]. intro z. intro Hz.
          apply in_or_app. right. right. exact Hz. }
        (* use rigidity checker to extract rule info *)
        pose proof (rigid_term_skip_inv l Cfull (con n0 s0) x (Hrig x Hns))
          as Hinv.
        destruct Hinv as (n0' & s0' & cR & argsR & tR & tx & Heq1 & Hrule & Hchk & Hxfv' & Hlkc & Hocc').
        injection Heq1 as Hn0eq Hs0eq. subst n0' s0'.
        (* pin tx to t via all-fresh Cfull *)
        assert (HallfrCf : all_fresh Cfull) by (eauto with model).
        symmetry in Hlkc.
        apply named_list_lookup_err_in in Hlkc.
        assert (HinCfull_xt : In (x, t) Cfull)
          by (rewrite Hpre'; apply in_or_app; right; left; reflexivity).
        pose proof (in_all_fresh_same _ _ _ _ HallfrCf Hlkc HinCfull_xt) as Heqtx.
        subst tx.
        exact (skip_var_decl_sort_wf_rigid no_sort eF a Hsound sg n0 s0 x1 Hrep
                  cR argsR tR Hrule Hchk Cfull pre t1 Hwfcf Hwfe1f x t c' sg' Hpre' Hxfv
                  Hocc' Hwfsub' Hdomsg' Hincl Hdomsgc Hagree).
    Qed.

    (* ============ SORT_EQ analogues (scon LHS) ============ *)

    (* Sort-LHS checkpoint, mirroring [skip_var_decl_sort_wf] but for a var
       occurring in a SORT LHS [scon n0 s0].  Same residual obligation
       (use->declared sort conversion). *)
    Lemma skip_var_decl_sort_wf_scon (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Htr : sort_transport_at l [])
      (Hsound : forall al, ain al eF -> asnd a al)
      (sg : subst) (n0 : V) (s0 : list term) (xs1 : V)
      (Hrep : @Theorems.represents_sort V V_Eqb V_default V_map V_trie sort_of X l a eF sg
                (scon n0 s0) xs1)
      (Cfull pre : ctx)
      (Hwfcf : wf_ctx l Cfull) (Hwft1f : wf_sort l Cfull (scon n0 s0))
      (x : V) (t : sort) (c' : ctx) (sg' : subst)
      (Hcfull : Cfull = pre ++ (x,t)::c')
      (Hxfv : In x (fv_args s0))
      (Hwfsub' : wf_subst l [] sg' c')
      (Hdomsg' : map fst sg' = map fst c')
      (Hdomsg : incl (map fst c') (map fst sg))
      (Hdomsgcf : map fst sg = map fst Cfull)
      (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y)
      : wf_term l [] (named_list_lookup default sg x) (t[/sg'/]).
    Proof.
      assert (Hwst : wf_sort l c' t).
      { subst Cfull.
        clear -Hwfcf.
        induction pre as [|[pn pt] pre IH]; cbn [app] in Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply IH. apply Hwfcf. }
      assert (Hwfc' : wf_ctx l c').
      { subst Cfull.
        assert (Hgen : forall pre0 cc, wf_ctx l (pre0 ++ cc) -> wf_ctx l cc).
        { clear. intros pre0; induction pre0 as [|[pn pt] pre0 IHp]; intros cc Hw.
          - cbn in Hw. exact Hw.
          - cbn in Hw. apply invert_wf_ctx_cons in Hw.
            destruct Hw as [_ [Hw' _] ]. exact (IHp cc Hw'). }
        pose proof (Hgen pre ((x,t)::c') Hwfcf) as Hsuf.
        apply invert_wf_ctx_cons in Hsuf.
        destruct Hsuf as [_ [Hwfc'' _] ]. exact Hwfc''. }
      rewrite (decl_sort_subst_prefix_eq sg sg' t c' Hwst Hdomsg' Hdomsg Hagree).
      (* Derive [wf_sort l [] (t[/sg/])] for the trailing argument of
         [covering_var_leaf_tr_args_aux]. *)
      assert (Hwfts : wf_sort l [] (t[/sg/])).
      { assert (Hwfts' : wf_sort l [] (t[/sg'/]))
          by (exact (wf_sort_subst_monotonicity Hwf Hwst Hwfc' Hwfsub')).
        rewrite <- (decl_sort_subst_prefix_eq sg sg' t c' Hwst Hdomsg' Hdomsg Hagree).
        exact Hwfts'. }
      (* source + (wf_subst-free) image wf_args of the LHS sort, sharing the
         rule ctx [cR], from the faithful sort representation under [Htr]. *)
      assert (Hdom : incl (map fst Cfull) (map fst sg))
        by (rewrite Hdomsgcf; apply incl_refl).
      pose proof (@Theorems.faithful_rep_sort_args_tr V V_Eqb V_Eqb_ok V_default V_map V_trie
                    sort_of X l Hwf Hsof Htr a eF sg Hsound n0 s0 Cfull Hwfcf Hwft1f Hdom xs1 Hrep)
        as Hfrs.
      destruct Hfrs as (cR & HwfcR & HwfaSrc & HwfaImg).
      (* [x] is in [dom sg]. *)
      assert (Hxin : In x (map fst sg)).
      { rewrite Hdomsgcf, Hcfull, map_app. apply in_or_app; right.
        cbn [map fst]. left; reflexivity. }
      assert (Hlk : named_list_lookup default sg x = subst_lookup sg x)
        by (apply (nll_default_indep sg x default (var x) Hxin)).
      rewrite Hlk.
      (* The covering args walk (under [Htr]) closes the leaf. *)
      exact (@covering_var_leaf_tr_args_aux V V_Eqb V_Eqb_ok l Hwf [] Cfull sg
               Htr ltac:(constructor) Hwfcf Hdomsgcf s0
               (fun e _ => @covering_var_leaf_tr V V_Eqb V_Eqb_ok V_default l Hwf [] Cfull sg
                             Htr ltac:(constructor) Hwfcf Hdomsgcf e)
               cR HwfcR HwfaSrc HwfaImg x t Hxfv
               ltac:(rewrite Hcfull; apply in_or_app; right; left; reflexivity)
               Hwfts).
    Qed.

    (* Rigid variant of [skip_var_decl_sort_wf_scon]: the [sort_transport_at]
       gate is replaced by pattern-rigidity checker booleans. *)
    Lemma skip_var_decl_sort_wf_scon_rigid (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      (sg : subst) (n0 : V) (s0 : list term) (xs1 : V)
      (Hrep : @Theorems.represents_sort V V_Eqb V_default V_map V_trie sort_of X l a eF sg
                (scon n0 s0) xs1)
      (cR : ctx) (argsR : list V)
      (Hrule : named_list_lookup_err l n0 = Some (sort_rule cR argsR))
      (Hchk : fst (check_args l s0 cR) = true)
      (Cfull pre : ctx)
      (Hwfcf : wf_ctx l Cfull) (Hwft1f : wf_sort l Cfull (scon n0 s0))
      (x : V) (t : sort) (c' : ctx) (sg' : subst)
      (Hcfull : Cfull = pre ++ (x,t)::c')
      (Hxfv : In x (fv_args s0))
      (Hocc : forall E, In (x, E) (snd (check_args l s0 cR)) -> E = t)
      (Hwfsub' : wf_subst l [] sg' c')
      (Hdomsg' : map fst sg' = map fst c')
      (Hdomsg : incl (map fst c') (map fst sg))
      (Hdomsgcf : map fst sg = map fst Cfull)
      (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y)
      : wf_term l [] (named_list_lookup default sg x) (t[/sg'/]).
    Proof.
      assert (Hwst : wf_sort l c' t).
      { subst Cfull.
        clear -Hwfcf.
        induction pre as [|[pn pt] pre IH]; cbn [app] in Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply Hwfcf.
        - apply invert_wf_ctx_cons in Hwfcf. apply IH. apply Hwfcf. }
      rewrite (decl_sort_subst_prefix_eq sg sg' t c' Hwst Hdomsg' Hdomsg Hagree).
      assert (Hdom : incl (map fst Cfull) (map fst sg))
        by (rewrite Hdomsgcf; apply incl_refl).
      pose proof (@Theorems.faithful_rep_sort_args_rigid V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of
                    X l Hwf Hsof a eF sg Hsound n0 s0 cR argsR Cfull Hrule Hchk Hwfcf Hwft1f Hdom xs1 Hrep)
        as Hfrs.
      destruct Hfrs as (HwfcR & HwfaSrc & HwfaImg).
      assert (Hxin : In x (map fst sg)).
      { rewrite Hdomsgcf, Hcfull, map_app. apply in_or_app; right.
        cbn [map fst]. left; reflexivity. }
      assert (Hlk : named_list_lookup default sg x = subst_lookup sg x)
        by (apply (nll_default_indep sg x default (var x) Hxin)).
      rewrite Hlk.
      exact (@PatternRigidity.covering_var_leaf_rigid_args_aux V V_Eqb V_Eqb_ok l Hwf
               [] Cfull sg Hwfcf Hdomsgcf s0
               (fun e _ => @PatternRigidity.covering_var_leaf_rigid V V_Eqb V_Eqb_ok l Hwf
                             [] Cfull sg Hwfcf Hdomsgcf e)
               cR HwfcR Hchk HwfaSrc HwfaImg x t Hxfv
               ltac:(rewrite Hcfull; apply in_or_app; right; left; reflexivity)
               Hocc).
    Qed.

    Lemma skip_decl_wf_from_image_sort (no_sort : V -> bool) (eF : instance X) (a : interp)
      (Hsound : forall al, ain al eF -> asnd a al)
      (sg : subst) (n0 : V) (s0 : list term) (xs1 : V)
      (Hrep : @Theorems.represents_sort V V_Eqb V_default V_map V_trie sort_of X l a eF sg
                (scon n0 s0) xs1)
      : forall c sub, wf_ctx l c -> wf_sort l c (scon n0 s0) ->
          (forall x, no_sort x = true -> rigid_sort_skip l c (scon n0 s0) x = true) ->
          map fst c = map fst sub ->
          map fst sg = map fst c ->
          (forall x, no_sort x = true -> In x (fv_sort (scon n0 s0))) ->
          (forall x, In x (map fst sub) ->
                map.get a (named_list_lookup default sub x)
                  = Some (inl (named_list_lookup default sg x))) ->
          skip_decl_wf no_sort a sub c.
    Proof.
      intros Cfull sub Hwfcf Hwft1f Hrig Hdom Hdomsgc Hskipset Hvals.
      cut (forall (c : ctx) sub,
             (exists pre, Cfull = pre ++ c) ->
             map fst c = map fst sub ->
             (forall x, In x (map fst sub) ->
                map.get a (named_list_lookup default sub x)
                  = Some (inl (named_list_lookup default sg x))) ->
             skip_decl_wf no_sort a sub c).
      { intro Hcut. apply Hcut; [exists (@nil (V*sort)); reflexivity | exact Hdom | exact Hvals]. }
      clear Hdom Hvals sub.
      intro c. induction c as [|[x t] c' IH]; intros sub Hpre Hdom Hvals.
      - cbn. exact I.
      - destruct sub as [|[x0 x'] sub']; cbn [map fst] in Hdom; [discriminate|].
        injection Hdom as Hxx0 Hdom'. subst x0.
        assert (Hwfc_suf : wf_ctx l ((x,t)::c')).
        { destruct Hpre as [pre Hpre'].
          assert (Hgen : forall pre0 cc, wf_ctx l (pre0 ++ cc) -> wf_ctx l cc).
          { clear. intros pre0; induction pre0 as [|[pn pt] pre0 IHp]; intros cc Hw.
            - cbn in Hw. exact Hw.
            - cbn in Hw. apply invert_wf_ctx_cons in Hw.
              destruct Hw as [_ [Hw' _] ]. exact (IHp cc Hw'). }
          eapply Hgen. rewrite <- Hpre'. exact Hwfcf. }
        apply invert_wf_ctx_cons in Hwfc_suf.
        destruct Hwfc_suf as [Hfresh [Hwfc' Hwst] ].
        cbn [skip_decl_wf]. split.
        2:{ apply IH; [ | exact Hdom' | ].
            - destruct Hpre as [pre Hpre']. exists (pre ++ [(x,t)]).
              rewrite <- app_assoc. cbn [app]. exact Hpre'.
            - intros y Hy. pose proof (Hvals y) as Hv. cbn beta in Hv.
              cbn [named_list_lookup map fst] in Hv.
              assert (Hyx : y <> x).
              { intro; subst y. unfold fresh in Hfresh.
                rewrite Hdom' in Hfresh. apply Hfresh. exact Hy. }
              pose proof (eqb_spec y x) as Hsp.
              destruct (eqb y x) eqn:Hyxb; [exfalso; apply Hyx; exact Hsp|].
              apply Hv. cbn [map fst]. right. exact Hy. }
        intros Hns sg' Hwfsub' Hdomsg' Hleaf'.
        assert (Hgx' : map.get a x' = Some (inl (named_list_lookup default sg x))).
        { pose proof (Hvals x (or_introl eq_refl)) as Hv.
          cbn [named_list_lookup] in Hv.
          pose proof (eqb_spec x x) as Hs.
          destruct (eqb x x); [exact Hv | exfalso; apply Hs; reflexivity]. }
        exists (named_list_lookup default sg x).
        split; [exact Hgx'|].
        assert (Hxfv : In x (fv_args s0)).
        { pose proof (Hskipset x Hns) as Hin0. cbn [fv_sort] in Hin0. exact Hin0. }
        assert (Hagree : forall y, In y (map fst c') ->
                  named_list_lookup default sg' y = named_list_lookup default sg y).
        { intros y Hy. rewrite Hdom' in Hy.
          pose proof (Hleaf' y Hy) as Hsg'y.
          pose proof (Hvals y) as Hsgy. cbn beta in Hsgy.
          assert (Hyx : y <> x).
          { intro; subst y. unfold fresh in Hfresh. rewrite Hdom' in Hfresh.
            apply Hfresh; exact Hy. }
          cbn [named_list_lookup map fst] in Hsgy.
          pose proof (eqb_spec y x) as Hsp.
          destruct (eqb y x) eqn:Hyxb; [exfalso; apply Hyx; exact Hsp|].
          specialize (Hsgy (or_intror Hy)).
          rewrite Hsg'y in Hsgy. injection Hsgy as Hsgy. exact Hsgy. }
        destruct Hpre as [pre Hpre'].
        assert (Hincl : incl (map fst c') (map fst sg)).
        { rewrite Hdomsgc. rewrite Hpre'.
          rewrite map_app. cbn [map app]. intro z. intro Hz.
          apply in_or_app. right. right. exact Hz. }
        (* use rigidity checker to extract rule info *)
        pose proof (rigid_sort_skip_inv l Cfull (scon n0 s0) x (Hrig x Hns))
          as Hinv.
        destruct Hinv as (n0' & s0' & cR & argsR & tx & Heq1 & Hrule & Hchk & Hxfv' & Hlkc & Hocc').
        injection Heq1 as Hn0eq Hs0eq. subst n0' s0'.
        assert (HallfrCf : all_fresh Cfull) by (eauto with model).
        symmetry in Hlkc.
        apply named_list_lookup_err_in in Hlkc.
        assert (HinCfull_xt : In (x, t) Cfull)
          by (rewrite Hpre'; apply in_or_app; right; left; reflexivity).
        pose proof (in_all_fresh_same _ _ _ _ HallfrCf Hlkc HinCfull_xt) as Heqtx.
        subst tx.
        exact (skip_var_decl_sort_wf_scon_rigid no_sort eF a Hsound sg n0 s0 xs1 Hrep
                  cR argsR Hrule Hchk Cfull pre Hwfcf Hwft1f x t c' sg' Hpre' Hxfv
                  Hocc' Hwfsub' Hdomsg' Hincl Hdomsgc Hagree).
    Qed.

  End AddCtxInvert.
End WithVar.
