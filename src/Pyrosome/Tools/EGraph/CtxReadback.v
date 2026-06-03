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
From Pyrosome.Theory Require Import Core ModelImpls.
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

  End AddCtxInvert.
End WithVar.
