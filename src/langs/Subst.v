
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core EasyWF.
Require Import String.

Local Notation ob := (con 0 [::]).
Local Notation hom a b := (con 1 [:: b; a]%exp_scope).
Local Notation id a := (con 2 [:: a]%exp_scope).
Local Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).

(* syntax of categories *)
Definition cat_stx : lang :=
  [::
     term_rule [:: hom 1 2; hom 0 1; ob; ob; ob]
               (hom 0 2);
     term_rule [:: ob] (hom 0 0);
     sort_rule [:: ob; ob];
     sort_rule [::]
  ].


(* TODO: put hints in right place *)

Hint Resolve type_wf_lang_recognizes : judgment.
Hint Resolve type_wf_rule_recognizes : judgment.
Hint Resolve type_wf_ctx_recognizes : judgment.
Hint Resolve type_wf_sort_recognizes : judgment.
Hint Resolve type_wf_term_recognizes : judgment.
Hint Resolve type_wf_subst_recognizes : judgment.


Definition cat_lang : lang :=
  (* compose associativity *)
  (term_le [:: hom 2 3; hom 1 2; hom 0 1; ob; ob; ob; ob]
           (cmp 0 1 3 (cmp 1 2 3 6 5) 4)
           (cmp 0 2 3 6 (cmp 0 1 2 5 4))
           (hom 0 3))::
  (* left identity *)
  (term_le [:: (hom 0 1); ob; ob]
               (cmp 0 1 1 (id 1) 2)
               2
               (hom 0 1))::
  (* right identity *)
  (term_le [:: (hom 0 1); ob; ob]
               (cmp 0 0 1 2 (id 0))
               2
               (hom 0 1))::cat_stx.


Lemma cat_lang_wf : wf_lang cat_lang.
Proof using .
  auto with judgment.
  (*recognize_lang.*)
Qed.
(*TODO: symmetry for rules;currently only go one direction *)


Lemma wf_ob c : wf_ctx cat_lang c -> wf_sort cat_lang c ob.
Proof using .
  auto with judgment.
Qed.

Local Notation ty a := (con 7 [:: a]%exp_scope).
Local Notation ty_subst a b s t := (con 8 [:: t; s; b; a]%exp_scope).
Local Notation el a t := (con 9 [:: t; a]%exp_scope).
Local Notation el_subst a b s t m := (con 10 [:: m; t; s; b; a]%exp_scope).

Local Notation emp := (con 15 [::]%exp_scope).
Local Notation forget a := (con 16 [:: a]%exp_scope).

Local Notation ext g a := (con 19 [:: a; g]%exp_scope) (*[:: ty 0; ob]*).
Local Notation snoc a b t g n := (con 20 [:: n; g; t; b; a]%exp_scope)
(*[:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]*).
Local Notation p a t := (con 21 [:: t; a]%exp_scope).
Local Notation q a t := (con 22 [:: t; a]%exp_scope).

(* convenience def to avoid repetition *)
Definition el_srt_subst a b g e :=
  (el a (ty_subst a b g e)).

Definition subst_lang : lang :=
  (term_le [:: el_srt_subst 0 1 2 3; ty 1; hom 0 1; ob; ob]
           (el_subst 0 (ext 1 3) (snoc 0 1 3 2 4)
                     (ty_subst (ext 1 3) 1 (p 1 3) 3) (q 1 3))
           4
           (el_srt_subst 0 1 2 3))::
  (term_le [:: el_srt_subst 0 1 2 3; ty 1; hom 0 1; ob; ob]
           (cmp 0 (ext 1 3) 1
                (p 1 3)
                (snoc 0 1 3 2 4))
           2
           (hom 0 1))::
  (term_rule [:: ty 0; ob]
             (el_srt_subst (ext 0 1) 0 (p 0 1) 1))::
  (term_rule [:: ty 0; ob] (hom (ext 0 1) 0))::
  (term_rule [:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]
             (hom 0 (ext 1 2)))::
  (term_rule [:: ty 0; ob] ob)::
  (term_le [::] (id emp) (forget emp) (hom emp emp))::
  (term_le [:: hom 0 1; ob; ob] (cmp 0 1 emp (forget 1) 2) (forget 0) (hom 0 emp))::
  (term_rule [:: ob] (hom 0 emp))::
  (term_rule [::] ob)::
  (* el_subst compose to sequence *)
  (term_le [:: ty 2; hom 1 2; hom 0 1; ob; ob; ob]
           (ty_subst 0 2 (cmp 0 1 2 4 3) 5)
           (ty_subst 0 1 3 (ty_subst 1 2 4 5))
           (ty 0))::
  (* id el_subst; may be the first rule that holds, but isn't recognized. *)
  (term_le [:: el 0 1; ty 0; ob] (el_subst 0 0 (id 0) 1 2) 2 (el 0 1))::
  (* ty_subst compose to sequence *)
  (term_le [:: ty 2; hom 1 2; hom 0 1; ob; ob; ob]
           (ty_subst 0 2 (cmp 0 1 2 4 3) 5)
           (ty_subst 0 1 3 (ty_subst 1 2 4 5))
           (ty 0))::
  (* id ty_subst *)
  (term_le [:: ty 0; ob] (ty_subst 0 0 (id 0) 1) 1 (ty 0))::
  (term_rule [:: el 1 3; ty 1; hom 0 1; ob; ob] (el 0 (ty_subst 0 1 2 3)))::
  (sort_rule [:: ty 0; ob])::
  (term_rule [:: ty 1; hom 0 1; ob; ob] (ty 0))::
  (sort_rule [:: ob])::cat_lang.

Require Import Setoid.

Lemma subst_lang_wf : wf_lang subst_lang.
Proof using .
  wf_lang_eauto.
  
  2:{ (* element identity substitution *)
    constructor;auto with judgment.
    
    (*TODO: should be handledby this rewriting:
      match goal with
      |- wf_term ?l ?c _ _ => 
      setoid_replace (el 0 1) with (el 0 (ty_subst 0 0 (id 0) 1))
                             using relation (le_sort l c) at 2
    end.
     *)
    apply:wf_term_conv; first by auto with judgment.
    instantiate (1:= el 0 (ty_subst 0 0 (id 0) 1)).
    auto with judgment.

    eapply sort_con_mor.
    eapply subst_cons_mor.
    eapply reflexivity.
    change ( [:: el 0 1; ty 0; ob] ) with ( [:: el 0 1]++[:: ty 0; ob] ).
    eapply le_mono_ctx.
    eapply le_term_by.
    instantiate (1:= ty 0).
    by compute.
  }
  {
    constructor; auto with judgment.
    apply: wf_term_conv; first by auto with judgment.
    instantiate (1 := (el 0 (ty_subst 0 (ext 1 3) (snoc 0 1 3 2 4) (ty_subst (ext 1 3) 1 (p 1 3) 3)))).
    apply:type_wf_term_recognizes; eauto with judgment.
    unfold el_srt_subst.
    eapply sort_con_mor.
    repeat eapply subst_cons_mor.
    auto with judgment.
    auto with judgment.
    
    (*TODO: eapply symmetry does something very bad; why?*)
    match goal with |- le_term ?l ?c _ _ ?t => eapply (@symmetry _ (fun x y => le_term l c x y t)) end.
    eauto with typeclass_instances.
    (* TODO: why doesn't this work? setoid_symmetry relation (fun x y => le_term l c x y t).*)
    eapply le_term_trans.
    2:{
    match goal with |- le_term ?l ?c _ _ ?t => eapply (@symmetry _ (fun x y => le_term l c x y t)) end.
    eauto with typeclass_instances.
    
    match goal with _ : wf_lang ?l |- _ => let e := eval cbv in (size l) in idtac e end.
    
    setoid_replace (ty_subst 0 (ext 1 3) (snoc 0 1 3 2 4) (ty_subst (ext 1 3) 1 (p 1 3) 3))
                   with (ty_subst 0 1 (cmp 0 (ext 1 3) 1 (p 1 3) (snoc 0 1 3 2 4)) 3).
    match goal with
      |- le_term _ _ 
    strategy: rewrite to compose, compose p with snoc
    TODO: add symmetric rules to fuller framework.

    instantiate
      (1:= (el 0 (ty_subst 0 1 2
                           (ty_subst (ext 1 3) 1 (p 1 3) 3)))).
    apply:type_wf_term_recognizes; eauto with judgment.
    compute.
Qed.
es
