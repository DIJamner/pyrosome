
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core EasyWF.
Require Import String.

Ltac guard_single_goal :=
  let n := numgoals in
  guard n < 2.


Ltac compute_adds :=
  repeat match goal with
           |- context [?X + ?Y] =>
           let res := eval compute in (X + Y) in
               change (X + Y) with res
         end.


Ltac clear_const_substs :=
  repeat match goal with
         | |- context [[ ?N |] [/?S/]] =>
           change [N |][/?S/] with [N|]
         end.

Ltac constructors :=
  progress repeat (constructor; guard_single_goal).

Ltac topswap :=
  let H1 := fresh in
  let H2 := fresh in
  move => H1 H2;
          move: H2 H1.

Definition ob := (con 0 [::]).
Definition hom a b := con 1 [:: b; a].
Definition id a := con 2 [:: a].
Definition cmp a b c f g := (con 3 [:: f; g; c; b; a]).

(* syntax of categories *)
Definition cat_stx : lang :=
  [::
     term_rule [:: hom (var 1) (var 2); hom (var 0) (var 1); ob; ob; ob]
               (hom (var 0) (var 2));
     term_rule [:: ob] (hom (var 0) (var 0));
     sort_rule [:: ob; ob];
     sort_rule [::]
  ].

Ltac recognize_lang :=
  match goal with
    |- wf_lang ?L =>
    suff: type_wf_lang L = Some tt;
    [ by apply type_wf_lang_recognizes
    | by cbv]
  end.

Ltac recognize_ctx :=  match goal with
    |- wf_ctx ?L ?C =>
    suff: type_wf_ctx L C = Some tt;
    [ apply type_wf_ctx_recognizes
    | by cbv]
  end.

Ltac recognize_sort :=  match goal with
    |- wf_sort ?L ?C ?T =>
    suff: type_wf_sort L C T = Some tt;
    [ apply type_wf_sort_recognizes
    | by cbv]
  end.

Ltac recognize_term :=  match goal with
    |- wf_term ?L ?C ?E ?T =>
    suff: type_wf_term L C E = Some T;
    [ apply type_wf_term_recognizes
    | by cbv]
  end.

Ltac recognize_subst :=  match goal with
    |- wf_subst ?L ?C ?S ?C' =>
    suff: type_wf_subst L C S C' = Some tt;
    [ apply type_wf_subst_recognizes
    | by cbv]
  end.

Ltac recognize_rule' :=
  match goal with
    |- wf_rule ?L ?R =>
    suff: type_wf_rule L R = Some tt;
    [ by apply type_wf_rule_recognizes
    | idtac]
  end.
Lemma cat_stx_wf : wf_lang cat_stx.
Proof using . recognize_lang. Qed.

(* TODO: put coercion, hint in right places *)
Coercion var : nat >-> exp.

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

Definition ty a := con 7 [:: a].
Definition ty_subst a b s t := con 8 [:: t; s; b; a].
Definition el a t := con 9 [:: t; a].
Definition el_subst a b s t m := con 10 [:: m; t; s; b; a].

Definition emp := con 15 [::].
Definition forget a := con 16 [:: a].

Definition ext g a := con 19 [:: a; g] (*[:: ty 0; ob]*).
Definition snoc a b t g n := con 20 [:: n; g; t; b; a]
(*[:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]*).
Definition p a t := con 21 [:: t; a].
Definition q a t := con 22 [:: t; a].

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

(*TODO: move to utils *)
Ltac unfold_tail l :=
  match l with
  | _::?l' => unfold_tail l'
  | _ => unfold l
  end.

(* TODO: move to EasyWF*)
Ltac wf_lang_eauto :=
   repeat match goal with
          | |- wf_lang ?l => unfold_tail l
         end;
  repeat match goal with
         | |- wf_lang (?R :: ?L) =>
           suff: wf_lang L;
             [intro;
              apply: wf_lang_cons;
              eauto with judgment|]
         | |- wf_lang nil => apply: wf_lang_nil
         end.

Lemma subst_lang_wf : wf_lang subst_lang.
Proof using .
  wf_lang_eauto.
  
  2:{ (* element identity substitution *)
    constructor;auto with judgment.     
    apply: wf_term_conv'.
    instantiate (1:= el 0 (ty_subst 0 0 (id 0) 1)).
    auto with judgment.
    change (el 0 (ty_subst 0 0 (id 0) 1)) with (el 0 1)[/[:: (ty_subst 0 0 (id 0) 1); var 0]/].
    change (el 0 1) at 3 with (el 0 1)[/[:: var 1; var 0]/].
    eapply le_sort_subst'.
    instantiate (1:=[:: ty 0; ob]).
    2:eauto with judgment.
    
    eapply le_subst_cons'.
    recognize_subst; eauto with judgment.
    eapply le_subst_cons'.
    recognize_subst; eauto with judgment.
    eauto with judgment.
    rewrite subst_nil.
    eapply le_term_refl'; eauto with judgment.
    change (ty 0) [/[:: var 0] /] with (ty 0).
    change [:: el 0 1; ty 0; ob] with ([:: el 0 1] ++ [:: ty 0; ob]).
    eapply mono_ctx; eauto with judgment.
  }
  {
    constructor; auto with judgment.
    apply: wf_term_conv'.
    instantiate
      (1:= (el 0 (ty_subst 0 1 2
                   (ty_subst (ext 1 3) 1 (p 1 3) 3)))).
    apply:type_wf_term_recognizes; eauto with judgment.
    compute.
Qed.
