Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Export Substable Model Term Rule.

Module Notations.
  Export Term.Notations.
  Export Rule.Notations.
End Notations.
Import Notations.

Create HintDb lang_core discriminated.

Ltac basic_core_crush := let x := autorewrite with utils term lang_core in * in
                                  let y := eauto 7 with utils term lang_core  model in
                                          generic_crush x y.
Ltac basic_core_firstorder_crush := let x := autorewrite with utils term lang_core in * in
                                  let y := eauto with utils term lang_core  model in
                                      generic_firstorder_crush x y.

                                           
(*
(*TODO: do I want these hints in model or lang_core?*)
Hint Unfold Model.wf_term : lang_core.
Hint Unfold Model.eq_term : lang_core.
Hint Unfold Model.wf_sort : lang_core.
Hint Unfold Model.eq_sort : lang_core.
*)

Hint Resolve wf_ctx_all_fresh : lang_core.
                                           
Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
    {|
      term_substable := _;
      sort_substable := _;
      eq_sort := eq_sort;
      (*TODO: rename the conflict*)
      Model.eq_term := eq_term;
      wf_sort := wf_sort;
      wf_term := wf_term;
    |}.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
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

  Notation Model := (@Model V term sort).

Section TermsAndRules.
  Context (l : lang).

  (*All assume wf_lang.
    All ctxs (other than in wf_ctx) are assumed to satisfy wf_ctx.
    Judgments whose assumptions take ctxs must ensure they are wf.
    Sorts are not assumed to be wf; the term judgments should guarantee
    that their sorts are wf.
   *)
  
  Inductive eq_sort : ctx -> sort -> sort -> Prop :=
  | eq_sort_by : forall c name t1 t2,
      In (name, sort_eq_rule c t1 t2) l ->
      eq_sort c t1 t2
  | eq_sort_subst : forall c s1 s2 c' t1' t2',
      (* Need to assert wf_ctx c here to satisfy
         assumptions' presuppositions
       *)
      wf_ctx c' ->
      eq_subst (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c c' s1 s2 ->
      eq_sort c' t1' t2' ->
      eq_sort c t1'[/s1/] t2'[/s2/]
  | eq_sort_refl : forall c t,
      wf_sort c t ->
      eq_sort c t t
  | eq_sort_trans : forall c t1 t12 t2,
      eq_sort c t1 t12 ->
      eq_sort c t12 t2 ->
      eq_sort c t1 t2
  | eq_sort_sym : forall c t1 t2, eq_sort c t1 t2 -> eq_sort c t2 t1
  with eq_term : ctx -> sort -> term -> term -> Prop :=
  | eq_term_subst : forall c s1 s2 c' t e1 e2,
      (* Need to assert wf_ctx c' here to satisfy
         assumptions' presuppositions
       *)
      wf_ctx c' ->
      eq_subst (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c c' s1 s2 ->
      eq_term c' t e1 e2 ->
      eq_term c t[/s2/] e1[/s1/] e2[/s2/]
  | eq_term_by : forall c name t e1 e2,
      In (name,term_eq_rule c e1 e2 t) l ->
      eq_term c t e1 e2
  | eq_term_refl : forall c e t,
      wf_term c e t ->
      eq_term c t e e
  | eq_term_trans : forall c t e1 e12 e2,
      eq_term c t e1 e12 ->
      eq_term c t e12 e2 ->
      eq_term c t e1 e2
  | eq_term_sym : forall c t e1 e2, eq_term c t e1 e2 -> eq_term c t e2 e1
  (* Conversion:

c |- e1 = e2 : t 
               ||
c |- e1 = e2 : t'
   *)
  | eq_term_conv : forall c t t',
      eq_sort c t t' ->
      forall e1 e2,
        eq_term c t e1 e2 ->
        eq_term c t' e1 e2
                (*
  (* TODO: do I want to allow implicit elements in substitutions? *)
  (* TODO: do I want to define this in terms of eq_args? *)
  with eq_subst : ctx -> ctx -> subst -> subst -> Prop :=
  | eq_subst_nil : forall c, eq_subst c [] [] []
  | eq_subst_cons : forall c c' s1 s2,
      eq_subst c c' s1 s2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        eq_term c t[/s2/] e1 e2 ->
        eq_subst c ((name, t)::c') ((name,e1)::s1) ((name,e2)::s2)*)
  with wf_term : ctx -> term -> sort -> Prop :=
  | wf_term_by : forall c n s args c' t,
      In (n, term_rule c' args t) l ->
      wf_args (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c s c' ->
      wf_term c (con n s) t[/(with_names_from c' s)/]
  | wf_term_conv : forall c e t t',
      (* We add this condition so that we satisfy the assumptions of eq_sort
         TODO: necessary? not based on current judgment scheme.
         wf_term c e t should imply wf_sort c t,
         and eq_sort c t t' should imply wf_sort c t


      wf_sort c t -> 
       *)
      wf_term c e t ->
      eq_sort c t t' ->
      wf_term c e t'
  | wf_term_var : forall c n t,
      NoDup (map fst c) ->
      In (n, t) c ->
      wf_term c (var n) t
  with wf_sort : ctx -> sort -> Prop :=
  | wf_sort_by : forall c n s args c',
      In (n, (sort_rule c' args)) l ->
      wf_args (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c s c' ->
      wf_sort c (scon n s).

  #[export] Instance core_model : Model := mut_mod eq_sort eq_term wf_sort wf_term.
  
  Notation eq_subst := (eq_subst (Model:= core_model)).
  Notation eq_args := (eq_args (Model:= core_model)).
  Notation wf_subst := (wf_subst (Model:= core_model)).
  Notation wf_args := (wf_args (Model:= core_model)).
  Notation wf_ctx := (wf_ctx (Model:= core_model)).

  Variant wf_rule : rule -> Prop :=
  | wf_sort_rule : forall c args,
      wf_ctx c ->
      sublist args (map fst c) ->
      wf_rule (sort_rule c args)
  | wf_term_rule : forall c args t,
      wf_ctx c ->
      wf_sort c t ->
      sublist args (map fst c) ->
      wf_rule (term_rule c args t)
  | eq_sort_rule : forall c t1 t2,
      wf_ctx c ->
      wf_sort c t1 ->
      wf_sort c t2 ->
      wf_rule (sort_eq_rule c t1 t2)
  | eq_term_rule : forall c e1 e2 t,
      wf_ctx c ->
      wf_sort c t ->
      wf_term c e1 t ->
      wf_term c e2 t ->
      wf_rule (term_eq_rule c e1 e2 t).

  
  
End TermsAndRules.

Hint Constructors eq_sort eq_term eq_subst eq_args
     wf_sort wf_term wf_subst wf_args wf_ctx
     wf_rule : lang_core.

  
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

  (*
  Defined by inlining nested datatypes then modifying the results of the mutual schemes below.
  The induction schemes for the nested types were pulled out into a separate section
  and various naming and implicit arguments changes were made for brevity
  and (some) legibility.

Scheme eq_sort_ind' := Minimality for eq_sort Sort Prop
  with eq_term_ind' := Minimality for eq_term Sort Prop
  with eq_subst_ind' := Minimality for eq_subst Sort Prop
  with wf_sort_ind' := Minimality for wf_sort Sort Prop
  with wf_term_ind' := Minimality for wf_term Sort Prop
  with wf_args_ind' := Minimality for wf_args Sort Prop
  with wf_ctx_ind' := Minimality for wf_ctx Sort Prop.

   *)
  Section JudgeInd.
    Context (l : lang) (P : ctx -> sort -> sort -> Prop)
            (P0 : ctx -> sort -> term -> term -> Prop)
            (P1 : ctx -> ctx -> subst -> subst -> Prop) (P2 : ctx -> sort -> Prop)
            (P3 : ctx -> term -> sort -> Prop) (P4 : ctx -> list term -> ctx -> Prop) 
            (P5 : ctx -> Prop)
            (f : forall (c : ctx) (name : V) (t1 t2 : sort),
                In (name, sort_eq_rule c t1 t2) l -> P c t1 t2)
            (f0 : forall (c : ctx) (s1 s2 : subst) (c' : ctx) (t1' t2' : sort),
                wf_ctx l c' ->
                P5 c' ->
                eq_subst l c c' s1 s2 ->
                P1 c c' s1 s2 ->
                eq_sort l c' t1' t2' ->
                P c' t1' t2' ->
                P c t1' [/s1 /] t2' [/s2 /])
            (f1 : forall (c : ctx) (t : sort), wf_sort l c t -> P2 c t -> P c t t)
            (f2 : forall (c : ctx) (t1 t12 t2 : sort),
                eq_sort l c t1 t12 -> P c t1 t12 -> eq_sort l c t12 t2 -> P c t12 t2 -> P c t1 t2)
            (f3 : forall (c : ctx) (t1 t2 : sort), eq_sort l c t1 t2 -> P c t1 t2 -> P c t2 t1)
            (f4 : forall (c : ctx) (s1 s2 : subst) (c' : ctx) (t : sort) (e1 e2 : term),
                wf_ctx l c' ->
                P5 c' ->
                eq_subst l c c' s1 s2 ->
                P1 c c' s1 s2 ->
                eq_term l c' t e1 e2 -> P0 c' t e1 e2 -> P0 c t [/s2 /] e1 [/s1 /] e2 [/s2 /])
            (f5 : forall (c : ctx) (name : V) (t : sort) (e1 e2 : term),
                In (name, term_eq_rule c e1 e2 t) l -> P0 c t e1 e2)
            (f6 : forall (c : ctx) (e : term) (t : sort),
                wf_term l c e t -> P3 c e t -> P0 c t e e)
            (f7 : forall (c : ctx) (t : sort) (e1 e12 e2 : term),
                eq_term l c t e1 e12 ->
                P0 c t e1 e12 -> eq_term l c t e12 e2 -> P0 c t e12 e2 -> P0 c t e1 e2)
            (f8 : forall (c : ctx) (t : sort) (e1 e2 : term),
                eq_term l c t e1 e2 -> P0 c t e1 e2 -> P0 c t e2 e1)
            (f9 : forall (c : ctx) (t t' : sort),
                eq_sort l c t t' ->
                P c t t' -> forall e1 e2 : term,
                    eq_term l c t e1 e2 -> P0 c t e1 e2 -> P0 c t' e1 e2)
            (f10 : forall c : ctx, P1 c [] [] [])
            (f11 : forall (c c' : ctx) (s1 s2 : subst),
                eq_subst l c c' s1 s2 ->
                P1 c c' s1 s2 ->
                forall (name : V) (t : sort) (e1 e2 : term),
                  eq_term l c t [/s2 /] e1 e2 ->
                  P0 c t [/s2 /] e1 e2 ->
                  P1 c ((name, t) :: c') ((name, e1) :: s1) ((name, e2) :: s2))
            (f12 : forall (c : ctx) (n : V) (s : list term) (args : list V) (c' : ctx),
                In (n, sort_rule c' args) l -> wf_args l c s c' -> P4 c s c' -> P2 c (scon n s))
            (f13 : forall (c : ctx) (n : V) (s : list term) (args : list V) (c' : ctx) (t : sort),
                In (n, term_rule c' args t) l ->
                wf_args l c s c' -> P4 c s c' -> P3 c (con n s) t [/with_names_from c' s /])
            (f14 : forall (c : ctx) (e : term) (t t' : sort),
                wf_term l c e t -> P3 c e t -> eq_sort l c t t' -> P c t t' -> P3 c e t')
            (f15 : forall (c : list (V * sort)) (n : V) (t : sort), In (n, t) c -> P3 c (var n) t)
            (f16 : forall c : ctx, P4 c [] [])
            (f17 : forall (c : ctx) (s : list term) (c' : named_list sort)
                          (name : V) (e : term) (t : sort),
                wf_term l c e t [/with_names_from c' s /] ->
                P3 c e t [/with_names_from c' s /] ->
                wf_args l c s c' -> P4 c s c' -> P4 c (e :: s) ((name, t) :: c')) 
            (f18 : P5 [])
            (f19 : forall (name : V) (c : named_list sort) (v : sort),
                fresh name c -> wf_ctx l c -> P5 c ->
                wf_sort l c v -> P2 c v -> P5 ((name, v) :: c)).

    Section Nested.
      Context (eq_sort_ind' : forall (c : ctx) (s s0 : sort), eq_sort l c s s0 -> P c s s0)
              (eq_term_ind' : forall (c : ctx) (s : sort) (t t0 : term),
                  eq_term l c s t t0 -> P0 c s t t0)
              (wf_sort_ind'
                : forall (c : ctx) (s : sort), wf_sort l c s -> P2 c s)
              (wf_term_ind'
                : forall (c : ctx) (t : term) (s : sort), wf_term l c t s -> P3 c t s).
      
      Fixpoint eq_subst_ind' (c c0 : ctx) (s s0 : subst) (e : eq_subst l c c0 s s0)
        : P1 c c0 s s0 :=
        match e in (Model.eq_subst c1 c2 s1 s2) return (P1 c1 c2 s1 s2) with
        | eq_subst_nil c1 => f10 c1
        | eq_subst_cons e0 name t e1 e2 e3 =>
            f11 e0 (eq_subst_ind' e0) name t e3 (eq_term_ind' e3)
        end.
      Fixpoint wf_args_ind' (c : ctx) (l0 : list term) (c0 : ctx) (w : wf_args l c l0 c0)
        : P4 c l0 c0 :=
        match w in (Model.wf_args c1 l1 c2) return (P4 c1 l1 c2) with
        | wf_args_nil c1 => f16 c1
        | wf_args_cons name e t w0 w1 =>
            f17 name t w0 (wf_term_ind' w0) w1 (wf_args_ind' w1)
        end.
      Fixpoint wf_ctx_ind' (c : ctx) (w : wf_ctx l c) {struct w} : P5 c :=
        match w in (Model.wf_ctx c0) return (P5 c0) with
        | wf_ctx_nil => f18
        | wf_ctx_cons v f20 w0 w1 =>
            f19 f20 w0 (wf_ctx_ind' w0) w1 (wf_sort_ind' w1)
        end.
    End Nested.

    Fixpoint eq_sort_ind' (c : ctx) (s s0 : sort) (e : eq_sort l c s s0) : P c s s0 :=
      match e in (eq_sort _ c0 s1 s2) return (P c0 s1 s2) with
      | eq_sort_by _ c0 name t1 t2 i => f c0 name t1 t2 i
      | eq_sort_subst w e0 e1 =>
          f0 w (wf_ctx_ind' wf_sort_ind' w) e0
             (eq_subst_ind' eq_term_ind' e0) e1 (eq_sort_ind' e1)
      | eq_sort_refl w => f1 w (wf_sort_ind' w)
      | eq_sort_trans e0 e1 => f2 e0 (eq_sort_ind' e0) e1 (eq_sort_ind' e1)
      | eq_sort_sym e0 => f3 e0 (eq_sort_ind' e0)
      end
    with eq_term_ind' (c : ctx) (s : sort) (t t0 : term) (e : eq_term l c s t t0) : P0 c s t t0 :=
           match e in (eq_term _ c0 s0 t1 t2) return (P0 c0 s0 t1 t2) with
           | eq_term_subst w e0 e3 =>
               f4 w (wf_ctx_ind' wf_sort_ind' w)
                  e0 (eq_subst_ind' eq_term_ind' e0) e3 (eq_term_ind' e3)
           | eq_term_by _ c0 name t1 e1 e2 i => f5 c0 name t1 e1 e2 i
           | eq_term_refl w => f6 w (wf_term_ind' w)
           | eq_term_trans e0 e3 =>
               f7 e0 (eq_term_ind' e0) e3 (eq_term_ind' e3)
           | eq_term_sym e0 => f8 e0 (eq_term_ind' e0)
           | eq_term_conv e0 e3 =>
               f9 e0 (eq_sort_ind' e0) e3 (eq_term_ind' e3)
           end
    with wf_sort_ind' (c : ctx) (s : sort) (w : wf_sort l c s) {struct w} : P2 c s :=
           match w in (wf_sort _ c0 s0) return (P2 c0 s0) with
           | wf_sort_by n args i w0 =>
               f12 n args i w0 (wf_args_ind' wf_term_ind' w0)
           end
    with wf_term_ind' (c : ctx) (t : term) (s : sort) (w : wf_term l c t s) : P3 c t s :=
           match w in (wf_term _ c0 t0 s0) return (P3 c0 t0 s0) with
           | wf_term_by n args t0 i w0 =>
               f13 n args t0 i w0 (wf_args_ind' wf_term_ind' w0)
           | wf_term_conv w0 e0 =>
               f14 w0 (wf_term_ind' w0) e0 (eq_sort_ind' e0)
           | wf_term_var _ c0 n t0 _ i => f15 c0 n t0 i
           end.

    
    Definition eq_subst_ind'' := eq_subst_ind' eq_term_ind'.
    Definition wf_args_ind'' := wf_args_ind' wf_term_ind'.
    Definition wf_ctx_ind'' := wf_ctx_ind' wf_sort_ind'.

    Combined Scheme judge_ind
         from eq_sort_ind', eq_term_ind', eq_subst_ind'',
              wf_sort_ind', wf_term_ind', wf_args_ind'',
      wf_ctx_ind''.
    
  End JudgeInd.


(*TODO: separate file for properties?*)

  (*TODO: move appropriate lemmas into Model.v?*)
Lemma invert_wf_subst_nil_cons l c n t c'
  : wf_subst l c [] ((n,t)::c') <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_subst_nil_cons : lang_core.

Lemma invert_wf_subst_cons_nil l c n e s
  : wf_subst l c ((n,e)::s) [] <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_subst_cons_nil : lang_core.

Lemma invert_wf_subst_nil_nil l c
  : wf_subst l c [] [] <-> True.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_subst_nil_nil : lang_core.

Lemma invert_wf_subst_cons_cons l c n e s m t c'
  : wf_subst l c ((n,e)::s) ((m,t)::c') <-> n = m /\ wf_subst l c s c' /\ wf_term l c e t[/s/].
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_subst_cons_cons : lang_core.


Lemma invert_wf_sort_rule l c args
  : wf_rule l (sort_rule c args) <-> wf_ctx l c /\ sublist args (map fst c).
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_sort_rule : lang_core.

Lemma invert_wf_term_rule l c args t
  : wf_rule l (term_rule c args t) <-> wf_ctx l c /\ sublist args (map fst c) /\ wf_sort l c t.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_term_rule : lang_core.

Lemma invert_wf_sort_eq_rule l c t1 t2
  : wf_rule l (sort_eq_rule c t1 t2) <-> wf_ctx l c /\ wf_sort l c t1 /\ wf_sort l c t2.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_sort_eq_rule : lang_core.

Lemma invert_wf_term_eq_rule l c e1 e2 t
  : wf_rule l (term_eq_rule c e1 e2 t) <-> wf_ctx l c /\ wf_term l c e1 t /\ wf_term l c e2 t /\ wf_sort l c t.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_wf_term_eq_rule : lang_core.


Local Lemma lang_mono l l'
  : incl l l' ->
    (forall c t1 t2,
        eq_sort l c t1 t2 ->
        eq_sort l' c t1 t2)
    /\ (forall c t e1 e2,
           eq_term l c t e1 e2 ->
           eq_term l' c t e1 e2)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           eq_subst l' c c' s1 s2)
    /\ (forall c t,
           wf_sort l c t ->
           wf_sort l' c t)
    /\ (forall c e t,
           wf_term l c e t ->
           wf_term l' c e t)
    /\ (forall c s c',
           wf_args l c s c' ->
           wf_args l' c s c')
    /\ (forall c,
           wf_ctx l c ->
           wf_ctx l' c).
Proof using.
  intro lincll.
  apply judge_ind; basic_goal_prep; basic_core_crush.
  assert (NoDup (map fst c)) by admit.
  basic_core_crush.
Admitted.

(*TODO: these make for bad hints.
  keep old statements (in addition) for the hint db?
  or just add none of them?
*)

Definition eq_sort_lang_monotonicity l l' (lincll' : incl l l')
  := proj1 (lang_mono lincll' ).
Local Hint Resolve eq_sort_lang_monotonicity : lang_core.

Definition eq_term_lang_monotonicity l l' (lincll' : incl l l')
  := proj1 (proj2 (lang_mono lincll')).
Local Hint Resolve eq_term_lang_monotonicity : lang_core.

Definition eq_subst_lang_monotonicity l l' (lincll' : incl l l')
  := proj1 (proj2 (proj2 (lang_mono lincll'))).
Local Hint Resolve eq_subst_lang_monotonicity : lang_core.

Definition wf_sort_lang_monotonicity l l' (lincll' : incl l l')
  := proj1 (proj2 (proj2 (proj2 (lang_mono lincll')))).
Local Hint Resolve wf_sort_lang_monotonicity : lang_core.

Definition wf_term_lang_monotonicity l l' (lincll' : incl l l')
  := proj1 (proj2 (proj2 (proj2 (proj2 (lang_mono lincll'))))).
Local Hint Resolve wf_term_lang_monotonicity : lang_core.

Definition wf_args_lang_monotonicity l l' (lincll' : incl l l')
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono lincll')))))).
Local Hint Resolve wf_args_lang_monotonicity : lang_core.

Definition wf_ctx_lang_monotonicity l l' (lincll' : incl l l')
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono lincll')))))).
Local Hint Resolve wf_ctx_lang_monotonicity : lang_core.

Lemma wf_rule_lang_monotonicity l l' r
  : incl l l' -> wf_rule l r -> wf_rule l' r.
Proof.
  inversion 2; basic_goal_prep; basic_core_crush.
Qed.
Local Hint Resolve wf_rule_lang_monotonicity : lang_core.

(*
  Some common special cases that are good for proof automation
*)
Local Lemma lang_mono_cons l name r
  : (forall c t1 t2,
        eq_sort l c t1 t2 ->
        eq_sort ((name,r)::l) c t1 t2)
    /\ (forall c t e1 e2,
           eq_term l c t e1 e2 ->
           eq_term ((name,r)::l) c t e1 e2)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           eq_subst ((name,r)::l) c c' s1 s2)
    /\ (forall c t,
           wf_sort l c t ->
           wf_sort ((name,r)::l) c t)
    /\ (forall c e t,
           wf_term l c e t ->
           wf_term ((name,r)::l) c e t)
    /\ (forall c s c',
           wf_args l c s c' ->
           wf_args ((name,r)::l) c s c')
    /\ (forall c,
           wf_ctx l c ->
           wf_ctx ((name,r)::l) c).
Proof using.
  apply lang_mono.
  basic_utils_crush.
Qed.

Definition eq_sort_lang_monotonicity_cons l name r
  := proj1 (lang_mono_cons l name r).
Hint Resolve eq_sort_lang_monotonicity_cons : lang_core.

Definition eq_term_lang_monotonicity_cons l name r
  := proj1 (proj2 (lang_mono_cons l name r)).
Hint Resolve eq_term_lang_monotonicity_cons : lang_core.

Definition eq_subst_lang_monotonicity_cons l name r
  := proj1 (proj2 (proj2 (lang_mono_cons l name r))).
Hint Resolve eq_subst_lang_monotonicity_cons : lang_core.

Definition wf_sort_lang_monotonicity_cons l name r
  := proj1 (proj2 (proj2 (proj2 (lang_mono_cons l name r)))).
Hint Resolve wf_sort_lang_monotonicity_cons : lang_core.

Definition wf_term_lang_monotonicity_cons l name r
  := proj1 (proj2 (proj2 (proj2 (proj2 (lang_mono_cons l name r))))).
Hint Resolve wf_term_lang_monotonicity_cons : lang_core.

Definition wf_args_lang_monotonicity_cons l name r
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono_cons l name r)))))).
Hint Resolve wf_args_lang_monotonicity_cons : lang_core.

Definition wf_ctx_lang_monotonicity_cons l name r
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono_cons l name r)))))).
Hint Resolve wf_ctx_lang_monotonicity_cons : lang_core.

Lemma wf_rule_lang_monotonicity_cons l name r' r
  : wf_rule l r -> wf_rule ((name, r') :: l) r.
Proof.
  inversion 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_rule_lang_monotonicity_cons : lang_core.


Local Lemma lang_mono_app l l'
  : (forall c t1 t2,
        eq_sort l c t1 t2 ->
        eq_sort (l'++l) c t1 t2)
    /\ (forall c t e1 e2,
           eq_term l c t e1 e2 ->
           eq_term (l'++l) c t e1 e2)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           eq_subst (l'++l) c c' s1 s2)
    /\ (forall c t,
           wf_sort l c t ->
           wf_sort (l'++l) c t)
    /\ (forall c e t,
           wf_term l c e t ->
           wf_term (l'++l) c e t)
    /\ (forall c s c',
           wf_args l c s c' ->
           wf_args (l'++l) c s c')
    /\ (forall c,
           wf_ctx l c ->
           wf_ctx (l'++l) c).
Proof using.
  apply lang_mono.
  eauto with utils.
 (*TODO: why does this fail: basic_utils_crush *)
Qed.

Definition eq_sort_lang_monotonicity_app l l'
  := proj1 (lang_mono_app l l').
Hint Resolve eq_sort_lang_monotonicity_app : lang_core.

Definition eq_term_lang_monotonicity_app l l'
  := proj1 (proj2 (lang_mono_app l l')).
Hint Resolve eq_term_lang_monotonicity_app : lang_core.

Definition eq_subst_lang_monotonicity_app l l'
  := proj1 (proj2 (proj2 (lang_mono_app l l'))).
Hint Resolve eq_subst_lang_monotonicity_app : lang_core.

Definition wf_sort_lang_monotonicity_app l l'
  := proj1 (proj2 (proj2 (proj2 (lang_mono_app l l')))).
Hint Resolve wf_sort_lang_monotonicity_app : lang_core.

Definition wf_term_lang_monotonicity_app l l'
  := proj1 (proj2 (proj2 (proj2 (proj2 (lang_mono_app l l'))))).
Hint Resolve wf_term_lang_monotonicity_app : lang_core.

Definition wf_args_lang_monotonicity_app l l'
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono_app l l')))))).
Hint Resolve wf_args_lang_monotonicity_app : lang_core.

Definition wf_ctx_lang_monotonicity_app l l'
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono_app l l')))))).
Hint Resolve wf_ctx_lang_monotonicity_app : lang_core.

Lemma wf_rule_lang_monotonicity_app l l' r
  : wf_rule l r -> wf_rule (l'++ l) r.
Proof.
  inversion 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_rule_lang_monotonicity_app : lang_core.

Lemma wf_subst_from_wf_args l c s c'
  : wf_args l c s c' ->
    wf_subst l c (with_names_from c' s) c'.
Proof.
  induction 1; basic_core_crush.
Qed.
  Hint Resolve wf_subst_from_wf_args : lang_core.

(* TODO: Don't always want this hint? but need it here
   Probably best to gate this behind a submodule import.
   TODO: other unfolds
*)
Hint Extern 5 (Model.wf_term _ _ _) => unfold Model.wf_term : lang_core.
Hint Extern 5 (Model.eq_term _ _ _ _) => unfold Model.eq_term : lang_core.
Hint Extern 5 (Model.wf_sort _ _) => unfold Model.wf_sort : lang_core.
Hint Extern 5 (Model.eq_sort _ _ _) => unfold Model.eq_sort : lang_core.

Lemma id_args_wf l c
  : forall c', sublist c c' -> wf_args l c' (id_args c) c.
  Proof.
    induction c; basic_goal_prep; basic_core_crush.
    constructor; basic_core_crush.
  Admitted.
Hint Resolve id_args_wf : lang_core.

Lemma eq_subst_dom_eq_r l c c' s1 s2
  : eq_subst l c c' s1 s2 ->
    map fst s2 = map fst c'.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_subst_dom_eq_r : lang_core.
     
Lemma eq_subst_dom_eq_l l c c' s1 s2
  : eq_subst l c c' s1 s2 ->
    map fst s1 = map fst c'.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_subst_dom_eq_l : lang_core.
     
Lemma wf_subst_dom_eq l c c' s
  : wf_subst l c s c' ->
    map fst s = map fst c'.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_subst_dom_eq : lang_core.

Lemma eq_subst_refl l c c' s : wf_subst l c s c' -> eq_subst l c c' s s.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_subst_refl : lang_core.


Lemma subst_name_fresh_from_ctx l c s c' n
  : wf_subst l c s c' -> fresh n c' -> fresh n s.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve subst_name_fresh_from_ctx : lang_core.

Lemma eq_subst_name_fresh_l_from_ctx l c s1 s2 c' n
  : eq_subst l c c' s1 s2 -> fresh n c' -> fresh n s1.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_subst_name_fresh_l_from_ctx : lang_core.

Lemma eq_subst_name_fresh_r_from_ctx l c s1 s2 c' n
  : eq_subst l c c' s1 s2 -> fresh n c' -> fresh n s2.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_subst_name_fresh_r_from_ctx : lang_core.

Lemma in_all_named_list {A} P (l : named_list A) n a
  : all P (map snd l) -> In (n,a) l -> P a.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Arguments in_all_named_list {A} [_] {_} {_} {_}.
  
Local Lemma wf_implies_ws l
  : ws_lang l ->
    (forall c t1 t2,
        eq_sort l c t1 t2 ->
        well_scoped (map fst c) t1 /\
        well_scoped (map fst c) t2)
    /\ (forall c t e1 e2,
           eq_term l c t e1 e2 ->
           well_scoped (map fst c) e1 /\
           well_scoped (map fst c) e2)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           all_fresh c' ->
           well_scoped (map fst c) s1 /\
           well_scoped (map fst c) s2)
    /\ (forall c t,
           wf_sort l c t ->
           well_scoped (map fst c) t)
    /\ (forall c e t,
           wf_term l c e t ->
           well_scoped (map fst c) e)
    /\ (forall c s c',
           wf_args l c s c' ->
           well_scoped (map fst c) s)
    /\ (forall c,
           wf_ctx l c -> ws_ctx c).
Proof using.
  intros; apply judge_ind; basic_goal_prep;
        basic_core_firstorder_crush.
  all:
    (*TODO: how to automate better/get into crush?*)
    try match goal with
        | [H0 : In (_,_) ?l, H1 : all _ (map snd ?l) |- _] =>
          let H' := fresh in
          pose proof (in_all_named_list H1 H0) as H';
            simpl in H'; basic_core_crush
        | [H : eq_subst _ _ ?c' ?s _|- well_scoped _ _[/?s/]] =>
          apply well_scoped_subst;    
            basic_core_crush;
            replace (map fst s) with (map fst c'); try symmetry;
              basic_core_crush
                
        | [H : eq_subst _ _ ?c' _ ?s |- well_scoped _ _[/?s/]] =>
          apply well_scoped_subst;    
            basic_core_crush;
            replace (map fst s) with (map fst c'); try symmetry;
              basic_core_crush
        end.
  all: assert (NoDup (map fst c)) as NoDupH by admit.
  all: specialize (H3 ltac:(basic_core_crush)).
  all: break.
  { eapply well_scoped_subst; try typeclasses eauto.
    trivial.
    eauto with model.
    basic_core_crush.
    }
  { eapply well_scoped_subst; try typeclasses eauto.
    trivial.
    eauto with model.
    basic_core_crush. }
  { eapply well_scoped_subst; try typeclasses eauto.
    trivial.
    eauto with model.
    basic_core_crush. }
  { eapply well_scoped_subst; try typeclasses eauto.
    trivial.
    eauto with model.
    basic_core_crush. }
Admitted.

Lemma eq_sort_implies_ws_l l c t1 t2
  : ws_lang l -> eq_sort l c t1 t2 -> well_scoped (map fst c) t1.
Proof.
  intros wsl eqs; apply (proj1 (proj1 (wf_implies_ws wsl) _ _ _ eqs)).
Qed.
Hint Resolve eq_sort_implies_ws_l : lang_core.

Lemma eq_sort_implies_ws_r l c t1 t2
  : ws_lang l -> eq_sort l c t1 t2 -> well_scoped (map fst c) t2.
Proof.
  intros wsl eqs; apply (proj2 (proj1 (wf_implies_ws wsl) _ _ _ eqs)).
Qed.
Hint Resolve eq_sort_implies_ws_r : lang_core.


Lemma eq_term_implies_ws_l l c t e1 e2
  : ws_lang l -> eq_term l c t e1 e2 -> well_scoped (map fst c) e1.
Proof.
  intros wsl eqs; apply (proj1 (proj1 (proj2 (wf_implies_ws wsl)) _ _ _ _ eqs)).
Qed.
Hint Resolve eq_term_implies_ws_l : lang_core.

Lemma eq_term_implies_ws_r l c t e1 e2
  : ws_lang l -> eq_term l c t e1 e2 -> well_scoped (map fst c) e2.
Proof.
  intros wsl eqs; apply (proj2 (proj1 (proj2 (wf_implies_ws wsl)) _ _ _ _ eqs)).
Qed.
Hint Resolve eq_term_implies_ws_r : lang_core.


Lemma eq_subst_implies_ws_l l c c' s1 s2
  : ws_lang l -> all_fresh c' -> eq_subst l c  c' s1 s2 -> well_scoped (map fst c) s1.
Proof.
  intros wsl allc eqs; apply (proj1 (proj1 (proj2 (proj2 (wf_implies_ws wsl))) _ _ _ _ eqs allc)).
Qed.
Hint Resolve eq_subst_implies_ws_l : lang_core.

Lemma eq_subst_implies_ws_r l c c' s1 s2
  : ws_lang l -> all_fresh c' -> eq_subst l c  c' s1 s2 -> well_scoped (map fst c) s2.
Proof.
  intros wsl allc eqs; apply (proj2 (proj1 (proj2 (proj2 (wf_implies_ws wsl))) _ _ _ _ eqs allc)).
Qed.
Hint Resolve eq_subst_implies_ws_r : lang_core.

Definition wf_sort_implies_ws l (wsl : ws_lang l)
  := proj1 (proj2 (proj2 (proj2 (wf_implies_ws wsl)))).
Hint Resolve wf_sort_implies_ws : lang_core.

Definition wf_term_implies_ws l  (wsl : ws_lang l)
  := proj1 (proj2 (proj2 (proj2 (proj2 (wf_implies_ws wsl))))).
Hint Resolve wf_term_implies_ws : lang_core.

Definition wf_args_implies_ws l (wsl : ws_lang l)
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (wf_implies_ws wsl)))))).
Hint Resolve wf_args_implies_ws : lang_core.

Definition wf_ctx_implies_ws l (wsl : ws_lang l)
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (wf_implies_ws wsl)))))).
Hint Resolve wf_ctx_implies_ws : lang_core.

Lemma wf_rule_implies_ws l r
  : ws_lang l ->
    wf_rule l r ->
    ws_rule r.
Proof.
  inversion 2; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_rule_implies_ws : lang_core.

Section Extension.
  Context (l_pre : lang).

  Inductive wf_lang_ext : lang -> Prop :=
  | wf_lang_nil : wf_lang_ext []
  | wf_lang_cons : forall l n r,
      fresh n (l++l_pre) ->
      wf_lang_ext l ->
      wf_rule (l++l_pre) r ->
      wf_lang_ext ((n,r)::l).
  Hint Constructors wf_lang_ext : lang_core.

  Lemma invert_wf_lang_nil
    : wf_lang_ext [] <-> True.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_wf_lang_nil : lang_core.

  Lemma invert_wf_lang_cons n r l
    : wf_lang_ext ((n,r)::l) <-> fresh n (l++l_pre) /\ wf_lang_ext l /\ wf_rule (l++l_pre) r.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_wf_lang_cons : lang_core.

  Lemma rule_in_wf l r name
    : wf_lang_ext l -> In (name,r) l -> wf_rule (l ++ l_pre) r.
  Proof.
    induction 1; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve rule_in_wf : lang_core.
  
  Lemma wf_lang_ext_all_fresh l : wf_lang_ext l -> all_fresh l.
  Proof.
    induction l; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve wf_lang_ext_all_fresh : lang_core.
  
  Lemma wf_lang_ext_all_fresh_with_pre l
    : all_fresh l_pre ->
      wf_lang_ext l ->
      all_fresh (l ++ l_pre).
  Proof.
    induction l; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve wf_lang_ext_all_fresh_with_pre : lang_core.

  Lemma wf_lang_implies_ws l
    : ws_lang l_pre -> wf_lang_ext l -> ws_lang (l++l_pre).
  Proof.
    induction 2; basic_goal_prep; basic_core_firstorder_crush.
  Qed.
  Hint Resolve wf_lang_implies_ws : lang_core.

End Extension.
Hint Constructors wf_lang_ext : lang_core.
Hint Rewrite invert_wf_lang_nil : lang_core.
Hint Rewrite invert_wf_lang_cons : lang_core.
Hint Resolve rule_in_wf : lang_core.
Hint Resolve wf_lang_ext_all_fresh : lang_core.
Hint Resolve wf_lang_ext_all_fresh_with_pre : lang_core.
Hint Resolve wf_lang_implies_ws : lang_core.


Ltac use_rule_in_wf :=
    match goal with
      [ H : wf_lang_ext _ ?l,
            Hin : In (_,_) ?l |-_] =>
      pose proof (rule_in_wf _ _ H Hin)
    end.
(*Notation so that extension lemmas still apply *)
Notation wf_lang l := (wf_lang_ext [] l).


Lemma wf_lang_concat l1 l2
  : wf_lang l1 ->
    wf_lang_ext l1 l2 ->
    wf_lang (l2 ++ l1).
Proof.
  induction 2; basic_goal_prep; basic_core_firstorder_crush.
Qed.
Hint Resolve wf_lang_concat : lang_core.

Lemma wf_lang_implies_ws_noext l
  : wf_lang l -> ws_lang l.
Proof.
  intro.
  rewrite <- (app_nil_r l).
  eauto with lang_core.
  apply  wf_lang_implies_ws; auto.
  compute; auto.
Qed.
Hint Resolve wf_lang_implies_ws_noext : lang_core.

Local Lemma ctx_mono l name t'
  : wf_lang l ->
    (forall c t1 t2,
        eq_sort l c t1 t2 ->
        eq_sort l ((name,t')::c) t1 t2)
    /\ (forall c t e1 e2,
          eq_term l c t e1 e2 ->
          eq_term l ((name,t')::c) t e1 e2)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           eq_subst l ((name,t')::c) c' s1 s2)
    /\ (forall c t,
           wf_sort l c t ->
           wf_sort l ((name,t')::c) t)
    /\ (forall c e t,
           wf_term l c e t ->
           wf_term l ((name,t')::c) e t)
    /\ (forall c s c',
           wf_args l c s c' ->
           wf_args l ((name,t')::c) s c')
    /\ (forall c,
           wf_ctx l c -> True).
Proof using.
  intro wfl.
  (*Intuition crush is much slower here than firstorder for some reason *)
  apply judge_ind; basic_goal_prep; basic_core_firstorder_crush.
  {
    replace t1 with t1[/id_subst c/]; [|basic_core_crush].
    replace t2 with t2[/id_subst c/]; [|basic_core_crush].
    eapply eq_sort_subst; [|basic_core_crush..].
    use_rule_in_wf; basic_core_crush.
  }
{
    replace t with t[/id_subst c/]; [|basic_core_crush].
    replace e1 with e1[/id_subst c/]; [|basic_core_crush].
    replace e2 with e2[/id_subst c/]; [|basic_core_crush].
    eapply eq_term_subst; [|basic_core_crush..].
    use_rule_in_wf; basic_core_crush.
    admit.
    admit.
  }
Admitted.

Definition eq_sort_ctx_monotonicity l name t' (wfl : wf_lang l)
  := proj1 (ctx_mono name t' wfl).
Hint Resolve eq_sort_ctx_monotonicity : lang_core.

Definition eq_term_ctx_monotonicity l name t' (wfl : wf_lang l)
  := proj1 (proj2 (ctx_mono name t' wfl)).
Hint Resolve eq_term_ctx_monotonicity : lang_core.

Definition eq_subst_ctx_monotonicity l name t' (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (ctx_mono name t' wfl))).
Hint Resolve eq_subst_ctx_monotonicity : lang_core.

Definition wf_sort_ctx_monotonicity l name t' (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (proj2 (ctx_mono name t' wfl)))).
Hint Resolve wf_sort_ctx_monotonicity : lang_core.

Definition wf_term_ctx_monotonicity l name t' (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (proj2 (proj2 (ctx_mono name t' wfl))))).
Hint Resolve wf_term_ctx_monotonicity : lang_core.

Definition wf_args_ctx_monotonicity l name t' (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (ctx_mono name t' wfl)))))).
Hint Resolve wf_args_ctx_monotonicity : lang_core.

Lemma in_ctx_wf l c n t
  : wf_lang l ->
    wf_ctx l c ->
    In (n,t) c ->
    wf_sort l c t.
Proof.
  induction 2; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve in_ctx_wf : lang_core.

(*TODO: figure out why I need this here?
  Should I include it in other places?
 *)
Lemma subst_lookup_hd n e s : (subst_lookup ((n, e) :: s) n) = e.
Proof.
  unfold subst_lookup; simpl.
  rewrite eqb_refl.
  reflexivity.
Qed.
(*TODO: move to Term and export?*)
Hint Rewrite subst_lookup_hd : term.

Lemma subst_lookup_tl n m e s
  : m <> n -> subst_lookup ((n, e) :: s) m = subst_lookup s m.
Proof.
  unfold subst_lookup; simpl.
  intros.
  rewrite <- eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma wf_term_lookup l c s c'
  : wf_lang l ->
    wf_subst l c s c' ->
    wf_ctx l c' ->
    forall n t,
    In (n,t) c' ->
    wf_term l c (subst_lookup s n) t [/s /].
Proof.
  
  (*TODO: debug; why is it needed twice?*)
  induction 2; basic_goal_prep;
    basic_core_firstorder_crush;
    basic_core_firstorder_crush.
  { apply []. }
  {
    (* TODO: Substable/Substable_ok split less frientdly to rewriting, needs erewrite *)
    case_eq (eqb n name).
    intros.
    apply eqb_eq in H7.
    unfold fresh in H2.
    apply in_map with (f:=fst) in H4.
    rewrite H7 in H4.
    apply H2 in H4.
    contradiction.
    intros.
    apply H6.
    assumption.
  }
  { basic_core_crush. }
  { apply []. }
Qed.
Hint Resolve wf_term_lookup : lang_core.  


Lemma wf_args_length_eq l c s c'
  : wf_args l c s c' ->
    length c' = length s.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_args_length_eq : lang_core.

(*Not all cases are necessary here,
  so I just use True instead of generating
  a new induction scheme
 *)
Local Lemma subst_mono l
  : wf_lang l ->
    (forall c t1 t2,
        eq_sort l c t1 t2 -> True)
    /\ (forall c t e1 e2,
           eq_term l c t e1 e2 -> True)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           wf_ctx l c -> 
           wf_ctx l c' -> 
           forall c'' s1' s2',
             eq_subst l c'' c s1' s2' ->
             eq_subst l c'' c' s1[/s1'/] s2[/s2'/])
    /\ (forall c t,
           wf_sort l c t ->
           wf_ctx l c -> 
           forall c'' s,
             wf_subst l c'' s c ->
           wf_sort l c'' t[/s/])
    /\ (forall c e t,
           wf_term l c e t ->
           wf_ctx l c -> 
           forall c'' s,
             wf_subst l c'' s c ->
           wf_term l c'' e[/s/] t[/s/])
    /\ (forall c s c',
           wf_args l c s c' ->
           wf_ctx l c -> 
           wf_ctx l c' -> 
           forall c'' s',
             wf_subst l c'' s' c ->
           wf_args l c'' s[/s'/] c')
    /\ (forall c,
           wf_ctx l c -> True).
Proof.
  intro wfl.
  apply judge_ind; basic_goal_prep; 
    try use_rule_in_wf;basic_core_firstorder_crush.
  {
    constructor; fold_Substable.
    { basic_core_crush. }
    {
      (*TODO: make this smoother*)
      unfold apply_subst at 2.
      unfold substable_subst.
      rewrite <- subst_assoc.
      eapply eq_term_subst; [|basic_core_crush..]; auto.
      replace (map fst s2) with (map fst c'); 
        basic_core_crush.
      (*TODO: why isn't this automatic? Make symmetric version?*)
      erewrite eq_subst_dom_eq_r; basic_core_crush.
      (*TODO: why isn't this automatic? Make symmetric version?*)
      erewrite eq_subst_dom_eq_r; basic_core_crush.
      apply [].
    }
  }
  {
    fold_Substable.
    (* erewrite <- subst_assoc; try typeclasses eauto; [| basic_core_crush]; fold_Substable. *)
    erewrite <- with_names_from_args_subst.
    econstructor; simpl; fold_Substable; basic_core_crush.
  }
  {
    constructor; fold_Substable; eauto.
    {
      erewrite with_names_from_args_subst.
      (*TODO: make this smoother*)
      unfold apply_subst at 3.
      unfold substable_subst.
      erewrite <- subst_assoc.
      (*TODO remove associativity hint?*)
      eauto with utils lang_core.
      basic_core_crush.
      basic_core_crush.
      apply [].
    }
  }
Qed.

Definition eq_subst_subst_monotonicity l (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (subst_mono wfl))).
Hint Resolve eq_subst_subst_monotonicity : lang_core.

Definition wf_sort_subst_monotonicity l (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (proj2 (subst_mono wfl)))).
Hint Resolve wf_sort_subst_monotonicity : lang_core.

Definition wf_term_subst_monotonicity l (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (proj2 (proj2 (subst_mono wfl))))).
Hint Resolve wf_term_subst_monotonicity : lang_core.

Definition wf_args_subst_monotonicity l (wfl : wf_lang l)
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (subst_mono wfl)))))).
Hint Resolve wf_args_subst_monotonicity : lang_core.

Local Lemma checked_subproperties l
  : wf_lang l ->
    (forall c t1 t2,
        eq_sort l c t1 t2 ->
        wf_ctx l c ->
        wf_sort l c t1 /\ wf_sort l c t2)
    /\ (forall c t e1 e2,
           eq_term l c t e1 e2 ->
           wf_ctx l c ->
           wf_term l c e1 t /\ wf_term l c e2 t /\ wf_sort l c t)
    /\ (forall c c' s1 s2,
           eq_subst l c c' s1 s2 ->
           wf_ctx l c ->
           wf_ctx l c' ->
           wf_subst l c s1 c' /\ wf_subst l c s2 c')
    /\ (forall c t,
           wf_sort l c t -> True)
    /\ (forall c e t,
           wf_term l c e t -> 
           wf_ctx l c ->
           wf_sort l c t)
    /\ (forall c s c',
           wf_args l c s c' -> True)
    /\ (forall c,
           wf_ctx l c -> True).
Proof using V V_Eqb V_default.
  intros; apply judge_ind; basic_goal_prep;
    try use_rule_in_wf;basic_core_crush.
Qed.

Lemma eq_sort_wf_l l c t1 t2
  : wf_lang l ->
    wf_ctx l c ->
    eq_sort l c t1 t2 ->
    wf_sort l c t1.
Proof.
  intros wfl wfc eqt.
  pose proof (proj1 (checked_subproperties wfl)
                    _ _ _ eqt wfc).
  intuition.
Qed.
Hint Resolve eq_sort_wf_l : lang_core.

Lemma eq_sort_wf_r l c t1 t2
  : wf_lang l ->
    wf_ctx l c ->
    eq_sort l c t1 t2 ->
    wf_sort l c t2.
Proof.
  intros wfl wfc eqt.
  pose proof (proj1 (checked_subproperties wfl)
                    _ _ _ eqt wfc).
  intuition.
Qed.
Hint Resolve eq_sort_wf_r : lang_core.

Lemma eq_term_wf_l l c e1 e2 t
  : wf_lang l ->
    wf_ctx l c ->
    eq_term l c t e1 e2 ->
    wf_term l c e1 t.
Proof.
  intros wfl wfc eqt.
  pose proof (proj1 (proj2 (checked_subproperties wfl))
                    _ _ _ _ eqt wfc).
  intuition.
Qed.
Hint Resolve eq_term_wf_l : lang_core.

Lemma eq_term_wf_r l c e1 e2 t
  : wf_lang l ->
    wf_ctx l c ->
    eq_term l c t e1 e2 ->
    wf_term l c e2 t.
Proof.
  intros wfl wfc eqt.
  pose proof (proj1 (proj2 (checked_subproperties wfl))
                    _ _ _ _ eqt wfc).
  intuition.
Qed.
Hint Resolve eq_term_wf_r : lang_core.

Lemma eq_term_wf_sort l c e1 e2 t
  : wf_lang l ->
    wf_ctx l c ->
    eq_term l c t e1 e2 ->
    wf_sort l c t.
Proof.
  intros wfl wfc eqt.
  pose proof (proj1 (proj2 (checked_subproperties wfl))
                    _ _ _ _ eqt wfc).
  intuition.
Qed.
Hint Resolve eq_term_wf_sort : lang_core.

Lemma eq_subst_wf_l l c c' s1 s2
  : wf_lang l ->
    wf_ctx l c ->
    wf_ctx l c' ->
    eq_subst l c c' s1 s2 ->
    wf_subst l c s1 c'.
Proof.
  intros wfl wfc wfc' eqt.
  pose proof (proj1 (proj2 (proj2 (checked_subproperties wfl)))
                    _ _ _ _ eqt wfc wfc').
  intuition.
Qed.
Hint Resolve eq_subst_wf_l : lang_core.

Lemma eq_subst_wf_r l c c' s1 s2
  : wf_lang l ->
    wf_ctx l c ->
    wf_ctx l c' ->
    eq_subst l c c' s1 s2 ->
    wf_subst l c s2 c'.
Proof.
  intros wfl wfc wfc' eqt.
  pose proof (proj1 (proj2 (proj2 (checked_subproperties wfl)))
                    _ _ _ _ eqt wfc wfc').
  intuition.
Qed.
  Hint Resolve eq_subst_wf_r : lang_core.

    (*
  Defined by inlining nested datatypes then modifying the results of the mutual schemes below.
  The induction schemes for the nested types were pulled out into a separate section
  and various naming and implicit arguments changes were made for brevity
  and (some) legibility.


Scheme wf_sort_ind'' := Minimality for wf_sort Sort Prop
  with wf_term_ind'' := Minimality for wf_term Sort Prop
  with wf_args_ind'' := Minimality for wf_args Sort Prop.

   *)
  Section WFJudgeInd.
    Context (l : lang)
            (P : ctx -> sort -> Prop)
            (P0 : ctx -> term -> sort -> Prop)
            (P1 : ctx -> list term -> ctx -> Prop)
            (f : forall (c : ctx) (n : V) (s : list term) (args : list V) (c' : ctx),
                In (n, sort_rule c' args) l -> wf_args l c s c' -> P1 c s c' -> P c (scon n s))
            (f0 : forall (c : ctx) (n : V) (s : list term) (args : list V) (c' : ctx) (t : sort),
                In (n, term_rule c' args t) l ->
                wf_args l c s c' -> P1 c s c' -> P0 c (con n s) t [/with_names_from c' s /])
            (f1 : forall (c : ctx) (e : term) (t t' : sort),
                wf_term l c e t -> P0 c e t -> eq_sort l c t t' -> P0 c e t')
            (f2 : forall (c : list (V * sort)) (n : V) (t : sort), In (n, t) c -> P0 c (var n) t)
            (f3 : forall c : ctx, P1 c [] [])
            (f4 : forall (c : ctx) (s : list term) (c' : named_list sort) (name : V) (e : term) (t : sort),
                wf_term l c e t [/with_names_from c' s /] ->
                P0 c e t [/with_names_from c' s /] ->
                wf_args l c s c' -> P1 c s c' -> P1 c (e :: s) ((name, t) :: c')).

    Section Nested.
       Context (wf_term_ind''
                : forall (c : ctx) (t : term) (s : sort), wf_term l c t s -> P0 c t s).
       Fixpoint wf_args_ind''' (c : ctx) (l0 : list term) (c0 : ctx) (w : wf_args l c l0 c0)
         : P1 c l0 c0 :=
           match w in (Model.wf_args c1 l1 c2) return (P1 c1 l1 c2) with
           | wf_args_nil c1 => f3 c1
           | wf_args_cons name _ t w0 w1 =>
               f4 name t w0 (wf_term_ind'' w0) w1 (wf_args_ind''' w1)
           end.
    End Nested.
    
    Fixpoint wf_term_ind'' (c : ctx) (t : term) (s : sort) (w : wf_term l c t s) : P0 c t s :=
           match w in (wf_term _ c0 t0 s0) return (P0 c0 t0 s0) with
           | @wf_term_by _ c0 n s0 args c' t0 i w0 =>
               f0 n args t0 i w0 (wf_args_ind''' wf_term_ind'' w0)
           | @wf_term_conv _ c0 e t0 t' w0 e0 => f1 w0 (wf_term_ind'' w0) e0
           | wf_term_var _ c0 n t0 _ i => f2 c0 n t0 i
           end.
    
    Definition wf_sort_ind'' (c : ctx) (s : sort) (w : wf_sort l c s) : P c s :=
      match w in (wf_sort _ c0 s0) return (P c0 s0) with
      | wf_sort_by n args i w0 =>
          f n args i w0 (wf_args_ind''' wf_term_ind'' w0)
      end.
    
    (*TODO: fix naming scheme*)
    Definition wf_args_ind'''' := wf_args_ind''' wf_term_ind''.

    (*TODO: used to only have 1 ' on sort, term.
      This was a typo. Let's see if fixing it breaks anything.
     *)
    Combined Scheme wf_judge_ind
             from wf_sort_ind'', wf_term_ind'', wf_args_ind''''.
  End WFJudgeInd.

Lemma eq_args_implies_eq_subst l c c' s1 s2
  : eq_args l c c' s1 s2 ->
    eq_subst l c c' (with_names_from c' s1) (with_names_from c' s2).
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.

Local Lemma lang_insert_mono l' l name r
  : (forall c t1 t2,
        eq_sort (l' ++ l) c t1 t2 ->
        eq_sort (l'++(name,r)::l) c t1 t2)
    /\ (forall c t e1 e2,
           eq_term (l' ++ l) c t e1 e2 ->
           eq_term (l'++(name,r)::l) c t e1 e2)
    /\ (forall c c' s1 s2,
           eq_subst (l' ++ l) c c' s1 s2 ->
           eq_subst (l'++(name,r)::l) c c' s1 s2)
    /\ (forall c t,
           wf_sort (l' ++ l) c t ->
           wf_sort (l'++(name,r)::l) c t)
    /\ (forall c e t,
           wf_term (l' ++ l) c e t ->
           wf_term (l'++(name,r)::l) c e t)
    /\ (forall c s c',
           wf_args (l' ++ l) c s c' ->
           wf_args (l'++(name,r)::l) c s c')
    /\ (forall c,
           wf_ctx (l' ++ l) c ->
           wf_ctx (l'++(name,r)::l) c).
Proof using.
  apply lang_mono.
  eauto with utils.
Qed.

Definition eq_sort_lang_insert_monotonicity l' l name r
  := proj1 (lang_insert_mono l' l name r).
Hint Resolve eq_sort_lang_insert_monotonicity : lang_core.


Lemma eq_sort_lang_insert_monotonicity_n l' l l'' c t1 t2
  :  eq_sort (l' ++ l) c t1 t2 ->
        eq_sort (l'++l''++l) c t1 t2.
Proof.
  induction l''; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_sort_lang_insert_monotonicity_n : lang_core.

Definition eq_term_lang_insert_monotonicity l' l name r
  := proj1 (proj2 (lang_insert_mono l' l name r)).
Hint Resolve eq_term_lang_insert_monotonicity : lang_core.

Definition eq_subst_lang_insert_monotonicity l' l name r
  := proj1 (proj2 (proj2 (lang_insert_mono l' l name r))).
Hint Resolve eq_subst_lang_insert_monotonicity : lang_core.

Definition wf_sort_lang_insert_monotonicity l' l name r
  := proj1 (proj2 (proj2 (proj2 (lang_insert_mono l' l name r)))).
Hint Resolve wf_sort_lang_insert_monotonicity : lang_core.

Definition wf_term_lang_insert_monotonicity l' l name r
  := proj1 (proj2 (proj2 (proj2 (proj2 (lang_insert_mono l' l name r))))).
Hint Resolve wf_term_lang_insert_monotonicity : lang_core.


Lemma wf_term_lang_insert_monotonicity_n l' l l'' c e t
  : wf_term (l' ++ l) c e t ->
    wf_term (l'++l''++l) c e t.
Proof.
  induction l''; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_term_lang_insert_monotonicity_n : lang_core.

Definition wf_args_lang_insert_monotonicity l' l name r
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_insert_mono l' l name r)))))).
Hint Resolve wf_args_lang_insert_monotonicity : lang_core.

Definition wf_ctx_lang_insert_monotonicity l' l name r
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_insert_mono l' l name r)))))).
Hint Resolve wf_ctx_lang_insert_monotonicity : lang_core.

Lemma wf_rule_lang_insert_monotonicity l' l name r' r
  : wf_rule (l'++l) r -> wf_rule (l'++(name, r') :: l) r.
Proof.
  inversion 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_rule_lang_insert_monotonicity : lang_core.


Lemma lang_insert_wf l' l r s
  : fresh s (l'++l) ->
    wf_rule l r ->
    wf_lang (l' ++ l) ->
    wf_lang (l' ++ (s,r)::l).
Proof.
  induction l'; inversion 3; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve lang_insert_wf : lang_core.

Theorem lang_sum_wf l1 l2 l_pre
  : all_fresh (l1++l2) ->
    wf_lang (l1++l_pre) ->
    wf_lang (l2++l_pre) ->
    wf_lang (l1++l2++l_pre).
Proof.
  induction l2; inversion 3; basic_goal_prep; basic_core_crush.
  apply lang_insert_wf; basic_core_crush.
  (*Not included in auto hints because it could trigger too often.
    TODO: assess whether this really impacts performance.
   *)
  eapply all_fresh_insert_is_fresh; eauto.
Qed.

(*TODO: prove strengthened version?
Theorem lang_sum_wf l1 l2 l_pre
  : all_fresh (l1++l2++l_pre) ->
    wf_lang l_pre ->
    wf_lang (l1++l_pre1) ->
    wf_lang (l2++l_pre2) ->
    incl l_pre1 l_pre ->
    incl l_pre2 l_pre ->
    wf_lang (l1++l2++l_pre).
Proof.
*)


Lemma eq_args_length_eq_l l c c' s1 s2
  : eq_args l c c' s1 s2 ->
    Datatypes.length c' = Datatypes.length s1.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_args_length_eq_l : lang_core.

Lemma eq_args_length_eq_r l c c' s1 s2
  : eq_args l c c' s1 s2 ->
    Datatypes.length c' = Datatypes.length s2.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve eq_args_length_eq_r : lang_core.


(*TODO: come up w/ a more systematic way of constructing this*)
Ltac with_rule_in_wf_crush :=
  let rewrite_tac := autorewrite with utils term lang_core in * in
  let hint_auto := eauto with utils term lang_core in
          subst; rewrite_tac; firstorder;
                   try use_rule_in_wf; rewrite_tac;
  firstorder (subst; rewrite_tac;(* repeat rewrite_strengthen;*) hint_auto;
              try (solve [ exfalso; hint_auto
                         | repeat (f_equal; hint_auto)])).


Lemma strengthen_fresh_name A n e (c' : named_list A) s
  : fresh n c' ->
    (map var (map fst c'))[/(n, e) :: s/]
    = (map var (map fst c'))[/s/].
Proof.
  induction c'; 
    basic_goal_prep; auto.
  f_equal; simpl; basic_utils_crush.
  unfold term_subst.
  simpl.
  apply subst_lookup_tl; eauto.
Qed.

Lemma wf_con_id_args_subst A (c' : named_list A) s
  : all_fresh c' ->
    length c' = length s ->
    (id_args c')[/with_names_from c' s/] = s.
Proof.
  revert s.
  induction c'; destruct s;
      basic_goal_prep; try f_equal;
        with_rule_in_wf_crush.
  fold_Substable.
  rewrite strengthen_fresh_name; auto.
Qed.
Hint Rewrite wf_con_id_args_subst : lang_core.
                   
Lemma term_con_congruence l c t name s1 s2 c' args t'
  : In (name, term_rule c' args t') l ->
    len_eq c' s2 ->
    t = t'[/with_names_from c' s2/] ->
    wf_lang l ->
    eq_args l c c' s1 s2 ->
    eq_term l c t (con name s1) (con name s2).
Proof.
  intros.
  assert (wf_ctx l c') by with_rule_in_wf_crush.
  rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_crush..].
  rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_crush..].
  subst.
  change (con ?n ?args[/?s/]) with (con n args)[/s/].
  eapply eq_term_subst; eauto.
  apply eq_args_implies_eq_subst; eauto.
  constructor.
  replace t' with t'[/id_subst c'/].
  eapply wf_term_by; basic_core_crush.
  (* basic_core_crush. *)
  admit.
Admitted.
                   
Lemma sort_con_congruence l c name s1 s2 c' args
  : In (name, sort_rule c' args) l ->
    len_eq c' s2 ->
    wf_lang l ->
    eq_args l c c' s1 s2 ->
    eq_sort l c (scon name s1) (scon name s2).
Proof.
  intros.
  assert (wf_ctx l c') by with_rule_in_wf_crush.
  rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_crush..].
  rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_crush..].
  subst.
  change (scon ?n ?args[/?s/]) with (scon n args)[/s/].
  eapply eq_sort_subst; eauto.
  apply eq_args_implies_eq_subst; eauto.
  constructor.
  eapply wf_sort_by; basic_core_crush.
Qed.

End WithVar.


                                           
#[export] Hint Constructors eq_sort eq_term eq_subst eq_args
     wf_sort wf_term wf_subst wf_args wf_ctx
     wf_rule : lang_core.

#[export] Hint Resolve eq_sort_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve eq_term_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve eq_subst_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve wf_sort_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve wf_term_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve wf_args_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve wf_ctx_lang_monotonicity_cons : lang_core.
#[export] Hint Resolve wf_rule_lang_monotonicity_cons : lang_core.

#[export] Hint Resolve eq_sort_lang_monotonicity_app : lang_core.
#[export] Hint Resolve eq_term_lang_monotonicity_app : lang_core.
#[export] Hint Resolve eq_subst_lang_monotonicity_app : lang_core.
#[export] Hint Resolve wf_sort_lang_monotonicity_app : lang_core.
#[export] Hint Resolve wf_term_lang_monotonicity_app : lang_core.
#[export] Hint Resolve wf_args_lang_monotonicity_app : lang_core.
#[export] Hint Resolve wf_args_lang_monotonicity_app : lang_core.
#[export] Hint Resolve wf_rule_lang_monotonicity_app : lang_core.


#[export] Hint Resolve wf_subst_from_wf_args : lang_core.
#[export] Hint Resolve id_args_wf : lang_core.
#[export] Hint Resolve eq_subst_dom_eq_r : lang_core.
#[export] Hint Resolve eq_subst_dom_eq_l : lang_core.
#[export] Hint Resolve wf_subst_dom_eq : lang_core.

#[export] Hint Resolve eq_subst_refl : lang_core.
#[export] Hint Resolve subst_name_fresh_from_ctx : lang_core.
#[export] Hint Resolve eq_subst_name_fresh_l_from_ctx : lang_core.
#[export] Hint Resolve eq_subst_name_fresh_r_from_ctx : lang_core.
Arguments in_all_named_list [V]%type_scope {A}%type_scope 
  [P]%function_scope {_} {_} {_}.

#[export] Hint Resolve wf_ctx_all_fresh : lang_core.

#[export] Hint Resolve eq_sort_implies_ws_l : lang_core.
#[export] Hint Resolve eq_sort_implies_ws_r : lang_core.
#[export] Hint Resolve eq_term_implies_ws_l : lang_core.
#[export] Hint Resolve eq_term_implies_ws_r : lang_core.
#[export] Hint Resolve eq_subst_implies_ws_l : lang_core.
#[export] Hint Resolve eq_subst_implies_ws_r : lang_core.

#[export] Hint Resolve wf_sort_implies_ws : lang_core.
#[export] Hint Resolve wf_term_implies_ws : lang_core.
#[export] Hint Resolve wf_args_implies_ws : lang_core.
#[export] Hint Resolve wf_ctx_implies_ws : lang_core.
#[export] Hint Resolve wf_rule_implies_ws : lang_core.

#[export] Hint Constructors wf_lang_ext : lang_core.
#[export] Hint Rewrite invert_wf_lang_nil : lang_core.
#[export] Hint Rewrite invert_wf_lang_cons : lang_core.
#[export] Hint Resolve rule_in_wf : lang_core.
#[export] Hint Resolve wf_lang_ext_all_fresh : lang_core.
#[export] Hint Resolve wf_lang_ext_all_fresh_with_pre : lang_core.
#[export] Hint Resolve wf_lang_implies_ws : lang_core.

(*TODO: duplicated to use outside of section; deduplicate? *)
Ltac use_rule_in_wf :=
    match goal with
      [ H : wf_lang_ext _ ?l,
            Hin : In (_,_) ?l |-_] =>
      pose proof (rule_in_wf _ _ H Hin)
    end.

(*Notation so that extension lemmas still apply *)
Notation wf_lang l := (wf_lang_ext [] l).

#[export] Hint Resolve wf_lang_concat : lang_core.
#[export] Hint Resolve wf_lang_implies_ws_noext : lang_core.


#[export] Hint Resolve eq_sort_ctx_monotonicity : lang_core.
#[export] Hint Resolve eq_term_ctx_monotonicity : lang_core.
#[export] Hint Resolve eq_subst_ctx_monotonicity : lang_core.
#[export] Hint Resolve wf_sort_ctx_monotonicity : lang_core.
#[export] Hint Resolve wf_term_ctx_monotonicity : lang_core.
#[export] Hint Resolve wf_args_ctx_monotonicity : lang_core.
#[export] Hint Resolve in_ctx_wf : lang_core.

#[export] Hint Resolve wf_term_lookup : lang_core.

#[export] Hint Resolve wf_args_length_eq : lang_core.


#[export] Hint Rewrite invert_wf_subst_nil_cons : lang_core.
#[export] Hint Rewrite invert_wf_subst_cons_nil : lang_core.
#[export] Hint Rewrite invert_wf_subst_nil_nil : lang_core.
#[export] Hint Rewrite invert_wf_subst_cons_cons : lang_core.
#[export] Hint Rewrite invert_wf_sort_rule : lang_core.
#[export] Hint Rewrite invert_wf_term_rule : lang_core.
#[export] Hint Rewrite invert_wf_sort_eq_rule : lang_core.
#[export] Hint Rewrite invert_wf_term_eq_rule : lang_core.

#[export] Hint Constructors wf_lang_ext : lang_core.
#[export] Hint Rewrite invert_wf_lang_nil : lang_core.
#[export] Hint Rewrite invert_wf_lang_cons : lang_core.
#[export] Hint Resolve rule_in_wf : lang_core.
#[export] Hint Resolve wf_lang_ext_all_fresh : lang_core.
#[export] Hint Resolve wf_lang_ext_all_fresh_with_pre : lang_core.
#[export] Hint Resolve wf_lang_implies_ws : lang_core.

#[export] Hint Resolve eq_subst_subst_monotonicity : lang_core.
#[export] Hint Resolve wf_sort_subst_monotonicity : lang_core.
#[export] Hint Resolve wf_term_subst_monotonicity : lang_core.
#[export] Hint Resolve wf_args_subst_monotonicity : lang_core.


#[export] Hint Resolve eq_sort_wf_l : lang_core.
#[export] Hint Resolve eq_sort_wf_r : lang_core.
#[export] Hint Resolve eq_term_wf_l : lang_core.
#[export] Hint Resolve eq_term_wf_r : lang_core.


#[export] Hint Resolve eq_term_wf_sort : lang_core.
#[export] Hint Resolve eq_subst_wf_l : lang_core.
#[export] Hint Resolve eq_subst_wf_r : lang_core.

#[export] Hint Resolve eq_sort_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve eq_sort_lang_insert_monotonicity_n : lang_core.
#[export] Hint Resolve eq_term_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve eq_subst_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve wf_sort_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve wf_term_lang_insert_monotonicity : lang_core.

#[export] Hint Resolve wf_term_lang_insert_monotonicity_n : lang_core.
#[export] Hint Resolve wf_args_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve wf_ctx_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve wf_rule_lang_insert_monotonicity : lang_core.
#[export] Hint Resolve lang_insert_wf : lang_core.

#[export] Hint Resolve eq_args_length_eq_l : lang_core.
#[export] Hint Resolve eq_args_length_eq_r : lang_core.

#[export] Hint Rewrite wf_con_id_args_subst : lang_core.



(*TODO: duplicated; dedup?*)
Ltac with_rule_in_wf_crush :=
  let rewrite_tac := autorewrite with utils term lang_core in * in
  let hint_auto := eauto with utils term lang_core in
          subst; rewrite_tac; firstorder;
                   try use_rule_in_wf; rewrite_tac;
  firstorder (subst; rewrite_tac;(* repeat rewrite_strengthen;*) hint_auto;
              try (solve [ exfalso; hint_auto
                         | repeat (f_equal; hint_auto)])).
