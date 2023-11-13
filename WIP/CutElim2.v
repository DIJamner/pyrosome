
Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils SymmetricInduction.
From Pyrosome.Theory Require Import Core.

Module Notations.
  Export Term.Notations.
  Export Rule.Notations.
End Notations.
Import Notations.


(*TODO: move to Utils*)
Lemma fresh_with_names_from [V' A B] v (c' : @NamedList.named_list V' A) (s : list B)
  : Datatypes.length c' = Datatypes.length s -> fresh v (with_names_from c' s) = fresh v c'.
Proof.
  intros.
  unfold fresh.
  basic_utils_crush.
Qed.
Hint Rewrite fresh_with_names_from : utils.


(*TODO: move to Rule.v*)
Local Ltac use_rule_in_ws :=
  match goal with
  | H:ws_lang ?l, Hin:In (_, _) ?l |- _ => pose proof (rule_in_ws _ _ H Hin)
  end.


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


(*TODO: move to term*)
Lemma ws_subst_from_ws_args args (c' : ctx) (s : list term)
  : length c' = length s ->
    all_fresh c' ->
    well_scoped args s ->
    well_scoped args (with_names_from c' s).
Proof.
  revert c'; induction s;
    destruct c';
    basic_goal_prep;
    basic_term_crush.
  eapply IHs; eauto.
Qed.
Hint Resolve ws_subst_from_ws_args : lang_core.


  (*TODO: move to Term *)
  Lemma term_ws_incl (t:term) args args'
    : well_scoped args t ->incl args args' -> well_scoped args' t.
  Proof.
    induction t;
      basic_goal_prep;
      basic_term_crush.
    revert dependent l;
      induction l;
      basic_goal_prep;
      basic_term_crush.
  Qed.
  
  Lemma sort_ws_incl (t:sort) args args'
    : well_scoped args t ->incl args args' -> well_scoped args' t.
  Proof.
    destruct t.
    revert dependent l;
      induction l;
      basic_goal_prep;
      basic_term_crush.
    eapply term_ws_incl; eauto.
  Qed.

  
  Lemma ws_ctx_in c n t
    : ws_ctx c -> In (n,t) c -> well_scoped (map fst c) t.
  Proof.
    induction c;
      basic_goal_prep;
      basic_term_crush.
    all:eapply sort_ws_incl; eauto.
    all: basic_utils_crush.
  Qed.
  Hint Resolve ws_ctx_in : lang_core.


  Notation PreModel := (@PreModel V term sort).

  
  #[export] Instance syntax_model : PreModel :=
    {|
      term_substable := _;
      sort_substable := _;
    |}.

  
Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
  {|
    premodel := syntax_model;
      (*TODO: rename the conflict*)
      Model.eq_sort := eq_sort;
      (*TODO: rename the conflict*)
      Model.eq_term := eq_term;
      Model.wf_sort := wf_sort;
      Model.wf_term := wf_term;
    |}.

Section Terms.
  Context (l : lang).

  Section WithCtx.
  Context (c : ctx).

  (*All assume wf_lang.
    All ctxs (other than in wf_ctx) are assumed to satisfy wf_ctx.
    Judgments whose assumptions take ctxs must ensure they are wf.
    Sorts are not assumed to be wf; the term judgments should guarantee
    that their sorts are wf.
   *)

  (* TODO: equations can be independent of wfness in this formulation.
     This means that eq_subst/eq_args don't need the full model.
     Currently have them duplicated, but ideally the ones in Model.v
     could be generalized to be usable here.
   *)
  Inductive eq_sort : sort -> sort -> Prop :=
  | eq_sort_by : forall name c' t1 t2 s1 s2,
      In (name, sort_eq_rule c' t1 t2) l ->
      eq_subst c' s1 s2 ->
      eq_sort t1[/s1/] t2[/s2/]
  | eq_sort_cong : forall name c' args s1 s2,
      In (name,sort_rule c' args) l ->
      eq_args c' s1 s2 ->
      eq_sort (scon name s1) (scon name s2)
  | eq_sort_trans : forall t1 t12 t2,
      eq_sort t1 t12 ->
      eq_sort t12 t2 ->
      eq_sort t1 t2
  | eq_sort_sym : forall t1 t2, eq_sort t1 t2 -> eq_sort t2 t1
  with eq_term : sort -> term -> term -> Prop :=
  | eq_term_by : forall name c' t e1 e2 s1 s2,
      In (name,term_eq_rule c' e1 e2 t) l ->
      eq_subst c' s1 s2 ->
      eq_term t[/s2/] e1[/s1/] e2[/s2/]
  | eq_term_cong : forall name c' args t s1 s2,
      In (name,term_rule c' args t) l ->
      eq_args c' s1 s2 ->
      eq_term t[/(with_names_from c' s2)/] (con name s1) (con name s2)
  | eq_term_var : forall n t,
      In (n, t) c ->
      eq_term t (var n) (var n)
  | eq_term_trans : forall t e1 e12 e2,
      eq_term t e1 e12 ->
      eq_term t e12 e2 ->
      eq_term t e1 e2
  | eq_term_sym : forall t e1 e2, eq_term t e1 e2 -> eq_term t e2 e1
  (* Conversion:

c |- e1 = e2 : t 
               ||
c |- e1 = e2 : t'
   *)
  | eq_term_conv : forall e1 e2 t t',
      eq_term t e1 e2 ->
      eq_sort t t' ->
      eq_term t' e1 e2
  with eq_subst : ctx -> subst -> subst -> Prop :=
  | eq_subst_nil : eq_subst [] [] []
  | eq_subst_cons : forall (c' : ctx) (s1 s2 : subst),
                    eq_subst c' s1 s2 ->
                    forall (name : V) (t : sort) (e1 e2 : term),
                    eq_term t [/s2 /] e1 e2 ->
                    eq_subst ((name, t) :: c') ((name, e1) :: s1)
                      ((name, e2) :: s2)
  with eq_args : ctx -> list term -> list term -> Prop :=
  | eq_args_nil : eq_args [] [] []
  | eq_args_cons : forall (c' : ctx) (es1 es2 : list term),
      eq_args c' es1 es2 ->
      forall (name : V) (t : sort) (e1 e2 : term),
        eq_term t [/with_names_from c' es2 /] e1 e2 ->
        eq_args ((name, t) :: c') (e1 :: es1) (e2 :: es2).                

  
  (* TODO: do I need these? make notations for reflexivity
  Inductive wf_term : ctx -> term -> sort -> Prop :=
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
      In (n, t) c ->
      wf_term c (var n) t
  with wf_sort : ctx -> sort -> Prop :=
  | wf_sort_by : forall c n s args c',
      In (n, (sort_rule c' args)) l ->
      wf_args (Model:= mut_mod eq_sort eq_term wf_sort wf_term) c s c' ->
      wf_sort c (scon n s).
   
  #[export] Instance cut_model : Model := mut_mod eq_sort eq_term wf_sort wf_term.
  
  Notation wf_subst := (wf_subst (Model:= cut_model)).
  Notation wf_args := (wf_args (Model:= cut_model)).
  Notation wf_ctx := (wf_ctx (Model:= cut_model)).
   *)

  
  (* TODO: bug? This doesn't work even w/ eq_subst and eq_args defined mutually.
  Combined Scheme eq_ind
    from eq_sort_ind, eq_term_ind, eq_subst_ind, eq_args_ind.
   *)    
  
  Section EqInd.
    Context (P_sort : sort -> sort -> Prop)
      (P_term : sort -> term -> term -> Prop)
      (P_subst : ctx -> subst -> subst -> Prop)
      (P_args : ctx -> list term -> list term -> Prop).

    (* sort hypotheses *)
    Context (Hsort0 : forall (c' : ctx) (name : V) t1 t2 s1 s2,
          In (name, sort_eq_rule c' t1 t2) l ->
          eq_subst c' s1 s2 ->
          P_subst c' s1 s2 ->
          P_sort t1[/s1/] t2[/s2/])
      (Hsort1 : forall (c' : ctx) (name : V) args s1 s2,
          In (name, sort_rule c' args) l ->
          eq_args c' s1 s2 ->
          P_args c' s1 s2 ->
          P_sort (scon name s1) (scon name s2))
      (Hsort2 : forall (t1 t12 t2 : sort),
          eq_sort t1 t12 -> P_sort t1 t12 ->
          eq_sort t12 t2 -> P_sort t12 t2 ->
          P_sort t1 t2)
      (Hsort3 : forall (t1 t2 : sort),
          eq_sort t1 t2 -> P_sort t1 t2 -> P_sort t2 t1).
    
    (* Term hypotheses *)
    Context (f : forall (c' : ctx) (name : V) (t : sort) (e1 e2 : term) s1 s2,
          In (name, term_eq_rule c' e1 e2 t) l ->
          eq_subst c' s1 s2 ->
          P_subst c' s1 s2 ->
          P_term t[/s2/] e1[/s1/] e2[/s2/])
      (f0 : forall (c' : ctx) (name : V) (t : sort) args s1 s2,
          In (name, term_rule c' args t) l ->
          eq_args c' s1 s2 ->
          P_args c' s1 s2 ->
          P_term t[/(with_names_from c' s2)/] (con name s1) (con name s2))
      (f01 : forall (n : V) (t : sort),
          In (n, t) c -> P_term t (var n) (var n))
      (f1 : forall (t : sort) (e1 e12 e2 : term),
          eq_term t e1 e12 -> P_term t e1 e12 ->
          eq_term t e12 e2 -> P_term t e12 e2 ->
          P_term t e1 e2)
      (f2 : forall (t : sort) (e1 e2 : term),
          eq_term t e1 e2 -> P_term t e1 e2 -> P_term t e2 e1)
      (f3 : forall (t t' : sort),
          eq_sort t t' -> P_sort t t' ->
          forall e1 e2 : term,
            eq_term t e1 e2 -> P_term t e1 e2 -> P_term t' e1 e2).

    (* subst hypotheses *)
    Context (f4 : P_subst [] [] [])
      (f5 : forall (c' : ctx) s1 s2,
          eq_subst c' s1 s2 ->
          P_subst c' s1 s2 ->
          forall (name : V) (t : sort) (e1 e2 : term),
            eq_term t [/s2/] e1 e2 ->
            P_term t [/s2/] e1 e2 ->
            P_subst ((name, t) :: c') ((name,e1) :: s1) ((name,e2) :: s2)).
    
    (* args hypotheses *)
    Context (f6 : P_args [] [] [])
      (f7 : forall (c' : ctx) s1 s2,
          eq_args c' s1 s2 ->
          P_args c' s1 s2 ->
          forall (name : V) (t : sort) (e1 e2 : term),
            eq_term t [/with_names_from c' s2/] e1 e2 ->
            P_term t [/with_names_from c' s2/] e1 e2 ->
            P_args ((name, t) :: c') (e1 :: s1) (e2 :: s2)).
    
    Section NestedArgs.
      Context (eq_term_ind' : forall (s : sort) (t t0 : term),
                  eq_term s t t0 -> P_term s t t0).
      Arguments eq_term_ind' {_ _ _} _.

      Arguments eq_args_cons {c'}%ctx_scope {es1 es2}%list_scope _
        {name t e1 e2} _.

      Arguments f7 {c'}%ctx_scope {s1 s2}%list_scope _ _ {name t e1 e2} _ _.
      
      Fixpoint eq_args_ind' {c0 : ctx} {s s0} (e : eq_args c0 s s0)
        : P_args c0 s s0 :=
        match e in (eq_args c2 s1 s2) return (P_args c2 s1 s2) with
        | eq_args_nil => f6
        | eq_args_cons e0 e3 =>
            f7 e0 (eq_args_ind' e0) e3 (eq_term_ind' e3)
        end.
    End NestedArgs.
    
    Section NestedSubst.
      Context (eq_term_ind' : forall (s : sort) (t t0 : term),
                  eq_term s t t0 -> P_term s t t0).
      Arguments eq_term_ind' {_ _ _} _.

      Arguments eq_subst_cons {c'}%ctx_scope {s1 s2}%list_scope _
        {name t e1 e2} _.

      Arguments f5 {c'}%ctx_scope {s1 s2}%list_scope _ _ {name t e1 e2} _ _.
      
      Fixpoint eq_subst_ind' {c0 : ctx} {s s0} (e : eq_subst c0 s s0)
        : P_subst c0 s s0 :=
        match e in (eq_subst c2 s1 s2) return (P_subst c2 s1 s2) with
        | eq_subst_nil => f4
        | eq_subst_cons e0 e3 =>
            f5 e0 (eq_subst_ind' e0) e3 (eq_term_ind' e3)
        end.
    End NestedSubst.

    Fixpoint eq_sort_ind' [t t0]
      (e : eq_sort t t0) : P_sort t t0 :=
           match e in (eq_sort t1 t2) return (P_sort t1 t2) with
           | eq_sort_by name c' e1 e2 s1 s2 i pa =>
               Hsort0 c' name e1 e2 s1 s2 i pa (eq_subst_ind' eq_term_ind' pa)
           | eq_sort_cong name c' args s1 s2 i pa =>
               Hsort1 c' name args s1 s2 i pa (eq_args_ind' eq_term_ind' pa)
           | eq_sort_trans _ _ _ e0 e3 =>
               Hsort2 _ _ _ e0 (eq_sort_ind' e0) e3 (eq_sort_ind' e3)
           | eq_sort_sym _ _ e0 => Hsort3 _ _ e0 (eq_sort_ind' e0)
           end
    with eq_term_ind' [s t t0]
      (e : eq_term s t t0) : P_term s t t0 :=
           match e in (eq_term s0 t1 t2) return (P_term s0 t1 t2) with
           | eq_term_by name c' t1 e1 e2 s1 s2 i pa =>
               f c' name t1 e1 e2 s1 s2 i pa (eq_subst_ind' eq_term_ind' pa)
           | eq_term_cong name c' args t1 s1 s2 i pa =>
               f0 c' name t1 args s1 s2 i pa (eq_args_ind' eq_term_ind' pa)
           | eq_term_var n t0 i => f01 n t0 i
           | eq_term_trans _ _ _ _ e0 e3 =>
               f1 _ _ _ _ e0 (eq_term_ind' e0) e3 (eq_term_ind' e3)
           | eq_term_sym _ _ _ e0 => f2 _ _ _ e0 (eq_term_ind' e0)
           | eq_term_conv _ _ _ _ e3 e0 =>
               f3 _ _ e0 (eq_sort_ind' e0) _ _ e3 (eq_term_ind' e3)
           end.
    
    Definition eq_args_ind'' := @eq_args_ind' eq_term_ind'.
    Definition eq_subst_ind'' := @eq_subst_ind' eq_term_ind'.

    Definition cut_ind :=
      conj eq_sort_ind'
        (conj eq_term_ind'              
           (conj eq_subst_ind''             
              eq_args_ind'')).
  End EqInd.

  
  Local Hint Constructors eq_sort eq_term eq_subst eq_args : lang_core.
  
  Local Lemma eq_refl_right
    : (forall t1 t2,
          eq_sort t1 t2 ->
          eq_sort t2 t2)
      /\ (forall t e1 e2,
             eq_term t e1 e2 ->
             eq_term t e2 e2)
      /\ (forall c' s1 s2,
             eq_subst c' s1 s2 ->
             eq_subst c' s2 s2)
      /\ (forall c' s1 s2,
             eq_args c' s1 s2 ->
             eq_args c' s2 s2).
  Proof using V_Eqb_ok.
    simple eapply cut_ind;
      basic_goal_prep;
      basic_core_crush.
  Qed.
        
  Definition eq_sort_refl_right := proj1 eq_refl_right.
  Local Hint Resolve eq_sort_refl_right : lang_core.
  
  Definition eq_term_refl_right := proj1 (proj2 eq_refl_right).
  Local Hint Resolve eq_term_refl_right : lang_core.

  Definition eq_subst_refl_right := proj1 (proj2 (proj2 eq_refl_right)).
  Local Hint Resolve eq_subst_refl_right : lang_core.
  
  Definition eq_args_refl_right := proj2 (proj2 (proj2 eq_refl_right)).
  Local Hint Resolve eq_args_refl_right : lang_core.

  
  Lemma eq_args_implies_eq_subst:
  forall [c' : NamedList.named_list V sort] [s1 s2 : list term],
    eq_args c' s1 s2 -> eq_subst c' (with_names_from c' s1) (with_names_from c' s2).
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
  Qed.
  Hint Resolve eq_args_implies_eq_subst : lang_core.

  
  Lemma eq_subst_map_fst_r c0 s0 s3
    : eq_subst c0 s0 s3 -> map fst s3 = map fst c0.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
  Qed.
  #[local] Hint Rewrite eq_subst_map_fst_r using eassumption : lang_core.

  Lemma eq_subst_map_fst_l c0 s0 s3
    : eq_subst c0 s0 s3 -> map fst s0 = map fst c0.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
  Qed.
  #[local] Hint Rewrite eq_subst_map_fst_l using eassumption : lang_core.


  Lemma eq_subst_fresh_r c0 s0 s3 n
    : eq_subst c0 s0 s3 -> fresh n c0 -> fresh n s3.
  Proof.
    unfold fresh; intros.
    erewrite eq_subst_map_fst_r; eauto.
  Qed.
  #[local] Hint Resolve eq_subst_fresh_r : lang_core.

  Lemma eq_subst_fresh_l c0 s0 s3 n
    : eq_subst c0 s0 s3 -> fresh n c0 -> fresh n s0.
  Proof.
    unfold fresh; intros.
    erewrite eq_subst_map_fst_l; eauto.
  Qed.
  #[local] Hint Resolve eq_subst_fresh_l : lang_core.

  
  
  Lemma eq_args_len_eq_r c' s1 s2
    : eq_args c' s1 s2 ->
      length s2 = length c'.
  Proof.
    induction 1; basic_goal_prep;
      basic_core_crush.
  Qed.
  (*Hint Rewrite eq_args_len_eq_r using eassumption : lang_core.*)
  
  
  Lemma eq_args_len_eq_l c' s1 s2
    : eq_args c' s1 s2 ->
      length s1 = length c'.
  Proof.
    induction 1; basic_goal_prep;
      basic_core_crush.
  Qed.
  (*Hint Rewrite eq_args_len_eq_l using eassumption : lang_core.*)
  
  Section __.
    Context (wsl : ws_lang l)
      (wsc : ws_ctx c).
    
    Lemma eq_implies_ws
      : (forall t1' t2',
            eq_sort t1' t2' ->
            well_scoped (map fst c) t1'
            /\ well_scoped (map fst c) t2')
        /\ (forall (t : Term.sort V) (e1 e2 : Term.term V),
               eq_term t e1 e2 ->
               well_scoped (map fst c) t
               /\ well_scoped (map fst c) e1
               /\ well_scoped (map fst c) e2)
        /\ (forall (c' : Term.ctx V) (s1 s2 : Term.subst V),
              eq_subst c' s1 s2 ->
              ws_ctx c' ->
              well_scoped (map fst c) s1
              /\ well_scoped (map fst c) s2)
        /\ (forall c' (s1 s2 : list term),
               eq_args c' s1 s2 ->
               ws_ctx c' ->
               well_scoped (map fst c) s1
               /\ well_scoped (map fst c) s2).
    Proof using V_Eqb_ok wsl wsc.
      simple eapply cut_ind;
        basic_goal_prep.
      all: try use_rule_in_ws.
      all: basic_goal_prep.
      all: autorewrite with utils model term lang_core in *.
      all: basic_goal_prep.
      all: intuition subst.
      all: try eapply well_scoped_subst; eauto; try typeclasses eauto.
      all: eauto with utils model term lang_core.
      all: try change (ws_subst ?a ?b) with (well_scoped a b).
      all: try change (ws_args ?a ?b) with (well_scoped a b).
      all: try erewrite eq_subst_map_fst_l by eassumption; eauto.
      all: try erewrite eq_subst_map_fst_r by eassumption; eauto.
      all: try eapply ws_subst_from_ws_args.
      all: try eauto using ws_all_fresh_ctx.
      all: try erewrite eq_args_len_eq_r; eauto.
      basic_utils_crush.
      erewrite eq_args_len_eq_r; eauto.
    Qed.

    Definition eq_sort_implies_ws_l t1' t2' (Heq : eq_sort t1' t2') :=
      proj1 ((proj1 eq_implies_ws) _ _ Heq).
    Definition eq_sort_implies_ws_r t1' t2' (Heq : eq_sort t1' t2') :=
      proj2 ((proj1 eq_implies_ws) _ _ Heq).
    Definition eq_term_implies_ws_sort t e1 e2 (Heq : eq_term t e1 e2) :=
      proj1 ((proj1 (proj2 eq_implies_ws)) _ _ _ Heq).
    Definition eq_term_implies_ws_l t e1 e2 (Heq : eq_term t e1 e2) :=
      proj1 (proj2 ((proj1 (proj2 eq_implies_ws)) _ _ _ Heq)).
    Definition eq_term_implies_ws_r t e1 e2 (Heq : eq_term t e1 e2) :=
      proj2 (proj2 ((proj1 (proj2 eq_implies_ws)) _ _ _ Heq)).
    Definition eq_subst_implies_ws_l c' s1 s2 (Heq : eq_subst c' s1 s2) Hws' :=
      proj1 ((proj1 (proj2 (proj2 eq_implies_ws))) _ _ _ Heq Hws').
    Definition eq_subst_implies_ws_r c' s1 s2 (Heq : eq_subst c' s1 s2) Hws' :=
      proj2 ((proj1 (proj2 (proj2 eq_implies_ws))) _ _ _ Heq Hws').
    Definition eq_args_implies_ws_l c' s1 s2 (Heq : eq_args c' s1 s2) Hws' :=
      proj1 ((proj2 (proj2 (proj2 eq_implies_ws))) _ _ _ Heq Hws').
    Definition eq_args_implies_ws_r c' s1 s2 (Heq : eq_args c' s1 s2) Hws' :=
      proj2 ((proj2 (proj2 (proj2 eq_implies_ws))) _ _ _ Heq Hws').
    
    Hint Resolve eq_sort_implies_ws_l : lang_core.
    Hint Resolve eq_sort_implies_ws_r : lang_core.
    Hint Resolve eq_term_implies_ws_sort : lang_core. 
    Hint Resolve eq_term_implies_ws_l : lang_core. 
    Hint Resolve eq_term_implies_ws_r : lang_core.  
    Hint Resolve eq_subst_implies_ws_l : lang_core.
    Hint Resolve eq_subst_implies_ws_r : lang_core.
    Hint Resolve eq_args_implies_ws_l : lang_core.
    Hint Resolve eq_args_implies_ws_r : lang_core.

  End __.
  
  
  End WithCtx.

  Local Hint Constructors eq_sort eq_term eq_subst eq_args : lang_core.
  Local Hint Resolve eq_sort_refl_right : lang_core.
  Local Hint Resolve eq_term_refl_right : lang_core.
  Local Hint Resolve eq_subst_refl_right : lang_core.
  Local Hint Resolve eq_args_refl_right : lang_core.
  Hint Resolve eq_args_implies_eq_subst : lang_core.

  #[local] Hint Rewrite eq_subst_map_fst_r using eassumption : lang_core.
  #[local] Hint Rewrite eq_subst_map_fst_l using eassumption : lang_core.
  #[local] Hint Resolve eq_subst_fresh_r : lang_core.
  #[local] Hint Resolve eq_subst_fresh_l : lang_core.

  
  Hint Resolve eq_sort_implies_ws_l : lang_core.
  Hint Resolve eq_sort_implies_ws_r : lang_core.
  Hint Resolve eq_term_implies_ws_sort : lang_core. 
  Hint Resolve eq_term_implies_ws_l : lang_core. 
  Hint Resolve eq_term_implies_ws_r : lang_core.  
  Hint Resolve eq_subst_implies_ws_l : lang_core.
  Hint Resolve eq_subst_implies_ws_r : lang_core.
  Hint Resolve eq_args_implies_ws_l : lang_core.
  Hint Resolve eq_args_implies_ws_r : lang_core.

  

  Inductive wf_ctx : named_list sort -> Prop :=
    wf_ctx_nil : wf_ctx []
  | wf_ctx_cons : forall name c t,
      fresh name c -> wf_ctx c -> eq_sort c t t -> wf_ctx ((name, t) :: c).
  Hint Constructors wf_ctx : lang_core.

  
  Lemma invert_wf_ctx_nil : wf_ctx [] <-> True.
  Proof. solve_invert_constr_eq_lemma. Qed.
  #[local] Hint Rewrite invert_wf_ctx_nil : lang_core.

  Lemma invert_wf_ctx_cons c n t
    : wf_ctx ((n,t)::c) <-> fresh n c /\ wf_ctx c /\ eq_sort c t t.
  Proof. solve_invert_constr_eq_lemma. Qed.
  #[local] Hint Rewrite invert_wf_ctx_cons : lang_core.

  
  Local Lemma ctx_mono c c'
    : incl c c' ->
      (forall t1 t2,
          eq_sort c t1 t2 ->
          eq_sort c' t1 t2)
      /\ (forall t e1 e2,
             eq_term c t e1 e2 ->
             eq_term c' t e1 e2)
      /\ (forall c'' s1 s2,
             eq_subst c c'' s1 s2 ->
             eq_subst c' c'' s1 s2)
      /\ (forall c'' s1 s2,
             eq_args c c'' s1 s2 ->
             eq_args c' c'' s1 s2).
  Proof using V_Eqb_ok.
    intro Hincl.
    eapply cut_ind;
      basic_goal_prep;
      basic_core_crush.
  Qed.

  Lemma in_ctx_wf n t c
    : wf_ctx c -> In (n, t) c -> eq_sort c t t.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    all:eapply ctx_mono; eauto; eauto with utils.
  Qed.
  Hint Resolve in_ctx_wf : lang_core.


  Lemma cut_id_subst_refl' c c'
    : incl c c' -> eq_subst c' c (id_subst c) (id_subst c).
  Proof.
    revert c'.
    induction c;
      basic_goal_prep;
      basic_core_crush.
    constructor; eauto.
    eapply eq_term_var.
    replace (s [/with_names_from c (map var (map fst c)) /]) with s; eauto.
    symmetry.
    eapply sort_subst_id.
    eauto.
  Qed.

  Lemma cut_id_subst_refl c
    : eq_subst c c (id_subst c) (id_subst c).
  Proof.
    eapply cut_id_subst_refl'; basic_utils_crush.
  Qed.
  Hint Resolve cut_id_subst_refl : lang_core.

  Definition sort_cut_admissible c' t1' t2' :=
    forall c s1 s2,
      eq_subst c c' s1 s2 ->
      wf_ctx c' ->
      eq_sort c t1' [/s1 /] t2' [/s2 /].
  Definition term_cut_admissible c' t e1 e2 :=
    forall c s1 s2,
      eq_subst c c' s1 s2 ->
      wf_ctx c' -> eq_term c t [/s2 /] e1 [/s1 /] e2 [/s2 /].

  (* TODO: this is the easier one to prove, connect via weakening*)
  Fixpoint ctx_cut_admissible c :=
    match c with
    | [] => True
    | (_,t)::c' =>
        sort_cut_admissible c' t t
        /\ ctx_cut_admissible c'
    end.
  (*
  Definition ctx_all_admissible c :=
    forall n t, In (n,t) c -> sort_cut_admissible c t t.*)

  (* avoids a mutual definition to have separate weak version*)
  Definition weak_sort_cut_admissible c' t1' t2' :=
    forall c s1 s2,
      eq_subst c c' s1 s2 ->
      wf_ctx c' -> ctx_cut_admissible c' ->
      eq_sort c t1' [/s1 /] t2' [/s2 /].
  Definition weak_term_cut_admissible c' t e1 e2 :=
    forall c s1 s2,
      eq_subst c c' s1 s2 ->
      wf_ctx c' -> ctx_cut_admissible c' ->
      eq_term c t [/s2 /] e1 [/s1 /] e2 [/s2 /].

  Definition weak_subst_cut_admissible c c' s1 s2 :=
    wf_ctx c -> ctx_cut_admissible c ->
    wf_ctx c' -> ctx_cut_admissible c' ->
    forall (c'' : Term.ctx V) (s1' s2' : Term.subst V),
      eq_subst c'' c s1' s2' ->
      eq_subst c'' c' s1 [/s1' /] s2 [/s2' /].
  
  Definition weak_args_cut_admissible c c' s1 s2 :=
    wf_ctx c -> ctx_cut_admissible c ->
    wf_ctx c' -> ctx_cut_admissible c' ->
    forall (c'' : Term.ctx V) s1' s2',
      eq_subst c'' c s1' s2' ->
      eq_args c'' c' s1 [/s1' /] s2 [/s2' /].

  Definition rule_cut_admissible r :=
    match r with
    | sort_eq_rule c t1 t2 =>
        ctx_cut_admissible c
        /\ sort_cut_admissible c t1 t1
        /\ sort_cut_admissible c t2 t2
    | term_eq_rule c e1 e2 t =>
        ctx_cut_admissible c
        /\ sort_cut_admissible c t t
        /\ term_cut_admissible c t e1 e1
        /\ term_cut_admissible c t e2 e2
    | sort_rule c args =>
        ctx_cut_admissible c
    | term_rule c args t =>
        ctx_cut_admissible c
        /\ sort_cut_admissible c t t
    end.
  
  Lemma eq_subst_sym' c c' s1 s2
    : eq_subst c c' s1 s2 -> wf_ctx c' -> ctx_cut_admissible c' -> eq_subst c c' s2 s1.
  Proof using .
    induction 1; intros.
    1:basic_core_crush.
    constructor.
    all:basic_goal_prep.
    1: basic_core_crush.
    
    eapply eq_term_conv; eauto using eq_term_sym.
    break.
    safe_invert H1.
    eapply H2; eauto.
  Qed.


  Variant wf_rule : rule -> Prop :=
  | wf_sort_rule : forall c args,
      wf_ctx c ->
      sublist args (map fst c) ->
      wf_rule (sort_rule c args)
  | wf_term_rule : forall c args t,
      wf_ctx c ->
      eq_sort c t t ->
      sublist args (map fst c) ->
      wf_rule (term_rule c args t)
  | eq_sort_rule : forall c t1 t2,
      wf_ctx c ->
      eq_sort c t1 t1 ->
      eq_sort c t2 t2 ->
      wf_rule (sort_eq_rule c t1 t2)
  | eq_term_rule : forall c e1 e2 t,
      wf_ctx c ->
      eq_sort c t t ->
      eq_term c t e1 e1 ->
      eq_term c t e2 e2 ->
      wf_rule (term_eq_rule c e1 e2 t).

  
  Lemma invert_wf_sort_rule c args
    : wf_rule (sort_rule c args) <-> wf_ctx c /\ sublist args (map fst c).
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_wf_sort_rule : lang_core.

  Lemma invert_wf_term_rule c args t
    : wf_rule (term_rule c args t) <-> wf_ctx c /\ sublist args (map fst c) /\ eq_sort c t t.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_wf_term_rule : lang_core.

  Lemma invert_wf_sort_eq_rule c t1 t2
    : wf_rule (sort_eq_rule c t1 t2) <-> wf_ctx c /\ eq_sort c t1 t1 /\ eq_sort c t2 t2.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_wf_sort_eq_rule : lang_core.

  Lemma invert_wf_term_eq_rule c e1 e2 t
    : wf_rule (term_eq_rule c e1 e2 t)
      <-> wf_ctx c /\ eq_term c t e1 e1 /\ eq_term c t e2 e2 /\ eq_sort c t t.
  Proof. solve_invert_constr_eq_lemma. Qed.
  Hint Rewrite invert_wf_term_eq_rule : lang_core.



  Section __.
    Context (wsl : ws_lang l).

    Lemma wf_ctx_implies_ws c
      : wf_ctx c -> ws_ctx c.
    Proof.
      induction 1;
        basic_goal_prep;
        basic_core_crush.
      eapply eq_sort_implies_ws_l; eauto.
    Qed.
    Hint Resolve wf_ctx_implies_ws : lang_core.

    
    Lemma wf_rule_implies_ws r
      : wf_rule r -> ws_rule r.
    Proof.
      destruct 1;
        basic_goal_prep;
        autorewrite with utils term lang_core in *;
        intuition eauto with lang_core.
    Qed.

    
    Lemma ctx_admissible_in c n t
      : wf_ctx c ->
        ctx_cut_admissible c ->
        In (n, t) c ->
        sort_cut_admissible c t t.
    Proof using V_Eqb_ok wsl.
      induction 1;
        basic_goal_prep;
        basic_core_crush.
      {
        clear H3.
        unfold sort_cut_admissible in *;
          intros.
        safe_invert H2.
        safe_invert H3.
        erewrite !strengthen_subst;
          try typeclasses eauto;
          eauto.
        all: try erewrite eq_subst_map_fst_l by eassumption; eauto.
        all: try erewrite eq_subst_map_fst_r by eassumption; eauto.
        all: try (eapply eq_subst_fresh_l; now eauto).
        all: try (eapply eq_subst_fresh_r; now eauto).
        all: eapply eq_sort_implies_ws_r; eauto with lang_core.
      }
      {
        clear H4.      
        unfold sort_cut_admissible in *;
          intros.
        safe_invert H3.
        eapply in_ctx_wf in H2; eauto.
        erewrite !strengthen_subst;
          try typeclasses eauto;
          eauto.
        2,4:basic_core_crush.
        all: try erewrite eq_subst_map_fst_l by eassumption; eauto.
        all: try erewrite eq_subst_map_fst_r by eassumption; eauto.
        all: eauto with lang_core.
      }
    Qed.

    
    
    Lemma refl_term_lookup c0 c s1 s2 n t
      : eq_subst c0 c s1 s2 ->
        wf_ctx c ->
        In (n, t) c ->
        eq_term c0 t [/s2 /] (term_subst_lookup s1 n) (term_subst_lookup s2 n).
    Proof.
      induction 1;
        basic_goal_prep;
        autorewrite with utils term lang_core model in *;
        [tauto|].
      intuition subst.
      {
        rewrite strengthen_subst with (Substable0 := _);
          try typeclasses eauto.
        all: try erewrite eq_subst_map_fst_r by eassumption; eauto.
        all:basic_core_crush.        
      }
      {
        cbn.
        case_match; basic_goal_prep; autorewrite with utils term lang_core model in *;
          subst.
        {
          erewrite strengthen_subst;
            try typeclasses eauto;
            eauto;
            basic_core_crush.
        }
        {
          change ((named_list_lookup (var ?n) ?s ?n)) with (subst_lookup s n).
          erewrite strengthen_subst;
            try typeclasses eauto;
            eauto.
          all: try erewrite eq_subst_map_fst_r by eassumption; eauto.
          all: basic_core_crush.
        }
      }
    Qed.
    Hint Resolve refl_term_lookup : lang_core.

  End __.

  (*
  (*Note: proof of this depends on weakening*)
  Context (lang_admissible : all rule_cut_admissible (map snd l)).
   *)

End Terms.

Hint Resolve eq_sort_by eq_term_by eq_sort_cong eq_term_cong : lang_core.
Hint Constructors eq_subst eq_args : lang_core.

Hint Resolve eq_sort_implies_ws_l : lang_core.
Hint Resolve eq_sort_implies_ws_r : lang_core.
Hint Resolve eq_term_implies_ws_sort : lang_core. 
Hint Resolve eq_term_implies_ws_l : lang_core. 
Hint Resolve eq_term_implies_ws_r : lang_core.  
Hint Resolve eq_subst_implies_ws_l : lang_core.
Hint Resolve eq_subst_implies_ws_r : lang_core.
Hint Resolve eq_args_implies_ws_l : lang_core.
Hint Resolve eq_args_implies_ws_r : lang_core.
Hint Resolve wf_ctx_implies_ws : lang_core.
Hint Resolve wf_rule_implies_ws : lang_core.


Hint Resolve refl_term_lookup : lang_core.

Hint Constructors wf_ctx wf_rule : lang_core.

Hint Rewrite invert_wf_ctx_nil : lang_core.
Hint Rewrite invert_wf_ctx_cons : lang_core.

Hint Rewrite invert_wf_sort_rule : lang_core.
Hint Rewrite invert_wf_term_rule : lang_core.
Hint Rewrite invert_wf_sort_eq_rule : lang_core.
Hint Rewrite invert_wf_term_eq_rule : lang_core.


Section LangMono.
  Context (l l': lang).
  Context (Hincl : incl l l').

  Section __.
    Context (c : ctx).
    Local Lemma lang_mono 
      : (forall t1 t2,
            eq_sort l c t1 t2 ->
            eq_sort l' c t1 t2)
        /\ (forall t e1 e2,
               eq_term l c t e1 e2 ->
               eq_term l' c t e1 e2)
        /\ (forall c' s1 s2,
               eq_subst l c c' s1 s2 ->
               eq_subst l' c c' s1 s2)
        /\ (forall c' s1 s2,
               eq_args l c c' s1 s2 ->
               eq_args l' c c' s1 s2).
    Proof using Hincl c.
      eapply cut_ind;
        basic_goal_prep;
        try solve [constructor; eauto].
      { eapply eq_sort_by; eauto. }
      { eapply eq_sort_cong; eauto. }
      { eapply eq_sort_trans; eauto. }
      { eapply eq_term_by; eauto. }
      { eapply eq_term_cong; eauto. }
      { eapply eq_term_trans; eauto. }
      { eapply eq_term_conv; eauto. }
    Qed.

    Definition eq_sort_lang_mono := proj1 lang_mono.
    Definition eq_term_lang_mono := proj1 (proj2 lang_mono).
    Definition eq_subst_lang_mono := proj1 (proj2 (proj2 lang_mono)).
    Definition eq_args_lang_mono := proj2 (proj2 (proj2 lang_mono)).
    
  End __.

  Hint Resolve eq_sort_lang_mono : lang_core.
  Hint Resolve eq_term_lang_mono : lang_core.
  
  Lemma ctx_lang_mono c
    : wf_ctx l c -> wf_ctx l' c.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
  Qed.    
  
  Hint Resolve ctx_lang_mono : lang_core.
  
  Lemma rule_mono r : wf_rule l r -> wf_rule l' r.
  Proof.
    destruct 1;
      basic_goal_prep;
      basic_core_crush.
  Qed.  

End LangMono.





Inductive wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang []
| wf_lang_cons : forall l n r,
    fresh n (l) ->
    wf_lang l ->
    wf_rule (l) r ->
    wf_lang ((n,r)::l).


Lemma wf_lang_implies_ws l
  : wf_lang l -> ws_lang l.
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
Qed.
Hint Resolve wf_lang_implies_ws : lang_core.



Lemma rule_in_wf l name r
  : wf_lang l -> In (name, r) l -> wf_rule l r.
Proof.
  induction 1;
    basic_goal_prep;
    [tauto|].
  eapply rule_mono; cycle 1;
    basic_core_crush.
Qed.
Hint Resolve rule_in_wf : lang_core.

Local Ltac use_rule_in_wf :=
  lazymatch goal with
  | H:wf_lang ?l, Hin:In (_, _) ?l |- _ => pose proof (rule_in_wf _ _ _ H Hin)
  end.

Section WithLang.
  Context (l : lang)
    (wfl : wf_lang l).

  Local Notation wf_ctx c := (wf_ctx l c).
  Local Notation eq_sort c' t1' t2' := (eq_sort l c' t1' t2').
  Local Notation eq_term c' t e1 e2 := (eq_term l c' t e1 e2).
  Local Notation eq_subst c c' s1' s2' := (eq_subst l c c' s1' s2').
  Local Notation eq_args c c' s1' s2' := (eq_args l c c' s1' s2').
  
  Local Notation weak_sort_cut_admissible c' t1' t2' := (weak_sort_cut_admissible l c' t1' t2').
  Local Notation weak_term_cut_admissible c' t e1 e2 := (weak_term_cut_admissible l c' t e1 e2).
  Local Notation weak_subst_cut_admissible c c' s1' s2' := (weak_subst_cut_admissible l c c' s1' s2').
  Local Notation weak_args_cut_admissible c c' s1' s2' := (weak_args_cut_admissible l c c' s1' s2').

  Context (Hla : all (rule_cut_admissible l) (map snd l)).
  Context (c : ctx).
  Context (wfc : wf_ctx c).
  Context (Hca : ctx_cut_admissible l c).

  Lemma weak_cut_admissible
    : (forall t1' t2',
          eq_sort c t1' t2' ->
          weak_sort_cut_admissible c t1' t2'
             /\ weak_sort_cut_admissible c t1' t1'
             /\ weak_sort_cut_admissible c t2' t2')
      /\ (forall (t : Term.sort V) (e1 e2 : Term.term V),
             eq_term c t e1 e2 ->
             weak_term_cut_admissible c t e1 e2
             /\ weak_term_cut_admissible c t e1 e1
             /\ weak_term_cut_admissible c t e2 e2
             /\ weak_sort_cut_admissible c t t)
      /\ (forall (c' : Term.ctx V) (s1 s2 : Term.subst V),
            eq_subst c c' s1 s2 ->
            weak_subst_cut_admissible c c' s1 s2
            /\ weak_subst_cut_admissible c c' s1 s1
            /\ weak_subst_cut_admissible c c' s2 s2)
      /\ (forall c' (s1 s2 : list term),
            eq_args c c' s1 s2 ->
            weak_args_cut_admissible c c' s1 s2
            /\ weak_args_cut_admissible c c' s1 s1
            /\ weak_args_cut_admissible c c' s2 s2).
  Proof.
    simple eapply cut_ind.
    all: unfold weak_term_cut_admissible, weak_sort_cut_admissible, weak_subst_cut_admissible, weak_args_cut_admissible.
    all: basic_goal_prep.
    all: try use_rule_in_wf; autorewrite with lang_core utils in *.
    all: repeat split.
    all: basic_goal_prep.
    all: erewrite ?subst_assoc; try typeclasses eauto;[|shelve..].
    all: fold_Substable.
    all: try lazymatch goal with
    | H : In _ ?l, lang_admissible : all _ (map snd ?l) |- _ =>
        eapply in_all_named_list in lang_admissible; eauto;
        cbn in lang_admissible
    end.
    all: try now intuition eauto with lang_core.
    {
      eapply eq_sort_trans; intuition eauto using eq_sort_by, eq_subst_refl_right.
    }
    {
      eapply eq_sort_sym; intuition eauto using eq_subst_refl_right, eq_subst_sym'.
    }
    {
      eapply eq_term_conv;
        try now intuition eauto with lang_core.
      eapply Hla;  intuition eauto using eq_subst_refl_right.
    }
    {
      rewrite <- !Substable.with_names_from_args_subst.
      eapply eq_term_cong; eauto.
      eapply H1; intuition eauto.
    }
    {
      rewrite <- !Substable.with_names_from_args_subst.
      eapply eq_term_conv.
      {
        eapply eq_term_cong; eauto.
        eapply H2; intuition eauto.
      }
      {
        eapply Hla; eauto.
        eapply eq_args_implies_eq_subst.
        eapply H1; eauto.
        all: intuition eauto using eq_subst_refl_right with lang_core.
      }     
    }
    {
      rewrite <- !Substable.with_names_from_args_subst.
      eapply eq_term_conv.
      {
        eapply eq_term_cong; eauto.
        eapply H3; intuition eauto.
      }
      {
        eapply Hla; eauto.
        eapply eq_args_implies_eq_subst.
        eapply H3; intuition eauto.
        all: intuition eauto using eq_subst_refl_right with lang_core.
      }     
    }
    {
      eapply Hla.
      2:basic_core_crush.
      rewrite <- !Substable.with_names_from_args_subst.
      eapply eq_args_implies_eq_subst.
      eapply H3; intuition eauto.
    }
    {
      eapply ctx_admissible_in; eauto with lang_core.
    }
    {
      eapply eq_term_trans; intuition eauto using eq_sort_by, eq_subst_refl_right.
    }
    {
      eapply eq_term_sym.
      eapply eq_term_conv; eauto using eq_subst_sym'.
    }
    1-3:eapply eq_term_conv; now eauto using eq_subst_refl_right.
    all: constructor; eauto.
    all: eapply eq_term_conv; [basic_core_crush|].
    all: unfold sort_cut_admissible in *.
    1-3: erewrite subst_assoc; try typeclasses eauto; eauto;
    erewrite ?eq_subst_map_fst_r by eassumption;
    [|basic_core_crush].
    all: fold_Substable.
    all:eauto using eq_subst_sym', eq_subst_refl_right,eq_args_implies_eq_subst.
    2:{
      erewrite subst_assoc; try typeclasses eauto; eauto using eq_subst_refl_right.
      {
        fold_Substable.
        eapply H11; eauto.
        rewrite <- !Substable.with_names_from_args_subst.
        eapply eq_subst_sym'; eauto.
        eapply eq_args_implies_eq_subst.
        eauto using eq_subst_refl_right.
      }
      rewrite ?map_fst_with_names_from.
      1:basic_core_crush.
      erewrite eq_args_len_eq_r; eauto.
    }
    all: rewrite !Substable.with_names_from_args_subst.
    all: unfold apply_subst at 4.
    all: unfold substable_subst.      
    all: erewrite <- subst_assoc; try typeclasses eauto; eauto using eq_subst_refl_right.
    Unshelve.
    all: rewrite ?map_fst_with_names_from.
    all: erewrite ?eq_subst_map_fst_r by eassumption.
    all: erewrite ?eq_subst_map_fst_l by eassumption.
    all: eauto with lang_core.
    all: erewrite eq_args_len_eq_r; eauto.
  Qed.

  Lemma ctx_cut_admissible c
    : wf_ctx c ->
      ctx_cut_admissible c.
  Proof.
    induction 1;
      basic_goal_prep
      
      /\ (forall c c' (s1 s2 : list term),
            eq_args c c' s1 s2 ->
            weak_args_cut_admissible c c' s1 s2
            /\ weak_args_cut_admissible c c' s1 s1
            /\ weak_args_cut_admissible c c' s2 s2).



  Context (wfl : wf_lang l).
  
  Local Lemma cut_implies_core 
    : (forall c t1 t2,
          eq_sort c t1 t2 ->
          Core.eq_sort l c t1 t2)
      /\ (forall c t e1 e2,
             eq_term c t e1 e2 ->
             Core.eq_term l c t e1 e2)
      /\ (forall c c' s1 s2,
             eq_subst c c' s1 s2 ->
             Model.eq_subst (Model := core_model l) c c' s1 s2)
      /\ (forall c c' s1 s2,
             eq_args c c' s1 s2 ->
             Model.eq_args (Model := core_model l) c c' s1 s2).
  Proof using V_Eqb_ok wfl.
    simple eapply cut_ind;
      basic_goal_prep;
      basic_core_crush.
    all: eauto using
           sort_con_congruence,
        Core.eq_sort_trans, Core.eq_sort_sym,
        term_con_congruence,
        Core.eq_term_trans, Core.eq_term_sym.
  Qed.

  Definition eq_sort_cut_implies_core := proj1 cut_implies_core.
  Local Hint Resolve eq_sort_cut_implies_core : lang_core.
  
  Definition eq_term_cut_implies_core := proj1 (proj2 cut_implies_core).
  Local Hint Resolve eq_term_cut_implies_core : lang_core.

  Definition eq_subst_cut_implies_core := proj1 (proj2 (proj2 cut_implies_core)).
  Local Hint Resolve eq_subst_cut_implies_core : lang_core.
  
  Definition eq_args_cut_implies_core := proj2 (proj2 (proj2 cut_implies_core)).
  Local Hint Resolve eq_args_cut_implies_core : lang_core.
    
  Lemma core_implies_cut
    : (forall c t1 t2,
          Core.eq_sort l c t1 t2 ->
          eq_sort c t1 t2)
      /\ (forall c t e1 e2,
             Core.eq_term l c t e1 e2 ->
             eq_term c t e1 e2)
      /\ (forall c c' s1 s2,
             Model.eq_subst (Model:= core_model l) c c' s1 s2 ->
             eq_subst c c' s1 s2)
      /\ (forall c t,
             wf_sort l c t ->
             eq_sort c t t)
      /\ (forall c e t,
             wf_term l c e t ->
             eq_term c t e e)
      /\ (forall c s c',
             wf_args (Model:= core_model l) c s c' ->
             eq_args c c' s s)
      /\ (forall c,
             Model.wf_ctx (Model:= core_model l) c -> True).
  Proof using (* V_Eqb_ok wfl *).
    simple eapply judge_ind.
    all: basic_goal_prep.
    all: basic_core_crush.
    {
      erewrite <- sort_subst_id with (c:=c) (a:= t1) by typeclasses eauto.
      erewrite <- sort_subst_id with (c:=c) (a:= t2) by typeclasses eauto.
      fold_Substable.
      eapply eq_sort_by; eauto.
      eapply cut_id_subst_refl.
    }
    {
      TODO: c' is arbitrary; how to get cut-admissibility for it?.
      Question: can I tie the loop on admissibility w/o core_implies_cut via an alternate wf_ctx?
                    
                                                          
      eapply weak_cut_admissible; eauto.
      admit (*TODO: depends on cut admissibility*).
    }
    {
      admit (*TODO: depends on cut admissibility*).
    }
    {
      erewrite <- sort_subst_id with (c:=c) (a:= t) by typeclasses eauto.
      erewrite <- subst_id with (c:=c) (a:= e1) by typeclasses eauto.
      erewrite <- subst_id with (c:=c) (a:= e2) by typeclasses eauto.
      fold_Substable.
      eapply eq_term_by; eauto.
      eapply cut_id_subst_refl.
    }
  Qed.
  
  

(* TODO: assess benefits of retaining symmetry, transitivity
Hint Constructors eq_sort eq_term eq_subst eq_args
     wf_sort wf_term wf_subst wf_args wf_ctx
     wf_rule : lang_core.
 *)

Hint Constructors eq_subst eq_args
     wf_sort wf_term wf_subst wf_args wf_ctx
     wf_rule : lang_core.

Hint Resolve eq_sort_by : lang_core.
Hint Resolve eq_sort_subst : lang_core.
Hint Resolve eq_sort_refl : lang_core.
Hint Resolve eq_term_by : lang_core.
Hint Resolve eq_term_subst : lang_core.
Hint Resolve eq_term_refl : lang_core.
Hint Resolve eq_term_conv : lang_core.

#[local] Hint Mode wf_ctx - - - - ! : lang_core.
#[local] Hint Mode wf_ctx - - - - ! : model.

#[local] Hint Mode wf_args - - - - ! - - : model.
#[local] Hint Mode wf_args - - - - - ! - : model.
#[local] Hint Mode wf_args - - - - - - ! : model.
#[local] Hint Mode wf_args - - - - ! - - : lang_core.
#[local] Hint Mode wf_args - - - - - ! - : lang_core.
#[local] Hint Mode wf_args - - - - - - ! : lang_core.

#[local] Hint Mode eq_sort - - ! - : lang_core.
#[local] Hint Mode eq_sort - - - ! : lang_core.
#[local] Hint Mode eq_term - - - ! - : lang_core.
#[local] Hint Mode eq_term - - - - ! : lang_core.
#[local] Hint Mode wf_term - - ! - : lang_core.
#[local] Hint Mode wf_sort - - ! : lang_core.
  
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
      | eq_sort_subst e1 e0 w =>
          f0 w (wf_ctx_ind' wf_sort_ind' w) e0
             (eq_subst_ind' eq_term_ind' e0) e1 (eq_sort_ind' e1)
      | eq_sort_refl w => f1 w (wf_sort_ind' w)
      | eq_sort_trans e0 e1 => f2 e0 (eq_sort_ind' e0) e1 (eq_sort_ind' e1)
      | eq_sort_sym e0 => f3 e0 (eq_sort_ind' e0)
      end
    with eq_term_ind' (c : ctx) (s : sort) (t t0 : term) (e : eq_term l c s t t0) : P0 c s t t0 :=
           match e in (eq_term _ c0 s0 t1 t2) return (P0 c0 s0 t1 t2) with
           | eq_term_subst e3 e0 w =>
               f4 w (wf_ctx_ind' wf_sort_ind' w)
                  e0 (eq_subst_ind' eq_term_ind' e0) e3 (eq_term_ind' e3)
           | eq_term_by _ c0 name t1 e1 e2 i => f5 c0 name t1 e1 e2 i
           | eq_term_refl w => f6 w (wf_term_ind' w)
           | eq_term_trans e0 e3 =>
               f7 e0 (eq_term_ind' e0) e3 (eq_term_ind' e3)
           | eq_term_sym e0 => f8 e0 (eq_term_ind' e0)
           | eq_term_conv e3 e0 =>
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
           | wf_term_var _ c0 n t0 i => f15 c0 n t0 i
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
