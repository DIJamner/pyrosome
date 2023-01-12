Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable.

Section WithVar.
  Context {V : Type}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  
  Notation Substable0 := (Substable0 V).
  Notation Substable := (Substable (V:=V)).

  Section WithModelArgs.
    Context {term sort : Type}.

    (* TODO: put this class in a separate module for better imports?
       TODO: separate into two classes, implement first in Term
             to avoid duplicating ctx?
     *)
    Class Model :=
      {
        ctx := named_list sort;
        subst := named_list term;
        term_substable :> Substable0 term;
        sort_substable :> Substable term sort;
        eq_sort : ctx -> sort -> sort -> Prop;
        eq_term : ctx -> sort -> term -> term -> Prop;
        wf_sort : ctx -> sort -> Prop;
        wf_term : ctx -> term -> sort -> Prop;
      }.

    Section WithModel.
      Context {Model : Model}.

      Fixpoint ws_ctx (c : ctx) : Prop :=
        match c with
        | [] => True
        | (n,t) :: c' => fresh n c' /\ well_scoped (map fst c') t /\ ws_ctx c'
        end.
      Arguments ws_ctx !c/.

      Lemma ws_all_fresh_ctx c
        : ws_ctx c -> all_fresh c.
      Proof using .
        induction c; basic_goal_prep; basic_utils_crush.
      Qed.
      
      Inductive eq_subst
        : ctx -> ctx -> subst -> subst -> Prop :=
        eq_subst_nil : forall c : ctx, eq_subst c [] [] []
      | eq_subst_cons : forall (c c' : ctx) (s1 s2 : subst),
          eq_subst c c' s1 s2 ->
          forall (name : V) (t : sort) (e1 e2 : term),
            eq_term c t [/s2 /] e1 e2 ->
            eq_subst c ((name, t) :: c') ((name, e1) :: s1) ((name, e2) :: s2).

      Inductive wf_args : ctx -> list term -> ctx -> Prop :=
      | wf_args_nil : forall c, wf_args c [] []
      | wf_args_cons : forall c s c' name e t,
          wf_term c e t[/with_names_from c' s/] ->
          (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
          wf_args c s c' ->
          wf_args c (e::s) ((name,t)::c').
      
      Inductive  wf_ctx : ctx -> Prop :=
      | wf_ctx_nil : wf_ctx []
      | wf_ctx_cons : forall name c v,
          fresh name c ->
          wf_ctx c ->
          wf_sort c v ->
          wf_ctx ((name,v)::c).

      Inductive eq_args : ctx -> ctx -> list term -> list term -> Prop :=
      | eq_args_nil : forall c, eq_args c [] [] []
      | eq_args_cons : forall c c' es1 es2,
          eq_args c c' es1 es2 ->
          forall name t e1 e2,
            (* assumed because the output ctx is wf: fresh name c' ->*)
            eq_term c t[/with_names_from c' es2/] e1 e2 ->
            eq_args c ((name, t)::c') (e1::es1) (e2::es2).
      
      Inductive wf_subst c : subst -> ctx -> Prop :=
      | wf_subst_nil : wf_subst c [] []
      | wf_subst_cons : forall s c' name e t,
          (* assumed because the output ctx is wf: fresh name c' ->*)
          wf_subst c s c' ->
          wf_term c e t[/s/] ->
          wf_subst c ((name,e)::s) ((name,t)::c').

      (* TODO: put this class in a separate module for better imports? *)
      Class Model_ok :=
        {
          term_substable_ok :> Substable0_ok term;
          sort_substable_ok :> Substable_ok term sort;

          (* Syntactic constructors *)
          eq_sort_subst : forall c s1 s2 c' t1' t2',
            (* Need to assert wf_ctx c here to satisfy
               assumptions' presuppositions
             *)
            wf_ctx c' ->
            eq_subst c c' s1 s2 ->
            eq_sort c' t1' t2' ->
            eq_sort c t1'[/s1/] t2'[/s2/];
          eq_sort_refl : forall c t,
            wf_sort c t ->
            eq_sort c t t;
          eq_sort_trans : forall c t1 t12 t2,
            eq_sort c t1 t12 ->
            eq_sort c t12 t2 ->
            eq_sort c t1 t2;
          eq_sort_sym : forall c t1 t2, eq_sort c t1 t2 -> eq_sort c t2 t1;
          
          eq_term_subst : forall c s1 s2 c' t e1 e2,
            (* Need to assert wf_ctx c' here to satisfy
               assumptions' presuppositions
             *)
            wf_ctx c' ->
            eq_subst c c' s1 s2 ->
            eq_term c' t e1 e2 ->
            eq_term c t[/s2/] e1[/s1/] e2[/s2/];
          eq_term_refl : forall c e t,
            wf_term c e t ->
            eq_term c t e e;
          eq_term_trans : forall c t e1 e12 e2,
            eq_term c t e1 e12 ->
            eq_term c t e12 e2 ->
            eq_term c t e1 e2;
          eq_term_sym : forall c t e1 e2, eq_term c t e1 e2 -> eq_term c t e2 e1;
          (* Conversion:
             c |- e1 = e2 : t 
                            ||
             c |- e1 = e2 : t'
           *)
          eq_term_conv : forall c t t',
            eq_sort c t t' ->
            forall e1 e2,
              eq_term c t e1 e2 ->
              eq_term c t' e1 e2;
          
          wf_term_conv : forall c e t t',
            wf_term c e t ->
            eq_sort c t t' ->
            wf_term c e t';
          wf_term_var : forall c n t,
            In (n, t) c ->
            wf_term c (inj_var n) t;

          (* Syntactic Lemmas *)
          wf_sort_subst_monotonicity
          : forall (c : ctx) (t : sort),
              wf_sort c t ->
              wf_ctx c ->
              forall (c'' : ctx) (s : subst), wf_subst c'' s c -> wf_sort c'' t [/s /];
          wf_term_subst_monotonicity
          : forall (c : ctx) (e : term) (t : sort),
            wf_term c e t ->
            wf_ctx c ->
            forall (c'' : ctx) (s : subst),
              wf_subst c'' s c -> wf_term c'' e [/s /] t [/s /];
          wf_sort_implies_ws
          : forall c t, wf_sort c t -> well_scoped (map fst c) t;
          wf_term_implies_ws
          : forall c e t, wf_term c e t -> well_scoped (map fst c) e;
        }.

    End WithModel.

  End WithModelArgs.

End WithVar.

Arguments Model (V term sort)%type_scope.
Arguments Model_ok {V term sort}%type_scope Model : rename.

Arguments ws_ctx {V term sort}%type_scope {Model} !c/.

(*TODO: separate hints from core? *)
Create HintDb model discriminated.

Lemma wf_ctx_all_fresh {V term sort} {Model : @Model V term sort} c
  : wf_ctx (Model:=Model) c -> all_fresh c.
Proof.
  induction 1; basic_goal_prep; basic_utils_crush.
Qed.
#[export] Hint Extern 1 (all_fresh _) => simple eapply wf_ctx_all_fresh : model.

Lemma invert_wf_ctx_nil {V term sort} {Model : @Model V term sort}
  : wf_ctx (Model:=Model) [] <-> True.
Proof. solve_invert_constr_eq_lemma. Qed.
#[export] Hint Rewrite @invert_wf_ctx_nil : model.

Lemma invert_wf_ctx_cons {V term sort} {Model : @Model V term sort} c n t
  : wf_ctx (Model:=Model) ((n,t)::c) <-> fresh n c /\ wf_ctx c /\ wf_sort c t.
Proof. solve_invert_constr_eq_lemma. Qed.
#[export] Hint Rewrite @invert_wf_ctx_cons : lang_core.
