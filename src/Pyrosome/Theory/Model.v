Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable.

Section WithVar.
  Context {V : Type}.

  Notation named_list := (named_list V).
  Notation named_map := (@named_map V).
  
  Notation Substable0 := (Substable0 V).
  Notation Substable := (Substable (V:=V)).

  Section WithModelArgs.
    Context {term sort : Type}.

    (* TODO: put this class in a separate module for better imports?
       TODO: separate into two classes, implement first in Term
             to avoid duplicating ctx?
     *)
    Class PreModel :=
      {
        term_substable :: Substable0 term;
        sort_substable :: Substable term sort;
      }.

    Local Notation ctx := (named_list sort).
    Local Notation subst := (named_list term).

    
      Class Model :=
        {
          premodel :: PreModel;
          eq_sort : ctx -> sort -> sort -> Prop;
          eq_term : ctx -> sort -> term -> term -> Prop;
          wf_sort : ctx -> sort -> Prop;
          wf_term : ctx -> term -> sort -> Prop;
        }.

      Section WithPreModel.
      Context {PreModel : PreModel}.

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
      End WithPreModel.

      Section WithModel.
        Context {Model : Model}.
      
      Inductive eq_subst (c : ctx) : ctx -> subst -> subst -> Prop :=
        eq_subst_nil : eq_subst c [] [] []
      | eq_subst_cons : forall (c' : ctx) (s1 s2 : subst),
          eq_subst c c' s1 s2 ->
          forall (name : V) (t : sort) (e1 e2 : term),
            eq_term c t [/s2 /] e1 e2 ->
            eq_subst c ((name, t) :: c') ((name, e1) :: s1) ((name, e2) :: s2).

      Inductive wf_args (c : ctx) : list term -> ctx -> Prop :=
      | wf_args_nil :  wf_args c [] []
      | wf_args_cons : forall s c' name e t,
          wf_term c e t[/with_names_from c' s/] ->
          (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
          wf_args c s c' ->
          wf_args c (e::s) ((name,t)::c').
      
      Inductive wf_ctx : ctx -> Prop :=
      | wf_ctx_nil : wf_ctx []
      | wf_ctx_cons : forall name c v,
          fresh name c ->
          wf_ctx c ->
          wf_sort c v ->
          wf_ctx ((name,v)::c).

      Inductive eq_args (c : ctx) : ctx -> list term -> list term -> Prop :=
      | eq_args_nil :  eq_args c [] [] []
      | eq_args_cons : forall c' es1 es2,
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
      
      Lemma wf_subst_from_wf_args c s c'
        : wf_args c s c' ->
          wf_subst c (with_names_from c' s) c'.
      Proof.
        induction 1; basic_goal_prep; constructor; eauto.
      Qed.

      (* TODO: put this class in a separate module for better imports? *)
      Class Model_ok :=
        {
          term_substable_ok :: Substable0_ok term;
          sort_substable_ok :: Substable_ok term sort;

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

       Context (Model_ok : Model_ok).
       
       (* The library version of this tactic is defined later, in Term.v*)
       Local Ltac fold_Substable :=
         try change (args_subst ?s ?e) with e[/s/];
         try change (subst_cmp ?s ?e) with e[/s/];
         try change (apply_subst0 ?s ?e) with e[/s/].

       
       Lemma eq_args_length_eq_l c c' s1 s2
         : eq_args c c' s1 s2 ->
           Datatypes.length c' = Datatypes.length s1.
       Proof.
         induction 1; basic_goal_prep; basic_utils_crush.
       Qed.
       #[local] Hint Resolve eq_args_length_eq_l : utils.

       Lemma eq_args_length_eq_r c c' s1 s2
         : eq_args c c' s1 s2 ->
           Datatypes.length c' = Datatypes.length s2.
       Proof.
         induction 1; basic_goal_prep; basic_utils_crush.
       Qed.
       #[local] Hint Resolve eq_args_length_eq_r : utils.

       Lemma eq_args_subst_monotonicity
         : forall c c' s1 s2,
           eq_args c c' s1 s2 ->
           wf_ctx c -> 
           wf_ctx c' -> 
           forall c'' s1' s2',
             eq_subst c'' c s1' s2' ->
             eq_args c'' c' s1[/s1'/] s2[/s2'/].
       Proof.
         induction 1;
           basic_goal_prep;
           constructor.
         {
           fold_Substable.
           safe_invert H2.
           basic_utils_crush.
         }
         {
           fold_Substable.
           safe_invert H2.
           rewrite with_names_from_args_subst.
           unfold apply_subst at 2; cbn.
           rewrite <- subst_assoc; eauto; try typeclasses eauto.
           2:{
             rewrite map_fst_with_names_from.
             1:eapply wf_sort_implies_ws; eauto.
             basic_utils_crush.
           }
           eapply eq_term_subst; cycle 1; eauto.
         }
       Qed.

       
       Lemma wf_subst_dom_eq c c' s
         : wf_subst c s c' ->
           map fst s = map fst c'.
       Proof.
         induction 1; basic_goal_prep; basic_utils_crush.
       Qed.
       #[local] Hint Resolve wf_subst_dom_eq : utils.
       
       Lemma wf_subst_subst_monotonicity
         : forall c c' s,
           wf_subst c s c' ->
           wf_ctx c -> 
           wf_ctx c' -> 
           forall c'' s',
             wf_subst c'' s' c ->
             wf_subst c'' s[/s'/] c'.
       Proof.
         induction 1;
           basic_goal_prep;
           constructor.
         {
           fold_Substable.
           safe_invert H2.
           basic_utils_crush.
         }
         {
           fold_Substable.
           safe_invert H2.
           unfold apply_subst at 3; cbn.
           rewrite <- subst_assoc; eauto; try typeclasses eauto.
           2:{
             erewrite wf_subst_dom_eq; eauto.
             eapply wf_sort_implies_ws; eauto.
           }
           eapply wf_term_subst_monotonicity; eauto.
         }
       Qed.

       
       Lemma eq_args_implies_eq_subst c c' s1 s2
         : eq_args c c' s1 s2 ->
           eq_subst c c' (with_names_from c' s1) (with_names_from c' s2).
       Proof.
         induction 1; basic_goal_prep; constructor; basic_utils_crush.
       Qed.

       
       Lemma eq_args_refl c s c'
         : wf_args c s c' ->
           eq_args c c' s s.
       Proof.
         induction 1;
           basic_goal_prep;
           constructor;
           basic_utils_crush.
         eapply eq_term_refl.
         eauto.
       Qed.

       Lemma eq_args_trans c c' s1 s12 s2
         : wf_ctx c' ->
           eq_args c c' s1 s12 ->
           eq_args c c' s12 s2 ->
           eq_args c c' s1 s2.
       Proof.
         intros Hctx H'; revert Hctx s2;
           induction H';
           inversion 2;
           subst;
           basic_goal_prep;
           constructor.
         {
           safe_invert Hctx.
           eauto.
         }
         {
           safe_invert Hctx.
           eapply eq_term_trans;
             eauto.
           eapply eq_term_conv; eauto.
           eapply eq_sort_subst; eauto.
           2:{
             eapply eq_sort_refl; eauto.
           }
           {
             eapply eq_args_implies_eq_subst.
             eauto.
           }
         }
       Qed.
       
       Lemma eq_args_sym c c' s1 s2
         : wf_ctx c' ->
           eq_args c c' s1 s2 ->
           eq_args c c' s2 s1.
       Proof.
         intros Hctx H'; revert Hctx;
           induction H';
           subst;
           basic_goal_prep;
           constructor.
         {
           safe_invert Hctx.
           eauto.
         }
         {
           safe_invert Hctx.
           eapply eq_term_sym;
           eapply eq_term_conv; eauto.
           eapply eq_sort_subst; eauto.
           2:{
             eapply eq_sort_refl; eauto.
           }
           {
             eapply eq_args_implies_eq_subst.
             eauto.
           }
         }
       Qed.

    End WithModel.

  End WithModelArgs.

End WithVar.

Arguments PreModel (V term sort)%type_scope.
Arguments Model {V term sort}%type_scope.
Arguments Model_ok {V term sort}%type_scope Model : rename.

Arguments ws_ctx {V term sort}%type_scope {PreModel} !c/.

Create HintDb model discriminated.

Lemma wf_ctx_all_fresh {V term sort} {Model : @Model V term sort} c
  : wf_ctx (Model:=Model) c -> all_fresh c.
Proof.
  induction 1; basic_goal_prep; basic_utils_crush.
Qed.
#[export] Hint Resolve wf_ctx_all_fresh : model.

Lemma invert_wf_ctx_nil V term sort (Model : @Model V term sort)
  : wf_ctx [] <-> True.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_ctx_nil using solve[typeclasses eauto] : model.

Lemma invert_wf_ctx_cons V term sort (Model : @Model V term sort) c n t
  : wf_ctx ((n,t)::c) <-> fresh n c /\ wf_ctx c /\ wf_sort c t.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_ctx_cons using solve[typeclasses eauto] : model.


Lemma invert_wf_subst_nil V term sort (Model : @Model V term sort) c c'
  : wf_subst c [] c' <-> c' = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_subst_nil using solve[typeclasses eauto] : model.

Lemma invert_wf_subst_ctx_nil V term sort (Model : @Model V term sort) c s
  : wf_subst c s [] <-> s = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_subst_ctx_nil using solve[typeclasses eauto] : model.

(*TODO: write a version that destructs c' w/ existentials? *)
Lemma invert_wf_subst_cons V term sort (Model : @Model V term sort) c s c' n n' e t
  : wf_subst c ((n,e)::s) ((n',t)::c') <-> n = n' /\ wf_subst c s c' /\ wf_term c e t [/s /].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_subst_cons using solve[typeclasses eauto] : model.


Lemma invert_wf_args_nil V term sort (Model : @Model V term sort) c c'
  : wf_args c [] c' <-> c' = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_args_nil using solve[typeclasses eauto] : model.

Lemma invert_wf_args_ctx_nil V term sort (Model : @Model V term sort) c s
  : wf_args c s [] <-> s = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_args_ctx_nil using solve[typeclasses eauto] : model.

(*TODO: write a version that destructs c' w/ existentials? *)
Lemma invert_wf_args_cons V term sort (Model : @Model V term sort) c s c' n e t
  : wf_args c (e::s) ((n,t)::c') <-> wf_args c s c' /\ wf_term c e t [/with_names_from c' s /].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_wf_args_cons using solve[typeclasses eauto] : model.



Lemma invert_eq_subst_nil_l V term sort (Model : @Model V term sort) c s c'
  : eq_subst c [] s c' <-> c' = [] /\ s = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_subst_nil_l using solve[typeclasses eauto] : model.

Lemma invert_eq_subst_nil_r V term sort (Model : @Model V term sort) c s c'
  : eq_subst c s [] c' <-> c' = [] /\ s = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_subst_nil_r using solve[typeclasses eauto] : model.

Lemma invert_eq_subst_ctx_nil V term sort (Model : @Model V term sort) c s1 s2
  : eq_subst c s1 s2 [] <-> s1 = [] /\ s2 = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_subst_ctx_nil using solve[typeclasses eauto] : model.

(*TODO: write a version that destructs c' w/ existentials? *)
Lemma invert_eq_subst_cons V term sort (Model : @Model V term sort) c s1 s2 c' n' n1 n2 e1 e2 t
  : eq_subst c ((n',t)::c') ((n1,e1)::s1) ((n2,e2)::s2)
    <-> n' = n1 /\ n1 = n2 /\ eq_subst c c' s1 s2 /\ eq_term c t [/s2 /] e1 e2.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_subst_cons using solve[typeclasses eauto] : model.


Lemma invert_eq_args_nil_l V term sort (Model : @Model V term sort) c s c'
  : eq_args c [] s c' <-> c' = [] /\ s = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_args_nil_l using solve[typeclasses eauto] : model.

Lemma invert_eq_args_nil_r V term sort (Model : @Model V term sort) c s c'
  : eq_args c s [] c' <-> c' = [] /\ s = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_args_nil_r using solve[typeclasses eauto] : model.

Lemma invert_eq_args_ctx_nil V term sort (Model : @Model V term sort) c s1 s2
  : eq_args c s1 s2 [] <-> s1 = [] /\ s2 = [].
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_args_ctx_nil using solve[typeclasses eauto] : model.

(*TODO: write a version that destructs c' w/ existentials? *)
Lemma invert_eq_args_cons V term sort (Model : @Model V term sort) c s1 s2 c' n e1 e2 t
  : eq_args c ((n,t)::c') (e1::s1) (e2::s2)
    <-> eq_args c c' s1 s2 /\ eq_term c t [/with_names_from c' s2 /] e1 e2.
Proof. prove_inversion_lemma. Qed.
#[export] Hint Rewrite invert_eq_args_cons using solve[typeclasses eauto] : model.


#[export] Hint Resolve wf_ctx_all_fresh : model.

#[export] Hint Resolve wf_subst_from_wf_args : model.
