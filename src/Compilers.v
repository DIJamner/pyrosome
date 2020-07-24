
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core.


Definition optimizer := exp -> exp.
Definition translation := list exp.

Variant pass :=
| opt_pass : optimizer -> pass
| trans_pass : translation -> pass.

Definition compiler := list pass.

Fixpoint translate (t : translation) (e : exp) : exp :=
  match e with
  | var x => var x
  | con n s => (nth_level (con 0 [::]) t n)[/ map (translate t) s/]
  end.

Definition run_pass (p : pass) : exp -> exp :=
  match p with
  | opt_pass o => o
  | trans_pass t => translate t
  end.

Definition compile : compiler -> exp -> exp :=
  foldr (fun p => Basics.compose (run_pass p)) id.

Fixpoint compiler_translation (c: compiler) : list translation :=
  match c with
  | [::] => [::]
  | (opt_pass _)::c' => compiler_translation c'
  | (trans_pass p)::c' => p::compiler_translation c'
  end.

(*todo: can also precompute start-to-end translation table*)
Definition translate_n : list translation -> exp -> exp :=
  foldr (fun p => Basics.compose (translate p)) id.

(* Properties *)
Definition optimizer_refines (o : optimizer) l
  := forall c,
    (forall t1 t2, le_sort l c t1 t2 -> le_sort l c t1 (o t2))
    /\ (forall e1 e2 t, le_term l c e1 e2 t -> le_term l c e1 (o e2) (o t)).

(* A simpler statement, but not quite the right property:
Definition optimizer_refines (o : optimizer) l
  := forall c,
    (forall t, wf_sort l c t -> le_sort l c t (o t))
     /\ (forall e t, wf_term l c e t -> le_term l c e (o e) (o t)). 
TODO: I might be able to use something closer to this if I prove o
respects substitution/behaves like syntax.
idea: define a notion of fns that agree with a syntactic object, like:
add [:: e] |- so as a constructor, prove that (so e) > (o e)
and (o e) is universal in that, ie if (so e) > e' then exists (unique) e'' where e' > e''
and (o e) > e''
*)

Definition translation_preserves (t : translation) l1 l2
  := forall c,
    (forall t1 t2, le_sort l1 c t1 t2 ->
                    le_sort l2 (map (translate t) c) (translate t t1) (translate t t2))
     /\ (forall e1 e2 t', le_term l1 c e1 e2 t' ->
                          le_term l2 (map (translate t) c)
                                  (translate t e1) (translate t e2) (translate t t')).

Definition compiler_refines (cmp : compiler) l1 l2
  := forall c, (forall t1 t2, le_sort l1 c t1 t2 ->
                    le_sort l2 (map (translate_n (compiler_translation cmp)) c)
                            (translate_n (compiler_translation cmp) t1)
                            (compile cmp t2))
     /\ (forall e1 e2 t', le_term l1 c e1 e2 t' ->
                          le_term l2 (map (translate_n (compiler_translation cmp)) c)
                            (translate_n (compiler_translation cmp) e1)
                            (compile cmp e2) (compile cmp t')).

Inductive compiler_refines' : compiler -> lang -> lang -> Prop :=
| cref_nil : forall l, compiler_refines' [::] l l
| cref_trans : forall t c' l1 l2 l3,
    compiler_refines' c' l1 l2 ->
    translation_preserves t l2 l3 ->
    compiler_refines' (trans_pass t::c') l1 l3
| cref_opt : forall o c' l1 l2,
    compiler_refines' c' l1 l2 ->
    optimizer_refines o l2 ->
    compiler_refines' (opt_pass o::c') l1 l2.

Lemma compiler_empty_id : compile [::] = id.
Proof using .
  by compute.
Qed.
 
Lemma map_compose {A B C : Type} (f : B -> C) (g : A -> B) l
  : map (Basics.compose f g) l = map f (map g l).
Proof using .
  elim: l; simpl; eauto.
  move => a l ->; eauto.
Qed.

Lemma compiler_refines_translation t c' l1 l2 l3
  : compiler_refines c' l1 l2 ->
    translation_preserves t l2 l3 ->
    compiler_refines (trans_pass t::c') l1 l3.
Proof using .
  unfold compiler_refines; unfold translation_preserves; unfold optimizer_refines.
    intros.
    specialize H with c.
    destruct H.
    simpl.
    rewrite map_compose.
    unfold Basics.compose.
    specialize H0 with (map (translate_n (compiler_translation c')) c).
    destruct H0.
    split; intros; eauto.
Qed.

Lemma compiler_refines_optimization o c' l1 l2
  : compiler_refines c' l1 l2 ->
    optimizer_refines o l2 ->
    compiler_refines (opt_pass o::c') l1 l2.
Proof using .
  unfold compiler_refines; unfold translation_preserves; unfold optimizer_refines.
  intros.
  specialize H with c.
  destruct H.
  simpl.
  unfold Basics.compose.
  specialize H0 with (map (translate_n (compiler_translation c')) c).
  destruct H0.
  split; intros; eauto with judgment.
Qed.
  
Lemma compiler_refines_by_pass c l1 l2
  : compiler_refines' c l1 l2 -> compiler_refines c l1 l2.
Proof using .
  elim; eauto using compiler_refines_optimization,
        compiler_refines_translation
          with judgment.
  unfold compiler_refines;
    intros; split; intros; rewrite !compiler_empty_id !map_id; done.
Qed.  

(* TODO: is the ' ver useful?
   Interesting note: it is not clear how to extend optimizers;
   easiest way is to apply it iff a program fragment is in the core lang
   otherwise, not clear what they should do.
   TODO: come up with a more restrictive type that strikes the right balance?
 *)

Definition subst_respecting t :=
  forall e s, t e[/s/] = (t e)[/map t s/].

Definition var_respecting t :=
  forall x, t (var x) = var x.

Fixpoint trans_fn_to_table (t : exp -> exp) (src : lang) : translation :=
  match src with
  | [::] => [::]
  | (sort_rule c)::src'
  | (term_rule c _)::src' =>
    t (con (size src') (id_subst (size c)))::(trans_fn_to_table t src')
  | _::src' => (con 0 [::])::(trans_fn_to_table t src')
  end.


Lemma id_subst_cmp : forall (s : subst),  subst_cmp (id_subst (size s)) s = s.
Admitted.


Lemma trans_fn_to_table_size t l : size (trans_fn_to_table t l) = size l.
Admitted.

Lemma nth_level_trans_table t l n c t'
  : (is_nth_level l n (sort_rule c) \/ (is_nth_level l n (term_rule c t'))) ->
    nth_level [0 | ] (trans_fn_to_table t l) n
    = t (con n (id_subst (size c))).
Proof.
  case.
  all: unfold is_nth_level; unfold nth_level.
  all: move /andP => [nlt].
  all: rewrite !trans_fn_to_table_size.
  all: rewrite !nlt.
  all: suff: n = size l - (size l - n.+1).+1.
  1,3:remember (size l - n.+1) as m.
  1,2: rewrite -!Heqm.
  1,2: move ->.
Admitted.
  
  

(*Seems true, but have technical mechanics to work out*)
Lemma trans_fn_representation_term t l c e t'
  : subst_respecting t ->
    var_respecting t ->
    wf_term l c e t' -> translate (trans_fn_to_table t l) e = t e.
Proof.
  unfold subst_respecting; intro srt.
  unfold var_respecting; intro vrt.
  elim: e t'; simpl; eauto.
  intros.
  rewrite -{2}(id_subst_cmp l0).
  rewrite -con_subst_cmp.
  rewrite srt.
  f_equal.
  {
    elim: l0 H0 H; simpl; eauto with judgment.
    intros.
    destruct H1.
    f_equal; eauto with judgment.
    apply: H1.
    (*2:{
      apply: map_ext'.(*TODO: need map_ext' for props?*)
             eapply H1.*)
    give_up.
    give_up.
  }
  {
    eapply nth_level_trans_table.
    give_up.
  }
  Unshelve.
  all: auto.
Admitted.
    
Lemma trans_fn_representation_sort t l c t'
  : subst_respecting t ->
    var_respecting t ->
    wf_sort l c t' -> translate (trans_fn_to_table t l) t' = t t'.
Proof.
  unfold subst_respecting; intro srt.
  unfold var_respecting; intro vrt.
  case: t'; simpl; eauto.
  intros.
  rewrite -{2}(id_subst_cmp l0).
  rewrite -con_subst_cmp.
  rewrite srt.
  f_equal.      
  2:{
    inversion H; subst.
    suff: (size l0 = size c'); first move ->.
    eapply nth_level_trans_table.
    tauto.
    give_up.
  }
   
