
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core.

(* each element is the map for that constructor *)
Definition compiler := list ((* target closing *) subst -> (* target *) exp). 

Fixpoint compile (cmp : compiler) (close : subst) (e : exp) : exp :=
  match e with
  | var x => var_lookup close x
  | con n s => nth_level (fun _ => con 0 [::]) cmp n (map (compile cmp close) s)
  end.

(*TODO: necessary? 
 make inductive instead if so
Fixpoint wf_cmp_subst tgt_l tgt_s cmp src_c :=
  match tgt_s, src_c with
  | [::],[::] => True
  | e::s', t::c' =>
    wf_cmp_subst tgt_l s' cmp c'
    /\ wf_term tgt_l [::] e (compile cmp s' t)
  | _,_ => False
  end.

 Conjecture : wf_ctx src_l c -> 
           wf_cmp_subst l s cmp c <-> wf_subst l [::] s (map (compile cmp s) c))*)

(*
TODO: seems wrong; specializing c too much; seems artificial
Is it sufficient to talk about closed terms?

First we specify the properties in terms of compile,
then inductively on the compiler. TODO: prove equivalent
*)
Definition sort_wf_preserving_sem cmp l1 l2 :=
  forall s c t, wf_ctx l1 c ->
                wf_subst l2 [::] s (map (compile cmp s) c) ->
                wf_sort l1 c t ->
                wf_sort l2 [::] (compile cmp s t).

Definition term_wf_preserving_sem cmp l1 l2 :=
  forall s c e t, wf_ctx l1 c ->
                wf_subst l2 [::] s (map (compile cmp s) c) ->
                wf_term l1 c e t ->
                wf_term l2 [::] (compile cmp s e) (compile cmp s t).

(*TODO: this is a stronger property; includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : lang) : compiler -> lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [::] [::]
| preserving_compiler_sort : forall cmp l cf c,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    (forall s, wf_subst target [::] s (map (compile cmp s) c) ->
               wf_sort target [::] (cf s)) ->
    preserving_compiler target (cf::cmp) (sort_rule c :: l)
| preserving_compiler_term : forall cmp l cf c t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    (forall s, wf_subst target [::] s (map (compile cmp s) c) ->
               wf_term target [::] (cf s) (compile cmp s t)) ->
    preserving_compiler target (cf::cmp) (term_rule c t :: l)
| preserving_compiler_sort_le : forall cmp l c t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    (forall s, wf_subst target [::] s (map (compile cmp s) c) ->
               le_sort target [::] (compile cmp s t1) (compile cmp s t2)) ->
    (* TODO: when I build in proof terms, this function will be useful *)
    preserving_compiler target ((fun _=>con 0[::])::cmp) (sort_le c t1 t2 :: l)
| preserving_compiler_term_le : forall cmp l c e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    (forall s, wf_subst target [::] s (map (compile cmp s) c) ->
               le_term target [::]
                       (compile cmp s t)
                       (compile cmp s e1)
                       (compile cmp s e2)) ->
    (* TODO: when I build in proof terms, this function will be useful *)
    preserving_compiler target ((fun _=>con 0[::])::cmp) (term_le c e1 e2 t :: l).

Lemma wf_ctx_empty_sort c t : ~wf_sort [::] c t.
Proof.
  by inversion.
Qed.

Lemma preserving_preserves_term cmp ls lt
  : preserving_compiler lt cmp ls ->
    term_wf_preserving_sem cmp ls lt.
Proof.
  unfold term_wf_preserving_sem.
  intros until e; move: s; elim: e; simpl.
  { give_up. }
  intros.
  (*TODO*) Admitted.
       

(*
    
  Lemma compiler_var_lookup
    :  wf_subst lt [::] s (map (compile cmp s) c) ->
       wf_term lt [::] (var_lookup s n) (compile cmp s t)

Lemma preserving_preserves_sort cmp ls lt
  : preserving_compiler lt cmp ls ->
    sort_wf_preserving_sem cmp ls lt.
Proof.
  unfold sort_wf_preserving_sem.
  
  elim; simpl.
  {
    intros; exfalso.
    by inversion H1.
  }
  {
    
    

(* something like this would be for closed ctxs
   Before using this one, the signature of compile should change though *)
Definition sort_wf_preserving_closed cmp l1 l2 :=
  forall t, wf_sort l1 [::] t -> wf_sort l2 [::] (compile cmp [::] t).

Lemma compiler_cat_sort_preserving cmp1 cmp2 l1 l2 lt
  : sort_wf_preserving cmp1 l1 lt ->
    sort_wf_preserving cmp2 l2 lt ->
    sort_wf_preserving (cmp1 ++ cmp2) (l1 ++ l2) lt.
Proof.
  elim: cmp1 l1; intros until l1; case l1; simpl; first easy.
  1,2: intro_to sort_wf_preserving.

(* =======================*)
Definition compiler := (* target closing *) subst -> (* src *) exp -> (* target *) exp.

Fixpoint compile_ctx cmp s c : ctx :=
  match s, c with
  | [::],[::] => [::]
  | e::s', t::c' => ::(compile_ctx cmp s' c')
  | _,_ => (* unreachable with wf inputs; is this okay? *) [::]
  end.

Definition sort_wf_preserving cmp l1 l2 :=
  forall s c t, wf_subst l2 [::] s (compile_ctx cmp s c) ->
                wf_sort l1 c t ->
                wf_sort l2 [::] (cmp s t).
(*================*)

(*
  TODO!!!: too weak; can't do eg closure conversion if the type is a metavar
*)
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
  inversion H; subst.
  f_equal.      
  2:{
    suff: (size l0 = size c'); first move ->.
    eapply nth_level_trans_table.
    tauto.
    give_up.
  }
  TODO: subst. ver. of lemma
*)
