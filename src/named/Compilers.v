Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core.
Import Exp.Notations.


(* each element is the image for that constructor or axiom*)
Variant compiler_case :=
 | term_case (args : list string) (e:exp)
 | sort_case (args : list string) (t:sort).
Definition compiler := named_list compiler_case. 

Section CompileFn.
  Context (tgt : lang)
          (cmp : compiler)
          (src : lang).

  (* does not use src or tgt, only cmp *)
  Fixpoint compile (e : exp) : exp :=
    match e with
    | var x => var x
    | con n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := con "ERR" [] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (term_case args e) => e[/combine args arg_terms/]
      | _ => default
      end
    end.
  
  (* does not use src or tgt, only cmp *)
  Definition compile_sort (t : sort) : sort :=
    match t with
    | scon n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := scon "ERR" [] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (sort_case args t) => t[/combine args arg_terms/]
      | _ => default
      end
    end.  
  
  Definition compile_args := map compile.

  Definition compile_subst (s : named_list exp) := named_map compile s.

  Definition compile_ctx (c:named_list sort) := named_map compile_sort c.

   (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
   *)
  Definition sort_wf_preserving_sem :=
    forall c t, wf_sort src c t ->
                wf_sort tgt (compile_ctx c) (compile_sort t).

  Definition term_wf_preserving_sem :=
    forall c e t,
      wf_term src c e t ->
      wf_term tgt (compile_ctx c) (compile e) (compile_sort t).

  Definition sort_eq_preserving_sem :=
    forall c t1 t2,
      eq_sort src c t1 t2 ->
      eq_sort tgt (compile_ctx c) (compile_sort t1) (compile_sort t2).
  
  Definition term_eq_preserving_sem :=
    forall c t e1 e2,
      eq_term src c t e1 e2 ->
      eq_term tgt (compile_ctx c) (compile_sort t) (compile e1) (compile e2).

  Definition args_wf_preserving_sem :=
    forall c s c',
      wf_args src c s c' ->
      wf_args tgt (compile_ctx c) (compile_args s) (compile_ctx c').

  Definition subst_eq_preserving_sem :=
    forall c c' s1 s2,
      eq_subst src c c' s1 s2 ->
      eq_subst tgt (compile_ctx c) (compile_ctx c') (compile_subst s1) (compile_subst s2).
   
  Definition ctx_wf_preserving_sem :=
    forall c, wf_ctx src c -> wf_ctx tgt (compile_ctx c).

  (*Set up to match the combined scheme for the judgment inductives *)
  Definition semantics_preserving :=
    sort_eq_preserving_sem /\ term_eq_preserving_sem /\ subst_eq_preserving_sem
    /\ sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
    /\ ctx_wf_preserving_sem.

End CompileFn.

(*
First we define an inductively provable (and in fact decidable) property 
of elaborated compilers.
*)

(*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : lang) : compiler -> lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [] []
| preserving_compiler_sort : forall cmp l n c args t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    wf_sort target (compile_ctx cmp c) t ->
    preserving_compiler target ((n,sort_case (map fst c) t)::cmp) ((n,sort_rule c args) :: l)
| preserving_compiler_term : forall cmp l n c args e t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    wf_term target (compile_ctx cmp c) e (compile_sort cmp t) ->
    preserving_compiler target ((n, term_case (map fst c) e)::cmp) ((n,term_rule c args t) :: l)
| preserving_compiler_sort_eq : forall cmp l n c t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    eq_sort target (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2) ->
    preserving_compiler target cmp ((n,sort_eq_rule c t1 t2) :: l)
| preserving_compiler_term_eq : forall cmp l n c e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    eq_term target (compile_ctx cmp c) (compile_sort cmp t) (compile cmp e1) (compile cmp e2) ->
    preserving_compiler target cmp ((n,term_eq_rule c e1 e2 t) :: l).


Lemma fresh_compile_ctx x cmp c
  : fresh x c -> fresh x (compile_ctx cmp c).
Proof.
  induction c; basic_goal_prep;
    pre_rewrite_core_crush.
Qed.
Hint Resolve fresh_compile_ctx : lang_core.


Lemma all_fresh_compile_ctx cmp c
  : all_fresh c -> all_fresh (compile_ctx cmp c).
Proof.
  induction c; basic_goal_prep;
    pre_rewrite_core_crush.
Qed.
Hint Resolve all_fresh_compile_ctx : pfcore.


Lemma compile_strengthen_term src tgt cmp c e t n cc
  : wf_term src c e t ->
    preserving_compiler tgt cmp src ->
    fresh n cmp ->
    compile ((n,cc)::cmp) e = compile cmp e.
Admitted.

Lemma compile_strengthen_sort src tgt cmp c t n cc
  : wf_sort src c t ->
    preserving_compiler tgt cmp src ->
    fresh n cmp ->
    compile_sort ((n,cc)::cmp) t = compile_sort cmp t.
Admitted.

Lemma compile_strengthen_ctx src tgt cmp c n cc
  : wf_ctx src c ->
    preserving_compiler tgt cmp src ->
    fresh n cmp ->
    compile_ctx ((n,cc)::cmp) c = compile_ctx cmp c.
Admitted.


Lemma fresh_lang_fresh_cmp lt cmp l n
  : preserving_compiler lt cmp l ->
    fresh n l -> fresh n cmp.
Proof.
  induction 1; basic_goal_prep;
    pre_rewrite_core_crush.
Qed.
Hint Resolve fresh_lang_fresh_cmp : lang_core.

Ltac rewrite_strengthen :=
  match goal with
  | [H : wf_ctx _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_ctx _ H pr); eauto with pfcore
  | [H : wf_sort _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_sort _ H pr); eauto with pfcore
  | [H : wf_term _ _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_term _ H pr); eauto with pfcore
  end.

(* TODO: work on
Ltac inductive_implies_semantic_rule :=
intros wfl pr wfl';
  revert wfl'; induction pr; simpl; [easy|..];
    repeat (simpl; autorewrite with bool_utils pfcore utils);
    intuition; subst;
      try match goal with
          | [wfl : wf_lang ?l, H: is_true((_,_) \in ?l)|-_] =>
            let H':= fresh in pose proof (rule_in_wf wfl H) as H'; safe_invert H'
          end;
      repeat rewrite_strengthen; [];
  cbn [compile_pf]; 
    repeat (simpl; autorewrite with bool_utils pfcore utils);
  assumption.
*)
  

Lemma inductive_implies_semantic_sort_axiom ls lt cmp name c t1 t2
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, sort_eq_rule c t1 t2) ls ->
    eq_sort lt (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2).
Proof.
  induction 2; basic_goal_prep; 
    pre_rewrite_core_crush.
  
Qed.


Lemma inductive_implies_semantic_term_axiom ls lt cmp name c e1 e2 t
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, wf_term_eq c e1 e2 t) \in ls ->
    eq_term lt (compile_ctx cmp c) (compile_pf cmp (ax name))
            (compile cmp t) (compile cmp e1) (compile cmp e2).
Proof.
  inductive_implies_semantic_rule.
Qed.


(*TODO: move to utils*)
Lemma with_names_from_map_is_named_map (A B C:Set) (f : A -> B) (l1 : named_list C) l2
  : with_names_from l1 (map f l2) = named_map f (with_names_from l1 l2).
Proof.
  revert l2; induction l1;
    destruct l2; break; subst; simpl; f_equal; eauto.
Qed.
(* TODO: do I want to rewrite like this?
  Hint Rewrite with_names_from_map_is_named_map : utils.*)


Lemma with_names_from_compile_ctx (A:Set) cmp c (s : list A)
  : with_names_from (compile_ctx cmp c) s
    = with_names_from c s.
Proof.
  revert s; induction c;
    destruct s; break; pfcore_crush.
  f_equal; pfcore_crush.
Qed.
  
Lemma wf_subst_from_wf_args l c s c'
  : wf_args l c s c' ->
    wf_subst l c (with_names_from c' s) c'.
Proof.
  induction 1; pfcore_crush.
Qed.
Hint Resolve wf_subst_from_wf_args : pfcore.
    
Definition id_args {A} (c : named_list A) : list wfexp :=
  map wf_var (map fst c).


Lemma compile_id_args A cmp (c : named_list A)
  : map (compile cmp) (id_args c) = id_args c.
Proof.
  unfold id_args.
  induction c; break; simpl; f_equal; pfcore_crush.
Qed.
Hint Rewrite compile_id_args : pfcore.

Lemma fst_equal_id_args_equal A B (c1 : named_list A) (c2 : named_list B)
  : map fst c1 = map fst c2 -> id_args c1 = id_args c2.
Proof.
  unfold id_args; move => ->; reflexivity.
Qed.

Lemma compile_ctx_fst_equal cmp c
  : map fst (compile_ctx cmp c) = map fst c.
Proof.
  induction c; break; simpl; f_equal; auto.
Qed.

Lemma id_args_wf l c
  : wf_args l c (id_args c) c.
Proof.
Admitted.
Hint Resolve id_args_wf : pfcore.


Lemma zip_map_fst_is_with_names_from (A B : Set) (c : named_list A) (s : list B)
  : zip (map fst c) s = with_names_from c s.
Proof.
  revert s; induction c; destruct s; break; cbn; pfcore_crush.
Qed.
Hint Rewrite zip_map_fst_is_with_names_from : utils.

Lemma inductive_implies_semantic_sort_rule_id ls lt cmp name c args
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, Pf.wf_sort_rule c args) \in ls ->
    wf_sort lt (compile_ctx cmp c) (compile cmp (wf_con name (id_args c))).
Proof.
  intros wfl pr wfl';
    revert wfl'; induction pr; simpl; [easy|..].
  all: pfcore_crush.
  {
    safe_invert H0; pfcore_crush.      
    cbn; pfcore_crush.
    eapply wf_sort_subst_monotonicity; pfcore_crush.
    erewrite with_names_from_names_eq.
    apply wf_subst_from_wf_args.
    repeat rewrite_strengthen.
    erewrite fst_equal_id_args_equal; pfcore_crush.
    by rewrite compile_ctx_fst_equal.
    by rewrite compile_ctx_fst_equal.
  }
  {
    cbn.
    my_case Hn (name =? n)%string; pfcore_crush.
    {
      (*TODO: automate in boolutils *)
      move: Hn => /eqP Hn; subst.
      exfalso.
      (*TODO: add modified lemma as hint*)
      pose proof (fresh_neq_in H4 H0).
      pfcore_crush.
    }
    case_match; pfcore_crush.
      
    eauto with pfcore.
    case_match.
    simpl in *.
  
  all: try solve [assert (wf_sort l c (wf_con name (id_args c))) by pfcore_crush;
                  repeat rewrite_strengthen].
  inversion H5.
  inversion H5.
  inversion H6.
Qed.

Lemma wf_con_id_args_subst (A:Set) name (c' : named_list A) s
  : size c' = size s -> (wfexp_subst (with_names_from c' s) (wf_con name (id_args c'))) = (wf_con name s).
Proof.
  intros ?.
  simpl; f_equal.
  unfold id_args.
Admitted.

Lemma compile_named_list_lookup ls cmp s n
  : compile ls cmp (named_list_lookup (wf_var n) s n)
  = named_list_lookup (wf_var n) (compile_subst ls cmp s) n.
Proof.
  induction s; break; 
    repeat (simpl; autorewrite with bool_utils pfcore utils); eauto with pfcore.
  case_match; 
    repeat (simpl; autorewrite with bool_utils pfcore utils); eauto with pfcore.
Qed.

Lemma compile_wfexp_subst ls cmp s e
  : (compile ls cmp (wfexp_subst s e))
    = wfexp_subst (compile_subst ls cmp s) (compile ls cmp e).
Proof.
  induction e; cbn.
  {
    apply compile_named_list_lookup.
  }
Admitted.
Hint Rewrite compile_wfexp_subst : pfcore.

Lemma compile_subst_with_names_from (A:Set) ls cmp (c':named_list A) s
  : (compile_subst ls cmp (with_names_from c' s)) = with_names_from c' (map (compile ls cmp) s).
Proof.
  unfold compile_subst.
  rewrite <- with_names_from_map_is_named_map.
  reflexivity.
Qed.

Lemma id_subst_id (A:Set) (c' : named_list A) e
  : wfexp_subst (with_names_from c' (id_args c')) e = e.
Proof.
Admitted.

Lemma id_subst_id_args (A:Set) (c' : named_list A) s
  : map (wfexp_subst (with_names_from c' (id_args c'))) s = s.
Proof.
  induction s; simpl; pfcore_crush; rewrite id_subst_id; pfcore_crush.
Qed.


Lemma compile_wfcon_sort ls cmp c' args s name t
  : all_fresh ls ->
    all_fresh cmp ->
    (name, Pf.wf_sort_rule c' args) \in ls ->
    (name, con_case t) \in cmp ->
    (compile ls cmp (wf_con name s)) = wfexp_subst (with_names_from c' (compile_args ls cmp s)) t.
Proof.
  intros.
  cbn.
  case_match.
  
  
Lemma inductive_implies_semantic_sort_rule ls lt cmp name c c' args s
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, Pf.wf_sort_rule c' args) \in ls ->
    (*wf_args ls c s c' ->*)
    wf_args lt (compile_ctx ls cmp c) (compile_args ls cmp s) (compile_ctx ls cmp c') ->
    wf_sort lt (compile_ctx ls cmp c) (compile ls cmp (wf_con name s)).
Proof.
  intros.
  replace (wf_con name s) with (wfexp_subst (with_names_from c' s) (wf_con name (id_args c'))).
  erewrite <- wf_con_id_args_subst.
  rewrite compile_wfexp_subst.
  eapply wf_sort_subst_monotonicity; pfcore_crush.
  {
    erewrite id_subst_id_args.
               cbn; pfcore_crush.
    pfcore_crush.
  2:{
    rewrite compile_subst_with_names_from.
    erewrite with_names_from_names_eq.
    eapply wf_subst_from_wf_args; pfcore_crush.
    unfold compile_ctx; rewrite named_map_fst_eq.
    reflexivity.
  }
  
.
    
  TODO: need the right rewrites
  eapply inductive_implies_semantic_sort_rule_id
  
  
  intros wfl pr wfl';
    revert wfl'; induction pr; simpl; [easy|..].
  all: pfcore_crush.
  {    
    safe_invert H0; pfcore_crush.      
    cbn; pfcore_crush.
    erewrite <- with_names_from_compile_ctx.
    eapply wf_sort_subst_monotonicity; pfcore_crush.
    apply wf_subst_from_wf_args.
    replace (compile_ctx l cmp c0)
      with (compile_ctx ((n, Pf.wf_sort_rule c0 args0) :: l) ((n, con_case t) :: cmp) c0);
      auto.
    erewrite compile_strengthen_ctx; pfcore_crush.
  }
  {
    (*Note: name != n*)
    TODO: issue is that substitution s can use n
                                                  
                                                    
    assert (wf_sort l c0 (wf_con name s)).
    rewrite_strengthen.
    
    
Fail Admitted.
(*  
  
  all: repeat (simpl; autorewrite with bool_utils pfcore utils);
    intuition; subst;
      try match goal with
          | [wfl : wf_lang ?l, H: is_true((_,_) \in ?l)|-_] =>
            let H':= fresh in pose proof (rule_in_wf wfl H) as H'; safe_invert H'
          end.
  all: repeat rewrite_strengthen.
  
  (* TODO: need subst monotonicity *)

  all: repeat (simpl; autorewrite with bool_utils pfcore utils);
    intuition; subst;
      try match goal with
          | [wfl : wf_lang ?l, H: is_true((_,_) \in ?l)|-_] =>
            let H':= fresh in pose proof (rule_in_wf wfl H) as H'; safe_invert H'
          end.
2:{  assert (name == 
all: repeat rewrite_strengthen.
{
  cbn [compile]; 
    repeat (simpl; autorewrite with bool_utils pfcore utils).
  
  assumption.
  inductive_implies_semantic_rule.
Qed.*)

(*TODO: will this arrangement be useful?
Lemma named_list_lookup_err_in_some {A:eqType} l x (v:A)
  : all_fresh l -> ((x, v) \in l) -> named_list_lookup_err l x = Some v.
Proof.
  intros ?.
  rewrite <- named_list_lookup_err_inb;
    autorewrite with bool_utils; auto.
Qed.  *)


Lemma term_eq_in_lang_proof_in_compiler name lt cmp ls c e1 e2 t
  : preserving_compiler lt cmp ls ->
    (name, wf_term_eq c e1 e2 t) \in ls ->
    exists p, (name, ax_case p) \in cmp.
Proof.
  induction 1; 
    repeat (simpl; autorewrite with bool_utils pfcore utils); eauto with pfcore.
  all: intuition.
  all: try match goal with [H : exists _,_|-_] => destruct H end.
  all: try solve[exists x; 
    repeat (simpl; autorewrite with bool_utils pfcore utils); by eauto with pfcore].
  exists eeq;
    repeat (simpl; autorewrite with bool_utils pfcore utils); by eauto with pfcore.
  Unshelve.
  exact (ax "").
Qed.

Lemma inductive_implies_semantic ls lt cmp
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    semantics_preserving ls lt cmp.
Proof.
  intros; apply judge_ind; intros;
    repeat (simpl; autorewrite with bool_utils pfcore utils in * ); eauto with pfcore.
  {
    apply inductive_implies_semantic_sort_axiom; assumption.
  }
  {
    apply inductive_implies_semantic_term_axiom; assumption.
  }
  {
    
    
    TODO: why is there s and es?
Proof.
  inductive_implies_semantic_rule.
Qed.
    TODO: con lemma
    constructor; eauto.
    
    rewrite compile_wfexp_subst in H5.
    
    
    clear H4 H5.
    match goal with
    |
    strategy: separate lemma?
     -context population tactic for adding e1, e2 wf, etc
    all: repeat match goal with
                | [H : wf_ctx _ _ |-_] =>
                  rewrite (compile_strengthen_ctx _ _ H); eauto with pfcore
                | [H : wf_sort _ _ _|-_] =>
                  rewrite (compile_strengthen_sort _ _ H); eauto with pfcore
                | [H : wf_term _ _ _ _ |-_] =>
                  rewrite (compile_strengthen_term _ _ H); eauto with pfcore
                | [H : le_sort _ _ _ _ _|-_] =>
                  solve[erewrite (compile_strengthen_sort_pf); eauto with pfcore]
                | [H : eq_term _ _ _ _ _ _ |-_] =>
                  solve[erewrite (compile_strengthen_term_pf); eauto with pfcore]
                end.
 
  cbn [compile_pf]; 
    repeat (simpl; autorewrite with bool_utils pfcore utils).
  assumption.
    
Abort.
