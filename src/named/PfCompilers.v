
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils BoolAsProp.
From Named Require Import Pf PfCore.
Require Import String.


(* each element is the image for that constructor or axiom*)
Variant compiler_case := con_case (e:wfexp) | ax_case (p : pf).
Definition compiler := named_list compiler_case. 

Definition eq_compiler_case cc1 cc2 : bool :=
  match cc1, cc2 with
  | con_case e1, con_case e2 => e1 == e2
  | ax_case p1, ax_case p2 => p1 == p2
  | _,_ => false
  end.

Lemma eq_compiler_caseP cc1 cc2 : reflect (cc1 = cc2) (eq_compiler_case cc1 cc2).
Proof using .
  destruct cc1; destruct cc2; simpl; solve_reflect_norec.
Qed.

Definition compiler_case_eqMixin := Equality.Mixin eq_compiler_caseP.

Canonical compiler_case_eqType := @Equality.Pack compiler_case compiler_case_eqMixin.


(*TODO: find right place for this *)
Definition get_rule_ctx r :=
  match r with
  | Pf.wf_sort_rule c _
  | Pf.wf_term_rule c _ _
  | wf_sort_le c _ _
  | wf_term_le c _ _ _ => c
  end.

Section CompileFn.
  Context (src tgt : wfexp_lang)
          (cmp : compiler).

  (*TODO: add args to compiler case so that lang argument is unnecessary?*)
  Fixpoint compile (e : wfexp) : wfexp :=
    match e with
    | wf_var x => wf_var x
    | wf_con n s =>
      let default := wf_con "ERR" [::] in
      let default_r := Pf.wf_sort_rule [::] [::] in
      let arg_terms := map compile s in
      let c := get_rule_ctx (named_list_lookup default_r src n) in
      let case := named_list_lookup (con_case default) cmp n in
      match case with
      | con_case e => wfexp_subst (with_names_from c arg_terms) e
      | _ => default
      end
    | wf_conv pt p => wf_conv (compile_pf pt) (compile p)
    end
  with compile_pf (e : pf) : pf :=
         match e with
         | ax n =>
           let default := ax "ERR" in
           match named_list_lookup_err cmp n  with
           | Some (ax_case p) => p
           | _ => default
           end
         | pf_refl e => pf_refl (compile e)
         | sym p => sym (compile_pf p)
         | trans p1 p2 => trans (compile_pf p1) (compile_pf p2)
         | pf_conv pt p => pf_conv (compile_pf pt) (compile_pf p)
         | pf_subst s p => pf_subst (named_map compile_pf s) (compile_pf p)
         end.
  
  Definition compile_args := map compile.

  Definition compile_subst (s : named_list wfexp) := named_map compile s.
  Definition compile_subst_pf (s : named_list pf) := named_map compile_pf s.

  Definition compile_ctx (c:named_list wfexp) := named_map compile c.

   (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
   *)
  Definition sort_wf_preserving_sem :=
    forall c t, wf_sort src c t ->
                wf_sort tgt (compile_ctx c) (compile t).

  Definition term_wf_preserving_sem :=
    forall c e t,
      wf_term src c e t ->
      wf_term tgt (compile_ctx c) (compile e) (compile t).

  Definition sort_le_preserving_sem :=
    forall c p t1 t2,
      le_sort src c p t1 t2 ->
      le_sort tgt (compile_ctx c) (compile_pf p)
              (compile t1) (compile t2).
  
  Definition term_le_preserving_sem :=
    forall c p t e1 e2,
      le_term src c p t e1 e2 ->
      le_term tgt (compile_ctx c) (compile_pf p)
              (compile t) (compile e1) (compile e2).

  Definition args_wf_preserving_sem :=
    forall c s c',
      wf_args src c s c' ->
      wf_args tgt (compile_ctx c) (compile_args s) (compile_ctx c').


  Definition subst_le_preserving_sem :=
    forall c c' p s1 s2,
      le_subst src c c' p s1 s2 ->
      le_subst tgt (compile_ctx c) (compile_ctx c') (compile_subst_pf p) (compile_subst s1) (compile_subst s2).
   
  Definition ctx_wf_preserving_sem :=
    forall c, wf_ctx src c -> wf_ctx tgt (compile_ctx c).

  (*Set up to match the combined scheme for the judgment inductives *)
  Definition semantics_preserving :=
    sort_le_preserving_sem /\ term_le_preserving_sem /\ subst_le_preserving_sem
    /\ sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
    /\ ctx_wf_preserving_sem.

End CompileFn.

(*
First we define an inductively provable (and in fact decidable) property 
of elaborated compilers.
*)

(*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : wfexp_lang) : compiler -> wfexp_lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [::] [::]
| preserving_compiler_sort : forall cmp l n c args t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    wf_sort target (compile_ctx l cmp c) t ->
    preserving_compiler target ((n,con_case t)::cmp) ((n,Pf.wf_sort_rule c args) :: l)
| preserving_compiler_term : forall cmp l n c args e t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    wf_term target (compile_ctx l cmp c) e (compile l cmp t) ->
    preserving_compiler target ((n, con_case e)::cmp) ((n,Pf.wf_term_rule c args t) :: l)
| preserving_compiler_sort_le : forall cmp l n c teq t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_sort target (compile_ctx l cmp c) teq (compile l cmp t1) (compile l cmp t2) ->
    preserving_compiler target ((n,ax_case teq)::cmp) ((n,wf_sort_le c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp l n c eeq e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_term target (compile_ctx l cmp c) eeq
            (compile l cmp t) (compile l cmp e1) (compile l cmp e2) ->
    preserving_compiler target ((n,ax_case eeq)::cmp) ((n,wf_term_le c e1 e2 t) :: l).

(* TODO: recover decision procedure?
   will probably use tactics for now, but I'll eventually want this
   for efficiency

Fixpoint check_preserving tgt (cmp:compiler) src : bool :=
  match cmp, src with
  | [::], [::] => true
  | (n,p)::cmp', (n',sort_rule_pf c args)::src' =>
    (n==n')&&
    (check_is_exp p) &&
    (check_sort_ok tgt (compile_ctx src' cmp' c) p) &&
    (check_preserving tgt cmp' src')
  | (n,p)::cmp', (n',term_rule_pf c args t)::src' => 
    (n==n')&&
    (check_is_exp p) &&
    (check_term_ok tgt (compile_ctx src' cmp' c) p (compile src' cmp' t)) &&
    (check_preserving tgt cmp' src')
  | (n,p)::cmp', (n',sort_le_pf c t1 t2)::src' => 
    (n==n')&&
    (check_sort_ok tgt (compile_ctx src' cmp' c) p) &&
    (compile src' cmp' t1 == proj_l tgt p) &&
    (compile src' cmp' t2 == proj_r tgt p) &&
    (check_preserving tgt cmp' src')
  | (n,p)::cmp', (n',term_le_pf c e1 e2 t)::src' => 
    (n==n')&&
    (check_term_ok tgt (compile_ctx src' cmp' c) p (compile src' cmp' t)) &&
    (compile src' cmp' e1 == proj_l tgt p) &&
    (compile src' cmp' e2 == proj_r tgt p) &&
    (check_preserving tgt cmp' src')
  | _, _ => false
  end.
*)


Lemma fresh_compile_ctx x s cmp c
  : fresh x c -> fresh x (compile_ctx s cmp c).
Proof.
  induction c; break; simpl in *; intros; break; break_goal;
    autorewrite with utils bool_utils in *; intuition auto.
Qed.


Lemma all_fresh_compile_ctx s cmp c
  : all_fresh c -> all_fresh (compile_ctx s cmp c).
Proof.
  induction c; break; simpl in *;
    intros; break; break_goal;auto;
      apply fresh_compile_ctx; assumption.
Qed.
Hint Resolve all_fresh_compile_ctx : pfcore.

(*TODO: move to utils; separate db?*)
Lemma false_False : false -> False.
Proof.
  intro h; inversion h.
Qed.
Hint Resolve false_False : pfcore.

(*
Lemma check_preservingP
  : forall t cmp s, all_fresh t ->
                    check_lang_ok s ->
    reflect (preserving_compiler t cmp s) (check_preserving t cmp s).
Proof.
  Opaque all_fresh.
  intros t cmp; induction cmp; intros s frt sok; destruct s; break;
   repeat (simpl in *; break;(lazymatch goal with
    | [H: ?a |- ?a] => exact H
    | [H: true = true |- _] => clear H
    | [H: true = _ |- _] => symmetry in H
    | [H: false = true|- _] => inversion H
    | [H: false = _ |- _] => symmetry in H
    | [H: is_true false|- _] => inversion H
    | [H: ?a = true |- _] => change (is_true a) in H
    | [H: (?a == ?a) = false|- _] => rewrite eq_refl in H
    | [H: (?a == ?b) = false,
       H' : ?a = ?b |- _] => exfalso; move: H => /negP H; apply H; apply /eqP; exact H'
    | [H: is_true(_ == _) |- _] => move: H => /eqP; intro H; subst
    | [|- reflect _ true] => constructor
    | [|- reflect _ false] => constructor
    | [|- reflect _ (match ?e with _=>_ end)] => destruct e
    | [|- reflect _ (_&&_)] =>
           destruct_reflect_andb_l; simpl
    | [|- reflect _ ?p] =>
      let eqn := fresh "eqn" in
      my_case eqn p; simpl
    | [H' : is_true(all_fresh ?l) -> ?a |- _] =>
      assert a; [apply H'|]; clear H'
    | [IH : forall _, _ -> _ -> reflect (preserving_compiler _ _ _) _,
       H : is_true(check_preserving ?t ?c ?s) |- preserving_compiler ?t ?c ?s] =>
      apply /IH; auto
    | [|- preserving_compiler _ _ _] => constructor
    | [H : check_preserving ?t ?cmp ?s = false,
       H' : preserving_compiler ?t ?cmp ?s|- _]=>
      move: H' => /IHcmp; rewrite H; auto
    | [H : is_true(check_sort_ok ?t ?c ?s) |- sort_ok ?t ?c ?s] =>
      apply /check_sort_okP; auto
    | [|- is_exp _]=> apply /check_is_expP; auto
    | [|- ~_] => let H:= fresh in intro H; inversion H; subst; clear H 
    | [H : check_term_ok _ _ ?e ?t = false, H' : term_ok _ _ ?e ?t|- _]=>
      move: H' => /check_term_okP; rewrite H; auto
    | [H : check_sort_ok _ _ ?t = false, H' : sort_ok _ _ ?t|- _]=>
      move: H' => /check_sort_okP; rewrite H; auto
    | [H : check_ctx_ok _ _ = false, H' : ctx_ok _ _|- _]=>
      move: H' => /check_ctx_okP; rewrite H; auto
    | [H : check_rule_ok _ _ = false, H' : rule_ok _ _|- _]=>
      move: H' => /check_rule_okP; rewrite H; auto
    | [H : check_is_exp ?e = false, H' : is_exp ?e|- _]=>
      move: H' => /check_is_expP; rewrite H; auto
    | [H : is_true(check_term_ok _ _ _ _)|- _]=>
      move: H => /check_term_okP H
    | [H : is_true(check_ctx_ok _ _)|- _]=>
      move: H => /check_ctx_okP H
    | [H : is_true(check_lang_ok _)|- _]=>
      move: H => /check_lang_okP H
    | [|- is_true(all_fresh (compile_ctx _ _ _))] =>
      apply all_fresh_compile_ctx
    | [H : ctx_ok ?l ?c |- is_true(all_fresh ?c)] =>
      apply (ctx_ok_all_fresh H)
    | [H : lang_ok ?l |- is_true(all_fresh ?l)] =>
      apply lang_ok_all_fresh
    | [|- _ -> False] => intro
    end ||
        match goal with [|-?P] => idtac P end)).
Qed.
*)


Lemma invert_pair_eq A B (a1 a2 : A) (b1 b2 : B)
  : (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof.  intuition; try inversion H; subst; eauto with pfcore. Qed.
Hint Rewrite invert_pair_eq : utils.


Lemma compile_strengthen_term l cmp c e t n r cc
  : wf_term l c e t ->
    fresh n l ->
    fresh n cmp ->
    compile ((n,r)::l) ((n,cc)::cmp) e = compile l cmp e.
Admitted.

Lemma compile_strengthen_sort l cmp c t n r cc
  : wf_sort l c t ->
    fresh n l ->
    fresh n cmp ->
    compile ((n,r)::l) ((n,cc)::cmp) t = compile l cmp t.
Admitted.

Lemma compile_strengthen_sort_pf l cmp c p t1 t2 n r cc
  : le_sort l c p t1 t2 ->
    fresh n l ->
    fresh n cmp ->
    compile_pf ((n,r)::l) ((n,cc)::cmp) p = compile_pf l cmp p.
Admitted.

Lemma compile_strengthen_term_pf l cmp c p e1 e2 t n r cc
  : le_term l c p t e1 e2 ->
    fresh n l ->
    fresh n cmp ->
    compile_pf ((n,r)::l) ((n,cc)::cmp) p = compile_pf l cmp p.
Admitted.

Lemma compile_strengthen_ctx l cmp c n r cc
  : wf_ctx l c ->
    fresh n l ->
    fresh n cmp ->
    compile_ctx ((n,r)::l) ((n,cc)::cmp) = compile_ctx l cmp.
Admitted.



Lemma fresh_lang_fresh_cmp lt cmp l n
  : preserving_compiler lt cmp l ->
    fresh n l -> fresh n cmp.
Proof.
  induction 1;
    repeat (simpl; autorewrite with bool_utils pfcore utils);
    intuition eauto.
Qed.
Hint Resolve fresh_lang_fresh_cmp : pfcore.

Ltac rewrite_strengthen :=
  match goal with
  | [H : wf_ctx _ _ |-_] =>
    rewrite (compile_strengthen_ctx _ _ H); eauto with pfcore
  | [H : wf_sort _ _ _|-_] =>
    rewrite (compile_strengthen_sort _ _ H); eauto with pfcore
  | [H : wf_term _ _ _ _ |-_] =>
    rewrite (compile_strengthen_term _ _ H); eauto with pfcore
  | [H : le_sort _ _ _ _ _|-_] =>
    solve[erewrite (compile_strengthen_sort_pf); eauto with pfcore]
  | [H : le_term _ _ _ _ _ _ |-_] =>
    solve[erewrite (compile_strengthen_term_pf); eauto with pfcore]
  end.

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
  

Lemma inductive_implies_semantic_sort_axiom ls lt cmp name c t1 t2
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, wf_sort_le c t1 t2) \in ls ->
    le_sort lt (compile_ctx ls cmp c) (compile_pf ls cmp (ax name)) (compile ls cmp t1) (compile ls cmp t2).
Proof.
  inductive_implies_semantic_rule.
Qed.


Lemma inductive_implies_semantic_term_axiom ls lt cmp name c e1 e2 t
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, wf_term_le c e1 e2 t) \in ls ->
    le_term lt (compile_ctx ls cmp c) (compile_pf ls cmp (ax name))
            (compile ls cmp t) (compile ls cmp e1) (compile ls cmp e2).
Proof.
  inductive_implies_semantic_rule.
Qed.


Lemma inductive_implies_semantic_sort ls lt cmp name c c' args s
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, Pf.wf_sort_rule c' args) \in ls ->
    wf_args ls c s c' ->
    wf_sort lt (compile_ctx ls cmp c) (compile ls cmp (wf_con name s)).
Proof.
  intros wfl pr wfl';
    revert wfl'; induction pr; simpl; [easy|..].

  intros.
  cbn.
  my_case Hn (name =? n)%string.
  TODO: need wfexp_subst monotonicity
  
  
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
Qed.

  

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

(*TODO: will this arrangement be useful?
Lemma named_list_lookup_err_in_some {A:eqType} l x (v:A)
  : all_fresh l -> ((x, v) \in l) -> named_list_lookup_err l x = Some v.
Proof.
  intros ?.
  rewrite <- named_list_lookup_err_inb;
    autorewrite with bool_utils; auto.
Qed.  *)


Lemma term_le_in_lang_proof_in_compiler name lt cmp ls c e1 e2 t
  : preserving_compiler lt cmp ls ->
    (name, wf_term_le c e1 e2 t) \in ls ->
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
                | [H : le_term _ _ _ _ _ _ |-_] =>
                  solve[erewrite (compile_strengthen_term_pf); eauto with pfcore]
                end.
 
  cbn [compile_pf]; 
    repeat (simpl; autorewrite with bool_utils pfcore utils).
  assumption.
    
Abort.
