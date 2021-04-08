
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils BoolAsProp.
From Named Require Import Pf PfCore.
Require Import String.


(* each element is the image for that constructor or axiom*)
Variant compiler_case := con_case (args : list string) (e:wfexp) | ax_case (p : pf).
Definition compiler := named_list compiler_case. 

Definition eq_compiler_case cc1 cc2 : bool :=
  match cc1, cc2 with
  | con_case args1 e1, con_case args2 e2 => (args1 == args2) && (e1 == e2)
  | ax_case p1, ax_case p2 => p1 == p2
  | _,_ => false
  end.

Lemma eq_compiler_caseP cc1 cc2 : reflect (cc1 = cc2) (eq_compiler_case cc1 cc2).
Proof using .
  destruct cc1; destruct cc2; simpl; solve_reflect_norec.
Qed.

Definition compiler_case_eqMixin := Equality.Mixin eq_compiler_caseP.

Canonical compiler_case_eqType := @Equality.Pack compiler_case compiler_case_eqMixin.

Section CompileFn.
  Context (src tgt : wfexp_lang)
          (cmp : compiler).

  (*TODO: add args to compiler case 
    or to wf_con (or split and axiomatize substitution)
    so that lang argument is unnecessary?*)
  Fixpoint compile (e : wfexp) : wfexp :=
    match e with
    | wf_var x => wf_var x
    | wf_con n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := wf_con "ERR" [::] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (con_case args e) => wfexp_subst (zip args arg_terms) e
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
    wf_sort target (compile_ctx cmp c) t ->
    preserving_compiler target ((n,con_case (map fst c) t)::cmp) ((n,Pf.wf_sort_rule c args) :: l)
| preserving_compiler_term : forall cmp l n c args e t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    wf_term target (compile_ctx cmp c) e (compile cmp t) ->
    preserving_compiler target ((n, con_case (map fst c) e)::cmp) ((n,Pf.wf_term_rule c args t) :: l)
| preserving_compiler_sort_le : forall cmp l n c teq t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_sort target (compile_ctx cmp c) teq (compile cmp t1) (compile cmp t2) ->
    preserving_compiler target ((n,ax_case teq)::cmp) ((n,wf_sort_le c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp l n c eeq e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_term target (compile_ctx cmp c) eeq
            (compile cmp t) (compile cmp e1) (compile cmp e2) ->
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


Lemma fresh_compile_ctx x cmp c
  : fresh x c -> fresh x (compile_ctx cmp c).
Proof.
  induction c; break; simpl in *; intros; break; break_goal;
    autorewrite with utils bool_utils in *; intuition auto.
Qed.


Lemma all_fresh_compile_ctx cmp c
  : all_fresh c -> all_fresh (compile_ctx cmp c).
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
    compile ((n,cc)::cmp) t = compile cmp t.
Admitted.

Lemma compile_strengthen_sort_pf src tgt cmp c p t1 t2 n cc
  : le_sort src c p t1 t2 ->
    preserving_compiler tgt cmp src ->
    fresh n cmp ->
    compile_pf ((n,cc)::cmp) p = compile_pf cmp p.
Admitted.

Lemma compile_strengthen_term_pf src tgt cmp c p e1 e2 t n cc
  : le_term src c p t e1 e2 ->
    preserving_compiler tgt cmp src ->
    fresh n cmp ->
    compile_pf ((n,cc)::cmp) p = compile_pf cmp p.
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
  induction 1;
    repeat (simpl; autorewrite with bool_utils pfcore utils);
    intuition eauto.
Qed.
Hint Resolve fresh_lang_fresh_cmp : pfcore.

Ltac rewrite_strengthen :=
  match goal with
  | [H : wf_ctx _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_ctx _ H pr); eauto with pfcore
  | [H : wf_sort _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_sort _ H pr); eauto with pfcore
  | [H : wf_term _ _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_term _ H pr); eauto with pfcore
  | [H : le_sort _ _ _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    solve[
     erewrite (compile_strengthen_sort_pf);
       [eauto with pfcore | | eauto with pfcore ..];
     eauto with pfcore]
  | [H : le_term _ _ _ _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    solve[
     erewrite (compile_strengthen_term_pf);
       [eauto with pfcore | | eauto with pfcore ..];
     eauto with pfcore]
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
    le_sort lt (compile_ctx cmp c) (compile_pf cmp (ax name)) (compile cmp t1) (compile cmp t2).
Proof.
  inductive_implies_semantic_rule.
Qed.


Lemma inductive_implies_semantic_term_axiom ls lt cmp name c e1 e2 t
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    (name, wf_term_le c e1 e2 t) \in ls ->
    le_term lt (compile_ctx cmp c) (compile_pf cmp (ax name))
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
