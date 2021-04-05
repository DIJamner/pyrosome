
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Pf PfCoreDefs.
Require Import String.


(* each element is the image for that constructor or axiom*)
Variant compiler_case := con_case (e:wfexp) | ax_case (p : pf).
Definition compiler := named_list compiler_case. 

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
    forall c c' s' args es es' c2 c2',
      ctx_compiles_to c c' ->
      args_compile_to c es c2 es' ->
      ctx_compiles_to c2 c2' ->
      size args = size s' ->
      subseq (zip args s') (with_names_from c2' es') ->
      wf_args tgt c' s' args es' c2'.


  Definition args_le_preserving_sem :=
    forall c c' s1' s2' args es1 es2 es1' es2' c2 c2',
      ctx_compiles_to c c' ->
      args_compile_to c es1 c2 es1' ->
      args_compile_to c es2 c2 es2' ->
      ctx_compiles_to c2 c2' ->
      size args = size s1' ->
      subseq (zip args s1') (with_names_from c2' es1') ->
      size args = size s2' ->
      subseq (zip args s2') (with_names_from c2' es2') ->
      le_args tgt c' c2' s1' s2' args es1' es2'.

  Definition ctx_wf_preserving_sem :=
    forall c c',
      ctx_compiles_to c c' ->
      wf_ctx tgt c'.

  Definition semantics_preserving :=
    sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
    /\ sort_le_preserving_sem /\ term_le_preserving_sem /\ args_le_preserving_sem.

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
  induction c; break; simpl in *; intros; break; break_goal; auto.
  rewrite in_cons.
  rewrite in_cons in H.
  apply /norP;
    move: H => /norP H;
  break; break_goal; auto.
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


(*
We then specify the semantic properties of compilation we expect.
 TODO: prove equivalent
 *)
Definition sort_preserving_sem cmp l1 l2 :=
  forall c t, sort_ok l1 c t ->
              sort_ok l2 (compile_ctx l1 cmp c) (compile l1 cmp t).

Definition term_preserving_sem cmp l1 l2 :=
  forall c e t, term_ok l1 c e t ->
                term_ok l2 (compile_ctx l1 cmp c) (compile l1 cmp e) (compile l1 cmp t).

Definition args_preserving_sem cmp l1 l2 :=
  forall c s c', args_ok l1 c s c' ->
                 args_ok l2 (compile_ctx l1 cmp c) (compile_args l1 cmp s) (compile_ctx l1 cmp c').

(* TODO: should need lemma about is_exp preservation *)

Lemma inductive_implies_semantic_sort_ok cmp ls lt
  : lang_ok ls -> lang_ok lt -> preserving_compiler lt cmp ls ->
    sort_preserving_sem cmp ls lt
with inductive_implies_semantic_term_ok cmp ls lt
  : lang_ok ls -> lang_ok lt -> preserving_compiler lt cmp ls ->
    term_preserving_sem cmp ls lt
with inductive_implies_semantic_args_ok cmp ls lt
  : lang_ok ls -> lang_ok lt -> preserving_compiler lt cmp ls ->
    args_preserving_sem cmp ls lt.
Proof.
  {
    unfold sort_preserving_sem.
    intros until t.
    destruct t; intro t_ok; inversion t_ok; subst; clear t_ok.
    {
      cbn.
      (*TODO: need subst ok*)
      apply sort_subst_ok.
