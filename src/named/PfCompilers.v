
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Pf PfCore.
Require Import String.


(* each element is the image for that constructor *)
Definition compiler := named_list pf. 

(*TODO: find right place for this *)
Definition get_rule_ctx r :=
  match r with
  | sort_rule_pf c _
  | term_rule_pf c _ _
  | sort_le_pf c _ _
  | term_le_pf c _ _ _ => c
  end.

Section CompileFn.
  Context (l : pf_lang) (*TODO: use pflang? makes no difference*)
          (cmp : compiler).

  Fixpoint compile (e : pf) : pf :=
    match e with
    | pvar x => pvar x
    | pcon n s =>
      let default := pcon "ERR" [::] in
      let default_r := sort_rule_pf [::] [::] in
      let arg_terms := map compile s in
      let constr_pf := named_list_lookup default cmp n in
      let c := get_rule_ctx (named_list_lookup default_r l n) in
      pf_subst (with_names_from c arg_terms) constr_pf
    (*TODO: unify ax and pcon?*)
    | ax n s =>
      let default := pcon "ERR" [::] in
      let default_r := sort_rule_pf [::] [::] in
      let arg_terms := map compile s in
      let constr_pf := named_list_lookup default cmp n in
      let c := get_rule_ctx (named_list_lookup default_r l n) in
      pf_subst (with_names_from c arg_terms) constr_pf
    | sym p => sym (compile p)
    | trans p1 p2 => trans (compile p1) (compile p2)
    | conv pt p => conv (compile pt) (compile p)
    end.

  Definition compile_args := map compile.

  Definition compile_subst (s : named_list pf) := named_map compile s.

  Definition compile_ctx (c:named_list pf) := named_map compile c.

End CompileFn.

(*

First we specify the properties in terms of compile,
then inductively on the compiler. TODO: prove equivalent

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


Definition semantics_preserving cmp l1 l2 :=
  sort_preserving_sem cmp l1 l2
  /\ term_preserving_sem cmp l1 l2
  /\ args_preserving_sem cmp l1 l2.

(*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : pf_lang) : compiler -> pf_lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [::] [::]
| preserving_compiler_sort : forall cmp l n c args t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    sort_ok target (compile_ctx l cmp c) t ->
    is_exp t ->
    preserving_compiler target ((n, t)::cmp) ((n,sort_rule_pf c args) :: l)
| preserving_compiler_term : forall cmp l n c args e t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    term_ok target (compile_ctx l cmp c) e (compile l cmp t) ->
    is_exp e ->
    (*is_exp t ->should I have this here? prob. not*)
    preserving_compiler target ((n, e)::cmp) ((n,term_rule_pf c args t) :: l)
| preserving_compiler_sort_le : forall cmp l n c teq t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    sort_ok target (compile_ctx l cmp c) teq ->
    compile l cmp t1 = proj_l target teq ->
    compile l cmp t2 = proj_r target teq ->
    preserving_compiler target ((n,teq)::cmp) ((n,sort_le_pf c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp l n c eeq e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    term_ok target (compile_ctx l cmp c) eeq (compile l cmp t) ->
    compile l cmp e1 = proj_l target eeq ->
    compile l cmp e2 = proj_r target eeq ->
    preserving_compiler target ((n,eeq)::cmp) ((n,term_le_pf c e1 e2 t) :: l).

(* TODO: decision procedure  for is_exp; move to Pf *)
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
