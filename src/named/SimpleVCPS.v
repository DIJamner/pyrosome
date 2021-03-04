Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp ARule ImCore Pf PfCore Compilers
     PfCompilers PfMatches ParStep IsPfOf.
Require Import String.
Require Import SimpleVSubst SimpleVSTLC.
Import Exp.Notations ARule.Notations Pf.Notations.


Require Coq.derive.Derive.

Set Default Proof Mode "Classic".

Definition stlc_bot :=
  ([:| 
      -----------------------------------------------
      #"bot" : #"ty"
  ])%arule:: stlc.

Import OptionMonad.
Fixpoint simple_subst_to_pf_ty (e:exp) : option pf :=
  match e with
  | var x => Some (pvar x)
  | con "->" [:: B; A] =>
    do pA <- simple_subst_to_pf_ty A;
       pB <- simple_subst_to_pf_ty B;
       ret (pcon "->" [:: pB; pA])
  | con "bot" [::] => Some (pcon "bot" [::])
  | _ => None
  end.


Fixpoint simple_subst_to_pf_env (e:exp) : option pf :=
  match e with
  | var x => Some (pvar x)
  | con "emp" [::] => Some (pcon "emp" [::])
  | con "ext" [:: A; G] =>
    do pa <- simple_subst_to_pf_ty A;
       pG <- simple_subst_to_pf_env G;
       ret (pcon "ext" [:: pa; pG])
  | _ => None
end.


Definition simple_subst_to_pf_sort (t:sort) : option pf :=
  match t with
  | scon "env" [::] => Some (pcon "env" [::])
  | scon "ty" [::] => Some (pcon "ty" [::])
  | scon "sub" [:: G'; G] =>
    do pG' <- simple_subst_to_pf_env G';
       pG <- simple_subst_to_pf_env G;
       ret (pcon "sub" [:: pG'; pG])
  | scon "el" [:: A; G] =>
    do pa <- simple_subst_to_pf_ty A;
       pG <- simple_subst_to_pf_env G;
       ret (pcon "el" [:: pa; pG])
  | scon "val" [:: A; G] =>
    do pa <- simple_subst_to_pf_ty A;
       pG <- simple_subst_to_pf_env G;
       ret (pcon "val" [:: pa; pG])
  | _ => None
  end.


Fixpoint simple_subst_to_pf_sub (c : pf_ctx) (e :exp) G_l : option (pf * pf) :=
  match e with
  | var x =>
    do (pcon "sub" [:: G_r;_]) <- named_list_lookup_err c x;
       ret (pvar x, G_r)
  | con "id" [::] =>
    do ret (pcon "id" [:: G_l], G_l)
  | con "cmp" [:: g; f] =>
    do (p_f,G_fr) <- simple_subst_to_pf_sub c f G_l;
       (p_g, G_gr) <- simple_subst_to_pf_sub c g G_fr;
       ret (pcon "cmp" [:: p_g; p_f; G_gr; G_fr; G_l], G_gr)
  | con "forget" [::] =>
    do ret (pcon "forget" [:: G_l], pcon "emp" [::])
  | con "snoc" [:: e; f] =>
    do (p_f,G_fr) <- simple_subst_to_pf_sub c f G_l;
       (p_e, pA) <- simple_subst_to_pf_val c e G_l;
       ret (pcon "snoc" [:: p_e; p_f; pA; G_fr; G_l], pcon "ext" [:: pA; G_fr])
  | con "wkn" [::] =>
    do (pcon "ext" [:: A; G]) <- Some G_l;
       ret (pcon "wkn" [:: A; G], G)
  | _ => None
  end
with simple_subst_to_pf_val c e G : option (pf * pf) :=
       match e with
       | var x =>
         do (pcon "val" [:: A; _]) <- named_list_lookup_err c x;
         ret (pvar x, A)
       | con "val_subst" [:: e; f] =>
         do (p_f,G_fr) <- simple_subst_to_pf_sub c f G;
            (p_e, pA) <- simple_subst_to_pf_val c e G_fr;
            ret (pcon "val_subst" [:: p_e; pA; p_f; G_fr; G], pA)
      | con "hd" [::] =>
        do (pcon "ext" [:: A; G]) <- Some G;
           ret (pcon "hd" [:: A; G], A)
       | con "lambda" [:: e; A] =>
         do pA <- simple_subst_to_pf_ty A;
            (p_e, pB) <- simple_subst_to_pf_el c e (pcon "ext" [:: pA; G]);
            ret (pcon "lambda" [:: p_e; pB; pA; G], pcon "->" [:: pB; pA])
       | _ => None
       end
with simple_subst_to_pf_el c e G : option (pf * pf) :=
       match e with
       | var x =>
         do (pcon "el" [:: A; _]) <- named_list_lookup_err c x;
         ret (pvar x, A)
       | con "el_subst" [:: e; f] =>
         do (p_f,G_fr) <- simple_subst_to_pf_sub c f G;
            (p_e, pA) <- simple_subst_to_pf_el c e G_fr;
            ret (pcon "el_subst" [:: p_e; pA; p_f; G_fr; G], pA)
      | con "ret" [:: v] =>
        do (pv,A) <- simple_subst_to_pf_val c v G;
           ret (pcon "ret" [:: pv; A; G], A)
       | con "app" [:: e'; e] =>
         do (p_e, pcon "->" [:: pB; pA]) <- simple_subst_to_pf_el c e G;
            (p_e', _) <- simple_subst_to_pf_el c e' G;
            ret (pcon "app" [:: p_e'; p_e; pB; pA; G], pB)
       | _ => None
end.

Definition simple_subst_to_pf_term (c : pf_ctx) (e :exp) t : option pf :=
  match t with
  | pcon "env" [::] => simple_subst_to_pf_env e
  | pcon "ty" [::] => simple_subst_to_pf_ty e
  | pcon "sub" [:: _ ; G_l] =>
    do (p,_) <- simple_subst_to_pf_sub c e G_l;
       ret p
  | pcon "el" [:: _ ; G] =>
    do (p,_) <- simple_subst_to_pf_el c e G;
       ret p
  | pcon "val" [:: _ ; G] =>
    do (p,_) <- simple_subst_to_pf_val c e G;
       ret p
  | _ => None
  end.



Fixpoint simple_subst_to_pf_ctx (c : ctx) : option pf_ctx :=
  match c with
  | [::] => do ret [::]
  | (n,t)::c' =>
    do pc' <- simple_subst_to_pf_ctx c';
       pt <- simple_subst_to_pf_sort t;
       ret (n,pt)::pc'
  end.

Definition simple_subst_to_pf_rule (r : rule) : option rule_pf :=
  match r with
  | sort_rule c args =>
    do pc <- simple_subst_to_pf_ctx c;
    ret sort_rule_pf pc args
  | term_rule c args t =>
    do pt <- simple_subst_to_pf_sort t;
       pc <- simple_subst_to_pf_ctx c;
    ret term_rule_pf pc args pt
  | sort_le c t1 t2 =>
    do pt1 <- simple_subst_to_pf_sort t1;
       pt2 <- simple_subst_to_pf_sort t2;
       pc <- simple_subst_to_pf_ctx c;
    ret sort_le_pf pc pt1 pt2
  | term_le c e1 e2 t =>
    do pt <- simple_subst_to_pf_sort t;
       pc <- simple_subst_to_pf_ctx c;
       pe1 <- simple_subst_to_pf_term pc e1 pt;
       pe2 <- simple_subst_to_pf_term pc e2 pt;
    ret term_le_pf pc pe1 pe2 pt
end.

Fixpoint simple_subst_to_pf_lang (l : lang) : option pf_lang :=
  match l with
  | [::] => do ret [::]
  | (n,r)::l' =>
    do pl' <- simple_subst_to_pf_lang l';
       pr <- simple_subst_to_pf_rule r;
       ret (n,pr)::pl'
  end.

Lemma stlc_bot_wf : wf_lang stlc_bot.
Proof.
  prove_wf_with_fn simple_subst_to_pf_lang.
Qed.

Definition stlc_bot_elab :=
  Eval compute in
    (match simple_subst_to_pf_lang stlc_bot with
     | Some pl => pl
     | None => [::]
     end).

(*
Definition twkn g a b := {{#"ty_subst"(#"ext"(g,a),g,#"wkn"(g,a),b)}}.
Definition ewkn g a b e := {{#"el_subst"(#"ext"(g,a),g,#"wkn"(g,a),b,e)}}.*)
Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | n'.+1 =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Fixpoint vwkn_n n e :=
  match n with
  | 0 => e
  | n'.+1 =>
    {{e #"val_subst" #"wkn" {vwkn_n n' e} }}
  end.

(*n is how many wknings to do on e*)
Definition bind_k n e A k :=
  {{e #"el_subst" (#"snoc" {wkn_n n} (#"lambda" {A} {k})) {e} }}.
Arguments bind_k n e A k/.

Definition ret_val v :=
  {{e #"app" (#"ret" #"hd") (#"ret" {vwkn_n 1 v})}}.

Definition double_neg t : exp :=
  {{e #"->" (#"->" {t} #"bot") #"bot"}}.
Arguments double_neg t /.

Definition get_rule_args r :=
  match r with
  | ARule.sort_rule _ args => args
  | ARule.term_rule _ args _ => args
  | ARule.sort_le c _ _ => map fst c
  | ARule.term_le c _ _ _ => map fst c
  end.

Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).

Definition cps_sort (c:string) args : sort :=
  match c, args with
  | "el", [:: A; G] =>
    {{s #"el" (#"ext" %G (#"->" %A #"bot")) #"bot" }}
  | _,_ => scon c (map var (lookup_args stlc c))
  end%string.
Definition cps (c : string) (args : list string) : exp :=
  match c, args with
  | "->", [:: B; A] =>
    {{e #"->" %A {double_neg (var B)} }}
  | "lambda", [:: e; B; A; G] =>
    {{e #"lambda" %A (#"ret" (#"lambda" (#"->" %B #"bot") %e))}}
  | "app", [:: e2; e1; B; A; G] =>
    let k := {{e #"ret" {vwkn_n 2 {{e #"hd"}} } }} in
    let x1 := {{e #"ret" {vwkn_n 1 {{e #"hd"}} } }} in
    let x2 := {{e #"ret" #"hd"}} in
    (*TODO: don't want the thunk here;
      need to push lambda under bind_ks
      (and ideally not have it at all)

TODO: wkn_n not sufficient; need to weaken leaving the continuation hypothesis
     *)
    bind_k 1 (var e1) {{e #"->" %A {double_neg (var B)} }}
    (bind_k 2 (var e2) (var A)
    {{e #"app" (#"app" {x1} {x2}) {k} }})
  | "el_subst", [:: e; A; g; G'; G] =>
    {{e #"el_subst" (#"snoc" (#"cmp" #"wkn" %g) #"hd") %e }}
  (*| "hd", [:: A] =>
    ret_val {{e #"hd"}} (var A)*)
  | "ret", [:: v; A; G] =>
    ret_val (var v)
  | _,_ => con c (map var (lookup_args stlc c))
  end%string.


Require Compilers.


Fixpoint elab_le_rule (tgt:pf_lang) pcc src' (src : string * rule_pf) :=
  match src with
  | (n, term_le_pf c e1 e2 t) =>
    do lhs <- Some (par_step_n tgt (compile src' pcc e1) 100);
       rhs <- Some (par_step_n tgt (compile src' pcc e2) 100);
       ! eq_pf_irr tgt (proj_r tgt lhs) (proj_r tgt rhs);
       ret (n,trans lhs (sym rhs))
  | _ => None (* No sort relations in this language *)
end.

Fixpoint elab_wf_rule (tgt:pf_lang) pcc' src' (cc : string*_) src : option (string * pf):=
  match src, cc with
  | (n, sort_rule_pf _ _), (n',sort_case t) =>
    do pt <- simple_subst_to_pf_sort t;
       ret (n,pt)
  | (n, term_rule_pf c _ t), (n',term_case e) =>
    do pt <- simple_subst_to_pf_term (compile_ctx src' pcc' c)
                                     e
                                     (compile src' pcc' t);
       ret (n,pt)
  | _,_ => None
end.

Fixpoint elab_compiler (tgt:pf_lang) (cc : Compilers.compiler) (src : pf_lang) : option compiler :=
  match src, cc with
  | [::], [::] => Some [::]
  | (n, sort_rule_pf _ _)::src', (n',sort_case t)::cc' =>
    do pt <- simple_subst_to_pf_sort t;
       pcc' <- elab_compiler tgt cc' src';
       ret (n,pt)::pcc'
  | (n, term_rule_pf c _ t)::src', (n',term_case e)::cc' =>
    do pcc' <- elab_compiler tgt cc' src';
       pt <- simple_subst_to_pf_term (compile_ctx src' pcc' c)
                                     e
                                     (compile src' pcc' t);
       ret (n,pt)::pcc'
  | (n, term_le_pf c e1 e2 t)::src', _ =>
    do pcc <- elab_compiler tgt cc src';
       lhs <- Some (par_step_n tgt (compile src' pcc e1) 100);
       rhs <- Some (par_step_n tgt (compile src' pcc e2) 100);
       ! eq_pf_irr tgt (proj_r tgt lhs) (proj_r tgt rhs);
       ret (n,trans lhs (sym rhs))::pcc
  | _,_ => None (* No sort relations in this language *)
  end.


Definition stlc_elab :=
  Eval compute in
    (match simple_subst_to_pf_lang stlc with
     | Some pl => pl
     | None => [::]
     end).

Definition comp :=
  Eval compute in (make_compiler cps_sort cps (nth_tail 0 stlc)).


(*TODO:move to IsPfOf*)
Definition get_rule_args_pf := 
fun r  =>
match r with
| sort_rule_pf _ args | term_rule_pf _ args _ => args
| sort_le_pf c _ _ | term_le_pf c _ _ _ => [seq i.1 | i <- c]
end.
Definition get_rule_sort r := 
match r with
| sort_rule_pf _ _
| sort_le_pf _ _ _ => pcon "ERR" [::]
| term_rule_pf _ _ t
| term_le_pf _ _ _ t => t
end.

Lemma elab_sort_by' (l : pf_lang) c : forall n s es,
    let r := named_list_lookup (sort_rule_pf [::] [::]) l n in
    let args := get_rule_args_pf r in
    let c' := get_rule_ctx r in
    (n, (sort_rule_pf c' args)) \in l ->
    is_pf_of_wf_args l c s args es c' ->
    is_pf_of_wf_sort l c (scon n s) (pcon n es).
Proof.
  eauto with pfcore.
Qed.

Lemma elab_term_by' l c : forall n s es t,
    let r := named_list_lookup (sort_rule_pf [::] [::]) l n in
    let args := get_rule_args_pf r in
    let c' := get_rule_ctx r in
    let t' := get_rule_sort r in
    (n, (term_rule_pf c' args t')) \in l ->
    is_pf_of_wf_args l c s args es c' ->
    t = (pf_subst (with_names_from c' es) t') ->
    is_pf_of_wf_term l c (con n s) (pcon n es) t.
Proof.
  intros; subst;
  eauto with pfcore.
Qed.

Ltac break_is_pf_of_wf_args :=
  cbn;
  repeat lazymatch goal with
    | [|- is_pf_of_wf_args _ _ _ (?n::_) _ ((?n,_)::_)] =>
      eapply elab_args_cons_ex
    | [|- is_pf_of_wf_args _ _ _ _ _ ((?n,_)::_)] =>
      eapply elab_args_cons_im
    | [|- is_pf_of_wf_args _ _ _ _ _ [::]] =>
      eapply elab_args_nil
    end.

Ltac solve_sort_equality :=
  compute;
  match goal with
    [|- ?t1 = ?t2] =>
    reflexivity ||
    fail "sort" t1 "is not unifiable with sort" t2
  end.
  
Ltac pcon :=
  lazymatch goal with
  | [|-is_pf_of_wf_sort ?l ?c ?t ?pt] =>
    let t' := eval compute in t in
    let pt' := eval compute in pt in
    (* should never succeed:
       assert_fails (is_evar t'; is_evar pt'); *)
    let c' := eval compute in c in
    change_no_check (is_pf_of_wf_sort l c' t' pt');
    eapply elab_sort_by'; [ by compute|break_is_pf_of_wf_args]
  | [|-is_pf_of_wf_term ?l ?c ?e ?pe ?t] =>
    let e' := eval compute in e in
    let pe' := eval compute in pe in
    (* should never succeed:
       assert_fails (is_evar e'; is_evar pe'); *)
    let c' := eval compute in c in
    let t' := eval compute in t in
    change_no_check (is_pf_of_wf_term l c' e' pe' t');
    eapply elab_term_by'; [ by compute| break_is_pf_of_wf_args | solve_sort_equality]
  end.

(*TODO something funny w/ printed evars in error; 
  maybe a backtracking thing?
*)
Ltac pvar :=
  eapply elab_term_var;
      apply named_list_lookup_err_in;
      match goal with
        [|- Some ?t = named_list_lookup_err ?c ?x] =>
        let t' := eval compute in t in
        let t_r := eval compute in (named_list_lookup_err c x) in
        change_no_check (Some t' = t_r);
        compute;
        reflexivity ||
        fail "attempted to use var" x "at type" t'
        "when it has type" t_r
      end.

(*TODO: move to the right place*)
Lemma is_pf_of_le_trans l p1 p2 t1 t12 t2
  : is_pf_of_le l p1 t1 t12 ->
    is_pf_of_le l p2 t12 t2 ->
    is_pf_of_le l (trans p1 p2) t1 t2.
Proof.
  unfold is_pf_of_le.
  cbn [proj_l proj_r].
  easy.
Qed.


Lemma is_pf_of_le_sym l p t1 t2
  : is_pf_of_le l p t1 t2 ->
    is_pf_of_le l (sym p) t2 t1.
Proof.
  unfold is_pf_of_le.
  cbn [proj_l proj_r].
  easy.
Qed.


Lemma is_pf_of_le_refl l t
  : is_exp t -> is_pf_of_le l t t t.
Proof.
Admitted.

  (*rewrite from left to right*)
    Require Import RuleStep.

    Ltac solve_one_rule_left_to_right_lhs rule_name :=
    lazymatch goal with
      [|- is_pf_of_le ?l ?p_evar ?lhs ?rhs] =>
      tryif is_evar rhs; is_evar p_evar
      then
        let x := eval compute in (rule_step_left l rule_name lhs) in
            lazymatch x with
            | Some ?p =>
              let rhs' := eval compute in (proj_r l p) in
              unify p_evar p;
              unify rhs' rhs;
              by compute
            | None => fail "rule" rule_name
                           "could not be rewritten from left to right in" lhs
            end
      else fail "rhs and p_evar not evars"
    end.

    (*TODO: reduce code duplication *)
    Ltac solve_one_rule_right_to_left_rhs rule_name :=
    lazymatch goal with
      [|- is_pf_of_le ?l ?p_evar ?lhs ?rhs] =>
      tryif is_evar lhs; is_evar p_evar
      then
        let x := eval compute in (rule_step_right l rule_name rhs) in
            lazymatch x with
            | Some ?p =>
              let lhs' := eval compute in (proj_l l p) in
              unify p_evar p;
              unify lhs' lhs;
              by compute
            | None => fail "rule" rule_name
                           "could not be rewritten from right to left in" rhs
            end
      else fail "lhs and p_evar not evars"
      end.

(*TODO: get better errors on these*)
Ltac le_rewrite rule_name :=
  first [ eapply is_pf_of_le_trans;
          [solve_one_rule_left_to_right_lhs rule_name |]
        | eapply is_pf_of_le_trans;
          [| eapply is_pf_of_le_sym;
             solve_one_rule_right_to_left_rhs rule_name]].

Ltac le_rewrite_rtl rule_name :=
  first [ eapply is_pf_of_le_trans;
          [eapply is_pf_of_le_sym;
           solve_one_rule_right_to_left_rhs rule_name |]
        | eapply is_pf_of_le_trans;
          [|solve_one_rule_left_to_right_lhs rule_name]].

Ltac le_reflexivity :=
      apply is_pf_of_le_refl; apply /check_is_expP; by compute.

Ltac reduce fuel :=
  lazymatch goal with
    [|- is_pf_of_le ?l ?p_evar ?lhs ?rhs] =>
    tryif is_evar p_evar
    then
      let lhsp := eval compute in (par_step_n l lhs fuel) in
          let rhsp := eval compute in (par_step_n l rhs fuel) in
              let lhs' := eval compute in (proj_r l lhsp) in
                  let rhs' := eval compute in (proj_r l rhsp) in
                      let p_r := open_constr:(trans _ (sym rhsp)) in
                      apply (@is_pf_of_le_trans l lhsp p_r lhs lhs' rhs);
                      [by compute |];
                      apply (is_pf_of_le_trans (t12 := rhs'));
                      [| by compute]
    else fail p_evar "not an evar"
  end.

Local Open Scope string.

Derive cps_elab
       SuchThat (is_pf_of_compiler stlc_bot_elab
                                   (make_compiler cps_sort cps stlc)
                                   cps_elab
                                   stlc_elab
         /\ preserving_compiler stlc_bot_elab cps_elab stlc_elab)
       As cps_elab_preserving.
Proof.
  split.
  repeat match goal with
           [|- is_pf_of_compiler _ _ _ _] => constructor
         end; try solve [ repeat first [ pvar | pcon]].
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {  reduce 100; le_reflexivity. }
  {
    match goal with
      [|- is_pf_of_le ?l ?p ?t1 ?t2] =>
      let t1' := eval compute in t1 in
      let t2' := eval compute in t2 in
      change_no_check (is_pf_of_le l p t1' t2')
    end.
    repeat first [le_rewrite "app_subst"
                 | le_rewrite "lambda_subst"
                 | le_rewrite "el_subst_ret"].
    reduce 100; le_reflexivity.
  }
  {
    reduce 100; le_reflexivity.
  }
  {
    reduce 100; le_reflexivity.
  }
  {
    apply /check_preservingP; by compute.
  }
Qed.
 
(* This way is much faster, but doesn't work if we would have
   needed to specify the rewrite strategy manually in the above proof.
   TODO: extend this method so that I can generate a rewrite trace
   in the interactive form above and then plug it into this 
   computational approach
*)
Definition cps_elab' :=
  Eval compute in
    (match elab_compiler stlc_bot_elab
                         (make_compiler cps_sort cps stlc)
                         stlc_elab with
     | Some pl => pl
     | None => [::]
     end).
Goal match cps_elab' with [::] => False | _ => True end.
    by compute.
Qed.
                      

Lemma cps_elab'_wf : preserving_compiler stlc_bot_elab cps_elab' stlc_elab.
Proof.
  apply /check_preservingP; by compute.
Qed.
