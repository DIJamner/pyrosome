Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp ARule ImCore Pf Compilers PfCompilers.
Require Import String.
Require Import SimpleSubst SimpleSTLC.
Import Exp.Notations ARule.Notations.


Require Coq.derive.Derive.

Set Default Proof Mode "Classic".

Definition stlc_bot :=
  ([:| 
      -----------------------------------------------
      #"bot" : #"ty"
  ])%arule:: stlc.

Import OptionMonad.
Definition simple_subst_to_pf_ty (e:exp) : option pf :=
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
       (p_e, pA) <- simple_subst_to_pf_el c e G_l;
       ret (pcon "snoc" [:: p_e; p_f; pA; G_fr; G_l], pcon "ext" [:: pA; G_fr])
  | con "wkn" [::] =>
    do (pcon "ext" [:: A; G]) <- Some G_l;
       ret (pcon "wkn" [:: A; G], G)
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
      | con "hd" [::] =>
        do (pcon "ext" [:: A; G]) <- Some G;
           ret (pcon "hd" [:: A; G], A)
       | con "lambda" [:: e; A] =>
         do pA <- simple_subst_to_pf_ty A;
            (p_e, pB) <- simple_subst_to_pf_el c e (pcon "ext" [:: pA; G]);
            ret (pcon "lambda" [:: p_e; pB; pA; G], pcon "->" [:: pB; pA])
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
Fixpoint wkn_n n e :=
  match n with
  | 0 => e
  | n'.+1 =>
    {{e #"el_subst" #"wkn" {wkn_n n' e} }}
  end.

Definition let_bind e k :=
  {{e #"app" {e} (#"lambda" {k})}}.
Arguments let_bind e k/.

Definition ret_val v :=
  {{e #"lambda" (#"app" #"hd" (#"el_subst" #"wkn" {v}))}}.
Arguments ret_val v/.

(* TODO: I'm embedding full terms into inferred terms; need to make work.
   Add escape hatch constr?*)

Definition double_neg t : exp :=
  {{e #"->" (#"->" {t} #"bot") #"bot"}}.
Arguments double_neg t /.

Definition lam e := {{e #"lambda" {e} }}.
Arguments lam e/.


Definition get_rule_args r :=
  match r with
  | ARule.sort_rule _ args => args
  | ARule.term_rule _ args _ => args
  | ARule.sort_le c _ _ => map fst c
  | ARule.term_le c _ _ _ => map fst c
  end.

Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).

Definition cps_sort (c:string) args : sort := scon c (map var args).
Definition cps (c : string) (args : list string) : exp :=
  match c, args with
  | "->", [:: B; A] =>
    double_neg {{e #"->" %A %B}}
  | "lambda", [:: e; A] =>
    ret_val {{e #"lambda" %A %e}}
  | "app", [:: e2; e1] =>
    let k := wkn_n 2 {{e #"hd"}} in
    let x1 := wkn_n 1 {{e #"hd"}} in
    let x2 := {{e #"hd"}} in
    {{e #"lambda" %"TODO"
        {let_bind (wkn_n 1 (var e1))
         (let_bind (wkn_n 2 (var e2))
         {{e #"app" {k} (#"app" {x1} {x2})}} ) } }}
  | _,_ => con c (map var args)
  end%string.

Require Compilers.

(*
Parameter simple_subst_to_pf_compiler : Compilers.compiler -> option compiler.
Definition cps_elab :=
  Eval compute in
    (match simple_subst_to_pf_compiler (make_compiler cps_sort cps stlc) with
     | Some pl => pl
     | None => [::]
     end).
Print cps_elab. TODO: maybe automate to this degree later*)

Derive cps_elab
       SuchThat (Some (make_compiler cps_sort cps stlc) = synth_compiler cps_elab stlc)
       /\ preserving_compiler stlc_bot_elab cps_elab stlc)
  As cps_preserving.
Proof.

Ltac prove_wf_sort_with_fn f :=
  match goal with
    [|- wf_lang ?l] =>
    remember (f l) as mp eqn:Heqmp;
    vm_compute in Heqmp;
    match goal with
      [ H : _ = Some ?pl|-_] =>
      pose (p:=pl); clear H;
      apply (@synth_wf_sort_related p)
    end
  end;
  by compute.

Require Import Ltac2.Constr.
Ltac2 refine_evar e p :=
  let x := Std.eval_vm None e in
  match Unsafe.kind x with
  | Unsafe.Evar e _ => Control.new_goal e > [| refine p]
  | _ => Control.throw_invalid_argument "not an evar"
  end.
Ltac2 get_ctx_size l r :=
  Std.eval_vm None
              '(size (get_rule_ctx
                        (named_list_lookup (sort_rule [::] [::])
                                           $l $r))).
Ltac2 rec list_pat szc :=
  match! szc with
  | 0 => open_constr:([::])
  | S ?n =>
    let rst := list_pat n in
    open_constr:(cons _ $rst)
  end.
Ltac2 refine_with_axiom p name :=
  match! goal with
    [_ : wf_lang ?l|-_] =>
    let s := list_pat (get_ctx_size l name) in
    refine_evar p '(ax $name $s)
  end. 
Ltac2 refine_with_con p name :=
  match! goal with
    [_ : wf_lang ?l|-_] =>
    let s := list_pat (get_ctx_size l name) in
    refine_evar p '(pcon $name $s)
  end. 
Require Import Ltac2.Option.
Local Ltac refine_with_axiom :=
  ltac2:(p name |- let p' := get (Ltac1.to_constr p) in
                   let name' := get (Ltac1.to_constr name) in
                   refine_with_axiom p' name').
Local Ltac refine_with_con :=
  ltac2:(p name |- let p' := get (Ltac1.to_constr p) in
                   let name' := get (Ltac1.to_constr name) in
                   refine_with_con p' name').
Open Scope string.

(*TODO: move
Lemma synth_le_term_complete l c t e1 e2
  : le_term l c t e1 e2 -> exists pf,
      Some (t,e1,e2) = synth_le_term stlc_bot pf c.
Proof.
  (*relies on subst lemma*)
Admitted.
 *)

(*TODO: move*)
Lemma rule_in_term_le l c e1 e2 t
  : (term_le c e1 e2 t) \in map snd l ->
    le_term l c t e1 e2.
Proof.
  intro rin.
  apply in_map_snd in rin.
  destruct rin.
  eauto with imcore.
Qed.

(*TODO: move*)
Lemma rule_in_sort_le l c t1 t2
  : (sort_le c t1 t2) \in map snd l ->
    le_sort l c t1 t2.
Proof.
  intro rin.
  apply in_map_snd in rin.
  destruct rin.
  eauto with imcore.
Qed.

Lemma cps_preserving : preserving_compiler stlc_bot (make_compiler cps_sort cps stlc) stlc.
Proof.
  pose proof stlc_bot_wf.
  repeat match goal with
         | [|- preserving_compiler _ _ _] =>
           constructor
         | [|- wf_sort _ _ ?t] =>
           remember (simple_subst_to_pf_sort t) as mp eqn:Heqmp;
             vm_compute in Heqmp;
             match goal with
               [ H : _ = Some ?pl|-_] =>
               pose (p:=pl); clear H;
                 apply (synth_wf_sort_related stlc_bot_wf (p:= p))
             end; by compute
  | [|- wf_term _ ?c ?e ?t] =>
           remember (simple_subst_to_pf_ctx c) as mc eqn:Heqmc;
             vm_compute in Heqmc;
             match goal with
               [ H : mc = Some ?p_c|-_] =>
               pose (pc:=p_c); clear H
             end;
           remember (simple_subst_to_pf_sort t) as mp eqn:Heqmp;
             vm_compute in Heqmp;
             match goal with
               [ H : mp = Some ?p_t|-_] =>
               pose (pt:=p_t); clear H
             end;
           remember (simple_subst_to_pf_term pc e pt) as mp' eqn:Heqmp';
             vm_compute in Heqmp';
             match goal with
               [ H' : mp' = Some ?p_e|-_] =>
               pose (pe:= p_e); clear H';
                 apply (synth_wf_term_related stlc_bot_wf (p:= pe))
             end; by compute
  | [|- le_term _ _ _ _ _] =>
    try by (apply rule_in_term_le; compute)
  | [|- le_sort _ _ _ _] =>
    try by (apply rule_in_sort_le; compute)
         end; cbn.
  apply preserving_compiler_term_le.
  Print preserving_compiler.
         | [|- preserving_compiler _ (_,term_case _] =>
           constructor
  {
    Eval compute in
        (let cmp:= (make_compiler cps_sort cps stlc) in
         let default := sort_case [::] (scon "ERR" [::]) in
          match {{e #"el_subst" #"id" %"e"}}with
  | var x => default
  | con n s =>
    let arg_terms := map (compile_term cmp) s in
    named_list_lookup default cmp n
          end).
    | term_case args c_case => args
    | _ =>  [::]
    end
  end
        ).
    TODO: args wrong?
    TODO: a (compiler?) bug here; g not in scope
                                             should id be subbed for g?
  }
    Search _ le_term.
    evar (p : pf).
    apply (synth_le_term_related H (p:=p)).
    
    refine_with_axiom p "id_right".
    Search pf_refl.
    
    assert (p = ax "cmp_id")
    cbn.
  match goal with
  end.
  Check synth_wf_sort_related.
  match goal with
    [|- wf_sort _ _ ?t] =>
    remember (simple_subst_to_pf_sort t) as mp eqn:Heqmp;
      vm_compute in Heqmp;
    match goal with
      [ H : _ = Some ?pl|-_] =>
      pose (p:=pl); clear H;
        apply (synth_wf_sort_related stlc_bot_wf (p:= p))
    end
  end.
  by compute.
  prove_wf_sort_with_fn simple_subst_to_pf_sort.

Fail.
  
Derive elab_cps
       SuchThat (elab_preserving_compiler elab_stlc_letk (make_compiler cps_sort cps (strip_args elab_stlc)) elab_cps elab_stlc)
       As elab_cps_pf.
Proof.
  simpl.
  repeat (match! goal with
  | [ |-  elab_preserving_compiler _ ((_,sort_case _ _)::_) _ _]=>
    apply preserving_compiler_sort'
  | [ |-  elab_preserving_compiler _ ((_,term_case _ _)::_) _ _]=>
    apply preserving_compiler_term'
  | [ |-  elab_preserving_compiler _ _ _ _]=>
    constructor
  | [|-_] => simpl; step_elab()
          end); repeat (simpl; step_elab()).

  {
    eapply Core.le_sort_refl'; repeat(simpl; step_elab()).
    eapply (Core.le_term_by' "->_subst"%string); repeat(simpl; step_elab()).
  }
  {
    eapply Core.le_sort_refl'; repeat(simpl; step_elab()).
    symmetry.
    eapply Core.le_term_trans.
    symmetry.
    eapply (Core.le_term_by' "->_subst"%string); repeat(simpl; step_elab()).
    eapply Core.le_term_refl'; repeat(simpl; step_elab()).
    (* making choices here*)
    symmetry.
    eapply (Core.le_term_by' "->_subst"%string); repeat(simpl; step_elab()).
  }
  {
    eapply Core.le_sort_refl'; repeat(simpl; step_elab()).
    eapply Core.le_term_trans.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat(simpl; step_elab()).
    eapply Core.le_term_trans.
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat(simpl; step_elab()).
    eapply Core.le_term_trans.
    eapply (Core.le_term_by' "->_subst"%string); repeat(simpl; step_elab()).
    eapply Core.le_term_refl'; repeat(simpl; step_elab()).
    {
      eapply Core.le_term_trans.
      eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat(simpl; step_elab()).
      eapply Core.le_term_trans.
      eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat(simpl; step_elab()).
      (* makes choices*)
      reflexivity.
    }
    {
      eapply Core.le_term_trans.
      eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat(simpl; step_elab()).
      eapply Core.le_term_trans.
      eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat(simpl; step_elab()).
      (* makes choices*)
      reflexivity.
    }
  }
  {
    eapply Core.le_sort_refl'; repeat(simpl; step_elab()).
    symmetry.
    eapply Core.le_term_trans.
    eapply (Core.le_term_by' "ty_subst_id"%string); repeat(simpl; step_elab()).
    symmetry.
    (* TODO: makes choices*)
    simpl.
ee    reflexivity.
  }
  {
    TODO: issue here
      
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  {
    eapply Core.le_sort_refl'; repeat(simpl; step_elab()).
    eapply (Core.le_term_by' "->_subst"%string); repeat(simpl; step_elab()).
  }
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).

  {
    eapply Core.le_sort_refl'; repeat(simpl; step_elab()).
    
    eapply (Core.le_term_by' "->_subst"%string); repeat(simpl; step_elab()).
  }
  simpl.
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  eapply Core.wf_term_conv> [|apply Core.wf_term_by'|]; repeat (simpl; step_elab()); repeat (simpl; step_elab()).
  simpl.
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  progress (repeat (simpl; step_elab())).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  repeat (simpl; step_elab()).
  (repeat (simpl; step_elab())).
  (repeat (simpl; step_elab())).
  (repeat (simpl; step_elab())).
  (repeat (simpl; step_elab())).
  (repeat (simpl; step_elab())).
  (repeat (simpl; step_elab())).
  simpl.
  repeat (simpl; step_elab()).
    try (solve [ repeat(simpl; step_elab())
               | repeat(apply elab_term_by'; repeat (simpl;step_elab()))]).
  {
   
    cbn.
    TODO: curr. proof missing weakenings inside cont type in Gamma
    apply elab_term_by'; repeat (cbn;step_elab()).
    {
      eapply elab_term_conv.
      apply elab_term_by'; repeat (cbn;step_elab()).
      {
        eapply elab_term_conv.
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        (* TODO: just a guess right now *)
        inst_elab '({{e #"->" (#"->" %"A" %"B") #"bot"}}).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        repeat(simpl; step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        apply elab_term_by'; repeat (cbn;step_elab()).
        step_elab().
        cbn.

        {
          eapply Core.le_sort_refl'; repeat (simpl; step_elab()).
          reflexivity.
          eapply Core.le_term_trans.
          eapply (@Core.le_term_by' "->_subst"%string); repeat (simpl;step_elab()); reflexivity.
          
          reflexivity.
          reflexivity.
          reflexivity.
          reflexivity.
        }
      }
      {
        cbn.
        apply elab_term_by'; repeat (cbn;step_elab()).
        
        cbn.
    }
          symmetry.
        
      cbn.
    {
      eapply elab_term_conv.
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).

      inst_elab '({{e #"->" (#"->" %"A" %"B") #"bot"}}).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      repeat (simpl;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      repeat (simpl;step_elab()).
      eapply Core.le_sort_refl'; repeat (simpl; step_elab()).
      reflexivity.
      cbn.
    }
    {
      apply elab_term_by'; repeat (cbn;step_elab()).
      apply elab_term_by'; repeat (cbn;step_elab()).
      cbn.
    Require Import Named.Recognizers.
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()).
    apply Core.wf_term_by'; repeat (cbn;step_elab()). 
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    cbn. TODO: apply ty_subst conversion
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
    apply elab_term_by'; repeat (cbn;step_elab()).
  }
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  solve [apply elab_term_by'; repeat (cbn;step_elab())].
  unfold elaboration.
  unfold elab_cat_lang_inst.
  unfold elab_cat_lang.
  repeat (match! goal with
  | [ |-  elab_preserving_compiler _ ((_,term_case _ _)::_) _ _]=>
    apply preserving_compiler_term'
  | [ |-  elab_preserving_compiler _ _ _ _]=>
    constructor
  | [|-_] => cbn; step_elab()
          end).

  apply preserving_compiler_term'; 
  cbv.
  TODO: friendly construxtors to figure out the issues?
  constructor.
  repeat constructor.
