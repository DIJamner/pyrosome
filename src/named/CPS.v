Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp.
From Named Require Import IExp IRule ICore ICompilers Subst STLC Tactics.
Import IExp.Notations IRule.Notations ARule.Notations.
Require Import String.
Require Import STLC_bot LetK.


Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".


(* equivalent definition
Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).
Definition id_compiler l :=
  make_compiler (fun c s => scon c (map var (lookup_args l c)))
                (fun c s => con c (map var (lookup_args l c)))
                (strip_args l).
*)

Fixpoint id_compiler (l : ARule.lang) : compiler :=
  match l with
  | (n,ARule.sort_rule c args)::l' =>
    (n,sort_case (map fst c) (scon n (map var args)))
      ::(id_compiler l')
  | (n,ARule.term_rule c args _)::l' =>
    (n,term_case (map fst c) (con n (map var args)))
      ::(id_compiler l')
  | (n,_)::l' => id_compiler l'
  | [::] => [::]
  end.

Fixpoint eid_compiler (l : ARule.lang) : Compilers.compiler :=
  match l with
  | (n,ARule.sort_rule c args)::l' =>
    (n,Compilers.sort_case (map fst c) (Exp.scon n (map Exp.var (map fst c))))
      ::(eid_compiler l')
  | (n,ARule.term_rule c args _)::l' =>
    (n,Compilers.term_case (map fst c) (Exp.con n (map Exp.var (map fst c))))
      ::(eid_compiler l')
  | (n,_)::l' => eid_compiler l'
  | [::] => [::]
  end.

(* TODO: generalize id compiler 
(* TODO: prove *) 
Lemma preserving_compiler_embed n r lt cmp ls
  : Core.fresh n lt ->
    Compilers.preserving_compiler lt cmp ls ->
    Compilers.preserving_compiler ((n,r)::lt) cmp ls.
Proof.
Admitted.

Lemma elab_preserving_compiler_embed n r lt cmp ecmp ls
  : Core.fresh n lt ->
    elab_preserving_compiler lt cmp ecmp ls ->
    elab_preserving_compiler ((n,r)::lt) cmp ecmp ls.
Proof.
Admitted.

Lemma fresh_strip_args
  : forall (l : named_list ARule.rule) (name : Exp.str_eqType),
       Core.fresh name (strip_args l) -> Core.fresh name l.
Proof.
Admitted.

Lemma preserving_id_compiler l
  : Core.wf_lang (strip_args l) -> elab_preserving_compiler l (id_compiler l) (eid_compiler l) l.
Proof.
  elim l; simpl; intros.
  { constructor. }
  {
    destruct a.
    simpl in *.
    destruct r; simpl in *; inversion H0; subst; constructor;
      eauto using elab_preserving_compiler_embed, fresh_strip_args.
    {
      eapply elab_sort_by'; simpl; rewrite eqb_refl; simpl; eauto.
      admit.
      {
        elim l1; cbn.
        {
          inversion H6; subst.
          revert H2.
          elim c; cbn.
          { constructor. }
          { intros.
            destruct a; cbn.
            inversion H2; subst.
            repeat(cbn; step_elab()); auto.
            inversion
            cbn.
      Search  _ (map _ (map _ _)).
      apply strip_args_fresh.
      Search strip_args.
    {
      
      
    split.

Derive elab_id_compiler
       SuchThat (forall lt ls, elab_preserving_compiler lt (id_compiler ls) (elab_id_compiler ls) ls)
       As elab_id_compiler_pf.
Proof.
  assert (exists b, elab_id_compiler = fun l => b l).
  eexists; cbv; reflexivity.
  destruct H as [eidc H].
  rewrite H.
  intros lt ls.
  induction ls.
  { cbn. constructor. }

Lemma preserving_id_compiler l
  : Core.wf_lang l -> elab_preserving_compiler l (id_compiler l) l.
Proof.
  elim l > [constructor|].
  intros p l'.
  destruct p.
  destruct r; cbn; constructor;
    try (fun () =>  apply preserving_compiler_embed).
  eauto.
  {
    eapply Core.wf_sort_by; eauto with judgment.
    ltac1:(instantiate (1:=c)).
    admit.
    
*)

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

Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).

Definition cps_sort (c:string) args : sort := scon c (map var args).
Definition cps (c : string) (args : list string) : exp :=
  match c, args with
  | "->", [:: B; A; G] =>
    double_neg {{e #"->" %A %B}}
  | "lambda", [:: e; B; A; G] =>
    ret_val {{e #"lambda" %e}}
  | "app", [:: e2; e1; b; a; g] =>
    let k := wkn_n 2 {{e #"hd"}} in
    let x1 := wkn_n 1 {{e #"hd"}} in
    let x2 := {{e #"hd"}} in
    {{e #"lambda"
      (#"let" {wkn_n 1 (var e1)}
      (#"let" {wkn_n 2 (var e2)}
      (#"app" {k} (#"app" {x1} {x2}))))}}
  | _,_ => con c (map var (lookup_args elab_stlc c))
  end%string.


Require Import Recognizers.

Ltac2 has_evar (c : constr) :=
  Control.plus (fun ()=> ltac1:(c|-has_evar c) (Ltac1.of_constr c); true)
               (fun _=> false).

Ltac2 reflexivity_no_evars () :=
  match! goal with
    [|- _ ?a ?b] =>
    match Bool.or (has_evar a) (has_evar b) with
    | true => Control.backtrack_tactic_failure "found evars in goal terms"
    | false => reflexivity
    end
  end.

Check Core.wf_term_conv.
(*TODO: I think I should make sure this never errors, might
  be what's causing double-repeat issues*)
Ltac2 step_elab () :=
  lazy_match! goal with
  | [|- elab_lang nil _] => constructor
  | [|- elab_lang _ _] => Control.plus (fun () => apply elab_pf) (fun _ => constructor)
  | [|- elab_rule _ _ _] => constructor
  | [|- elab_ctx _ _ _] => constructor
  | [|- elab_args _ _ _ _ _ [::]] => apply elab_args_nil
  | [|- elab_args _ _ _ (?n::_) _ ((?n,?t)::_)] =>
      apply elab_args_cons_ex
  | [|- elab_args _ _ _ _ _ ((?n,?t)::_)] =>
      eapply elab_args_cons_im
  (* special case to force existentials to the empty list*)
  | [|- elab_subst _ _ _ (with_names_from [::] ?l) [::]] =>
        assert ($l = [::]) > [reflexivity | apply elab_subst_nil]
  | [|- elab_subst _ _ _ _ [::]] => apply elab_subst_nil
  | [|- elab_subst _ _ ((?n,?e)::_) ((?n,?ee)::_) ((?n,?t)::_)] =>
      apply elab_subst_cons_ex > [solve_fresh ()| | |]
  | [|- elab_subst _ _ _ ((?n,?ee)::_) ((?n,?t)::_)] =>
      eapply elab_subst_cons_im > [solve_fresh ()| | |]
  | [|- elab_sort _ _ _ _] => apply elab_sort_by'
  | [|- Core.le_args _ _ _ _ _] =>constructor
  (* TODO: tmp; try shelving any wfness side-conditions; do elab first*)
  | [|- Core.wf_args _ _ _ _] =>(*first [apply wf_args_no_conv_recognizes; vm_compute; reflexivity
                                      | apply Core.wf_args_cons
                                      | apply Core.wf_args_nil]*) Control.shelve()
  | [|- Core.wf_subst _ _ _ _] =>(*constructor*) Control.shelve()
  | [|- Core.wf_sort _ _ _] => (*first [apply wf_sort_no_conv_recognizes; vm_compute; reflexivity
                                     | apply Core.wf_sort_by']*) Control.shelve()
  | [|- Core.wf_term _ _ (Exp.var _) _] => (*(*TODO: potential eargerness here*)apply Core.wf_term_var*) Control.shelve()
  | [|- Core.wf_term _ _ ?t _] =>(*
    match (is_evar t) with
    | true => Control.shelve()
    | false => try (solve[apply wf_term_no_conv_recognizes; vm_compute; reflexivity])
    end*) Control.shelve()
    (*eapply Core.wf_term_conv> [ | eapply Core.wf_term_by' | ]*)
  | [|- elab_term _ _ (var _) _ _] =>
    eapply elab_term_conv > [apply elab_term_var; solve_in() |..]
  | [|- elab_term _ _ _ (Exp.var _) _] => 
    eapply elab_term_conv > [apply elab_term_var; solve_in() |..]
  | [|- elab_term _ _ (con _ _) _ _] => 
    eapply elab_term_conv > [apply elab_term_by' |..]
  | [|- elab_term _ _ _ (Exp.con _ _) _] => 
    eapply elab_term_conv > [apply elab_term_by' |..]
  | [|- elab_term _ _ ?e ?ee _] =>
    match Bool.and (is_evar e) (is_evar ee) with
    | true => Control.shelve()
    | false => ()
    end
  | [|- is_true((?n,?e)\in ?l)]=> 
      assert ($e = named_list_lookup $e $l $n); vm_compute; solve[auto]
  | [|- is_true (_ \in _)] => solve_in ()
  | [|- is_true (fresh _ _)] => solve_fresh ()
  | [|- is_true (_ \notin _)] => solve_fresh ()
  | [|- is_true (subseq _ _)] => vm_compute; reflexivity
  | [|- is_true true] => reflexivity
  | [|- len_eq _ _] => constructor  
  | [|- _ = _] => try (solve[reflexivity| cbv; f_equal])
  | [|- Core.le_term _ _ _ _ _]=>
    try (solve[apply Core.le_term_by_nameless; vm_compute; reflexivity
              | reflexivity_no_evars ()])
  | [|- Core.le_sort _ _ _ _]=>
    try (solve[apply Core.le_sort_by_nameless; vm_compute; reflexivity
              | reflexivity_no_evars()])
end.

Import Exp.Notations.
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
