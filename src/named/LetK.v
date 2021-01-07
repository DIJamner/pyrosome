Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp Core.
From Named Require Import IExp IRule ICore ICompilers Subst STLC Tactics.
Import Exp.Notations.
Import IExp.Notations IRule.Notations ARule.Notations.
Require Import String.


Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

Require Import STLC_bot.

(*TODO: copied from Let.v. Deal with this*)
 Lemma elab_args_cons_ex' l c : forall s args (es:list Exp.exp) c' name e ee t,
    fresh name c' ->
    (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
    elab_args l c s args es c' ->
    (* TODO: some langs want this first, some want it later.
       Which is better?*)
    elab_term l c e ee (Exp.apply_subst (with_names_from c' es) t) ->
    Core.wf_sort (strip_args l) c' t ->
    elab_args l c (e::s) (name::args) (ee::es) ((name,t)::c').
 Proof.
   eauto with judgment.
 Qed.
(* TODO: let/k? *)
 Definition stlc_letk :=
  [::
  [:> "G" : #"env",
      "A" : #"ty" %"G",
      "e" : #"el" %"G" (#"->" (#"->" %"A" #"bot") #"bot"),
      "body" : #"el" (#"ext" %"G" %"A") #"bot"
      ----------------------------------------------- ("let beta")
      #"let" %"e" %"body" = #"app" %"e" (#"lambda" %"body")
      : #"el" %"G" #"bot"
     ];
  [:| "G" : #"env",
      "A" : #"ty" %"G",
      "e" : #"el" %"G" (#"->" (#"->" %"A" #"bot") #"bot"),
      "body" : #"el" (#"ext" %"G" %"A") #"bot"
      -----------------------------------------------
      #"let" "e" "body"  : #"el" %"G" #"bot"
  ]]%irule++stlc_bot.
  
Derive elab_stlc_letk
       SuchThat (elab_lang stlc_letk elab_stlc_letk)
       As elab_stlc_letk_pf.
Proof.
  repeat (elab easy_le_tac);
    repeat (elab easy_le_tac).
  simpl in *.
  symmetry.
  eapply (@Core.le_sort_refl' "el"%string);
    repeat (elab easy_le_tac).
  eapply (@Core.le_term_by' "bot_subst"%string);
    repeat (elab easy_le_tac).
Qed.
  

Instance elab_stlc_let_inst : Elaborated stlc_letk :=
  {
  elaboration := elab_stlc_letk;
  elab_pf := elab_stlc_letk_pf;
  }.


(*TODO: copied from Tactics; should haveuse definitive version *)
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

(*TODO: I think I should make sure this never errors, might
  be what's causing double-repeat issues*)
Import Control.
Ltac2 elab_true := elab.
Ltac2 rec elab () :=
  simpl;
  match! goal with
  | [|- elab_lang nil _] => constructor; enter elab
  | [|- elab_lang _ _] => (Control.plus (fun () => apply elab_pf) (fun _ => constructor)); enter elab
  | [tll : ARule.lang|- elab_rule ?l _ _] =>
    let tll := Control.hyp tll in
    (*TODO: precompute this? definitely at least needs simpl but maybe not here
    let n := Std.eval_vm None constr:(size $tll - size $l) in*)
    ltac1:(l tll|-change l with (nth_tail (size tll - size l) tll))
            (Ltac1.of_constr l) (Ltac1.of_constr tll);
    constructor; enter elab
  | [|- elab_ctx _ _ _] => constructor;enter elab
  | [|- elab_args _ _ _ _ _ [::]] => apply elab_args_nil;enter elab
  | [|- elab_args _ _ _ (?n::_) _ ((?n,?t)::_)] =>
      apply elab_args_cons_ex;enter elab
  | [|- elab_args _ _ _ _ _ ((?n,?t)::_)] =>
      eapply elab_args_cons_im;enter elab
  (* special case to force existentials to the empty list*)
  | [|- elab_subst _ _ _ (with_names_from [::] ?l) [::]] =>
        assert ($l = [::]) > [reflexivity | apply elab_subst_nil;enter elab]
  | [|- elab_subst _ _ _ _ [::]] => apply elab_subst_nil;enter elab
  | [|- elab_subst _ _ ((?n,?e)::_) ((?n,?ee)::_) ((?n,?t)::_)] =>
      apply elab_subst_cons_ex > [solve_fresh ()| | |]; enter elab
  | [|- elab_subst _ _ _ ((?n,?ee)::_) ((?n,?t)::_)] =>
      eapply elab_subst_cons_im > [solve_fresh ()| | |]; enter elab
  | [|- elab_sort _ _ _ _] => apply elab_sort_by'; enter elab
  | [|- Core.le_args _ _ _ _ _] =>constructor; enter elab
  (* TODO: tmp; try shelving any wfness side-conditions; do elab first*)
  | [|- Core.wf_args _ _ _ _] =>(*first [apply wf_args_no_conv_recognizes; vm_compute; reflexivity
                                      | apply Core.wf_args_cons
                                      | apply Core.wf_args_nil]*)()
  | [|- Core.wf_subst _ _ _ _] =>(*constructor*) ()
  | [|- Core.wf_sort ?l ?c ?t] =>
    (*time: mean ~0.03 high ~0.3*)
    match Bool.or (has_evar l) (Bool.or (has_evar c) (has_evar t)) with
    | true => ()
    | false => apply wf_sort_no_conv_recognizes; vm_compute; reflexivity
    end
  | [|- Core.wf_term _ _ (Exp.var _) _] =>
    eapply Core.wf_term_conv > [apply Core.wf_term_var; solve_in() |enter elab ..]
  | [|- Core.wf_term ?l ?c ?e ?t] =>
    match has_evar '(Core.wf_term $l $c $e $t) with
    | true => ()
    | false => apply wf_term_no_conv_recognizes; vm_compute; reflexivity
    end
    (*eapply Core.wf_term_conv> [ | eapply Core.wf_term_by' | ]*)
  | [|- elab_term _ _ (var _) _ _] =>
    eapply elab_term_conv > [apply elab_term_var; solve_in() |enter elab ..]
  | [|- elab_term _ _ _ (Exp.var _) _] =>
                 (*
TODO: no speedup vs this;
maybe could assrt wf ctx to avoid wf sort assumptions?
eapply elab_term_conv > [apply elab_term_var; solve_in() | enter elab ..]*)
                  apply elab_term_conv_var ; enter elab 
  | [|- elab_term _ _ (con _ _) _ _] => 
    eapply elab_term_conv > [apply elab_term_by';enter elab | enter elab ..]
  | [|- elab_term _ _ _ (Exp.con _ _) _] => 
    eapply elab_term_conv > [apply elab_term_by';enter elab | enter elab ..]
  | [|- elab_term _ _ ?e ?ee _] =>
    match Bool.and (is_evar e) (is_evar ee) with
    | true => ()
    | false => ()
    end
  | [|- is_true((?n,?e)\in ?l)]=> 
      assert ($e = named_list_lookup $e $l $n); cbv; solve[auto]
  | [|- is_true (_ \in _)] => solve_in ()
  | [|- is_true (fresh _ _)] => solve_fresh ()
  | [|- is_true (_ \notin _)] => solve_fresh ()
  | [|- is_true (subseq _ _)] => vm_compute; reflexivity
  | [|- is_true true] => reflexivity
  | [|- len_eq _ _] => constructor;enter elab
  | [|- _ = _] => try (solve[reflexivity| cbv; f_equal])
  | [|- Core.le_term _ _ _ _ _]=>
    (*time: mean ~0.02 high ~0.3*)
    try (solve[apply Core.le_term_by_nameless; vm_compute; reflexivity
              | reflexivity_no_evars ()])
  | [|- Core.le_sort _ _ _ _]=>
    (*time: mean ~0.3 high ~0.5*)
    try (solve[apply Core.le_sort_by_nameless; vm_compute; reflexivity
              | reflexivity_no_evars()])
  | [ |-  elab_preserving_compiler _ ((_,sort_case _ _)::_) _ _]=>
    apply preserving_compiler_sort';enter elab
  | [ |-  elab_preserving_compiler _ ((_,term_case _ _)::_) _ _]=>
    apply preserving_compiler_term';enter elab
  | [ |-  elab_preserving_compiler _ _ _ _]=>
    constructor;enter elab
end.


Definition compile_letk_sort (c:string) args : sort := scon c (map var args).
Arguments compile_letk_sort c args/.

(*TODO:move helper somewhere; duped from CPS*)
Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).


Definition compile_letk (c : string) (args : list string) : exp :=
  if c == "let"%string
  then con "app" [:: con "lambda" [:: var "body"]; var "e"]
  else con c (map var (lookup_args elab_stlc c)).
Arguments compile_letk c args /.

Derive elab_compile_letk
       SuchThat (elab_preserving_compiler
                   elab_stlc_letk
                   (make_compiler compile_letk_sort
                                  compile_letk
                                  (strip_args elab_stlc_letk))
                   elab_compile_letk
                   elab_stlc_letk)
       As elab_compile_letk_preserving.
Proof.
  (* TODO: use Tactics.elab easy_le_tac.*)
  repeat (elab ()).
  {
    eapply le_sort_refl';
      repeat (elab_true (fun()=>())).
    symmetry.
    eapply (@le_term_by' "bot_subst"%string);
      repeat (elab_true easy_le_tac).
  }
Qed.
