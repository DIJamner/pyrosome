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
 Definition stlc_let :=
  [::
  [:> "G" : #"env",
      "A" : #"ty" %"G",
      "B" : #"ty" %"G",
      "e" : #"el" %"G" %"A",
      "body" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B")
      ----------------------------------------------- ("let beta")
      #"let" %"e" %"body" = #"app" (#"lambda" %"body")  %"e"
      : #"el" %"G" %"B"
     ];
  [:| "G" : #"env",
      "A" : #"ty" %"G",
      "B" : #"ty" %"G",
      "e" : #"el" %"G" %"A",
      "body" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"B")
      -----------------------------------------------
      #"let" "e" "body"  : #"el" %"G" %"B"
  ]]%irule++stlc.
  
Derive elab_stlc_let
       SuchThat (elab_lang stlc_let elab_stlc_let)
       As elab_stlc_let_pf.
Proof.
  (* Used for 2 reasons:
     1. because the order of arguments in elab_args_cons_ex is bad
        for this language at least
     2. to use recursion instead of repeat
   *)
  Ltac2 rec tac () :=
      simpl;
      match! goal with
      | [|- elab_args _ _ _ _ _ {{c }}] => step_elab(); Control.enter tac
      | [|- elab_args _ _ _ _ _ _] =>
        (Control.plus (fun ()=> apply elab_args_cons_ex')
                     (fun _ => step_elab())); Control.enter tac
      | [|- elab_term _ _ _ _ _] =>
        (Control.plus step_elab (fun _ => elab_term_by())); Control.enter tac
      | [|- _] => step_elab(); Control.enter tac
  end .
  tac().
Qed.
  

Instance elab_stlc_let_inst : Elaborated stlc_let :=
  {
  elaboration := elab_stlc_let;
  elab_pf := elab_stlc_let_pf;
  }.

(*
(* TODO: general-purpose lemma that macro-like languages
   like this can be compiled away
 *)
Definition compile_macro_sort (c:string) args : sort := scon c (map var args).

(*TODO:move helper somewhere; duped from CPS*)
Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).
Definition compile_macro
           (* macro components *)
           name e
           (c : string) (args : list string) : exp :=
    if c == name
    then e
    else con c (map var (lookup_args elab_stlc c)).
  
Derive elab_compile_macro
  SuchThat
  (forall target c name t args e eq_name (elab_macro elab_target : ARule.lang),
    let macro_ext :=
        [:: (eq_name,term_le c (con name (map var args)) e t);
        (name,term_rule c args t)]
    in
    let compiler := ICompilers.make_compiler compile_macro_sort
                                  (compile_macro name e)
                                  (strip_args (elab_macro++elab_target))
    in
    elab_lang target elab_target ->
    elab_lang (macro_ext ++ target) (elab_macro++elab_target) ->
    elab_preserving_compiler elab_target
                             compiler
                             (elab_compile_macro ...)
                             (elab_macro++elab_target))
    As compile_macro_preserving.
 *)

(*TODO: copied from CPS; should have definitive version *)
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
Ltac2 rec elab () :=
  simpl;
  lazy_match! goal with
  | [|- elab_lang nil _] => constructor; enter elab
  | [|- elab_lang _ _] => (Control.plus (fun () => apply elab_pf) (fun _ => constructor)); enter elab
  | [|- elab_rule _ _ _] => constructor;enter elab
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
  | [|- Core.wf_sort _ _ _] => (*first [apply wf_sort_no_conv_recognizes; vm_compute; reflexivity
                                     | apply Core.wf_sort_by']*) ()
  | [|- Core.wf_term _ _ (Exp.var _) _] => (*(*TODO: potential eargerness here*)apply Core.wf_term_var*) ()
  | [|- Core.wf_term _ _ ?t _] =>(*
    match (is_evar t) with
    | true => Control.shelve()
    | false => try (solve[apply wf_term_no_conv_recognizes; vm_compute; reflexivity])
    end*) ()
    (*eapply Core.wf_term_conv> [ | eapply Core.wf_term_by' | ]*)
  | [|- elab_term _ _ (var _) _ _] =>
    eapply elab_term_conv > [apply elab_term_var; solve_in() |enter elab ..]
  | [|- elab_term _ _ _ (Exp.var _) _] => 
    eapply elab_term_conv > [apply elab_term_var; solve_in() | enter elab ..]
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
      assert ($e = named_list_lookup $e $l $n); vm_compute; solve[auto]
  | [|- is_true (_ \in _)] => solve_in ()
  | [|- is_true (fresh _ _)] => solve_fresh ()
  | [|- is_true (_ \notin _)] => solve_fresh ()
  | [|- is_true (subseq _ _)] => vm_compute; reflexivity
  | [|- is_true true] => reflexivity
  | [|- len_eq _ _] => constructor;enter elab
  | [|- _ = _] => try (solve[reflexivity| cbv; f_equal])
  | [|- Core.le_term _ _ _ _ _]=>
    try (solve[apply Core.le_term_by_nameless; vm_compute; reflexivity
              | reflexivity_no_evars ()])
  | [|- Core.le_sort _ _ _ _]=>
    try (solve[apply Core.le_sort_by_nameless; vm_compute; reflexivity
              | reflexivity_no_evars()])
end.


Definition compile_let_sort (c:string) args : sort := scon c (map var args).
Arguments compile_let_sort c args/.

(*TODO:move helper somewhere; duped from CPS*)
Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [::] [::]) l n).


Definition compile_let (c : string) (args : list string) : exp :=
  if c == "let"%string
  then con "app" [:: var "e"; con "lambda" [:: var "body"]]
  else con c (map var (lookup_args elab_stlc c)).
Arguments compile_let c args /.

Derive elab_compile_let
       SuchThat (elab_preserving_compiler
                   elab_stlc
                   (make_compiler compile_let_sort
                                  compile_let
                                  (strip_args elab_stlc_let))
                   elab_compile_let
                   elab_stlc_let)
       As elab_compile_let_preserving.
Proof.
  
  simpl.
  repeat (match! goal with
  | [ |-  elab_preserving_compiler _ ((_,sort_case _ _)::_) _ _]=>
    apply preserving_compiler_sort'
  | [ |-  elab_preserving_compiler _ ((_,term_case _ _)::_) _ _]=>
    apply preserving_compiler_term'
  | [ |-  elab_preserving_compiler _ _ _ _]=>
    constructor
    |[|- wf_sort _ _ _] =>
     try (solve [apply wf_sort_no_conv_recognizes; vm_compute; reflexivity])
  | [|-_] => Control.enter elab
          end).
Qed.
