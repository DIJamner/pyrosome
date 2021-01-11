(*********************************************
Tactics for deriving well-formed languages
**********************************************)


Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Exp ARule.
From Named Require ICore.
Import ICore.IndependentJudgment.
Require Import String.

Require Import Named.Recognizers.
Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".


(* TODO: move to tactics*)


(* TODO: move*)
Definition id_subst : list string -> Exp.subst :=
  map (fun x => (x, Exp.var x)).

Lemma id_subst_exp_identity e args : Exp.exp_subst (id_subst args) e = e.
Admitted.
Lemma id_subst_sort_identity t args : Exp.sort_subst (id_subst args) t = t.
Admitted.

Lemma id_subst_fold x args : (x,Exp.var x)::(id_subst args) = id_subst (x::args).
Proof using.
  simpl; reflexivity.
Qed.

Lemma sort_subst_fold s n l
  : Exp.scon n (map (Exp.exp_subst s) l)
    = Exp.apply_subst s (Exp.scon n l).
Proof using .
  simpl; reflexivity.
Qed.

Ltac2 solve_in () :=
  solve [ vm_compute; reflexivity
        | repeat (rewrite in_cons);
          rewrite in_nil;
          rewrite Bool.orb_false_r;
          ltac1:(apply /eqP);
          reflexivity].

Ltac2 solve_fresh () := vm_compute; reflexivity.

(* Reduce size of language terms for smaller goals *)
Fixpoint nth_tail {A} (n: nat) (l : list A) : list A :=
  match n,l with
  | 0,_ => l
  | S_,[::]=> [::]
  | S n', _::l'=> nth_tail n' l'
  end.

Arguments nth_tail : simpl never.

(* TODO: put with nth_tail*)
Lemma nth_tail_nil {A} n : @nth_tail A n [::] = [::].
Proof.
  destruct n; simpl; reflexivity.
Qed.


Lemma nth_tail_S_cons {A} n (e:A) l : nth_tail n.+1 (e::l) = nth_tail n l.
Proof.
  reflexivity.
Qed.      

Lemma nth_tail_cons_eq {A} (a:A) l n l'
  : a::l = nth_tail n l' -> l = nth_tail n.+1 l'.
Proof.
  revert a l l'.
  induction n.
  {
    intros; destruct l';
      cbv[nth_tail] in*;
      inversion H; auto.
  }
  {
    intros; destruct l'.
    {
      cbv[nth_tail] in*;
        inversion H; auto.
    }
    {
      rewrite nth_tail_S_cons.
      rewrite nth_tail_S_cons in H.
      eauto.
    }
  }
Qed.


(*TODO: I think I should make sure this never errors, might
  be what's causing double-repeat issues*)
(* TODO: outdated; remove?
Ltac2 step_elab () :=
  lazy_match! goal with
  | [|- elab_lang nil _] => constructor
  | [|- elab_lang _ _] => Control.plus (fun () => apply elab_pf) (fun _ => constructor)
  | [tll : ARule.lang|- elab_rule ?l _ _] =>
    let tll := Control.hyp tll in
    (*TODO: precompute this? definitely at least needs simpl but maybe not here
    let n := Std.eval_vm None constr:(size $tll - size $l) in*)
    ltac1:(l tll|-change l with (nth_tail (size tll - size l) tll))
            (Ltac1.of_constr l) (Ltac1.of_constr tll);
    constructor
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
  | [|- Core.le_args _ _ _ _ _] =>constructor
  | [|- Core.wf_args _ _ _ _] =>first [apply wf_args_no_conv_recognizes; vm_compute; reflexivity
                                     | apply Core.wf_sort_by']
  | [|- Core.wf_subst _ _ _ _] =>constructor
  | [|- elab_sort _ _ _ _] => apply elab_sort_by'
  | [|- Core.wf_sort _ _ _] => first [apply wf_sort_no_conv_recognizes; vm_compute; reflexivity
                                     | apply Core.wf_sort_by']
  | [|- Core.wf_term _ _ (Exp.var _) _] => apply Core.wf_term_var
  | [|- Core.wf_term _ _ _ _] => try (apply wf_term_no_conv_recognizes; vm_compute; reflexivity)
  | [|- elab_term _ _ (var _) _ _] => apply elab_term_var; solve_in()
  | [|- elab_term _ _ _ (Exp.var _) _] => apply elab_term_var; solve_in()
  | [|- is_true((?n,?e)\in ?l)]=> 
      assert ($e = named_list_lookup $e $l $n); cbv(*vm_compute doesn't work*); solve[auto]
  | [|- is_true (_ \in _)] => solve_in ()
  | [|- is_true (fresh _ _)] => solve_fresh ()
  | [|- is_true (_ \notin _)] => solve_fresh ()
  | [|- is_true (subseq _ _)] => vm_compute; reflexivity
  | [|- is_true true] => reflexivity
  | [|- len_eq _ _] => constructor  
  | [|- _ = _] => try (solve[reflexivity| cbv; f_equal])
  | [|- Core.le_term _ _ _ _ _]=>
      try (solve[apply Core.le_term_by_nameless; vm_compute; reflexivity])
  | [|- Core.le_sort _ _ _ _]=>
      try (solve[apply Core.le_sort_by_nameless; vm_compute; reflexivity])
end.
*)

(* TODO: move to tactics or utils*)
Require Import Ltac2.Constr.
Ltac2 is_evar e :=
  match Unsafe.kind e with
  | Unsafe.Evar _ _ => true
  | _ => false
  end.

Ltac2 shelve_if b :=
  match b with
  | true => Control.shelve ()
  | false => ()
  end.

Ltac2 error_if b e :=
  match b with
  | true => Control.zero e
  | false => ()
  end.


(*_TODO: check if necessary anymore
Transparent get_rule_args.
Transparent get_rule_ctx.
*)

(*
Ltac2 elab_term_by ():=
    apply elab_term_by'; repeat(simpl;step_elab()).
*)

Require Import Ltac2.Constr.
(*
Ltac2 refine_elab pat :=
  let g := match! goal with
           | [|- elab_term _ _ _ ?g _] => g
           | [|- elab_sort _ _ _ ?g ] => g
           | [|- Core.wf_term _ _ ?g _] => g
           | [|- Core.wf_sort _ _ ?g] => g
           end in
  match Unsafe.kind g with
  | Unsafe.Evar n _ => Control.new_goal n > [| refine pat]
  | _ => ()
  end.

Ltac2 inst_elab pat :=
  let g := match! goal with
           | [|- elab_term _ _ ?g _ _] => g
           | [|- elab_sort _ _ ?g _ ] => g
           | [|- Core.wf_term _ ?g _ _] => g
           | [|- Core.wf_sort _ ?g _] => g
           end in
  match Unsafe.kind g with
  | Unsafe.Evar n _ => Control.new_goal n > [| refine pat]
  | _ => ()
  end.
*)

(*TODO: copied from CPS; should make this the definitive version *)
Require Import Recognizers.
Require Import Compilers.
Import Control.

(*was bugged: used first-class backtracking when it's not supposed to; plus is no good here*)
Ltac2 has_evar (c : constr) :=
  match case(fun()=> ltac1:(c|-has_evar c) (Ltac1.of_constr c)) with
  | Val _ => true
  | Err _ => false
  end.

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

(*TODO: prove / put in the right place
 *)
Definition get_rule_ctx r :=
  match r with
  | sort_rule c _
  | term_rule c _ _
  | sort_le c _ _
  | term_le c _ _ _ => c
  end.

Definition get_rule_args r :=
  match r with
  | sort_rule _ args
  | term_rule _ args _ => args
  | sort_le c _ _
  | term_le c _ _ _ => map fst c
  end.

Definition get_rule_sort r :=
  match r with
  | sort_rule _ _
  | sort_le _ _ _ => scon "ERR" [::]
  | term_rule _ _ t
  | term_le _ _ _ t => t
  end.

(* TODO: compute s from es? *)
Parameter wf_sort_by' : forall (n : string) (l : lang) (c : ctx) (s es : seq exp),
       let r := named_list_lookup (sort_rule [::] [::]) l n in
       let c' := get_rule_ctx r in
       let args := get_rule_args r in
       (n, sort_rule c' args) \in l -> wf_args l c s args es c' -> wf_sort l c (scon n s).

(* TODO: compute s from es? *)
Parameter wf_term_by'
     : forall (n : string) (l : lang) (c : ctx) (s es : seq exp) (t : sort),
       let r := named_list_lookup (sort_rule [::] [::]) l n in
       let c' := get_rule_ctx r in
       let t' := get_rule_sort r in
       let args := get_rule_args r in
       (n, term_rule c' args t') \in l ->
       wf_args l c s args es c' -> t = t' [/with_names_from c' s /] -> wf_term l c (con n s) t.


(* TODO: put in right place*)
Fixpoint make_compiler
           (cmp_sort : string -> list string -> sort)
           (cmp_exp : string -> list string -> exp)
           (l : Rule.lang) : compiler :=
  match l with
  | (n,Rule.sort_rule c)::l' =>
    (n,sort_case (map fst c) (cmp_sort n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,Rule.term_rule c _)::l' => (n,term_case (map fst c) (cmp_exp n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,_)::l' => 
    (make_compiler cmp_sort cmp_exp l')
  | [::] => [::]
  end.

Lemma preserving_compiler_term' target
  : forall cmp l n c args e t case_args,
    case_args = map fst c ->
    preserving_compiler target cmp l ->
    wf_term target (compile_ctx cmp c) e (compile_sort cmp t) ->
    preserving_compiler target
                             ((n, term_case case_args e)::cmp)
                             ((n,term_rule c args t) :: l).
Proof using .
  intros.
  rewrite H.
  constructor; eauto.
Qed.


Lemma preserving_compiler_sort' target
  : forall cmp l n c args t case_args,
    case_args = map fst c ->
    preserving_compiler target cmp l ->
    wf_sort target (compile_ctx cmp c) t ->
    preserving_compiler target
                             ((n, sort_case case_args t)::cmp)
                             ((n,ARule.sort_rule c args ) :: l).
Proof using .
  intros.
  rewrite H.
  constructor; eauto.
Qed.

Ltac2 elab  (sublang_wf_pf : constr) (le_tac : unit -> unit) :=
  let rec elab () :=
      simpl;
(*TODO: try? balance partial completion w/ error reporting
  maybe use plus w/ error printing?
 *)
  try (lazy_match! goal with
  | [|- wf_lang nil] => constructor; enter elab
  | [|- wf_lang _] => (Control.plus (fun () => exact $sublang_wf_pf) (fun _ => constructor)); enter elab
  | [tll : ARule.lang|- wf_rule ?l ?r] =>
    let tll := Control.hyp tll in
    (*TODO: precompute this? definitely at least needs simpl but maybe not here
    let n := Std.eval_vm None constr:(size $tll - size $l) in*)
    (*TODO: change instead of changewith for performance*)
    ltac1:(l tll|-change l with (nth_tail (size tll - size l) tll))

            (Ltac1.of_constr l) (Ltac1.of_constr tll);
    constructor; enter elab
  | [|- wf_ctx _ _] => constructor;enter elab
  | [|- wf_args _ _ _ _ _ [::]] => apply wf_args_nil;enter elab
  | [|- wf_args _ _ _ (?n::_) _ ((?n,?t)::_)] =>
      apply wf_args_cons_ex;enter elab
  | [|- wf_args _ _ _ _ _ ((?n,?t)::_)] =>
    eapply wf_args_cons_im;enter elab
                                 (*TODO: handle substs
  (* special case to force existentials to the empty list*)
  | [|- elab_subst _ _ _ (with_names_from [::] ?l) [::]] =>
        assert ($l = [::]) > [reflexivity | apply elab_subst_nil;enter elab]
  | [|- elab_subst _ _ _ _ [::]] => apply elab_subst_nil;enter elab
  | [|- elab_subst _ _ ((?n,?e)::_) ((?n,?ee)::_) ((?n,?t)::_)] =>
      apply elab_subst_cons_ex > [solve_fresh ()| | |]; enter elab
  | [|- elab_subst _ _ _ ((?n,?ee)::_) ((?n,?t)::_)] =>
      eapply elab_subst_cons_im > [solve_fresh ()| | |]; enter elab
*)
   | [|- wf_sort _ _ _] => eapply wf_sort_by'; enter elab
   (* TODO: port to ICore..wf_sort?                                                 
  | [|- Core.wf_sort ?l ?c ?t] =>
    match has_evar '(Core.wf_sort $l $c $t) with
    | true => ()
    | false => try (apply wf_sort_no_conv_recognizes; vm_compute; reflexivity)
    end; apply wf_sort_by'; enter elab
    
  | [|- Core.wf_term _ _ (Exp.var _) _] =>
    eapply Core.wf_term_conv > [apply Core.wf_term_var; elab() |enter elab ..]
  | [|- Core.wf_term ?l ?c ?e ?t] =>
    match has_evar '(Core.wf_term $l $c $e $t) with
    | true => ()
    | false => apply wf_term_no_conv_recognizes; vm_compute; reflexivity
    end
    (*eapply Core.wf_term_conv> [ | eapply Core.wf_term_by' | ]*)*)
  | [|- wf_term _ _ (var _) _] =>
    ()(*eapply wf_term_conv > [|apply wf_term_var; elab() |enter elab ..]>[elab()|..]*)
  | [|- wf_term _ _ (con _ _) _] => 
    eapply wf_term_conv > [|eapply wf_term_by';enter elab | enter elab ..]>[elab()|..]
  | [|- wf_term _ _ ?e _] =>
    match is_evar e with
    | true => ()
    | false => Message.print (Message.concat
                                   (Message.of_string "Encountered unprocessable term ")
                                   (Message.of_constr e))
    end
  | [|- is_true((?n,?e)\in ?l)]=>
    (*TODO: this can be improved a bit*)
      assert ($e = named_list_lookup $e $l $n); cbv; solve[auto]
  | [|- is_true (_ \in _)] => solve_in ()
  | [|- is_true (fresh _ _)] => solve_fresh ()
  | [|- is_true (_ \notin _)] => solve_fresh ()
  | [|- is_true (subseq _ _)] => vm_compute; reflexivity
  | [|- is_true true] => reflexivity
  | [|- len_eq _ _] => constructor;enter elab
  | [|- _ = _] => try (solve[reflexivity| cbv; f_equal])
  | [|- le_term _ _ _ _ _]=>
    try (first[ reflexivity_no_evars () | progress le_tac ; enter elab])
  | [|- le_sort _ _ _ _]=>
  (* TODO: fix up: try (first[  reflexivity_no_evars() | progress le_tac; enter elab])*)
    progress le_tac; enter elab
  | [ |-  preserving_compiler _ ((_,sort_case _ _)::_) _ _]=>
    apply preserving_compiler_sort';enter elab
  | [ |-  preserving_compiler _ ((_,term_case _ _)::_) _ _]=>
    apply preserving_compiler_term';enter elab
  | [ |-  preserving_compiler _ _ _ _]=>
    constructor;enter elab
  | [ |- ?g] =>
    (*Message.print (Message.concat
                     (Message.of_string "Discovered unprocessable goal: ")
                     (Message.of_constr g))*)()
 (*  Control.backtrack_tactic_failure "could not process goal"*)
end) in elab ().

Ltac2 easy_le_tac() :=
  first[ reflexivity
        | apply Core.le_term_by_nameless; vm_compute; reflexivity
        | apply Core.le_sort_by_nameless; vm_compute; reflexivity].
