Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils Monad.
From Named Require Import Exp ARule Matches ImCore Pf.

(*
Inductive interactive : Type -> Type :=
| interact_recieve B : (pf -> interactive B) -> interactive B
| interact_ret A : A -> interactive A
| interact_fail A : interactive A.
 *)
  

Definition interactive Q A : Type :=
  list Q (*list of ordered inputs*) ->
  (*partial fn returning remaining inputs*)
  option (A * list Q).

Definition interact_bind Q A B
           (f : A -> interactive Q B)
           (ma : interactive Q A) : interactive Q B :=
  fun inputs =>
    match ma inputs with
    | Some (a, inputs') =>
      f a inputs'
    | None => None
    end.

Definition interact_ret Q A a : interactive Q A :=
  fun inputs => Some (a,inputs).

Definition ask {Q} : interactive Q Q :=
  fun inputs =>
    match inputs with
    | q::inputs' =>
      Some (q,inputs')
    | [::] => None
    end.


Definition ask_for {D} (data:D) {Q} : interactive Q Q :=
  fun inputs =>
    match inputs with
    | q::inputs' =>
      Some (q,inputs')
    | [::] => None
    end.


Definition ask_satisfying {Q} (p : Q -> Prop) : interactive Q Q :=
  fun inputs =>
    match inputs with
    | q::inputs' =>
      Some (q,inputs')
    | [::] => None
    end.


Definition ask_for_satisfying
           {D} (data:D)
           {Q} (p : Q -> Prop) : interactive Q Q :=
  fun inputs =>
    match inputs with
    | q::inputs' =>
      Some (q,inputs')
    | [::] => None
    end.

Definition ask_satisfying_checked {Q} (p : Q -> bool)
  : interactive Q Q :=
  fun inputs =>
    match inputs with
    | q::inputs' =>
      if p q then Some (q,inputs') else None
    | [::] => None
    end.

Instance interactive_monad Q : Monad (interactive Q) :=
  {
  Mret := @interact_ret Q;
  Mbind := @interact_bind Q;
  Mfail := fun _ _ => None
  }.                     


Definition find_result_such_that
           {Q} {A}
           (ma : interactive Q A)
           (P : A -> Prop) : Prop :=
  exists (inputs : list Q) res,
    omap fst (ma inputs) = Some res
    /\ P res.

Arguments Mbind : simpl never.
Arguments Mret : simpl never.


Inductive ShouldSatisfy {A} {D} (var : A) (data : D) : Prop :=
  shouldsatisfy.

(*Note: doesn't work if tl is in an assumption *)
Ltac instantiate_term tm vl :=
  (try lazymatch goal with
         [H : ShouldSatisfy tm _|-_] =>
         clear H
       end);
    let H := fresh in 
    assert (tm = vl) as H; [cbv; reflexivity|];
    rewrite ?H; clear H tm.

Ltac coerce_input_to_cons tl :=
  let hd := fresh "hd" in evar (hd : nat);
  let tl' := fresh "tl" in evar (tl' : list nat);
  instantiate_term tl (hd::tl').  

Ltac process_interactive :=
 lazymatch goal with
  | [|- context ctx[(Mbind ?f ask ?tl)]] =>
    let hd := fresh "hd" in evar (hd : nat);
    let tl' := fresh "tl" in evar (tl' : list nat);
    instantiate_term tl (hd::tl');
    let cmp := eval cbn beta in (f hd tl') in
    let x := context ctx [cmp]in
    change x
  | [|- context ctx[(Mbind ?f (ask_for ?d) ?tl)]] =>
    let hd := fresh "hd" in evar (hd : nat);
    let tl' := fresh "tl" in evar (tl' : list nat);
    instantiate_term tl (hd::tl');
    let cmp := eval cbn beta in (f hd tl') in
    let x := context ctx [cmp]in
    change x;
    pose proof (shouldsatisfy hd d)
  | [|- context ctx[(Mbind ?f (ask_satisfying ?p) ?tl)]] =>
    let hd := fresh "hd" in evar (hd : nat);
    let tl' := fresh "tl" in evar (tl' : list nat);
    instantiate_term tl (hd::tl');
    let cmp := eval cbn beta in (f hd tl') in
    let x := context ctx [cmp]in
    change x; assert (p hd)
  | [|- context ctx[(Mret ?a ?tl)]] =>
    let x := context ctx [Some (a,tl)] in
    change x
 end.

Ltac exit_interactive :=
  match goal with
    [|- omap fst (Some (?cmp,?intl)) = Some ?res /\ ?P ?res] =>
    instantiate_term intl open_constr:([::]);
    unfold res;
    split;[ cbn; reflexivity|]; clear res
  end.

Ltac enter_interactive :=
  unfold find_result_such_that;
  match goal with
  [ |- exists _ (_:?A),_] =>
  let tl := fresh "tl" in
  evar (tl : list nat);
  exists tl;
  let res := fresh "res" in
  evar (res : A);
  exists res
  end.


(* example *)
Local Definition ask_and_add : interactive nat nat :=
  do a <- ask_satisfying Nat.even;
     b <- ask_for "second num"%string;
     ret (a + b)%nat.

Goal find_result_such_that ask_and_add (eq 7).
  unfold ask_and_add.
  enter_interactive.
  repeat process_interactive.
  instantiate_term hd 0.
  done.
  instantiate_term hd0 7.
  exit_interactive.
  reflexivity.
Qed.

(*TODO: move generic version to monad file*)
Definition lift {Q A} (oa : option A) : interactive Q A :=
  match oa with
  | Some x => do ret x
  | None => Mfail
  end.


             
(* Pf-specific code; todo: separate file? *)

(*TODO: put in Pf.v?*)
Definition check_le_sort l c t t' pf :=
  Some(t',t) = synth_le_sort l (synth_le_term l) pf c.

Definition check_wf_term l c e t pf :=
  Some(t,e) = synth_wf_term l pf c.

Section WithLang.
  Context (l : lang).

  Section InnerLoop.
    Context (elab_term : ctx -> exp -> sort -> interactive pf pf).

    (*TODO*)
    
    (* separate for termination purposes*)
    Fixpoint elab_args_all_implicit (c:ctx) name c'
      : interactive pf (list pf) :=
      match c' with
      | [::] => do ret [::]
      | (an,t)::c'' =>
        (*TODO: decide the right way to ask for this:
          implicit or elaborated, conv'ing to t or not
         *)
        do ps <- elab_args_all_implicit c name c'';
           s <- lift (synth_wf_args (synth_wf_term l) ps c c');
           e <- ask_for_satisfying
                  (name ++ " argument: " ++ an)%string
                  (fun pf => exists e,
                       check_wf_term l c e t[/with_names_from c' s/] pf);
           ret (e::ps)
    end.
    
    Fixpoint elab_args c s args name c' {struct s}
      : interactive pf (list pf) :=
      match args, s with
      | [::], [::] => elab_args_all_implicit c name c'
      | [::], _ => Mfail
      | an::args', [::] => Mfail
      | an::args', e::s' =>
        let elab_implicits :=
            fix elab_implicits c' :=
              match c' with
              | [::] => Mfail
              | (an',t)::c'' =>
                if an' == an then
                  do ps <- elab_args c s' args' name c'';
                     s <- lift (synth_wf_args (synth_wf_term l) ps c c'');
                     pe <- elab_term c e t[/with_names_from c'' s/];
                     ret (pe::ps)
                else 
                (*TODO: decide the right way to ask for this:
                  implicit or elaborated, conv'ing to t or not
                 *)
                do ps <- elab_implicits c'';
                   s <- lift (synth_wf_args (synth_wf_term l) ps c c');
                   e <- ask_for_satisfying
                        (name ++ " argument: " ++ an)%string
                        (fun pf => exists e,
                             check_wf_term l c e
                                 t[/with_names_from c' s/] pf);
                   ret (e::ps)
              end in
    elab_implicits c'
    end.
  End InnerLoop.   
        
  Fixpoint elab_term c e t : interactive pf pf :=
    match e with
    | var x =>
      do t' <- lift (named_list_lookup_err c x);
       cv <- ask_satisfying (check_le_sort l c t' t);
       ret (conv cv (pvar x))
  | con name s =>
    do (term_rule c' args t')
         <?- lift (named_list_lookup_err l name);
      es <- elab_args elab_term c s args name c';
      s <- lift (synth_wf_args (synth_wf_term l) es c c');
      cv <- ask_satisfying (check_le_sort l c t'[/with_names_from c' s/] t);
     ret (conv cv (pcon name es))
  end.

  
  Fixpoint elab_sort c t : interactive pf pf :=
    match t with
    | scon name s =>
    do (sort_rule c' args)
         <?- lift (named_list_lookup_err l name);
       es <- elab_args elab_term c s args name c';
       ret (pcon name es)
    end.
  
