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

(*TODO: move statement to monad file *)
Lemma monad_bind_ret {Q A B} (f : A -> interactive Q B) (a : A)
  : Mbind f (Mret a) = f a.
Proof.
  cbn.
  unfold interact_bind.
  unfold interact_ret.
  reflexivity.
Qed.

(*weakened associativity
  to avoid using extensionality
*)
Lemma Mbind_assoc Q A B C
      (f : A -> interactive Q B)
      (g : B -> interactive Q C)
      a
      inputs
    : Mbind g (Mbind f a) inputs
      = Mbind (fun x => Mbind g (f x)) a inputs.
Proof.
  cbn.
  unfold interact_bind.
  case ain: (a inputs); break; reflexivity.
Qed.
  
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

Definition focus {A} (a:A) := a.
Opaque focus.
Arguments focus : simpl never.

Global Opaque Mbind Mret.

(*TODO: replace one interactive with this*)
Ltac process_interactive :=
  lazymatch goal with
  | [tl : list ?Q |-
     context ctx[(Mbind ?f (focus ask) ?tl)]] =>
    let hd := fresh "hd" in evar (hd : Q);
    let tl' := fresh "tl" in evar (tl' : list Q);
    instantiate_term tl (hd::tl');
    let x := context ctx [focus (f hd tl')]in
    change x
  | [tl : list ?Q |-
     context ctx[(Mbind ?f (focus (ask_for ?d)) ?tl)]] =>
    let hd := fresh "hd" in evar (hd : Q);
    let tl' := fresh "tl" in evar (tl' : list Q);
    instantiate_term tl (hd::tl');
    let x := context ctx [focus (f hd tl')]in
    change x;
    pose proof (shouldsatisfy hd d)
  | [tl : list ?Q |-
     context ctx
        [(Mbind ?f (focus (ask_for_satisfying ?d ?p)) ?tl)]] =>
    let hd := fresh "hd" in evar (hd : Q);
    let tl' := fresh "tl" in evar (tl' : list Q);
    instantiate_term tl (hd::tl');
    let x := context ctx [focus (f hd tl')]in
    change x;
    pose proof (shouldsatisfy hd d);
    assert (p hd)
  | [tl : list ?Q |-
     context ctx
        [(Mbind ?f (focus (ask_satisfying ?p)) ?tl)]] =>
    let hd := fresh "hd" in evar (hd : Q);
    let tl' := fresh "tl" in evar (tl' : list Q);
    instantiate_term tl (hd::tl');
    let x := context ctx [focus (f hd tl')]in
    change x; assert (p hd)
  | [|- context ctx[(Mret ?a ?tl)]] =>
    let x := context ctx [Some (a,tl)] in
    change x
   | [|- context ctx [Mbind ?f (focus (Mret ?a))] ]=>
      let x := context ctx [focus (f a)] in
      change x
   | [|- context [Mbind _ (Mbind _ _) _] ]=>
      rewrite Mbind_assoc
   | [|- context ctx [focus ?comp] ]=>
    let comp' := eval hnf in comp in
    lazymatch comp' with
    | Mbind ?f (Mret ?a) ?tl =>
      let x := context ctx [focus (f a tl)] in
      change x
    | Mbind ?f ?cmp ?tl =>
      let x := context ctx [Mbind f (focus cmp) tl] in
      change x
             
    | Mbind ?f (Mret ?a) =>
      let x := context ctx [focus (f a)] in
      change x
    | Mbind ?f ?cmp =>
      let x := context ctx [Mbind f (focus cmp)] in
      change x
    | Mret ?a =>  
      let x := context ctx [focus (Mret a)] in
      change x
    | fun=> None =>
      fail "Reached monad failure:" comp
    end
  end.


Ltac exit_interactive :=
  match goal with
    [|- omap fst (focus (Some (?cmp,?intl))) = Some ?res /\ ?P ?res] =>
    instantiate_term intl open_constr:([::]);
    unfold res;
    split;[ cbn; reflexivity|]; clear res
  end.

Ltac enter_interactive :=
  match goal with
  [ |- @find_result_such_that ?Q ?A ?ma ?p] =>
  let tl := fresh "tl" in
  evar (tl : list Q);
  exists tl;
  let res := fresh "res" in
  evar (res : A);
  exists res;
  change (omap fst (focus (ma tl)) = Some res /\ p res)
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
  {
    instantiate_term hd 0.
    done.
  }
  instantiate_term hd0 7.
  repeat process_interactive.
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
    Fixpoint elab_args_all_implicit {A} (debug : A) (c:ctx) c'
      : interactive pf (list pf) :=
      match c' with
      | [::] => do ret [::]
      | (an,t)::c'' =>
        (*TODO: decide the right way to ask for this:
          implicit or elaborated, conv'ing to t or not
         *)
        do ps <- elab_args_all_implicit debug c c'';
           s <- lift (synth_wf_args (synth_wf_term l) ps c c'');
           e <- ask_for_satisfying
                  (c,debug, " argument: " ++ an)%string
                  (fun pf => exists e,
                       check_wf_term l c e t[/with_names_from c'' s/] pf);
           ret (e::ps)
    end.
    
    Fixpoint elab_args {A} (debug : A) c s args c' {struct s}
      : interactive pf (list pf) :=
      match args, s with
      | [::], [::] => elab_args_all_implicit debug c c'
      | [::], _ => Mfail
      | an::args', [::] => Mfail
      | an::args', e::s' =>
        let elab_implicits :=
            fix elab_implicits c' :=
              match c' with
              | [::] => Mfail
              | (an',t)::c'' =>
                if an' == an then
                  do ps <- elab_args debug c s' args' c'';
                     s <- lift (synth_wf_args (synth_wf_term l) ps c c'');
                     pe <- elab_term c e t[/with_names_from c'' s/];
                     ret (pe::ps)
                else 
                (*TODO: decide the right way to ask for this:
                  implicit or elaborated, conv'ing to t or not
                 *)
                do ps <- elab_implicits c'';
                   s <- lift (synth_wf_args (synth_wf_term l) ps c c'');
                   e <- ask_for_satisfying
                        (c,debug,  " argument: " ++ an)%string
                        (fun pf => exists e,
                             check_wf_term l c e
                                 t[/with_names_from c'' s/] pf);
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
      es <- elab_args elab_term e c s args c';
      s <- lift (synth_wf_args (synth_wf_term l) es c c');
      cv <- ask_satisfying (check_le_sort l c t'[/with_names_from c' s/] t);
     ret (conv cv (pcon name es))
  end.

  
  Definition elab_sort c t : interactive pf pf :=
    match t with
    | scon name s =>
    do (sort_rule c' args)
         <?- lift (named_list_lookup_err l name);
       es <- elab_args elab_term t c s args c';
       ret (pcon name es)
    end.

  Fixpoint elab_ctx c : interactive pf (named_list pf) :=
    match c with
    | [::] => do ret [::]
    | (n,t)::c' =>
      do pt <- elab_sort c' t; 
         pc' <- elab_ctx c';
         ret (n,pt)::pc'
    end.

  Definition elab_rule r : interactive pf rule_pf :=
    match r with
    | sort_rule c args =>
      do cp <- elab_ctx c;
         ret sort_rule_pf cp args
    | term_rule c args t =>
      do cp <- elab_ctx c;
         tp <- elab_sort c t;
         ret term_rule_pf cp args tp
    | sort_le c t1 t2 =>
      do cp <- elab_ctx c;
         p1 <- elab_sort c t1;
         p2 <- elab_sort c t2;
         ret sort_le_pf cp p1 p2
    | term_le c e1 e2 t =>
      do cp <- elab_ctx c;
         pe1 <- elab_term c e1 t;
         pe2 <- elab_term c e2 t;
         tp <- elab_sort c t;
         ret term_le_pf cp pe1 pe2 tp
    end.      
  
End WithLang.

Fixpoint elab_lang l : interactive pf (named_list rule_pf) :=
  match l with
  | [::] => do ret [::]
  | (n,r)::l' =>
    do pr <- elab_rule l' r;
       pl' <- elab_lang l';
       ret (n,pr)::pl'
  end.              

Definition find_wf_lang_elaboration (l : lang) :=
  find_result_such_that (elab_lang l) (fun pl => Some l = synth_wf_lang pl).
