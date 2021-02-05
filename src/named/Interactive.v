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

(*TODO: this is just itrees with failure, but not coinductive; actually use the library?
*)
Inductive interactive (E : Type -> Type) A : Type :=
| iret (a:A)
| ifail
| itau (i : interactive E A)
| iask {D} (d:E D) (k : D -> interactive E A).

Arguments iret {E A}.
Arguments ifail {E A}.
Arguments itau {E A}.
Arguments iask {E A D} d k.        

Fixpoint ibind {E A B} (f : A -> interactive E B) (ma : interactive E A) : interactive E B :=
  match ma with
  | iret a => f a
  | ifail => ifail
  | itau i => itau (ibind f i)
  | iask _ d k => iask d (fun q => ibind f (k q))
  end.
Arguments ibind {E A B} f !ma/.

(* fixes the input q when able.
   Note: may add itaus
 *)
Fixpoint maybe_handle {E A}
           (handler : forall D, E D -> option D)
           (ma : interactive E A) : interactive E A :=
  match ma with
  | iret a => iret a
  | ifail => ifail
  | itau i => itau (maybe_handle handler i)
  | iask D d k =>
    match handler D d with
    | Some q => itau (maybe_handle handler (k q))
    | None => iask d k
    end
  end.

Fixpoint handle {E A}
           (handler : forall D, E D -> D)
           (ma : interactive E A) : interactive (fun=>void) A :=
  match ma with
  | iret a => iret a
  | ifail => ifail
  | itau i => itau (handle handler i)
  | iask D d k => itau (handle handler (k (handler D d)))
  end.

Fixpoint handle_idx {E A}
           (handler : forall D, nat -> E D -> D)
           (ma : interactive E A) n : interactive (fun=>void) A :=
  match ma with
  | iret a => iret a
  | ifail => ifail
  | itau i => itau (handle_idx handler i n)
  | iask D d k => itau (handle_idx handler (k (handler D n d)) n.+1)
  end.

Instance interactive_monad E : Monad (interactive E) :=
  {
  Mret := @iret E;
  Mbind := @ibind E;
  Mfail := @ifail E
  }.

Variant interactiveF (E : Type -> Type) A : Type :=
| iretF (a:A)
| ifailF
| itauF (i : interactive E A)
| iaskF {D} (d:E D) (k : D -> interactive E A).
Arguments iretF {E A}.
Arguments ifailF {E A}.
Arguments itauF {E A}.
Arguments iaskF {E A D} d k.        

Definition iforce {E A} (i : interactive E A) : interactiveF E A :=
  match i with
  | iret a => iretF a
  | ifail => ifailF
  | itau i => itauF i
  | iask _ d k => iaskF d k
  end.

Arguments iforce {E A} !i/.

Definition ifold {E A} (i : interactiveF E A) : interactive E A :=
  match i with
  | iretF a => iret a
  | ifailF => ifail
  | itauF i => itau i
  | iaskF _ d k => iask d k
  end.
Arguments ifold {E A} !i/.


Lemma force_interactive {E A} (i : interactive E A)
  : i = ifold (iforce i).
Proof.
  destruct i; simpl; reflexivity.
Qed.

(*TODO: the first is just the semantics and the second
  requires a custom relation. Are either needed anymore?
Lemma monad_bind_ret {E A B} (f : A -> interactive E B) (a : A)
  : Mbind f (Mret a) = f a.
Proof.
  match goal with
    [|- ?a = ?b] =>
    rewrite (force_interactive a)
            (force_interactive b)
  end.
  cbv.
  reflexivity.
Qed.

Lemma Mbind_assoc {E A B C}
      (f : A -> interactive E B)
      (g : B -> interactive E C)
      a
    : Mbind g (Mbind f a) = Mbind (fun x => Mbind g (f x)) a.
Proof.
Qed.
*)

(* clears itaus*)
Fixpoint run {E A} n (i : interactive E A) : option A :=
   match i,n with
  | itau _, 0 => None
  | itau i', S n' => run n' i'
  | iret a, _ => Some a
  | _, _ => None
   end.

Definition handle_from_list {E} (l : list (forall D, E D -> D)) default D (n : nat)
  := nth default l n D.

Definition find_result_such_that
           {E} {A}
           (ma : interactive E A)
           (P : A -> Prop) : Prop :=
  exists l h n res,
    run n (handle_idx (handle_from_list l h) ma 0) = Some res /\ P res.

(*TODO: update ltac
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
*)


Definition ask {E D} (q : E D) : interactive E D :=
  iask q iret.

(* example *)
Variant natE : Type -> Type :=
  natEpred (p : nat -> bool) : natE nat.

Local Definition ask_and_add : interactive natE nat :=
  do a <- ask (natEpred Nat.even);
     b <- ask (natEpred Nat.odd);
     ret (a + b)%nat.

Require Import Ltac2.Constr.
Require Import Ltac2.Ltac2.

Ltac2 refine_evar e pat :=
  let e' := Std.eval_vm None e in
  match Unsafe.kind e' with
  | Unsafe.Evar n _ => Control.new_goal n > [|refine pat]
  | _ => ()(*TODO: fail*)
  end.

Set Default Proof Mode "Classic".

Ltac enter_interactive n :=
  match goal with
  [ |- @find_result_such_that ?E ?A ?ma ?p] =>
  let tl := fresh "tl" in
  evar (tl : list (forall D, E D -> D));
  exists tl;
  let h := fresh "h" in
  evar (h : forall {D}, E D -> D);
  exists h; (*TODO: refine*)
  exists n;
  let res := fresh "res" in
  evar (res : A);
  exists res;
  change (run n (handle_idx (handle_from_list tl h) ma 0) = Some res /\ p res)
  end.


(*Note: doesn't work if tl is in an assumption *)
Ltac instantiate_term tm vl :=
    let H := fresh in 
    assert (tm = vl) as H; [cbv; reflexivity|];
    rewrite ?H; clear H tm.

Ltac coerce_input_to_cons tl :=
  match type of tl with
  | list ?A =>
    let hd := fresh "hd" in evar (hd : A);
    let tl' := fresh "tl" in evar (tl' : list A);
    instantiate_term tl (hd::tl')
  end.

Goal find_result_such_that ask_and_add (eq 7).
  unfold ask_and_add.
  enter_interactive 100.
  cbn.
  coerce_input_to_cons tl.
  coerce_input_to_cons tl0.
  assert (hd = fun _ '(natEpred p) => 0); [cbv;reflexivity| cbn].
  assert (hd0 = fun _ '(natEpred p) => 7); [cbv;reflexivity| cbn].
  split; cbv;reflexivity.
  Unshelve.
  exact (fun _ '(natEpred p) => 0).
  exact [::].
Qed.

(*TODO: move generic version to monad file*)
Definition lift {Q A} (oa : option A) : interactive Q A :=
  match oa with
  | Some x => do ret x
  | None => Mfail
  end.


             
(* Pf-specific code; todo: separate file? *)

(*TODO: decide what should be proofs and what should be exps*)
Variant PfGoal : Type -> Type :=
| le_sort_goal (c:named_list pf) (t1 t2: pf) : PfGoal pf
(*TODO what is the right interface for elaboration?*)
| expand_sort_args (t : sort) : PfGoal (list exp)
(*TODO what is the right interface for elaboration?*)
| expand_term_args (e : exp) (t : sort) : PfGoal (list exp).
                 
(*TODO: put in Pf.v?*)
Definition check_le_sort l c t t' pf :=
  Some(t',t) = synth_le_sort l (synth_le_term l) pf c.

Definition check_wf_term l c e t pf :=
  Some(t,e) = synth_wf_term l pf c.

(* Operates on already-elaborated (i.e. noimplicit arguments) languages *)
Section WithLang.
  Context (l : named_list rule_pf).

  Print pf.
  (*TODO: move to Pf*)
  Fixpoint pf_subst (s : named_list pf) p :=
    match p with
    | pvar x => named_list_lookup (pvar x) s x
    | ax n s' => ax n (map (pf_subst s) s')
    | pcon n s' => pcon n (map (pf_subst s) s')
    | sym p' => sym (pf_subst s p')
    | trans p1 p2 => trans (pf_subst s p1) (pf_subst s p2)
    | conv pt p => conv (pf_subst s pt) (pf_subst s p)
    end.

  Section InnerLoop.
    Context (term_to_pf : named_list pf -> exp -> pf -> interactive PfGoal pf).
    Fixpoint args_to_pf c s (c' : named_list pf) {struct s}
      : interactive PfGoal (list pf) :=
      match c', s with
      | [::], [::] => do ret [::]
      | (_,t)::c'', e::s' =>
        do ps' <- args_to_pf c s' c'';
           pe <- term_to_pf c e (pf_subst (with_names_from c'' ps') t);
           ret pe::ps'
      | _, _ => Mfail
      end.
  End InnerLoop.   
        
  Fixpoint term_to_pf (c : named_list pf) e (t:pf) {struct e} : interactive PfGoal pf :=
    match e with
    | var x =>
      do t' <- lift (named_list_lookup_err c x);
       cv <- ask (le_sort_goal c t' t);
       ret (conv cv (pvar x))
  | con name s =>
    do (term_rule_pf c' args t')
         <?- lift (named_list_lookup_err l name);
      ps <- args_to_pf term_to_pf c s c';
      cv <- ask (le_sort_goal c (pf_subst (with_names_from c' ps) t') t);
     ret (conv cv (pcon name ps))
  end.
  
  Definition sort_to_pf c t : interactive PfGoal pf :=
    match t with
    | scon name s =>
    do (sort_rule_pf c' args)
         <?- lift (named_list_lookup_err l name);
       ps <- args_to_pf term_to_pf c s c';
       ret (pcon name ps)
    end.

  Fixpoint ctx_to_pf c : interactive PfGoal (named_list pf) :=
    match c with
    | [::] => do ret [::]
    | (n,t)::c' =>
      do pc' <- ctx_to_pf c';
         pt <- sort_to_pf pc' t;
         ret (n,pt)::pc'
    end.

  Definition rule_to_pf r : interactive PfGoal rule_pf :=
    match r with
    | sort_rule c args =>
      do cp <- ctx_to_pf c;
         ret sort_rule_pf cp args
    | term_rule c args t =>
      do cp <- ctx_to_pf c;
         tp <- sort_to_pf cp t;
         ret term_rule_pf cp args tp
    | sort_le c t1 t2 =>
      do cp <- ctx_to_pf c;
         p1 <- sort_to_pf cp t1;
         p2 <- sort_to_pf cp t2;
         ret sort_le_pf cp p1 p2
    | term_le c e1 e2 t =>
      do cp <- ctx_to_pf c;
         tp <- sort_to_pf cp t;
         pe1 <- term_to_pf cp e1 tp;
         pe2 <- term_to_pf cp e2 tp;
         ret term_le_pf cp pe1 pe2 tp
    end.      
  
End WithLang.

Fixpoint lang_to_pf l : interactive PfGoal (named_list rule_pf) :=
  match l with
  | [::] => do ret [::]
  | (n,r)::l' =>
    do pl' <- lang_to_pf l';
       pr <- rule_to_pf pl' r;
       ret (n,pr)::pl'
  end.              


Definition find_lang_pf_with p l help :=
  exists elab : lang -> interactive PfGoal lang,
    find_result_such_that (do el <- elab l; pl <- help (lang_to_pf l);ret pl)
                          (fun pl => synth_wf_lang pl = Some l /\ p = pl).

Section Elaborators.
  Context (term_elaborator : lang -> ctx -> exp -> sort -> interactive PfGoal exp)
          (sort_elaborator : lang -> ctx -> sort -> interactive PfGoal sort).

  Fixpoint ctx_elaborator (l : lang) (c : ctx) : interactive PfGoal ctx :=
    match c with
    | [::] => do ret [::]
    | (n,t)::c' =>
      do pc' <- ctx_elaborator l c';
         pt <- sort_elaborator l c' t;
         ret (n,pt)::pc'
    end.

  Definition rule_elaborator l r : interactive PfGoal rule :=
    match r with
    | sort_rule c args =>
      do cp <- ctx_elaborator l c;
         ret sort_rule cp args
    | term_rule c args t =>
      do cp <- ctx_elaborator l c;
         tp <- sort_elaborator l c t;
         ret term_rule cp args tp
    | sort_le c t1 t2 =>
      do cp <- ctx_elaborator l c;
         p1 <- sort_elaborator l c t1;
         p2 <- sort_elaborator l c t2;
         ret sort_le cp p1 p2
    | term_le c e1 e2 t =>
      do cp <- ctx_elaborator l c;
         pe1 <- term_elaborator l c e1 t;
         pe2 <- term_elaborator l c e2 t;
         tp <- sort_elaborator l c t;
         ret term_le cp pe1 pe2 tp
    end.

  
  Fixpoint lang_elaborator l : interactive PfGoal lang :=
    match l with
    | [::] => do ret [::]
    | (n,r)::l' =>
      do pr <- rule_elaborator l' r;
         pl' <- lang_elaborator l';
         ret (n,pr)::pl'
    end.

  (*Not directly used by any of the above, 
    but may be used by the term and sort elaborators *)
  Fixpoint args_elaborator l c es c' :=
       match es,c' with
       | [::],[::] => do ret [::]
       | e::es', (_,t)::c'' =>
         do es'' <- args_elaborator l c es' c'';
            (*TODO: check whether this should be es''*)
            ee <- term_elaborator l c  e t[/with_names_from c'' es'/];
            ret (ee::es'')
       | _,_ => Mfail
       end.

End Elaborators.
  
Fixpoint default_term_elaborator n l c e (t : sort) : interactive PfGoal exp :=
  match e,n with
  | var x, _ => do ret var x
  | con _ _, 0 => Mfail
  | con name s, S n' =>
    do (term_rule c' args t')
         <?- lift (named_list_lookup_err l name);
       es <- ask (expand_term_args e t);
       es' <- args_elaborator (default_term_elaborator n') l c es c';
       ret (con name es)
  end.


Definition default_sort_elaborator n l c '(scon name s) :=
    do (sort_rule c' args)
         <?- lift (named_list_lookup_err l name);
       es <- ask (expand_sort_args (scon name s));
       es' <- args_elaborator (default_term_elaborator n) l c es c';
       ret (scon name es).

(*Convenience definition. Asks for manual elaboration every time*)
Definition default_lang_elaborator n :=
  lang_elaborator (default_term_elaborator n) (default_sort_elaborator n).


Fixpoint handle_refls {A} (i : interactive PfGoal A) : interactive PfGoal A :=
  match i with
  | iret a => iret a
  | itau i => itau (handle_refls i)
  | ifail => ifail
  | iask _ (le_sort_goal c t1 t2) k =>
    (*wfness proofs also prove reflexivity*)
    (*TODO: need proof equality*)
    if (t1 == t2) then itau (handle_refls (k t1))
    else iask (le_sort_goal c t1 t2) (fun a => handle_refls (k a))
  | iask _ q k => iask q (fun a => handle_refls (k a))
  end.
                    
