Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import IExp IRule ICore Subst STLC.
Require Import String.


Require Import Named.Tactics.
Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

Definition stlc_bot :=
  [:| "G" : #"env"
      -----------------------------------------------
      "bot" : #"ty" %"G"
  ]::stlc.
  
Derive elab_stlc_bot
       SuchThat (elab_lang stlc_bot elab_stlc_bot)
       As elab_stlc_bot_pf.
Proof.
  repeat (repeat (cbn;step_elab())).
Qed.  

Instance elab_stlc_bot_inst : Elaborated stlc_bot :=
  {
  elaboration := elab_stlc_bot;
  elab_pf := elab_stlc_bot_pf;
  }.


From Named Require Import Compilers.
  
Fixpoint make_compiler
           (cmp_sort : string -> list string -> Exp.sort)
           (cmp_exp : string -> list string -> Exp.exp)
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


Definition id_compiler :=
  make_compiler (fun c s => Exp.srt c (map Exp.var s))
                (fun c s => Exp.con c (map Exp.var s)).

(* TODO: prove *) 
Lemma preserving_compiler_embed p lt cmp ls
  : preserving_compiler lt cmp ls ->
    preserving_compiler (p::lt) cmp ls.
Proof.
Admitted.

Lemma preserving_id_compiler l
  : Core.wf_lang l -> preserving_compiler l (id_compiler l) l.
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
    
  
(*Definition to_cmp l c' : compiler :=
  map c' (map fst l).*)

(*
Definition twkn g a b := {{#"ty_subst"(#"ext"(g,a),g,#"wkn"(g,a),b)}}.
Definition ewkn g a b e := {{#"el_subst"(#"ext"(g,a),g,#"wkn"(g,a),b,e)}}.*)
Fixpoint wkn_n n e :=
  match n with
  | 0 => e
  | n'.+1 =>
    let e' := wkn_n n' e in
    {{e #"el_subst" #"wkn" !e'}}
  end.

Definition let_bind e k :=
  {{e #"app" !e (#"snoc" #"id" (#"lambda" !k))}}.

Definition ret_val v :=
  {{e #"lambda" (#"app" #"hd" (#"el_subst" #"wkn" !v))}}.

(* TODO: I'm embedding full terms into inferred terms; need to make work.
   Add escape hatch constr?*)

Definition double_neg t :=
    {{e #"->" (#"->" !t #"bot") #"bot"}}.  

Definition lam e := {{e #"lambda" !e}}.

Definition cps_sort (c:string) args : sort := srt c (map Exp.var args).
Definition cps (c : string) args : exp :=
  match c, args with
  | "->", [:: B; A; G] =>
    double_neg {{e #"->" !A !B}}
  | "lambda", [:: e; B; A; G] =>
    ret_val {{e #"lambda" %e}}
  | "app", [:: e2; e1; b; a; g] =>
    let k := wkn_n 2 {{e #"hd"}} in
    let x1 := wkn_n 1 {{e #"hd"}} in
    let x2 := {{e #"hd"}} in
    lam
      (let_bind (wkn_n 1 e1)
      (let_bind (wkn_n 2 e2)
      {{e #"app" %k (#"app" %x1 %x2)}}))
  | _,_ => con c args
  end%string.

