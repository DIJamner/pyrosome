Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp ARule ImCore Pf PfCore Compilers PfCompilers PfMatches ParStep.
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

(* To prove preservation of beta reduction w/ an arbitrary expression
   as the argument, need continuation shuffling axiom (see Bowman et al):
   e' (\x. e) = e[(e' id)/x]
*)
Definition stlc_no_beta :=
  [::[:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el" (#"ext" %"G" %"A") %"B",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("lambda_subst")
      #"el_subst" %"g" (#"lambda" %"A" %"e")
      = #"lambda" %"A" (#"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e")
      : #"el" %"G'" (#"->" %"A" %"B")
  ];
  [:> "G" : #"env", "A" : #"ty", "B" : #"ty",
      "e" : #"el"%"G" (#"->" %"A" %"B"),
      "e'" : #"el" %"G" %"A",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("app_subst")
      #"el_subst" %"g" (#"app" %"e" %"e'")
      = #"app" (#"el_subst" %"g" %"e") (#"el_subst" %"g" %"e'")
      : #"el" %"G'" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"el" %"G" (#"->" %"A" %"B"),
       "e'" : #"el" %"G" %"A"
       -----------------------------------------------
       #"app" "e" "e'" : #"el" %"G" %"B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : #"el" (#"ext" %"G" %"A") %"B"
       -----------------------------------------------
       #"lambda" "A" "e" : #"el" %"G" (#"->" %"A" %"B")
  ];
  [:| "t" : #"ty", "t'": #"ty"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty"
  ]]%arule++subst_lang.

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

Definition bind_k e A k :=
  {{e #"app" {e} (#"lambda" {A} {k})}}.
Arguments bind_k e A k/.

Definition ret_val v A :=
  {{e #"lambda" (#"->" {A} #"bot") (#"app" #"hd" {wkn_n 1 v})}}.
Arguments ret_val v A/.

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
    {{s #"el" %G {double_neg (var A)} }}
  | _,_ => scon c (map var (lookup_args stlc c))
  end%string.
Definition cps (c : string) (args : list string) : exp :=
  match c, args with
  | "->", [:: B; A] =>
    {{e #"->" %A {double_neg (var B)} }}
  | "lambda", [:: e; B; A; G] =>
    (*knock-on effect of changing ext: e needs a subst*)
    ret_val {{e #"lambda" %A (#"el_subst" (#"snoc" (#"cmp" #"wkn" #"id") {ret_val {{e #"hd"}} (var A) }) %e)}}
            {{e #"->" %A {double_neg (var B)} }}
  | "app", [:: e2; e1; B; A; G] =>
    let k := wkn_n 2 {{e #"hd"}} in
    let x2 := wkn_n 1 {{e #"hd"}} in
    let x1 := {{e #"hd"}} in
    {{e #"lambda" (#"->" %B #"bot")
    {bind_k (wkn_n 1 (var e2)) (var A)
    (bind_k (wkn_n 2 (var e1)) {{e #"->" %A {double_neg (var B)} }}
            {{e #"app" (#"app" {x1} {x2}) {k} }})} }}
  | "hd", [:: A] =>
    ret_val {{e #"hd"}} (var A)
  | "ext", [:: A; G] =>
    {{e #"ext" %G {double_neg (var A)} }}
  | _,_ => con c (map var (lookup_args stlc c))
  end%string.

(*  !!!!!!!!!!!!!!!
TODO: need continuation shuffling?

!!!!!!!!!!!! *)

Require Compilers.


Definition stlc_no_beta_elab :=
  Eval compute in
    (match simple_subst_to_pf_lang stlc_no_beta with
     | Some pl => pl
     | None => [::]
     end).

(*TODO: need to compile ctx, type*)
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

Definition cps_elab :=
  Eval compute in
    let n := 0 in
    (match elab_compiler stlc_bot_elab
                         (make_compiler cps_sort cps (nth_tail n stlc_no_beta))
                         (nth_tail n stlc_no_beta_elab) with
     | Some pl => pl
     | None => [::]
     end).
Goal match cps_elab with [::] => False | _ => True end.
    by compute.
Qed.

(*
Lemma term_ok_con'
  : forall (l : pf_lang) (c : pf_ctx) (name : str_eqType) (c' : named_list_set pf) (args : seq string) (t t' : pf) (s : seq pf),
    (name, term_rule_pf c' args t) \in l -> args_ok l c s c' ->
    t' = (pf_subst (with_names_from c' (map (proj_r l) s)) t) ->
    term_ok l c (pcon name s) t'.
Proof.
Admitted.*)

  
Lemma cps_elab_wf : preserving_compiler stlc_bot_elab cps_elab stlc_no_beta_elab.
Proof.
  apply /check_preservingP; by compute.
Qed.











(*



Goal true = false.
  pose (p := (head (""%string,sort_rule_pf [::] [::]) (nth_tail 2 stlc_elab))).
  compute in p.
  match goal with
    [ p:= (?s,term_le_pf ?cc ?ee1 ?ee2 ?tt)|-_] =>
    pose (n := s); pose (c:=cc); pose (e1:= ee1); pose (e2:=ee2); pose (t:= tt)
  end.
  pose (src' := nth_tail 3 stlc_elab).
  pose (pcc := cps_elab).
  pose (tgt := stlc_bot_elab).
  pose (lhs:=(par_step_n tgt (compile src' pcc e1) 100)).
  pose (rhs := (par_step_n tgt (compile src' pcc e2) 100)).
  compute in lhs.
  compute in rhs.
  
  Eval compute in ((proj_r tgt lhs) == (proj_r tgt rhs)).
  Eval compute in (do lhs <- Some (par_step_n tgt (compile src' pcc e1) 100);
       rhs <- Some (par_step_n tgt (compile src' pcc e2) 100);
       (*TODO: failing on terms that seem identical?*)
       (*! eq_pf_irr tgt (proj_r tgt lhs) (proj_r tgt rhs);*)
       (* attempt to reduce both sides to the same normal form *)
       ret (n,trans lhs (sym rhs))::pcc).
  let e1 := constr:(pcon "el_subst"%string
         [:: pcon "app" [:: pvar "e'"; pvar "e"; pvar "B"; pvar "A"; pvar "G"]; 
            pvar "B"; pvar "g"; pvar "G"; pvar "G'"]) in
  let x := eval compute in (proj_r stlc_bot_elab (par_step_n stlc_bot_elab (compile stlc_elab cps_elab e1) 100))
    in pose (t1 := x).


   let e1 := constr:(pcon "app"
         [:: pcon "el_subst" [:: pvar "e'"; pvar "A"; pvar "g"; pvar "G"; pvar "G'"];
             pcon "el_subst"
               [:: pvar "e"; pcon "->" [:: pvar "B"; pvar "A"]; pvar "g"; pvar "G"; pvar "G'"];
             pvar "B"; pvar "A"; pvar "G'"]) in
  let x := eval compute in (proj_r stlc_bot_elab (par_step_n stlc_bot_elab (compile stlc_elab cps_elab e1) 100))
    in pose (t2 := x).
   Eval compute in (eq_pf_irr stlc_bot_elab t1 t2).






{
    cbn. (*TODO: do these rules need eta? 
           should have a baseline check that projections line up in elab.
          *)
    Ltac dive1 :=
       eapply term_ok_con'; [rewrite <-named_list_lookup_err_inb;
                          apply /eqP; by compute| |by compute];
    repeat match goal with
      [|-args_ok _ _ _ _]=>
    first [ apply /check_args_okP; by compute
          | constructor]
           end.
    repeat dive1.
    cbn.
    TODO: issue: using e in a position where ctx is G,A,(dneg A) instead of G,(dneg A)
    eapply term_ok_con'.
    {
      rewrite <-named_list_lookup_err_inb.
      apply /eqP.
        by compute.
          by compute.
    }
    2: by compute.
    cbn.
    constructor.
    apply /check_args_okP; by compute.
    eapply term_ok_con'; [rewrite <-named_list_lookup_err_inb;
                          apply /eqP; by compute| |by compute].
    repeat match goal with
      [|-args_ok _ _ _ _]=>
    first [ apply /check_args_okP; by compute
          | constructor]
    end.
    
    eapply term_ok_trans.
    4:{
      match goal with
        [|- is_true (eq_pf_irr _ ?a ?b)] =>
        assert (a=b);[ reflexivity| by compute]
      end.
    }
    apply /check_term_okP; by compute.
    apply /check_term_okP; by compute.
    {
      
      match goal with
        [|- is_true (eq_pf_irr _ ?a ?b)] =>
        assert (a=b);[ reflexivity
      end.
      
      
      TODO: did I forget to do a subst somewhere?
    }
    
    
  2: apply /check_is_expP; by compute.
  {
    cbv -[compile_ctx stlc_bot_elab].
    eapply term_ok_con'.
    rewrite <-named_list_lookup_err_inb.
    apply /eqP.
      by compute.
      by compute.
    2:{ by compute. }
    constructor.
    constructor.
    constructor.
    
    apply /check_args_okP; by compute.
    {
      cbn.
      eapply term_ok_con'.
      rewrite <-named_list_lookup_err_inb.
      apply /eqP.
        by compute.
      by compute.
      2:{ by compute. }
      constructor.
      constructor.
      apply /check_args_okP; by compute.
      {
        cbn.
      rewr
      apply /check_term_okP; by compute.
    eauto.
    
 *)
