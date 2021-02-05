
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp ARule.
From Named Require Import ImCore Pf.
From Named Require Import SimpleSubst.
Import Exp.Notations ARule.Notations.
Require Import String.

Set Default Proof Mode "Classic".

Definition stlc :=
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
  [:> "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"el" (#"ext" %"G" %"A") %"B",
      "e'" : #"el" %"G" %"A"
      ----------------------------------------------- ("STLC_beta")
      #"app" (#"lambda" %"A" %"e") %"e'"
      = #"el_subst" (#"snoc" #"id" %"e'") %"e"
      : #"el" %"G" %"B"
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
Definition simple_subst_to_pf_ty (e:exp) : option pf :=
  match e with
  | var x => Some (pvar x)
  | con "->" [:: B; A] =>
    do pA <- simple_subst_to_pf_ty A;
       pB <- simple_subst_to_pf_ty B;
       ret (pcon "->" [:: pB; pA])
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

Lemma simple_stlc_wf : wf_lang (nth_tail 1 stlc).
Proof.
  prove_wf_with_fn simple_subst_to_pf_lang.
Qed.

