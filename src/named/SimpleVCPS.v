Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix SimpleVSubst SimpleVSTLC Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Definition bot_ty :=
  [[:| 
      -----------------------------------------------
      #"bot" : #"ty"
  ]]%arule.



Derive bot_ty_elab
       SuchThat (Pre.elab_lang subst_elab bot_ty bot_ty_elab)
       As bot_ty_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve bot_ty_wf : elab_pfs.


Definition stlc_bot := bot_ty_elab ++ stlc_elab ++ subst_elab.
Lemma stlc_bot_wf : wf_lang stlc_bot.
Proof. eauto 7 with auto_elab elab_pfs. Qed.

Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Fixpoint vwkn_n n e :=
  match n with
  | 0 => e
  | S n' =>
    {{e #"val_subst" #"wkn" {vwkn_n n' e} }}
  end.

(*n is how many wknings to do on e*)
Definition bind_k n e A k :=
  {{e #"el_subst" (#"snoc" {wkn_n n} (#"lambda" {A} {k})) {e} }}.
Arguments bind_k n e A k/.

Definition ret_val v :=
  {{e #"app" (#"ret" #"hd") (#"ret" {vwkn_n 1 v})}}.

Definition double_neg t : exp :=
  {{e #"->" (#"->" {t} #"bot") #"bot"}}.
Arguments double_neg t /.

Definition cps : compiler :=
  match # from (stlc_elab ++ subst_elab) with
  | {{s #"el" "G" "A"}} => {{s #"el" (#"ext" %"G" (#"->" %"A" #"bot")) #"bot" }}
  | {{e #"->" "A" "B"}} => {{e #"->" %"A" {double_neg (var "B")} }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"lambda" %"A" (#"ret" (#"lambda" (#"->" %"B" #"bot") %"e"))}}
  | {{e #"app" "G" "A" "B" "e" "e'"}} =>
    let k := {{e #"ret" {vwkn_n 2 {{e #"hd"}} } }} in
    let x1 := {{e #"ret" {vwkn_n 1 {{e #"hd"}} } }} in
    let x2 := {{e #"ret" #"hd"}} in
    bind_k 1 (var "e") {{e #"->" %"A" {double_neg (var "B")} }}
    (bind_k 2 (var "e'") (var "A")
    {{e #"app" (#"app" {x1} {x2}) {k} }})
  | {{e #"el_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"el_subst" (#"snoc" (#"cmp" #"wkn" %"g") #"hd") %"e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    ret_val (var "v")
  end.


Lemma cps_beta_preserved :
eq_term stlc_bot
    {{c"G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e"
       : # "el" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         #"bot",
       "e'" : # "el" (# "ext" %"G" (# "->" %"A" #"bot")) #"bot",
       "G'" : #"env",
       "g" : # "sub" %"G'" %"G"}} {{s# "el" (# "ext" %"G'" (# "->" %"B" #"bot")) #"bot"}}
    {{e# "el_subst" (# "ext" %"G'" (# "->" %"B" #"bot")) (# "ext" %"G" (# "->" %"B" #"bot"))
       (# "snoc" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G" (# "->" %"B" #"bot")
        (# "cmp" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'" %"G"
         (# "wkn" %"G'" (# "->" %"B" #"bot")) %"g") (# "hd" %"G'" (# "->" %"B" #"bot"))) #"bot"
       (# "el_subst" (# "ext" %"G" (# "->" %"B" #"bot"))
        (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "snoc" (# "ext" %"G" (# "->" %"B" #"bot")) %"G"
         (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
         (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G" (# "wkn" %"G" (# "->" %"B" #"bot"))
          (# "id" %"G"))
         (# "lambda" (# "ext" %"G" (# "->" %"B" #"bot"))
          (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
          (# "el_subst"
           (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
            (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G" (# "->" %"A" #"bot"))
           (# "snoc"
            (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"G" (# "->" %"A" #"bot")
            (# "cmp"
             (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
              (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
             (# "ext" %"G" (# "->" %"B" #"bot")) %"G"
             (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
              (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
             (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G"
              (# "wkn" %"G" (# "->" %"B" #"bot")) (# "id" %"G")))
            (# "lambda"
             (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
              (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A" #"bot"
             (# "app"
              (# "ext"
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
              # "->" %"B" #"bot") #"bot"
              (# "app"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
               (# "->" (# "->" %"B" #"bot") #"bot")
               (# "ret"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                (# "val_subst"
                 (# "ext"
                  (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                   (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                 (# "wkn"
                  (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                   (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                 (# "hd" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))))
               (# "ret"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
                (# "hd"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")))
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
               # "->" %"B" #"bot")
               (# "val_subst"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "wkn"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
                # "->" %"B" #"bot")
                (# "val_subst"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                 (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "->" %"B" #"bot")
                 (# "hd" %"G" (# "->" %"B" #"bot")))))))) #"bot" %"e'"))) #"bot" %"e")}}
    {{e# "el_subst" (# "ext" %"G'" (# "->" %"B" #"bot"))
       (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
       (# "snoc" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'"
        (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
        (# "cmp" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'" %"G'"
         (# "wkn" %"G'" (# "->" %"B" #"bot")) (# "id" %"G'"))
        (# "lambda" (# "ext" %"G'" (# "->" %"B" #"bot"))
         (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
         (# "el_subst"
          (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
           (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G'" (# "->" %"A" #"bot"))
          (# "snoc"
           (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
            (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"G'" (# "->" %"A" #"bot")
           (# "cmp"
            (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
            (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'"
            (# "wkn" (# "ext" %"G'" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
            (# "cmp" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'" %"G'"
             (# "wkn" %"G'" (# "->" %"B" #"bot")) (# "id" %"G'")))
           (# "lambda"
            (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A" #"bot"
            (# "app"
             (# "ext"
              (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
             # "->" %"B" #"bot") #"bot"
             (# "app"
              (# "ext"
               (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
              (# "->" (# "->" %"B" #"bot") #"bot")
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
               (# "val_subst"
                (# "ext"
                 (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "wkn"
                 (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                (# "hd" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))))
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
               (# "hd"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")))
             (# "ret"
              (# "ext"
               (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
              # "->" %"B" #"bot")
              (# "val_subst"
               (# "ext"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
               (# "wkn"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
               # "->" %"B" #"bot")
               (# "val_subst"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "wkn" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "->" %"B" #"bot")
                (# "hd" %"G'" (# "->" %"B" #"bot")))))))) #"bot"
          (# "el_subst" (# "ext" %"G'" (# "->" %"A" #"bot")) (# "ext" %"G" (# "->" %"A" #"bot"))
           (# "snoc" (# "ext" %"G'" (# "->" %"A" #"bot")) %"G" (# "->" %"A" #"bot")
            (# "cmp" (# "ext" %"G'" (# "->" %"A" #"bot")) %"G'" %"G"
             (# "wkn" %"G'" (# "->" %"A" #"bot")) %"g") (# "hd" %"G'" (# "->" %"A" #"bot"))) #"bot"
           %"e'")))) #"bot"
       (# "el_subst"
        (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "snoc" (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
         (# "cmp" (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
          %"G'" %"G"
          (# "wkn" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")) %"g")
         (# "hd" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))) #"bot"
        %"e")}}.
Proof.
Admitted.
(*  pose proof (elab_lang_implies_wf stlc_bot_wf).
  solve[by_reduction].
  Unshelve.
  all: repeat t'.
Qed.
*)

Lemma cps_subst_preserved
  : eq_term stlc_bot
    {{c"G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : # "el" (# "ext" (# "ext" %"G" %"A") (# "->" %"B" #"bot")) #"bot",
       "v" : # "val" %"G" %"A"}} {{s# "el" (# "ext" %"G" (# "->" %"B" #"bot")) #"bot"}}
    {{e# "el_subst" (# "ext" %"G" (# "->" %"B" #"bot"))
       (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
       (# "snoc" (# "ext" %"G" (# "->" %"B" #"bot")) %"G"
        (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
        (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G" (# "wkn" %"G" (# "->" %"B" #"bot"))
         (# "id" %"G"))
        (# "lambda" (# "ext" %"G" (# "->" %"B" #"bot"))
         (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
         (# "el_subst"
          (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
           (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G" (# "->" %"A" #"bot"))
          (# "snoc"
           (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
            (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"G" (# "->" %"A" #"bot")
           (# "cmp"
            (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G" (# "->" %"B" #"bot"))
            %"G"
            (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
            (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G"
             (# "wkn" %"G" (# "->" %"B" #"bot")) (# "id" %"G")))
           (# "lambda"
            (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A" #"bot"
            (# "app"
             (# "ext"
              (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
             # "->" %"B" #"bot") #"bot"
             (# "app"
              (# "ext"
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
              (# "->" (# "->" %"B" #"bot") #"bot")
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
               (# "val_subst"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "wkn"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                (# "hd" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))))
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
               (# "hd"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")))
             (# "ret"
              (# "ext"
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
              # "->" %"B" #"bot")
              (# "val_subst"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
               (# "wkn"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
               # "->" %"B" #"bot")
               (# "val_subst"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "->" %"B" #"bot")
                (# "hd" %"G" (# "->" %"B" #"bot")))))))) #"bot"
          (# "app" (# "ext" %"G" (# "->" %"A" #"bot")) %"A" #"bot"
           (# "ret" (# "ext" %"G" (# "->" %"A" #"bot")) (# "->" %"A" #"bot")
            (# "hd" %"G" (# "->" %"A" #"bot")))
           (# "ret" (# "ext" %"G" (# "->" %"A" #"bot")) %"A"
            (# "val_subst" (# "ext" %"G" (# "->" %"A" #"bot")) %"G"
             (# "wkn" %"G" (# "->" %"A" #"bot")) %"A" %"v")))))) #"bot"
       (# "app" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
        (# "ret" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
         (# "hd" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")))
        (# "ret" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
         (# "val_subst"
          (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")) %"G"
          (# "wkn" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
          (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
          (# "lambda" %"G" %"A" (# "->" (# "->" %"B" #"bot") #"bot")
           (# "ret" (# "ext" %"G" %"A") (# "->" (# "->" %"B" #"bot") #"bot")
            (# "lambda" (# "ext" %"G" %"A") (# "->" %"B" #"bot") #"bot" %"e"))))))}}
    {{e# "el_subst" (# "ext" %"G" (# "->" %"B" #"bot"))
       (# "ext" (# "ext" %"G" %"A") (# "->" %"B" #"bot"))
       (# "snoc" (# "ext" %"G" (# "->" %"B" #"bot")) (# "ext" %"G" %"A") (
        # "->" %"B" #"bot")
        (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" (# "ext" %"G" %"A")
         (# "wkn" %"G" (# "->" %"B" #"bot")) (# "snoc" %"G" %"G" %"A" (# "id" %"G") %"v"))
        (# "hd" %"G" (# "->" %"B" #"bot"))) #"bot" %"e"}}.
Proof.
Admitted.
(*  pose proof (elab_lang_implies_wf stlc_bot_wf).
  solve[by_reduction].
  Unshelve.
  all: repeat t'.
Qed. *)
  

Derive cps_elab
       SuchThat (elab_preserving_compiler [] stlc_bot cps cps_elab (nth_tail 1 stlc_bot))
       As cps_elab_preserving.
Proof.
  pose proof stlc_bot_wf.
  setup_elab_compiler.

  all: try solve[ repeat t; repeat t'].
  
  1-14:solve[ compute_eq_compilation;by_reduction].
 apply cps_subst_preserved.
 apply cps_beta_preserved.
 solve[ compute_eq_compilation;by_reduction].
 Unshelve.
 all: repeat t'. 
Qed.


Local Lemma stlc_wf' : wf_lang (nth_tail 1 stlc_bot).
Proof.
  change (nth_tail 1 stlc_bot) with (stlc_elab ++ subst_elab).
  eauto 7 with auto_elab elab_pfs.
Qed.

Goal semantics_preserving stlc_bot cps_elab (nth_tail 1 stlc_bot).
Proof.
  apply inductive_implies_semantic.
  - apply stlc_wf'.
  - apply stlc_bot_wf.
  - eapply elab_compiler_implies_preserving.
    change  (nth_tail 1 stlc_bot) with  (nth_tail 1 stlc_bot ++ []).
    change (cps_elab) with (cps_elab ++[]).
    eapply elab_compiler_prefix_implies_elab;
    eauto using cps_elab_preserving with lang_core.
Qed.

(*
TODO: make proof generate fully evalled cps_elab to print w/ the notation
Eval compute in cps_elab.
*)
