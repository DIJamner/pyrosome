
Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix
     SimpleVSubst SimpleEvalCtx NatHeap (*TODO: separate nats out*) Matches.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Definition exn_def : lang :=
  {[l
  [:|  "G" : #"env",
       "e" : #"exp" "G" #"nat", (*TODO: nat exns or other?*)
       "A" : #"ty"
       -----------------------------------------------
       #"throw" "e" : #"exp" "G" "A"
  ];
  [:|  "G" : #"env",
       "A" : #"ty",
       "e" : #"exp" "G" "A",
       "e'" : #"exp" (#"ext" "G" #"nat") "A" (*TODO: nat exns or other?*)
       -----------------------------------------------
       #"do_catch" "e" "e'" : #"exp" "G" "A"
  ];
  [:=  "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "v" : #"val" "G" #"nat",
       "E" : #"Ectx" "G" "A" "B",
       "e'" : #"exp" (#"ext" "G" #"nat") "B" (*TODO: nat exns or other?*)
       ----------------------------------------------- ("catch-throw")
       #"do_catch" (#"plug" "E" (#"throw" (#"ret" "v"))) "e'" (*TODO: Ectx or no? *)
       = #"exp_subst" (#"snoc" #"id" "v") "e'"
       : #"exp" "G" "B"
  ]
  ]}.


Derive exn
       SuchThat (Pre.elab_lang (eval_ctx
                                  ++ nat_exp
                                  ++ nat_lang
                                  ++ exp_subst
                                  ++ value_subst)
                               exn_def
                               exn)
       As exn_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exn_wf : elab_pfs.

     
