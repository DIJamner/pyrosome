
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

(*TODO: curr. runs out of mem*)
Fail.

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
       "e'" : #"exp" (#"ext" "G" #"nat") "B" (*TODO: nat exns or other?*)
       ----------------------------------------------- ("catch-throw")
       #"do_catch" (#"throw" (#"ret" "v")) "e'" (*TODO: Ectx or no? *)
       = #"exp_subst" (#"snoc" #"id" "v") "e'"
       : #"exp" "G" "B"
  ]
  ]}.


Derive exn
       SuchThat (Pre.elab_lang (nat_exp
                                  ++ nat_lang
                                  ++ exp_subst
                                  ++ value_subst)
                               exn_def
                               exn)
       As exn_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exn_wf : elab_pfs.

(*TODO: move this to separate file*)
Require Import SimpleVCPS.


(*g is the necessary weakening of e *)
Definition bind_k n e A k :=
  {{e #"blk_subst" (#"snoc" {wkn_n n} (#"cont" {A} {k})) {e} }}.
Arguments bind_k n e A k/.

(*TODO: extract the identity compiler for vals*)
(*TODO: depends on products*)
Definition cps_subst_def : compiler :=
  match # from (exp_subst ++ value_subst) with
  | {{s #"exp" "G" "A"}} =>
    {{s #"blk" (#"ext" (#"ext" "G"  (#"neg" #"nat")) (#"neg" "A")) }}
  | {{e #"exp_subst" "G" "G'" "g" "A" "e" }} =>
    {{e #"blk_subst" {under (under {{e"g"}}) } "e" }}
  | {{e #"ret" "G" "A" "v"}} =>
    {{e #"jmp" #"hd" (#"val_subst" {wkn_n 2} "v")}}
  end.


Derive cps_subst
       SuchThat (elab_preserving_compiler []
                                          (cps_lang
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          cps_subst_def
                                          cps_subst
                                          (exp_subst ++ value_subst))
       As cps_subst_preserving.
Proof. auto_elab_compiler. Qed.
#[export] Hint Resolve cps_subst_preserving : elab_pfs.
     
Require Import SimpleVSTLC.

Definition pm_hd_pair e :=
  {{e #"pm_pair" #"hd"
            (*TODO: remember why wkn here*)
          (#"blk_subst" {under (under {{e #"wkn"}})} {e})}}.
  

Definition cps_def : compiler :=
  match # from (stlc) with
  | {{e #"->" "A" "B"}} =>
    {{e #"neg" (#"prod" "A" (#"prod" (#"neg" #"nat") (#"neg" "B"))) }}
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"cont" (#"prod" "A" (#"prod" (#"neg" #"nat") (#"neg" "B")))
        {pm_hd_pair (pm_hd_pair (var "e"))} }}
  | {{e #"app" "G" "A" "B" "e" "e'"}} =>
    bind_k 1 (var "e") {{e #"neg" (#"prod" "A" (#"prod" (#"neg" #"nat") (#"neg" "B")))}}
    (bind_k 2 (var "e'") (var "A")
    {{e #"jmp" {ovar 1} (#"pair" {ovar 0} (#"pair" {ovar 3} {ovar 2})) }})
  end.

Derive cps
       SuchThat (elab_preserving_compiler cps_subst
                                          (cps_prod_lang
                                             ++ nat_exp
                                             ++ nat_lang
                                             ++ cps_lang
                                             ++ block_subst
                                             ++ value_subst)
                                          cps_def
                                          cps
                                          stlc)
       As cps_preserving.
Proof. auto_elab_compiler. Qed.
  setup_elab_compiler.
  all: repeat t.
  Optimize Heap.
  unshelve(solve [ compute_eq_compilation; by_reduction ]); repeat t'; eauto
   with elab_pfs auto_elab.
  TODO: Still too much ram
  compute_eq_compilation.
    eapply eq_term_trans. 
    {
      step_if_concrete.
    }
    {
      eapply eq_term_sym.
      step_if_concrete.
    }
  }
  Unshelve.
  all:repeat t'; eauto
   with elab_pfs auto_elab.
  
  unshelve(solve [ compute_eq_compilation; by_reduction ]); repeat t'; eauto
   with elab_pfs auto_elab.
  unshelve(solve [ compute_eq_compilation; by_reduction ]); repeat t'; eauto
   with elab_pfs auto_elab.
  Unshelve.
  all: repeat t'; eauto
   with elab_pfs auto_elab.
Qed.
#[export] Hint Resolve cps_preserving : elab_pfs.

TODO: a bit more complicated
Definition catch e :=
  {{e "cont" #"nat" {e} }}.

Definition exn_cps_def : compiler :=
  match # from (stlc) with
  | {{e #"throw" "G" "e" "A" }} =>
    bind_k 1 (var "e") {{e#"nat"}}
           {{e#"jmp" {ovar 2} {ovar 0} }}
  | {{e#"do_catch" "G" "A" "e" "e'"}} =>
    bind_k 1 (var "e") (var "A")
           {{e #"jmp" {ovar 1} (#"pair" {ovar 0}
                                 (#"pair" {catch (var "e'")}
                                   {ovar 2})) }})

    
  | {{e #"lambda" "G" "A" "B" "e"}} =>
    {{e #"cont" (#"prod" "A" (#"prod" (#"neg" #"nat") (#"neg" "B")))
        {pm_hd_pair (pm_hd_pair (var "e"))} }}
  | {{e #"app" "G" "A" "B" "e" "e'"}} =>
    bind_k 1 (var "e") {{e #"neg" (#"prod" "A" (#"prod" (#"neg" #"nat") (#"neg" "B")))}}
    (bind_k 2 (var "e'") (var "A")
    {{e #"jmp" {ovar 1} (#"pair" {ovar 0} (#"pair" {ovar 3} {ovar 2})) }})
  end.
