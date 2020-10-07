
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From excomp Require Import Utils Exp Rule Core EasyWF langs.Subst.


Notation arr g a b := (con 27 [:: b; a; g]%exp_scope).
Notation lam g a b e := (con 28 [:: e; b; a; g]%exp_scope).
Notation app g a b e1 e2 := (con 29 [:: e2; e1; b; a; g]%exp_scope).
Definition ty_wkn g a b :=  (ty_subst (ext g a) g (p g a) b).
Definition stlc :=
  (term_le [:: el 0 1; el (ext 0 1) (ty_wkn 0 1 2); ty 0; ty 0; ob]
           (app 0 1 2 (lam 0 1 2 3) 4)
           (el_subst 0 (ext 0 1)
                     (snoc 0 0 1 (id 0) 4) (ty_wkn 0 1 2) 3)
           (el 0 2))::
  (term_rule [:: el 0 1;
                 el 0 (arr 0 1 2);
                 ty 0; ty 0; ob]
             (el 0 2))::
  (term_rule [:: el (ext 0 1) (ty_wkn 0 1 2);
             ty 0; ty 0; ob]
             (el 0 (arr 0 1 2)))::
  (term_rule [:: ty 0; ty 0; ob] (ty 0))::
  subst_lang.
      
Lemma stlc_wf : wf_lang stlc.
Proof using.
  pose p:= subst_lang_wf.
  cbv in p.
  (* TODO: improve this *)  
  wf_lang_eauto.
  all: try done.
  {
    constructor; eauto with judgment.
    eapply wf_term_conv.
    eauto with judgment.
    ltac2:(apply_term_constr ()).
    eapply wf_subst_cons; eauto with judgment.
    eapply wf_subst_cons; eauto with judgment.
    eapply wf_subst_cons; eauto with judgment.
    {
      ltac2:(apply_term_constr()).
      eapply wf_subst_cons; eauto with judgment.
      cbv.
      eapply wf_term_conv.
      eauto with judgment.
      eapply wf_term_var.
      ltac2:(unify_nth_level()).
      eapply sort_con_mor.
      eapply subst_cons_mor.
      eauto with judgment.
      symmetry.
      instantiate (1 := ty 0).
      cbv.
      ltac2:(apply_term_rule constr:(11)).
      eauto with judgment.      
    }
    {
      cbv.
      eapply sort_con_mor.
      eapply le_subst_cons.
      eauto with judgment.
      instantiate (1:= ty 0).
      cbv.
      eapply le_term_trans.
      symmetry.
      Eval cbv in (nth_level (sort_rule [::]) subst_lang 12).
      instantiate
        (1:=ty_subst 0 0
                     (cmp 0 (ext 0 1) 0 (Subst.p 0 1)
                          (snoc 0 0 1 (id 0) 4)) 2).
      cbv.
      ltac2:(apply_term_rule constr:(12)).
      repeat (eapply le_subst_cons; eauto with judgment).
      eapply le_term_trans.
      {
        evar (s:subst).
        suff: (ty 0) = (ty 0)[/s/]; unfold s.
        intro ts.
        rewrite ->ts at 21.
        
        eapply term_con_mor.
        eapply le_subst_cons.
        2: eauto with judgment.
        eapply le_subst_cons.
        2:{
          
          instantiate (2:= hom 0 1).
          instantiate (2 := [:: var 0; var 0]).
          instantiate (1 := id 0).
          cbv.
          ltac2:(apply_term_rule constr:(23)).
          eapply le_subst_cons; eauto with judgment.
        }
        {          
          eapply le_subst_cons; eauto with judgment.
        }
      by compute.
      }
      {
        
        Eval cbv in (nth_level (sort_rule [::]) subst_lang 11).
        ltac2:(apply_term_rule constr:(11)).
        eauto with judgment.
      }
    }
  }

  Unshelve.
    all: solve [ exact (con 0 [::]) | exact [::]].
Qed.
