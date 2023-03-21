Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.VSubst.
Import Core.Notations.

Require Coq.derive.Derive.


Definition stlc_def : lang :=
  {[l/subst
  [:| "G" : #"env",
      "t" : #"ty" "G", "t'": #"ty" "G"
      -----------------------------------------------
      #"->" "t" "t'" : #"ty" "G"
  ];
  [:| "G" : #"env",
       "A" : #"ty" "G",
       "B" : #"ty" "G",
       "e" : #"exp" (#"ext" "G" "A") (#"ty_subst" #"wkn" "B")
       -----------------------------------------------
       #"lambda" "A" "e" : #"val" "G" (#"->" "A" "B")
  ];
  [:| "G" : #"env",
       "A" : #"ty" "G",
       "B" : #"ty" "G",
       "e" : #"exp" "G" (#"->" "A" "B"),
       "e'" : #"exp" "G" "A"
       -----------------------------------------------
       #"app" "e" "e'" : #"exp" "G" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty" "G",
      "B" : #"ty" "G",
      "e" : #"exp" (#"ext" "G" "A") (#"ty_subst" #"wkn" "B"),
      "v" : #"val" "G" "A"
      ----------------------------------------------- ("STLC-beta")
      #"app" (#"ret" (#"lambda" "A" "e")) (#"ret" "v")
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" "B"
  ]
  ]}.
(*
  1. add unif vars
  2. generate sort eqns at each con
  3. simplify eqns:
     a. for injective constrs, apply congruence if possible
     b. for x = e/e = x, move to 'evar' map

Ltac algo:
-as existing, but leave all sort eqns unprocessed
-apply refl if concrete
- apply congruence if evar
- once fixed, reduce both sides

 *)
          
    Ltac split_sub s :=
           lazymatch s with
           | {{e #"cmp" {?G1} {?G2} {?G3} {?s1} {?s2} }} =>
               lazymatch s1 with
               | con "cmp" _ => 
                   lazymatch split_sub s1 with
                   | (?s11, ?G1', ?s12) =>
                       constr:((s11, G1', {{e #"cmp" {G1'} {G2} {G3} {s12} {s2} }}))
                   end
               | _ =>
                   lazymatch s2 with
                   | con "cmp" _ => 
                       lazymatch split_sub s2 with
                       | (?s21, ?G2', ?s22) =>
                           constr:(({{e #"cmp" {G1} {G2'} {G2} {s1} {s21} }}, G2', s22))
                       end
                   | _ => constr:((s1, G2, s2))
                   end
               end
           end.
         

         (*TODO: is this too optimistic in the non-ground case for s, s'?*)
         Ltac align_subs G_out s G_out' s' e e' :=
           first [ lazymatch split_sub s with
                   | (?s1, ?G12, ?s2) =>
                       lazymatch split_sub s' with
                       | (?s1', ?G12', ?s2') =>
                           unify s1 s1'; align_subs G_out s2 G_out' s2' e e'
                       end
                       || unify s1 s';
                       let x := constr:({{e #"ty_subst" {G12} {G_out} {s2} {e} }}) in
                       unify x e'
                   end
                 | lazymatch split_sub s' with
                   | (?s1', ?G12', ?s2') =>
                       unify s s1';
                       let x := constr:({{e #"ty_subst" {G12'} {G_out'} {s2'} {e'} }}) in
                       unify e x
                   end
                 | unify s s'; unify e e'].
         Ltac elab_ty_subst :=
         match goal with
         | |- eq_term _ _ _ {{e #"ty_subst" {?G1} {?G2} {?s} {?e} }}
                {{e #"ty_subst" {_} {?G2'} {?s'} {?e'} }} =>
             align_subs G2 s G2' s' e e'
         end.
         
       Create HintDb injective_con discriminated.

       Variant for_db {A} (a : A) : Prop := inst_for_db.
       
       Hint Resolve (inst_for_db "ext") : injective_con.
       Hint Resolve (inst_for_db "->") : injective_con.

         (*TODO: better way to avoid polluting namespace?*)
       Ltac is_injective n :=
         let H' := fresh in
         assert (for_db n) as H' by (typeclasses eauto 1 with injective_con);
         [clear H'].
         
       Ltac shelve_break_elab_term :=
  cbn-[nth_tail];
   lazymatch goal with
   | |- elab_term _ _ ?e ?ee ?t =>
         tryif (is_evar e; is_evar ee) then shelve else eapply elab_term_conv ;
          [ (eapply elab_term_var; [ solve_in ]) || (eapply elab_term_by; [ solve_in | break_down_elab_args ])
          | sort_cong; shelve ]
   end with
        (*elab_args -> list elab_term; should never fail.
        returns goals for explicit terms,
        shelves goals for implicit terms *)
        break_down_elab_args :=
    (eapply elab_args_cons_ex'; [solve_len_eq |repeat shelve_break_elab_term | break_down_elab_args])
    || (eapply elab_args_cons_im; [break_down_elab_args | shelve (*TODO: what to run here?*)])
    || eapply elab_args_nil.
       
       Ltac try_cong :=
                lazymatch goal with
                | |- eq_term _ _ _ (con ?n ?s1) (con ?n ?s2) =>
                    tryif is_injective n
                    then eapply term_con_congruence;
                         [solve_in | sort_cong | assumption
                         | repeat (eapply eq_args_cons || eapply eq_args_nil)];
                         cbn -[nth_tail]
                    else fail
                end.
       
       Ltac process_eq := lazymatch goal with
           | |- eq_term _ _ _ ?e1 ?e2 =>
               (*unconstrained evars*)
               tryif (is_evar e1 + is_evar e2) then (eapply eq_term_refl; [shelve])
               else tryif has_evar e1 + has_evar e2 then try_cong else by_reduction
                                   end.


       
       Ltac is_goal_ground :=
         let g := match goal with |- ?g => g end in
         is_ground g.
       Ltac try_break_elab_term ::=
  cbn-[nth_tail];
   lazymatch goal with
   | |- elab_term _ _ ?e ?ee ?t =>
         tryif (is_evar e; is_evar ee) then shelve else eapply elab_term_conv ;
          [ (eapply elab_term_var; [ solve_in ]) ||
              (eapply elab_term_by; [ solve_in | Matches.break_down_elab_args ])
          | try (sort_cong; repeat process_eq_term) ]
   end;try (is_goal_ground; by_reduction).
                              
Derive stlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_def stlc)
       As stlc_wf.
Proof.
  setup_elab_lang.
  - unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab.
  - unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab.
  - unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab.
  -
    eapply eq_term_rule.
     {
       break_down_elab_ctx.
     }
     {
       break_elab_sort.
     }
     {       
       try_break_elab_term.
     }
     {

       
       unshelve shelve_break_elab_term;
       cbn - [nth_tail];
       try lazymatch goal with
             | |- term => shelve
             | |- wf_term _ _ _ _ => shelve
         end.

       Ltac try_cong' :=
                lazymatch goal with
                | |- eq_term _ _ _ (con ?n ?s1) (con ?n ?s2) =>
                    tryif assert (for_db n) by (typeclasses eauto 1 with injective_con)
                    then eapply term_con_congruence;
                         [solve_in | sort_cong | assumption
                         | repeat (eapply eq_args_cons || eapply eq_args_nil)];
                         cbn -[nth_tail]
                    else fail
                end.
       
       Ltac process_eq' := lazymatch goal with
           | |- eq_term _ _ _ ?e1 ?e2 =>
               (*unconstrained evars*)
               tryif (is_evar e1 + is_evar e2) then (eapply eq_term_refl; [shelve])
               else tryif has_evar e1 + has_evar e2 then try_cong' else by_reduction
                                   end.
       
         all:repeat process_eq'.
       (*TODO: why is it different the second time?*)
       all:repeat process_eq'.
       {
         reduce.
         elab_ty_subst.
         reduce.
         term_cong.
         eapply eq_term_refl.
         by_reduction.
       }
       all: try by_reduction.
     }
  - unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab.
  - unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab.
  - unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
      try apply eq_term_refl; cleanup_auto_elab.
    Unshelve.
    all: try apply eq_term_refl; cleanup_auto_elab.
Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.

