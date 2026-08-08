Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import StlcModel StlcNormalization.
Import Core.Notations.

(* The equational toolkit for [stlc_unit].

   Each of the language's 18 equations is repackaged here as a directly usable
   lemma: the equation instance is stated with explicit term arguments in the
   abbreviation vocabulary of Gluing/StlcModel.v ([Cmp], [Snoc], [ValSubst],
   ...), and carries exactly the well-formedness hypotheses the instantiation
   needs -- one [wf_term] per variable of the rule's context, at that variable's
   sort, already instantiated by the preceding arguments.  The congruence rules
   for the seven constructors the later layers use get the same treatment.

   Nothing here guesses shapes from the surface notation.  The rules themselves
   are not transcribed at all: [rule_of] reads them out of the compiled language
   and each [r_*] below is its [vm_compute]d value, so the statements of the
   instance lemmas are checked against the real rules by conversion. *)

Definition rule_of (n : string) : rule string :=
  match named_list_lookup_err stlc_unit n with
  | Some r => r
  | None => sort_rule [] []
  end.

Ltac in_stlc_unit := apply named_list_lookup_err_in; vm_compute; reflexivity.

(* ---------------------------------------------------------------- *)
(* The rules, read off the compiled language                          *)
(* ---------------------------------------------------------------- *)

Definition r_id_right := Eval vm_compute in rule_of "id_right".
Definition r_id_left := Eval vm_compute in rule_of "id_left".
Definition r_cmp_assoc := Eval vm_compute in rule_of "cmp_assoc".
Definition r_val_subst_id := Eval vm_compute in rule_of "val_subst_id".
Definition r_val_subst_cmp := Eval vm_compute in rule_of "val_subst_cmp".
Definition r_cmp_forget := Eval vm_compute in rule_of "cmp_forget".
Definition r_id_emp_forget := Eval vm_compute in rule_of "id_emp_forget".
Definition r_wkn_snoc := Eval vm_compute in rule_of "wkn_snoc".
Definition r_snoc_hd := Eval vm_compute in rule_of "snoc_hd".
Definition r_cmp_snoc := Eval vm_compute in rule_of "cmp_snoc".
Definition r_snoc_wkn_hd := Eval vm_compute in rule_of "snoc_wkn_hd".
Definition r_exp_subst_id := Eval vm_compute in rule_of "exp_subst_id".
Definition r_exp_subst_cmp := Eval vm_compute in rule_of "exp_subst_cmp".
Definition r_exp_subst_ret := Eval vm_compute in rule_of "exp_subst ret".
Definition r_exp_subst_app := Eval vm_compute in rule_of "exp_subst app".
Definition r_val_subst_lambda := Eval vm_compute in rule_of "val_subst lambda".
Definition r_stlc_beta := Eval vm_compute in rule_of "STLC-beta".
Definition r_val_subst_tt := Eval vm_compute in rule_of "val_subst tt".

Definition r_ret := Eval vm_compute in rule_of "ret".
Definition r_app := Eval vm_compute in rule_of "app".
Definition r_lambda := Eval vm_compute in rule_of "lambda".
Definition r_val_subst := Eval vm_compute in rule_of "val_subst".
Definition r_exp_subst := Eval vm_compute in rule_of "exp_subst".
Definition r_snoc := Eval vm_compute in rule_of "snoc".
Definition r_cmp := Eval vm_compute in rule_of "cmp".

Lemma in_id_right : In ("id_right", r_id_right) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_id_left : In ("id_left", r_id_left) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_cmp_assoc : In ("cmp_assoc", r_cmp_assoc) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_val_subst_id : In ("val_subst_id", r_val_subst_id) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_val_subst_cmp : In ("val_subst_cmp", r_val_subst_cmp) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_cmp_forget : In ("cmp_forget", r_cmp_forget) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_id_emp_forget : In ("id_emp_forget", r_id_emp_forget) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_wkn_snoc : In ("wkn_snoc", r_wkn_snoc) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_snoc_hd : In ("snoc_hd", r_snoc_hd) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_cmp_snoc : In ("cmp_snoc", r_cmp_snoc) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_snoc_wkn_hd : In ("snoc_wkn_hd", r_snoc_wkn_hd) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_exp_subst_id : In ("exp_subst_id", r_exp_subst_id) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_exp_subst_cmp : In ("exp_subst_cmp", r_exp_subst_cmp) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_exp_subst_ret : In ("exp_subst ret", r_exp_subst_ret) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_exp_subst_app : In ("exp_subst app", r_exp_subst_app) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_val_subst_lambda : In ("val_subst lambda", r_val_subst_lambda) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_stlc_beta : In ("STLC-beta", r_stlc_beta) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_val_subst_tt : In ("val_subst tt", r_val_subst_tt) stlc_unit.
Proof. in_stlc_unit. Qed.

Lemma in_ret : In ("ret", r_ret) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_app : In ("app", r_app) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_lambda : In ("lambda", r_lambda) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_val_subst : In ("val_subst", r_val_subst) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_exp_subst : In ("exp_subst", r_exp_subst) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_snoc : In ("snoc", r_snoc) stlc_unit.
Proof. in_stlc_unit. Qed.
Lemma in_cmp : In ("cmp", r_cmp) stlc_unit.
Proof. in_stlc_unit. Qed.

(* ---------------------------------------------------------------- *)
(* Generic drivers                                                    *)
(* ---------------------------------------------------------------- *)

(* A rule's context is well formed, since the language is. *)
Lemma stlc_unit_eq_rule_ctx_wf (name : string) c' e1 e2 t
  : In (name, term_eq_rule c' e1 e2 t) stlc_unit ->
    wf_ctx (Model := core_model stlc_unit) c'.
Proof.
  intro Hin.
  pose proof (rule_in_wf (l_pre := []) _ _ stlc_unit_wf Hin) as Hr.
  rewrite app_nil_r in Hr.
  inversion Hr; subst; assumption.
Qed.

(* Instantiating an equation rule at a well-formed substitution.  [s] fills in
   the rule's context, most-recent-first. *)
Lemma stlc_unit_eq_inst (name : string) c' e1 e2 t (s : subst string)
  : In (name, term_eq_rule c' e1 e2 t) stlc_unit ->
    wf_subst (Model := core_model stlc_unit) [] s c' ->
    eq_term stlc_unit [] t[/s/] e1[/s/] e2[/s/].
Proof.
  intros Hin Hs.
  eapply eq_term_subst.
  - eapply eq_term_by; exact Hin.
  - apply eq_subst_refl; exact Hs.
  - eapply stlc_unit_eq_rule_ctx_wf; exact Hin.
Qed.

(* Instantiating a term rule's congruence. *)
Lemma stlc_unit_cong_inst (name : string) c' args t' (s1 s2 : list (term string))
  : In (name, term_rule c' args t') stlc_unit ->
    eq_args (Model := core_model stlc_unit) [] c' s1 s2 ->
    eq_term stlc_unit [] t'[/with_names_from c' s2/]
      (con name s1) (con name s2).
Proof.
  intros Hin Hargs.
  eapply term_con_congruence.
  - exact Hin.
  - right; reflexivity.
  - apply stlc_unit_wf.
  - exact Hargs.
Qed.

Ltac wf_subst_solve :=
  repeat apply wf_subst_cons;
  first [ apply wf_subst_nil | eassumption ].

Ltac eq_args_solve :=
  repeat apply eq_args_cons;
  first [ apply eq_args_nil | eassumption ].

(* ---------------------------------------------------------------- *)
(* value_subst: the substitution calculus                             *)
(* ---------------------------------------------------------------- *)

Lemma eq_id_right G G' f
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] f (Ssub G G') ->
    eq_term stlc_unit [] (Ssub G G') (Cmp G G' G' f (Id G')) f.
Proof.
  intros.
  apply (stlc_unit_eq_inst in_id_right
           (s := [("f", f); ("G'", G'); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_id_left G G' f
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] f (Ssub G G') ->
    eq_term stlc_unit [] (Ssub G G') (Cmp G G G' (Id G) f) f.
Proof.
  intros.
  apply (stlc_unit_eq_inst in_id_left
           (s := [("f", f); ("G'", G'); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_cmp_assoc G1 G2 G3 G4 f g h
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] G4 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] h (Ssub G3 G4) ->
    eq_term stlc_unit [] (Ssub G1 G4)
      (Cmp G1 G2 G4 f (Cmp G2 G3 G4 g h))
      (Cmp G1 G3 G4 (Cmp G1 G2 G3 f g) h).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_cmp_assoc
           (s := [("h", h); ("g", g); ("f", f);
                  ("G4", G4); ("G3", G3); ("G2", G2); ("G1", G1)])).
  wf_subst_solve.
Qed.

Lemma eq_val_subst_id G A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Sval G A) (ValSubst G G (Id G) A v) v.
Proof.
  intros.
  apply (stlc_unit_eq_inst in_val_subst_id
           (s := [("v", v); ("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_val_subst_cmp G1 G2 G3 f g A v
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G3 A) ->
    eq_term stlc_unit [] (Sval G1 A)
      (ValSubst G1 G2 f A (ValSubst G2 G3 g A v))
      (ValSubst G1 G3 (Cmp G1 G2 G3 f g) A v).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_val_subst_cmp
           (s := [("v", v); ("A", A); ("g", g); ("f", f);
                  ("G3", G3); ("G2", G2); ("G1", G1)])).
  wf_subst_solve.
Qed.

Lemma eq_cmp_forget G G' g
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    eq_term stlc_unit [] (Ssub G Emp)
      (Cmp G G' Emp g (Forget G')) (Forget G).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_cmp_forget
           (s := [("g", g); ("G'", G'); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_id_emp_forget
  : eq_term stlc_unit [] (Ssub Emp Emp) (Id Emp) (Forget Emp).
Proof.
  apply (stlc_unit_eq_inst in_id_emp_forget (s := [])).
  wf_subst_solve.
Qed.

Lemma eq_wkn_snoc G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Ssub G G')
      (Cmp G (Ext G' A) G' (Snoc G G' g A v) (Wkn G' A)) g.
Proof.
  intros.
  apply (stlc_unit_eq_inst in_wkn_snoc
           (s := [("v", v); ("A", A); ("g", g); ("G'", G'); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_snoc_hd G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G G') ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Sval G A)
      (ValSubst G (Ext G' A) (Snoc G G' g A v) A (Hd G' A)) v.
Proof.
  intros.
  apply (stlc_unit_eq_inst in_snoc_hd
           (s := [("v", v); ("A", A); ("g", g); ("G'", G'); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_cmp_snoc G1 G2 G3 f g A v
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G2 A) ->
    eq_term stlc_unit [] (Ssub G1 (Ext G3 A))
      (Cmp G1 G2 (Ext G3 A) f (Snoc G2 G3 g A v))
      (Snoc G1 G3 (Cmp G1 G2 G3 f g) A (ValSubst G1 G2 f A v)).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_cmp_snoc
           (s := [("v", v); ("A", A); ("g", g); ("f", f);
                  ("G3", G3); ("G2", G2); ("G1", G1)])).
  wf_subst_solve.
Qed.

Lemma eq_snoc_wkn_hd G A
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    eq_term stlc_unit [] (Ssub (Ext G A) (Ext G A))
      (Snoc (Ext G A) G (Wkn G A) A (Hd G A)) (Id (Ext G A)).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_snoc_wkn_hd (s := [("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

(* ---------------------------------------------------------------- *)
(* exp_subst                                                          *)
(* ---------------------------------------------------------------- *)

Lemma eq_exp_subst_id G A e
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] e (Sexp G A) ->
    eq_term stlc_unit [] (Sexp G A) (ExpSubst G G (Id G) A e) e.
Proof.
  intros.
  apply (stlc_unit_eq_inst in_exp_subst_id
           (s := [("e", e); ("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_exp_subst_cmp G1 G2 G3 f g A e
  : wf_term stlc_unit [] G1 Senv ->
    wf_term stlc_unit [] G2 Senv ->
    wf_term stlc_unit [] G3 Senv ->
    wf_term stlc_unit [] f (Ssub G1 G2) ->
    wf_term stlc_unit [] g (Ssub G2 G3) ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] e (Sexp G3 A) ->
    eq_term stlc_unit [] (Sexp G1 A)
      (ExpSubst G1 G2 f A (ExpSubst G2 G3 g A e))
      (ExpSubst G1 G3 (Cmp G1 G2 G3 f g) A e).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_exp_subst_cmp
           (s := [("e", e); ("A", A); ("g", g); ("f", f);
                  ("G3", G3); ("G2", G2); ("G1", G1)])).
  wf_subst_solve.
Qed.

(* [exp_subst ret]: substitution commutes with the value/expression coercion.
   The rule's context interleaves the two environments, so [g] and [G'] come
   first in [s]. *)
Lemma eq_exp_subst_ret G G' g A v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] v (Sval G A) ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sexp G' A)
      (ExpSubst G' G g A (Ret G A v))
      (Ret G' A (ValSubst G' G g A v)).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_exp_subst_ret
           (s := [("g", g); ("G'", G'); ("v", v); ("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

(* ---------------------------------------------------------------- *)
(* stlc                                                               *)
(* ---------------------------------------------------------------- *)

Lemma eq_exp_subst_app G G' g A B e e'
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp G (Arr A B)) ->
    wf_term stlc_unit [] e' (Sexp G A) ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sexp G' B)
      (ExpSubst G' G g B (App G A B e e'))
      (App G' A B (ExpSubst G' G g (Arr A B) e) (ExpSubst G' G g A e')).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_exp_subst_app
           (s := [("g", g); ("G'", G'); ("e'", e'); ("e", e);
                  ("B", B); ("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_val_subst_lambda G G' g A B e
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp (Ext G A) B) ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sval G' (Arr A B))
      (ValSubst G' G g (Arr A B) (Lam G A B e))
      (Lam G' A B
         (ExpSubst (Ext G' A) (Ext G A)
            (Snoc (Ext G' A) G (Cmp (Ext G' A) G' G (Wkn G' A) g) A (Hd G' A))
            B e)).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_val_subst_lambda
           (s := [("g", g); ("G'", G'); ("e", e);
                  ("B", B); ("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

Lemma eq_stlc_beta G A B e v
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] A Sty ->
    wf_term stlc_unit [] B Sty ->
    wf_term stlc_unit [] e (Sexp (Ext G A) B) ->
    wf_term stlc_unit [] v (Sval G A) ->
    eq_term stlc_unit [] (Sexp G B)
      (App G A B (Ret G (Arr A B) (Lam G A B e)) (Ret G A v))
      (ExpSubst G (Ext G A) (Snoc G G (Id G) A v) B e).
Proof.
  intros.
  apply (stlc_unit_eq_inst in_stlc_beta
           (s := [("v", v); ("e", e); ("B", B); ("A", A); ("G", G)])).
  wf_subst_solve.
Qed.

(* ---------------------------------------------------------------- *)
(* unit                                                               *)
(* ---------------------------------------------------------------- *)

Lemma eq_val_subst_tt G G' g
  : wf_term stlc_unit [] G Senv ->
    wf_term stlc_unit [] G' Senv ->
    wf_term stlc_unit [] g (Ssub G' G) ->
    eq_term stlc_unit [] (Sval G' Unit)
      (ValSubst G' G g Unit (Tt G)) (Tt G').
Proof.
  intros.
  apply (stlc_unit_eq_inst in_val_subst_tt
           (s := [("g", g); ("G'", G'); ("G", G)])).
  wf_subst_solve.
Qed.

(* ---------------------------------------------------------------- *)
(* Congruences                                                        *)
(* ---------------------------------------------------------------- *)

(* Note the asymmetry: the sorts of the later hypotheses, and of the conclusion,
   are instantiated at the RIGHT-hand arguments.  That is what [eq_args]
   provides and what [term_con_congruence] concludes. *)

Lemma Ret_cong G1 G2 A1 A2 v1 v2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sval G2 A2) v1 v2 ->
    eq_term stlc_unit [] (Sexp G2 A2) (Ret G1 A1 v1) (Ret G2 A2 v2).
Proof.
  intros.
  apply (stlc_unit_cong_inst in_ret
           (s1 := [v1; A1; G1]) (s2 := [v2; A2; G2])).
  eq_args_solve.
Qed.

Lemma App_cong G1 G2 A1 A2 B1 B2 e1 e2 e1' e2'
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] Sty B1 B2 ->
    eq_term stlc_unit [] (Sexp G2 (Arr A2 B2)) e1 e2 ->
    eq_term stlc_unit [] (Sexp G2 A2) e1' e2' ->
    eq_term stlc_unit [] (Sexp G2 B2)
      (App G1 A1 B1 e1 e1') (App G2 A2 B2 e2 e2').
Proof.
  intros.
  apply (stlc_unit_cong_inst in_app
           (s1 := [e1'; e1; B1; A1; G1]) (s2 := [e2'; e2; B2; A2; G2])).
  eq_args_solve.
Qed.

Lemma Lam_cong G1 G2 A1 A2 B1 B2 e1 e2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] Sty B1 B2 ->
    eq_term stlc_unit [] (Sexp (Ext G2 A2) B2) e1 e2 ->
    eq_term stlc_unit [] (Sval G2 (Arr A2 B2))
      (Lam G1 A1 B1 e1) (Lam G2 A2 B2 e2).
Proof.
  intros.
  apply (stlc_unit_cong_inst in_lambda
           (s1 := [e1; B1; A1; G1]) (s2 := [e2; B2; A2; G2])).
  eq_args_solve.
Qed.

Lemma ValSubst_cong G1 G2 G1' G2' g1 g2 A1 A2 v1 v2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Senv G1' G2' ->
    eq_term stlc_unit [] (Ssub G2 G2') g1 g2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sval G2' A2) v1 v2 ->
    eq_term stlc_unit [] (Sval G2 A2)
      (ValSubst G1 G1' g1 A1 v1) (ValSubst G2 G2' g2 A2 v2).
Proof.
  intros.
  apply (stlc_unit_cong_inst in_val_subst
           (s1 := [v1; A1; g1; G1'; G1]) (s2 := [v2; A2; g2; G2'; G2])).
  eq_args_solve.
Qed.

Lemma ExpSubst_cong G1 G2 G1' G2' g1 g2 A1 A2 e1 e2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Senv G1' G2' ->
    eq_term stlc_unit [] (Ssub G2 G2') g1 g2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sexp G2' A2) e1 e2 ->
    eq_term stlc_unit [] (Sexp G2 A2)
      (ExpSubst G1 G1' g1 A1 e1) (ExpSubst G2 G2' g2 A2 e2).
Proof.
  intros.
  apply (stlc_unit_cong_inst in_exp_subst
           (s1 := [e1; A1; g1; G1'; G1]) (s2 := [e2; A2; g2; G2'; G2])).
  eq_args_solve.
Qed.

Lemma Snoc_cong G1 G2 G1' G2' g1 g2 A1 A2 v1 v2
  : eq_term stlc_unit [] Senv G1 G2 ->
    eq_term stlc_unit [] Senv G1' G2' ->
    eq_term stlc_unit [] (Ssub G2 G2') g1 g2 ->
    eq_term stlc_unit [] Sty A1 A2 ->
    eq_term stlc_unit [] (Sval G2 A2) v1 v2 ->
    eq_term stlc_unit [] (Ssub G2 (Ext G2' A2))
      (Snoc G1 G1' g1 A1 v1) (Snoc G2 G2' g2 A2 v2).
Proof.
  intros.
  apply (stlc_unit_cong_inst in_snoc
           (s1 := [v1; A1; g1; G1'; G1]) (s2 := [v2; A2; g2; G2'; G2])).
  eq_args_solve.
Qed.

Lemma Cmp_cong X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2
  : eq_term stlc_unit [] Senv X1 Y1 ->
    eq_term stlc_unit [] Senv X2 Y2 ->
    eq_term stlc_unit [] Senv X3 Y3 ->
    eq_term stlc_unit [] (Ssub Y1 Y2) f1 f2 ->
    eq_term stlc_unit [] (Ssub Y2 Y3) g1 g2 ->
    eq_term stlc_unit [] (Ssub Y1 Y3)
      (Cmp X1 X2 X3 f1 g1) (Cmp Y1 Y2 Y3 f2 g2).
Proof.
  intros.
  apply (stlc_unit_cong_inst in_cmp
           (s1 := [g1; f1; X3; X2; X1]) (s2 := [g2; f2; Y3; Y2; Y1])).
  eq_args_solve.
Qed.
