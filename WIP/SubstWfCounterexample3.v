(* Refutation of the SIDE-CONDITION-SORT conjecture:

     Define a "side-condition sort" as a sort that appears as the sort
     of an unreferenced variable in an equation rule of the language
     (a variable of the equation's context that the equation's
     conclusion does not mention).

     Conjecture: if no sort in c is a side-condition sort, then

       wf_lang l -> wf_ctx l c -> wf_sort l c t ->
       wf_term l c e t -> wf_term l [] e[/s/] t ->
       map fst c = map fst s ->
       (forall x, In x (fv e) <-> In x (map fst c)) ->
       wf_subst l [] s c.

   This is FALSE.  The flaw: an inhabitation gate does not have to be
   discharged by a context VARIABLE of the gate's sort -- it can be
   discharged by a COMPOUND term, manufactured by a constructor applied
   to context variables of perfectly innocent sorts.  Restricting the
   sorts of c therefore does not control which gates open over c.

   The language (all sorts closed -- no sort takes arguments):
     A  : Sort                      ("A",  sort_rule [] [])
     B  : Sort                      ("B",  sort_rule [] [])
     S  : Sort                      ("S",  sort_rule [] [])
     bb : B                         ("bb", term_rule [] [] B)
     f  : (q:A) -> S                ("f",  term_rule [q:A] S)
     h  : (p:B) -> B                ("h",  term_rule [p:B] B)
     E  : [w : S] |- A == B         (sort_eq_rule)

   The only equation is E; its only context variable w is unreferenced
   (the conclusion A == B is closed), so the side-condition sorts of
   the language are exactly [S].

   The counterexample:
     c = [x : A],  e = h x,  t = B,  s = [x |-> bb].

   - No sort of c is a side-condition sort: c's sorts are [A], and A
     is not S (we even prove head-symbol disjointness, which subsumes
     comparison up to renaming/instantiation; and we prove the variant
     where EVERY equation-context sort counts, referenced or not).
   - wf_term l c (h x) B: the argument x is used at sort B via the
     conversion A == B, gated in c by the MANUFACTURED witness
     f x : S  (x : A is all it takes to open the gate!).
   - e[/s/] = h bb is wf in []: bb : B directly, no conversion needed.
   - fv e = [x] = dom c,  map fst c = map fst s.
   - BUT wf_subst l [] s c demands bb : A, which is UNDERIVABLE:
     in the empty context the gate never opens.  S's only constructor
     f needs a closed term of sort A; closed terms of sort A can only
     arise from B (i.e. bb) via the very conversion being gated.
     The circle never starts.

   The refutation of `bb : A` is by a 2-valued denotational model.
   All sorts are closed, so the model needs no environment at all:
     [[B]] = full,   [[A]] = [[S]] = every other sort = empty,
   and a sort's denotation depends only on its HEAD SYMBOL, so it is
   invariant under substitution.  E is vacuously sound ([[S]] empty),
   f is vacuously sound ([[A]] empty), bb and h land in [[B]] = full.
   Soundness over all judgments is proved with judge_ind; then
   wf_term l [] bb A would force [[A] = full, contradiction. *)

Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Import Core.Notations.

Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).
Notation wf_subst l :=
  (wf_subst (Model:= core_model l)).
Notation wf_ctx l :=
  (wf_ctx (Model:= core_model l)).
Notation wf_args l :=
  (wf_args (Model:= core_model l)).
Notation eq_subst l :=
  (eq_subst (Model:= core_model l)).

(* ------------------------------------------------------------------ *)
(* Side-condition sorts (the user's definition, formalized)            *)
(* ------------------------------------------------------------------ *)

Definition sort_head (t : sort) : string :=
  match t with scon n _ => n end.

(* The sorts of the context variables of an equation rule that are not
   referenced by the equation's conclusion(s). *)
Definition rule_side_condition_sorts (r : rule) : list sort :=
  match r with
  | sort_eq_rule c' t1 t2 =>
      let used := fv_sort t1 ++ fv_sort t2 in
      map snd (filter (fun p => negb (existsb (String.eqb (fst p)) used)) c')
  | term_eq_rule c' e1 e2 t =>
      let used := fv e1 ++ fv e2 ++ fv_sort t in
      map snd (filter (fun p => negb (existsb (String.eqb (fst p)) used)) c')
  | _ => []
  end.

Definition side_condition_sorts (l : lang) : list sort :=
  flat_map (fun p => rule_side_condition_sorts (snd p)) l.

(* "t is not a side-condition sort", compared at the head symbol.
   Head-symbol disjointness is the MOST GENEROUS reading: it is implied
   by syntactic equality, by equality up to renaming, and by
   "is an instance of"; refuting the property under this hypothesis
   refutes it under every finer comparison. *)
Definition side_condition_free (l : lang) (c : ctx) : Prop :=
  forall t, In t (map snd c) ->
            ~ In (sort_head t) (map sort_head (side_condition_sorts l)).

(* Even stronger variant: count EVERY equation-context sort,
   referenced or not. *)
Definition equation_ctx_sorts (l : lang) : list sort :=
  flat_map (fun p => match snd p with
                     | sort_eq_rule c' _ _ => map snd c'
                     | term_eq_rule c' _ _ _ => map snd c'
                     | _ => []
                     end) l.

Definition equation_ctx_sort_free (l : lang) (c : ctx) : Prop :=
  forall t, In t (map snd c) ->
            ~ In (sort_head t) (map sort_head (equation_ctx_sorts l)).

(* ------------------------------------------------------------------ *)
(* The language and the counterexample data                            *)
(* ------------------------------------------------------------------ *)

Definition A_ : sort := scon "A" [].
Definition B_ : sort := scon "B" [].
Definition S_ : sort := scon "S" [].
Definition bb_ : term := con "bb" [].
Definition f_ (e : term) : term := con "f" [e].
Definition h_ (e : term) : term := con "h" [e].

(* snoc order: later entries are earlier rules. *)
Definition cex3_lang : lang :=
  [("E", sort_eq_rule [("w", S_)] A_ B_);
   ("h", term_rule [("p", B_)] ["p"] B_);
   ("f", term_rule [("q", A_)] ["q"] S_);
   ("bb", term_rule [] [] B_);
   ("S", sort_rule [] []);
   ("B", sort_rule [] []);
   ("A", sort_rule [] [])].

Definition cex3_c : ctx := [("x", A_)].
Definition cex3_e : term := h_ (var "x").
Definition cex3_t : sort := B_.
Definition cex3_s : subst := [("x", bb_)].

(* Sanity: the side-condition sorts of the language are exactly [S]. *)
Lemma cex3_sc_sorts : side_condition_sorts cex3_lang = [S_].
Proof. reflexivity. Qed.

(* The hypothesis of the conjecture HOLDS: no sort of c is a
   side-condition sort. *)
Lemma cex3_side_condition_free : side_condition_free cex3_lang cex3_c.
Proof.
  intros t Ht; cbn in Ht.
  destruct Ht as [Ht|[]]; subst.
  cbn. intuition congruence.
Qed.

(* It even holds in the strongest form: c's sort heads are disjoint
   from the heads of ALL equation-context sorts. *)
Lemma cex3_equation_ctx_sort_free : equation_ctx_sort_free cex3_lang cex3_c.
Proof.
  intros t Ht; cbn in Ht.
  destruct Ht as [Ht|[]]; subst.
  cbn. intuition congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* The denotational model                                              *)
(* ------------------------------------------------------------------ *)

(* All sorts of the language are closed, so the model needs no
   environment: a sort denotes full (true) or empty (false) by its
   head symbol alone.  Only B is inhabited. *)
Definition den_sort (t : sort) : bool :=
  match t with scon n _ => String.eqb n "B" end.

(* The denotation only looks at the head, so it is substitution
   invariant -- this is what makes the soundness proof trivial
   compared to a model with environments. *)
Lemma den_sort_subst (s : subst) t : den_sort t[/s/] = den_sort t.
Proof. destruct t; reflexivity. Qed.

(* c is satisfiable: every declared sort is nonempty. *)
Definition sat (c : ctx) : Prop :=
  forall p, In p c -> den_sort (snd p) = true.

(* ------------------------------------------------------------------ *)
(* Soundness of the model, by judge_ind                                *)
(* ------------------------------------------------------------------ *)

Lemma model_soundness
  : (forall c t1 t2,
        eq_sort cex3_lang c t1 t2 ->
        sat c -> den_sort t1 = den_sort t2)
    /\ (forall c t e1 e2,
           eq_term cex3_lang c t e1 e2 ->
           sat c -> den_sort t = true)
    /\ (forall c c' s1 s2,
           eq_subst cex3_lang c c' s1 s2 ->
           sat c -> sat c')
    /\ (forall c t, wf_sort cex3_lang c t -> True)
    /\ (forall c e t,
           wf_term cex3_lang c e t ->
           sat c -> den_sort t = true)
    /\ (forall c s c',
           wf_args cex3_lang c s c' ->
           sat c -> sat c')
    /\ (forall c, wf_ctx cex3_lang c -> True).
Proof.
  apply judge_ind.
  (* eq_sort_by: only rule E = [w:S] |- A == B; sat c gives [[S]] full,
     but [[S]] is empty: vacuous. *)
  - intros c name t1 t2 Hin Hsat.
    cbn in Hin.
    destruct Hin as [Hin|Hin].
    2: { exfalso; repeat (destruct Hin as [Hin|Hin]; [congruence|]); exact Hin. }
    inversion Hin; subst.
    specialize (Hsat ("w", S_) ltac:(left; reflexivity)).
    cbv in Hsat. cbv. exact Hsat.
  (* eq_sort_subst *)
  - intros c s1 s2 c' t1' t2' Hwfc _ Heqs IHeqs Heq IHeq Hsat.
    rewrite !den_sort_subst.
    exact (IHeq (IHeqs Hsat)).
  (* eq_sort_refl *)
  - intros; reflexivity.
  (* eq_sort_trans *)
  - intros c t1 t12 t2 _ IH1 _ IH2 Hsat.
    etransitivity; [exact (IH1 Hsat) | exact (IH2 Hsat)].
  (* eq_sort_sym *)
  - intros c t1 t2 _ IH Hsat. symmetry. exact (IH Hsat).
  (* eq_term_subst *)
  - intros c s1 s2 c' t e1 e2 Hwfc _ Heqs IHeqs Heqt IHeqt Hsat.
    rewrite den_sort_subst.
    exact (IHeqt (IHeqs Hsat)).
  (* eq_term_by: no term equations in the language *)
  - intros c name t e1 e2 Hin.
    exfalso; cbn in Hin.
    repeat (destruct Hin as [Hin|Hin]; [congruence|]); exact Hin.
  (* eq_term_refl *)
  - intros c e t _ IH Hsat. exact (IH Hsat).
  (* eq_term_trans *)
  - intros c t e1 e12 e2 _ IH1 _ IH2 Hsat. exact (IH1 Hsat).
  (* eq_term_sym *)
  - intros c t e1 e2 _ IH Hsat. exact (IH Hsat).
  (* eq_term_conv *)
  - intros c t t' Heq IHeq e1 e2 _ IHe Hsat.
    rewrite <- (IHeq Hsat). exact (IHe Hsat).
  (* eq_subst_nil *)
  - intros c Hsat p Hp. destruct Hp.
  (* eq_subst_cons *)
  - intros c c' s1 s2 _ IHeqs name t e1 e2 _ IHeqt Hsat p Hp.
    destruct Hp as [Hp|Hp].
    + subst p. cbn.
      rewrite <- (den_sort_subst s2 t).
      exact (IHeqt Hsat).
    + exact (IHeqs Hsat p Hp).
  (* wf_sort_by -> True *)
  - intros; exact I.
  (* wf_term_by: case analysis on which term rule *)
  - intros c n s args c' t Hin _ IHargs Hsat.
    rewrite den_sort_subst.
    cbn in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]];
      try congruence; inversion Hin; subst.
    + (* h : (p:B) -> B *) reflexivity.
    + (* f : (q:A) -> S : vacuous, [[A]] is empty *)
      specialize (IHargs Hsat ("q", A_) ltac:(left; reflexivity)).
      cbv in IHargs. congruence.
    + (* bb : B *) reflexivity.
  (* wf_term_conv *)
  - intros c e t t' _ IHe _ IHeq Hsat.
    rewrite <- (IHeq Hsat). exact (IHe Hsat).
  (* wf_term_var *)
  - intros c n t Hin Hsat. exact (Hsat (n, t) Hin).
  (* wf_args_nil *)
  - intros c Hsat p Hp. destruct Hp.
  (* wf_args_cons *)
  - intros c s c' name e t _ IHe _ IHargs Hsat p Hp.
    destruct Hp as [Hp|Hp].
    + subst p. cbn.
      rewrite <- (den_sort_subst (with_names_from c' s) t).
      exact (IHe Hsat).
    + exact (IHargs Hsat p Hp).
  (* wf_ctx_nil -> True *)
  - exact I.
  (* wf_ctx_cons -> True *)
  - intros; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* The refutation                                                      *)
(* ------------------------------------------------------------------ *)

Lemma cex3_bb_not_A : ~ wf_term cex3_lang [] bb_ A_.
Proof.
  intro H.
  destruct model_soundness as (_ & _ & _ & _ & Hwf & _ & _).
  specialize (Hwf _ _ _ H ltac:(intros p Hp; destruct Hp)).
  cbv in Hwf. congruence.
Qed.

Lemma cex3_not_wf_subst : ~ wf_subst cex3_lang [] cex3_s cex3_c.
Proof.
  intro H.
  inversion H; subst; clear H.
  apply cex3_bb_not_A.
  (* the y-entry obligation is wf_term [] bb_ (A_[/[]/]) ≡ wf_term [] bb_ A_ *)
  assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The positive hypotheses                                             *)
(* ------------------------------------------------------------------ *)

Lemma cex3_lang_wf : wf_lang cex3_lang.
Proof.
  repeat constructor; basic_core_crush; try congruence.
  all: eapply wf_sort_by; [basic_core_crush | constructor].
Qed.

Lemma cex3_ctx_wf : wf_ctx cex3_lang cex3_c.
Proof.
  repeat ((eapply wf_sort_by + constructor); basic_core_crush); try congruence.
Qed.

Lemma cex3_t_wf : wf_sort cex3_lang cex3_c cex3_t.
Proof.
  eapply wf_sort_by; [basic_core_crush | constructor].
Qed.

(* The manufactured gate witness:  f x : S  in c. *)
Lemma cex3_fx_S : wf_term cex3_lang cex3_c (f_ (var "x")) S_.
Proof.
  change S_ with S_[/with_names_from ([("q", A_)] : ctx) [var "x"]/].
  eapply wf_term_by.
  - basic_core_crush.
  - eapply wf_args_cons.
    + cbn. eapply wf_term_var. basic_core_crush.
    + constructor.
Qed.

(* The gated conversion in c:  A == B, witnessed by f x. *)
Lemma cex3_eq_A_B : eq_sort cex3_lang cex3_c A_ B_.
Proof.
  change A_ with A_[/[("w", f_ (var "x"))] : subst/] at 1.
  change B_ with B_[/[("w", f_ (var "x"))] : subst/].
  eapply eq_sort_subst.
  - eapply eq_sort_by. cbn. left. reflexivity.
  - eapply eq_subst_cons; [constructor|].
    cbn. eapply eq_term_refl. exact cex3_fx_S.
  - repeat constructor; basic_core_crush; try congruence.
    all: eapply wf_sort_by; [basic_core_crush | constructor].
Qed.

(* Hypothesis 1: e = h x is wf in c (x used at sort B via the
   conversion). *)
Lemma cex3_e_wf : wf_term cex3_lang cex3_c cex3_e cex3_t.
Proof.
  change cex3_t with B_[/with_names_from ([("p", B_)] : ctx) [var "x"]/].
  eapply wf_term_by.
  - basic_core_crush.
  - eapply wf_args_cons.
    + cbn. eapply wf_term_conv.
      * eapply wf_term_var. basic_core_crush.
      * exact cex3_eq_A_B.
    + constructor.
Qed.

Lemma cex3_bb_wf : wf_term cex3_lang [] bb_ B_.
Proof.
  eapply (@wf_term_by string _ cex3_lang [] "bb" [] [] [] B_).
  all: [> basic_core_crush | constructor].
Qed.

(* Hypothesis 2: e[/s/] = h bb is wf in the empty context -- no
   conversion needed, bb is a B directly. *)
Lemma cex3_e_subst_wf : wf_term cex3_lang [] cex3_e[/cex3_s/] cex3_t.
Proof.
  change cex3_e[/cex3_s/] with (con (V:=string) "h" [bb_]).
  change cex3_t with B_[/with_names_from ([("p", B_)] : ctx) [bb_]/].
  eapply wf_term_by.
  - basic_core_crush.
  - eapply wf_args_cons; [| constructor].
    cbn. exact cex3_bb_wf.
Qed.

(* Hypothesis 3: domains line up. *)
Lemma cex3_fst_eq : map fst cex3_c = map fst cex3_s.
Proof. reflexivity. Qed.

(* Hypothesis 4: e mentions exactly the variables of c. *)
Lemma cex3_fv : forall x, In x (fv cex3_e) <-> In x (map fst cex3_c).
Proof. intro x; cbn; tauto. Qed.

(* ------------------------------------------------------------------ *)
(* The packaged refutations                                            *)
(* ------------------------------------------------------------------ *)

Theorem subst_wf_property_with_side_conditions_is_false
  : ~ (forall (l : lang) (c : ctx) (e : term) (t : sort) (s : subst),
          wf_lang l ->
          wf_ctx l c ->
          wf_sort l c t ->
          wf_term l c e t ->
          wf_term l [] e[/s/] t ->
          map fst c = map fst s ->
          (forall x, In x (fv e) <-> In x (map fst c)) ->
          side_condition_free l c ->
          wf_subst l [] s c).
Proof.
  intro H.
  apply cex3_not_wf_subst.
  apply (H cex3_lang cex3_c cex3_e cex3_t cex3_s
           cex3_lang_wf cex3_ctx_wf cex3_t_wf
           cex3_e_wf cex3_e_subst_wf cex3_fst_eq cex3_fv
           cex3_side_condition_free).
Qed.

(* Stronger: the property stays false even if c's sort heads avoid the
   sorts of ALL equation-context variables, referenced or not. *)
Theorem subst_wf_property_with_equation_ctx_freedom_is_false
  : ~ (forall (l : lang) (c : ctx) (e : term) (t : sort) (s : subst),
          wf_lang l ->
          wf_ctx l c ->
          wf_sort l c t ->
          wf_term l c e t ->
          wf_term l [] e[/s/] t ->
          map fst c = map fst s ->
          (forall x, In x (fv e) <-> In x (map fst c)) ->
          equation_ctx_sort_free l c ->
          wf_subst l [] s c).
Proof.
  intro H.
  apply cex3_not_wf_subst.
  apply (H cex3_lang cex3_c cex3_e cex3_t cex3_s
           cex3_lang_wf cex3_ctx_wf cex3_t_wf
           cex3_e_wf cex3_e_subst_wf cex3_fst_eq cex3_fv
           cex3_equation_ctx_sort_free).
Qed.
