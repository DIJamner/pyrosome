Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule.

 
Lemma downshift_inj n e e' : Some e' = constr_downshift n e -> e' %!n = e.
Proof.
  elim: e e' => //=; intros until e'.
  - by case => ->.
  - case nlen0: (n <=n0); [|done].
    move => someeq.
    suff: exists e, (try_map (constr_downshift n) l) = Some e.
    2:{
      apply: omap_some; eauto.
    }
    case => l'.
    move => mapeq.
    pose p := mapeq.
    move: p someeq ->.
    simpl.
    case.
    move ->.
    simpl.
    rewrite subnKC; auto.
    f_equal.
    move: H mapeq.
    elim: l l' => //=.
    move => l' _.
    by case => <- =>//=.
    intro_to and.
    case => eIH lIH.
    case leq: (try_map (constr_downshift n) l) => //=.
    case aeq: (constr_downshift n a) => //=.
    case=> <- //=.
    f_equal.
    eauto.
    apply: H; eauto.
Qed.



(*
Lemma rule_downshift_inj r r0 n : Some r0 = rule_constr_downshift n r -> r0 %%!n = r.
Proof.
  case: r => //=;
  intro_to (@eq (option rule)).
  case cc: (try_map (constr_downshift n) c); simpl; try done.
  case.
  move ->; simpl.
  f_equal.
  symmetry in cc.
  move: cc.
  Check downshift_inj.
  Search _ constr_downshift.
Admitted.*)

    
(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   Expression constructors contain the level of the sort/term rule that proves them wf.
   This is a deruijn level version of how Jon Sterling does it, but without symmetry
   
   For all judgments except wf_ctx and wf_lang,
   we assume the language and input context (where applicable) are well-formed.

   For the relational judgments, we assume all arguments are well-formed.
 *)
Inductive le_sort (l : lang) c : exp -> exp -> Prop :=
| le_sort_by : forall t1 t2,
    ({< c |- t1 <# t2}) \in l ->(*TODO: reverse <# notation?*)
    le_sort l c t1 t2
| le_sort_subst : forall s1 s2 c' t1' t2',
    le_subst l c s1 s2 c' ->
    le_sort l c' t1' t2' ->
    le_sort l c t1'[/s1/] t2'[/s2/]
| le_sort_refl : forall t,
    le_sort l c t t
| le_sort_trans : forall t1 t12 t2,
    le_sort l c t1 t12 ->
    le_sort l c t12 t2 ->
    le_sort l c t1 t2
with le_term (l : lang) c : exp -> exp -> exp -> Prop :=
| le_term_subst : forall s1 s2 c' e1 e2 t,
    le_subst l c s1 s2 c' ->
    le_term l c' e1 e2 t ->
    le_term l c e1[/s1/] e2[/s2/] t[/s2/]
    (*choosing s1 would be a strictly stronger conclusion.
      However, e2[/s2/] may not always have that type, so we must choose s2 *)
| le_term_by : forall e1 e2 t,
    ({< c |- e1 <# e2 .: t}) \in l ->
    le_term l c e1 e2 t
| le_term_refl : forall e t,
    le_term l c e e t
| le_term_trans : forall e1 e12 e2 t,
    le_term l c e1 e12 t ->
    le_term l c e12 e2 t ->
    le_term l c e1 e2 t
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv : forall e1 e2 t t',
    le_term l c e1 e2 t ->
    le_sort l c t t' ->
    le_term l c e1 e2 t'
with le_subst (l : lang) c : subst -> subst -> ctx -> Prop :=
| le_subst_nil : le_subst l c [::] [::] [::]
| le_subst_cons : forall s1 s2 c' e1 e2 t,
    le_subst l c s1 s2 c' ->
    le_term l c e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
      this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (e1::s1) (e2::s2) (t::c').

Inductive wf_sort l c : exp -> Prop :=
| wf_sort_by : forall n s c',
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (con n s)
with wf_term l c : exp -> exp -> Prop :=
| wf_term_by : forall n s c' t,
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| wf_term_conv : forall e t t',
    (* TODO: prove this isn't needed:
       wf_sort l c t' ->*)
    wf_term l c e t ->
    le_sort l c t t' ->
    wf_term l c e t'
| wf_term_var : forall n t,
    is_nth_level c n t ->
    wf_term l c (var n) t
with wf_subst l c : subst -> ctx -> Prop :=
| wf_subst_nil : wf_subst l c [::] [::]
| wf_subst_cons : forall s c' e t,
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c').

Inductive wf_ctx l : ctx -> Prop :=
| wf_ctx_nil : wf_ctx l [::]
| wf_ctx_cons : forall c v,
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c).

Variant wf_rule l : rule -> Prop :=
| wf_sort_rule : forall c,
    wf_ctx l c ->
    wf_rule l ({| c |- sort})
| wf_term_rule : forall c t,
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l ({| c |- t})
| le_sort_rule : forall c t1 t2,
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l ({< c |- t1 <# t2})
| le_term_rule : forall c e1 e2 t,
    wf_ctx l c ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l ({< c |- e1 <# e2 .: t}).

Inductive wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).


(* build a database of presuppositions and judgment facts *)
Create HintDb judgment discriminated.
Hint Constructors wf_sort le_sort
     wf_term le_term
     wf_subst le_subst
     wf_ctx wf_rule wf_lang : judgment.



(* monotonicity of judgments under language extension *)

(* Tactics *)

Ltac intro_term :=
  match goal with
  | [|- lang _ -> _] => intro
  | [|- seq (rule _) -> _] => intro
  | [|- exp _ -> _] => intro
  | [|- ctx _ -> _] => intro
  | [|- seq (exp _) -> _] => intro
  | [|- rule _ -> _] => intro
  | [|- subst _ -> _] => intro
  end.
  
Ltac solve_wf_with t :=
  solve [ (constructor + idtac); apply: t; eauto
        | intro_term; solve_wf_with t
        | move => _; solve_wf_with t].


Scheme le_sort_ind' := Minimality for le_sort Sort Prop
  with le_subst_ind' := Minimality for le_subst Sort Prop
  with le_term_ind' := Minimality for le_term Sort Prop.

Combined Scheme le_ind
         from le_sort_ind', le_subst_ind', le_term_ind'.

Scheme wf_sort_ind' := Minimality for wf_sort Sort Prop
  with wf_subst_ind' := Minimality for wf_subst Sort Prop
  with wf_term_ind' := Minimality for wf_term Sort Prop.

Combined Scheme wf_ind
         from wf_sort_ind',
         wf_subst_ind',
         wf_term_ind'.

(*TODO: needed?
Ltac expand_rule_shift :=
  match goal with
  | |- context [ {| ?c ::%! 1 |- sort}] =>
    change ({| ?c ::%! 1 |- sort})
      with ({| c |- sort})%%!1
  | |- context [ {| ?c ::%! 1 |- ?t %! 1}] =>
    change ({| ?c ::%! 1 |- ?t %! 1})
      with ({| c |- t})%%!1
  | |- context [ {<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?t1 %! 1 <# ?t2 %! 1}] =>
    change ({<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?t1 %! 1 <# ?t2 %! 1})
      with ({<c1 <# c2 |- t1 <# t2})%%!1
  | |- context [ {<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?e1%!1 <# ?e2%!1 .: ?t1 %! 1 <# ?t2 %! 1}] =>
    change ({<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?e1%!1 <# ?e2%!1 .: ?t1 %! 1 <# ?t2 %! 1})
      with ({<c1 <# c2 |- e1 <# e2 .: t1 <# t2})%%!1
  end. *)

(* TOOD: move to utils *)
Lemma is_nth_level_cons {A : eqType} l n t (r : A) : is_nth_level l n t -> is_nth_level (r::l) n t.
Proof using .  
  unfold is_nth_level.
  move /andP => [nlts] /eqP <-.
  simpl.
  apply /andP; split.
  auto.
  rewrite subSn; auto.
Qed.

Lemma wf_subst_len_eq l c s c' : wf_subst l c s c' -> size s = size c'.
Proof using .
  elim: s c'.
  - case; simpl; auto; intro_to wf_subst; by inversion.
  - intros until c'; elim: c'.
    + simpl; auto; intro_to wf_subst; by inversion.
    + simpl; intros; f_equal;
      specialize H with l1; destruct H;
      inversion H1;
      eauto with judgment.
Qed.

Lemma le_subst_len_eq_r l c s1 s2 c' : le_subst l c s1 s2 c' -> size s2 = size c'.
Proof using .
  elim: s2 s1 c'.
  - case; intros until c'; case:c'; simpl; auto; intro_to le_subst; by inversion.
  - intros until s1; case:s1; intros until c'; case:c';
      try by (intro_to le_subst; inversion).
    simpl; intros; f_equal.
    inversion H0; eauto.
Qed.
Lemma le_subst_len_eq_l l c s1 s2 c' : le_subst l c s1 s2 c' -> size s1 = size c'.
Proof using .
  elim: s1 s2 c'.
  - case; intros until c'; case:c'; simpl; auto; intro_to le_subst; by inversion.
  - intros until s2; case:s2; intros until c'; case:c';
      try by (intro_to le_subst; inversion).
    simpl; intros; f_equal.
    inversion H0; eauto.
Qed.


(* TODO: move to utils*)
Lemma nth_level_size_lt {A:eqType} l n e : @is_nth_level A l n e -> n < size l.
Proof using .
  unfold is_nth_level.
  move /andP; tauto.
Qed.


Lemma wf_is_ws l c
  : (forall t, wf_sort l c t -> ws_exp (size c) t)
    /\ (forall s c', wf_subst l c s c' -> ws_subst (size c) s)
    /\ (forall e t, wf_term l c e t -> ws_exp (size c) e).
Proof using .
  Scheme t_ind := Minimality for wf_sort Sort Prop
  with s_ind := Minimality for wf_subst Sort Prop
  with e_ind := Minimality for wf_term Sort Prop.

  Combined Scheme ind from t_ind, s_ind, e_ind.
  move: c;
  apply: ind; simpl; intros;
  try apply /andP; auto; try apply: nth_level_size_lt; eauto.
Qed.
Definition wf_is_ws_sort l c := proj1 (wf_is_ws l c).
Hint Resolve wf_is_ws_sort : judgment.

Definition wf_is_ws_subst l c := proj1 (proj2 (wf_is_ws l c)).
Hint Resolve wf_is_ws_subst : judgment.

Definition wf_is_ws_term l c := proj2 (proj2 (wf_is_ws l c)).
Hint Resolve wf_is_ws_term : judgment.

Lemma wf_is_ws_ctx l c : wf_ctx l c -> ws_ctx c.
Proof.
  elim: c; simpl; first by auto.
  intro_to wf_ctx; inversion; apply /andP; eauto with judgment.
Qed.
Hint Resolve wf_is_ws_ctx : judgment.

Lemma wf_is_ws_rule l r : wf_rule l r -> ws_rule r.
Proof.
  case: r; intro_to wf_rule; inversion; simpl.
  all: try repeat (apply /andP; split).
  all:eauto with judgment.
  give_up(*TODO: prob have to show directly *).
Admitted.
Hint Resolve wf_is_ws_rule : judgment.

Lemma le_subst_refl l c s c' : wf_subst l c s c' -> le_subst l c s s c'.
Proof using .
  elim; econstructor; eauto with judgment.
Qed.
Hint Resolve le_subst_refl : judgment.


Lemma lookup_wf l c n t c' s
  : wf_ctx l c -> is_nth_level c n t ->
    wf_subst l c' s c -> wf_term l c' (var_lookup s n) t [/s /].
Proof.
  elim: c n; simpl.
  intros n _.
  inversion.
  intro_to wf_ctx; inversion; subst.
  unfold is_nth_level.
  case: n; simpl.
  intro.
  inversion; subst.
  unfold var_lookup.
  unfold nth_level; simpl.
  (* TODO
  Search _ nth.
  rewrite
  eauto with judgment.

  Fail.*)
Admitted.


Lemma rule_in_ws l r : wf_lang l -> r \in l -> ws_rule r.
Proof using .
 elim; first by compute.
 intro_to is_true.
 rewrite in_cons; case /orP; first move /eqP ->; eauto with judgment. 
Qed.
Hint Resolve rule_in_ws : judgment.

(* Monotonicity under substitution
TODO: need wf_ctx for c' is subst case? (to get ws) *)
Lemma mono_le_subst l c
  : (forall t1 t2,
        le_sort l c t1 t2 ->
        forall c' s1 s2, le_subst l c' s1 s2 c ->
                         le_sort l c' t1[/s1/] t2[/s2/])
    /\ (forall s1 s2 c',
           le_subst l c s1 s2 c' -> ws_ctx c' ->
           forall c'' s1' s2', le_subst l c'' s1' s2' c ->
                               le_subst l c'' (subst_cmp s1 s1') (subst_cmp s2 s2') c')
    /\ (forall e1 e2 t,
           le_term l c e1 e2 t ->
           forall c' s1 s2, le_subst l c' s1 s2 c ->
                            le_term l c' e1[/s1/] e2[/s2/] t[/s2/]).
Proof with eauto with judgment using.
  move: c; apply: le_ind; intros; simpl...
  move: H3; simpl; move /andP => [wst wsc].
  constructor...
  (*TODO: this step is automatable*)
  rewrite sep_subst_cmp...
  (*TODO: this step is automatable*)
  erewrite le_subst_len_eq_r...
Qed.

Lemma mono_wf_subst l c
  : wf_lang l (*TODO: just used for wsness; handle differently? ws syntax?*)->
    (forall t,
           wf_sort l c t -> wf_ctx l c ->
           forall c' s, wf_subst l c' s c ->
                        wf_sort l c' t[/s/])
    /\ (forall s c',
           wf_subst l c s c' -> wf_ctx l c ->
           forall c'' s', wf_subst l c'' s' c ->
                          wf_subst l c'' (subst_cmp s s') c')
    /\ (forall e t,
           wf_term l c e t -> wf_ctx l c ->
           forall c' s, wf_subst l c' s c ->
                        wf_term l c' e[/s/] t[/s/]).
Proof with eauto with judgment using .
  move => wfl; move:c; apply wf_ind; intros; simpl; econstructor...
  { (* wf_term_subst *)
    (*TODO: automatable*)
    rewrite sep_subst_cmp...
    erewrite le_subst_len_eq_r...
  }
  { (* wf_term_by *)
    rewrite -sep_subst_cmp.
    unfold exp_subst; simpl...
    erewrite le_subst_len_eq_r...
    apply is_nth_level_in in H;
      apply rule_in_ws in H...
    move: H => /andP; easy.
  }
  { (* wf var*)
    unfold exp_subst; simpl.
    apply: lookup_wf...
  }
Qed.

Definition mono_subst_le_sort l c := proj1 (mono_le_subst l c).
Hint Resolve mono_subst_le_sort : judgment.

Definition mono_subst_le_subst l c := proj1 (proj2 (mono_le_subst l c)).
Hint Resolve mono_subst_le_subst : judgment.

Definition mono_subst_le_term l c := proj2 (proj2 (mono_le_subst l c)).
Hint Resolve mono_subst_le_term : judgment.

Definition mono_subst_wf_sort l c wfl := proj1 (@mono_wf_subst l c wfl).
Hint Resolve mono_subst_wf_sort : judgment.

Definition mono_subst_wf_subst l c wfl :=
  proj1 (proj2 (@mono_wf_subst l c wfl)).
Hint Resolve mono_subst_wf_subst : judgment.

Definition mono_subst_wf_term l c wfl :=
  proj2 (proj2 (@mono_wf_subst l c wfl)).
Hint Resolve mono_subst_wf_term : judgment.

Lemma wf_subst_ctx l c s c' : wf_subst l c s c' -> wf_ctx l c'.
Proof.
  elim; eauto with judgment.
Qed.
Hint Resolve wf_subst_ctx :judgment.

Lemma mono_ext_le l r c
  : (forall t1 t2,
        le_sort l c t1 t2 -> wf_rule l r ->
        le_sort (r::l) c t1 t2)
    /\ (forall s1 s2 c',
           le_subst l c s1 s2 c' ->
           wf_rule l r ->
           le_subst (r::l) c s1 s2 c')
    /\ (forall e1 e2 t,
           le_term l c e1 e2 t ->
           wf_rule l r ->
           le_term (r::l) c e1 e2 t).
Proof with eauto with judgment using.
  move: c; apply le_ind...
  all: intro_to is_true; intro H; constructor...
  all: rewrite in_cons H; by apply orbT.
Qed.

Lemma mono_ext_wf l r c  
    : (forall t,
           wf_sort l c t -> wf_ctx l c -> wf_rule l r -> wf_sort (r::l) c t)
    /\ (forall s c',
           wf_subst l c s c' -> wf_ctx l c -> wf_rule l r -> wf_subst (r::l) c s c')
    /\ (forall e t,
           wf_term l c e t -> wf_ctx l c -> wf_rule l r ->  wf_term (r::l) c e t).
Proof with eauto with judgment using .
  move: c; apply wf_ind...
  all: try by econstructor; eauto with judgment; rewrite in_cons; apply /orP; auto.
  all: try by econstructor; eauto with judgment; apply is_nth_level_cons.
  {
    econstructor...
    eapply mono_ext_le...
  }
Qed.
(* TODO: add as hint? *)

Lemma mono_ext_ctx l r c : wf_rule l r -> wf_ctx l c -> wf_ctx (r::l) c.
Proof.
  elim: c; simpl; intro_to wf_ctx; inversion; subst; constructor;
    eauto with judgment.
  eapply mono_ext_wf; eauto with judgment.  
Qed.

Lemma mono_ext_rule l r r' : wf_rule l r -> wf_rule l r' -> wf_rule (r::l) r'.
Proof using .
  move => wfr.
  inversion; constructor; try by constructor; auto.
  all: try by eapply mono_ext_wf...
  all: eapply mono_ext_ctx; eauto with judgment.
Qed.

Lemma wf_lang_prefix l1 l2 : wf_lang (l1 ++ l2) -> wf_lang l2.
Proof using .
  elim: l1; auto.
  move => r l1 IH.
  rewrite cat_cons => wfl.
  inversion wfl.
  eauto.
Qed.

Lemma wf_lang_rst : forall l a, wf_lang (a :: l) -> wf_lang l.
Proof using .
  intro_to wf_lang; inversion; eauto.
Qed.

Lemma rule_in_wf l r : wf_lang l -> r \in l -> wf_rule l r.
Proof using .
 elim; first by compute.
 intro_to is_true.
 rewrite in_cons; case /orP; first move /eqP ->; eauto using mono_ext_rule.
Qed.
Hint Resolve rule_in_wf : judgment.

Lemma le_subst_trans l c c' s1 s2 s3
  : le_subst l c s1 s2 c' -> le_subst l c s2 s3 c' ->
    le_subst l c s1 s3 c'.
Proof.
  elim: s1 s2 s3 c';
    intros until s2; case: s2;
    intros until s3; case: s3;
    intros until c'; case: c';
      eauto with judgment;
      intro_to le_subst; repeat inversion; subst.
  econstructor; eauto with judgment.
Qed.


Lemma exp_subst_strengthen e s2 e2
  : ws_exp (size s2) e -> e[/e2::s2/] = e[/s2/].
Proof.
  elim: e.
  {
    intro n.
    unfold exp_subst.
    unfold var_lookup.
    unfold nth_level.
    simpl.
    intro nlt.
    suff: (n < (size s2).+1).
    move => ->.
    rewrite nlt.
    (*TODO: some nat math*)
Admitted.

Lemma subst_cmp_strengthen e s2 s1
  : ws_subst (size s2) s1 -> subst_cmp s1 (e::s2) = subst_cmp s1 s2.
Proof.
  elim s1; simpl; auto.
  move => e1 s1' IH /andP [wse wss].
  f_equal; eauto using exp_subst_strengthen.
Qed.



Lemma id_subst_cmp s : (subst_cmp (id_subst (size s)) s) = s.
Proof.
  remember (size s) as sz.
  move: Heqsz.
  elim: sz s; simpl.
  {
    intros s H; symmetry in H; move: H.
    by move /size0nil.
  }
  {
    intros n IH; case; simpl.
    by move => /eqP //=.
    intros e s; case.
    intro neq.
    rewrite id_subst_size.
    f_equal.
    {
      unfold exp_subst; simpl.
      rewrite neq.
      unfold var_lookup.
      unfold nth_level.
      simpl.
      rewrite ltnSn.
      by rewrite sub_n_n.
    }
    {
      rewrite subst_cmp_strengthen; eauto with judgment.
      (*TODO: fairly easy*)
      give_up.
    }
  }      
Admitted.

Lemma id_subst_le l c c'
      : le_subst l c (id_subst (size c')) (id_subst (size c')) c'.
Proof.
Admitted.
Hint Resolve id_subst_le : judgment.

Lemma le_mono_ctx l c
  : (forall t1 t2,
        le_sort l c t1 t2 ->
        forall c', le_sort l (c' ++ c) t1 t2)
    /\ (forall s1 s2 c',
           le_subst l c s1 s2 c' ->
           forall c'', le_subst l  (c'' ++ c) s1 s2 c')
    /\ (forall e1 e2 t,
           le_term l c e1 e2 t ->
           forall c', le_term l (c' ++ c) e1 e2 t).
Proof with eauto with judgment using.
  move: c; apply le_ind...
  {
    intros.
    elim: c'; simpl...
    intros e c' IH.
    rewrite -(@id_subst_identity t1 (size(c'++c)))
    -(@id_subst_identity t2 (size(c'++c))).
    eapply le_sort_subst...
  }
  {
    intros.
    elim: c'; simpl...
    intros e c' IH.
    rewrite -(@id_subst_identity e1 (size(c'++c)))
    -(@id_subst_identity e2 (size(c'++c)))
    -(@id_subst_identity t (size(c'++c))).
    eapply le_term_subst...
  }
Qed.


Lemma wf_ctx_suffix l c' c : wf_ctx l (c' ++ c) -> wf_ctx l c.
Proof using .
  elim: c'; auto; simpl.
  intro_to wf_ctx; inversion; eauto.
Qed.
Hint Resolve wf_ctx_suffix : judgment.


Lemma wf_ctx_tail l t c : wf_ctx l (t :: c) -> wf_ctx l c.
Proof using .
  intro_to wf_ctx; inversion; eauto.
Qed.
Hint Resolve wf_ctx_tail : judgment.

Lemma id_subst_wf l c c'
      : wf_subst l (c'++ c) (id_subst (size c)) c.
Proof.
Admitted.
Hint Resolve id_subst_wf : judgment.



Lemma is_nth_level_suffix {A : eqType} c' c n (t : A) : is_nth_level c n t -> is_nth_level (c'++c) n t.
Proof using .
  elim: c'; simpl; auto using is_nth_level_cons.
Qed.
Hint Resolve is_nth_level_suffix : judgment.

Lemma wf_mono_ctx l c
  : wf_lang l ->
    (forall t,
        wf_sort l c t ->
        forall c', wf_ctx l (c' ++ c) -> wf_sort l (c' ++ c) t)
    /\ (forall s c',
           wf_subst l c s c' ->
           forall c'', wf_ctx l (c'' ++ c) ->
                       wf_subst l (c'' ++ c) s c')
    /\ (forall e t,
           wf_term l c e t ->
           forall c', wf_ctx l (c' ++ c) ->
                      wf_term l (c' ++ c) e t).
Proof with eauto with judgment using .
  move => wfl.
  move: c; apply wf_ind...
  {
    intros until c'.
    elim: c'; simpl...
    intros e' c' IH wfc.
    rewrite -(@id_subst_identity e (size(c'++c)))
    -(@id_subst_identity t' (size(c'++c))).
    change (e'::(c'++c)) with ([::e']++(c'++c)).
    eapply mono_subst_wf_term...
  }
Qed.

  
(* Preservation of judgments under rewriting *)
Add Parametric Relation l c : exp (le_sort l c)
   reflexivity proved by (le_sort_refl l c)
   transitivity proved by (@le_sort_trans l c)
     as le_sort_rel.
Add Parametric Relation l c c' : subst (fun x y => le_subst l c x y c')
   (*reflexivity proved by (le_subst_refl l c)
     not reflexive unless I implement ws syntax
    *)
   transitivity proved by (@le_subst_trans l c c')
   as le_subst_rel.
Add Parametric Relation l c t : exp (fun x y => le_term l c x y t)
   reflexivity proved by (fun x => le_term_refl l c x t)
   transitivity proved by (fun x y z => @le_term_trans l c x y z t)
   as le_term_rel.

Require Import Setoid Morphisms Program.Basics.

Local Notation subst_sig l c c' :=  (fun s1 s2 => le_subst l c s1 s2 c').
Local Notation term_sig l c t :=  (fun e1 e2 => le_term l c e1 e2 t).

Add Parametric Morphism l c c' : exp_subst
  with signature subst_sig l c c' ==> (le_sort l c') ==>(le_sort l c) as sort_subst_mor.
Proof.
  intro_to le_sort; inversion;
    eauto with judgment.
Qed.

Definition dep_respectful {A : Type} {B : Type}
           (R : relation A) (R' : A -> A -> relation B) :=
    Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R R'.
Local Notation "@( x , y ) : R , R'" :=
  (@dep_respectful _ _ (R%signature) (fun x y =>R'%signature))
    (right associativity, at level 56) : signature_scope.

(* We have to write the instance manually because dep_respectful
   isn't yet supported by the automatic machinery*)
Instance term_subst_mor_Proper (l : lang) (c c': ctx) t
  : Morphisms.Proper (@(_,s2) : (subst_sig l c c'), term_sig l c' t ==> term_sig l c t[/s2/])%signature exp_subst.
Proof.
  unfold Proper.
  unfold dep_respectful.
  unfold respectful.
  eauto with judgment.
Qed.

Definition term_subst_mor  : forall (l : lang) (c c' : ctx) (t : exp) (x y : subst),
       subst_sig l c c' x y ->
       forall x0 y0 : exp, le_term l c' x0 y0 t -> le_term l c x0 [/x /] y0 [/y /] t[/y/].
  refine (fun (l : lang) (c c' : ctx) (t : exp) => _).
  eapply @proper_prf.
  eauto with typeclass_instances.
  Unshelve.
  eapply term_subst_mor_Proper.
Defined.

Add Parametric Morphism l c c' c'' (_:ws_ctx c'') : subst_cmp
    with signature subst_sig l c' c'' ==> subst_sig l c c' ==> subst_sig l c c''
      as subst_subst_mor.
Proof with eauto with judgment using.
  intro_to le_subst; intros les; elim: les H...
Qed.

Add Parametric Morphism l c e : (wf_term l c e)
    with signature le_sort l c ==> impl as wf_term_sort_mor.
Proof.
  unfold impl.
  eauto with judgment.
Qed.



   
Add Parametric Morphism l c c' n : (con n)
    with signature subst_sig l c c' ==> le_sort l c as sort_con_mor.
Proof.
  intros.
  suff: (le_sort l c (con n (id_subst (size c')))[/x/] (con n (id_subst (size c')))[/y/]);
    eauto with judgment.
  rewrite !con_subst_cmp.
  erewrite <-le_subst_len_eq_l at 1; eauto.
  replace (size c') with (size y).
  rewrite !id_subst_cmp.
  eauto with judgment.
  erewrite le_subst_len_eq_r; eauto.
Qed.

(* We have to write the instance manually because dep_respectful
   isn't yet supported by the automatic machinery*)
Instance subst_cons_mor_Proper (l : lang) (c c': ctx) t
  : Morphisms.Proper (@(_,s2) : (subst_sig l c c'), term_sig l c t[/s2/] ==> subst_sig l c (t::c'))%signature
                     (flip cons).
Proof.
  unfold Proper.
  unfold dep_respectful.
  unfold respectful.
  unfold flip.
  eauto with judgment.
Qed.

Definition subst_cons_mor  : forall (l : lang) (c c' : ctx) (t : exp) (x y : subst),
       subst_sig l c c' x y ->
       forall x0 y0 : exp, le_term l c x0 y0 t[/y/] -> le_subst l c (x0::x) (y0::y) (t::c').
  refine (fun (l : lang) (c c' : ctx) (t : exp) => _).
  eapply @proper_prf.
  eauto with typeclass_instances.
  Unshelve.
  eapply subst_cons_mor_Proper.
Defined.

Instance term_con_mor_Proper (l : lang) (c c': ctx) n t
  : Morphisms.Proper (@(_,s2) : (subst_sig l c c'), term_sig l c t[/s2/])%signature (con n).
Proof.
  unfold Proper.
  unfold dep_respectful.
  intros.
  suff: (le_term l c (con n (id_subst (size c')))[/x/] (con n (id_subst (size c')))[/y/] t[/y/]);
    eauto with judgment.
  rewrite !con_subst_cmp.
  erewrite <-le_subst_len_eq_l at 1; eauto.
  replace (size c') with (size y).
  rewrite !id_subst_cmp.
  eauto with judgment.
  erewrite le_subst_len_eq_r; eauto.
Qed.

Definition term_con_mor  : forall (l : lang) (c c' : ctx) n (t : exp) (x y : subst),
       subst_sig l c c' x y -> le_term l c (con n x) (con n y) t[/y/].
  refine (fun (l : lang) (c c' : ctx) n (t : exp) => _).
  eapply @proper_prf.
  eauto with typeclass_instances.
  Unshelve.
  eapply term_con_mor_Proper.
Defined.



(*TODO: should this be true?/do I need it to be true?
Lemma wf_term_subst_mor l c (_:wf_lang l)
  : (forall s1 s2 c', le_subst l c s1 s2 c' -> wf_subst l c s1 c' <-> wf_subst l c s2 c')
    /\ (forall e1 e2 t, le_term l c e1 e2 t -> wf_term l c e1 t <-> wf_term l c e2 t).
Proof.
  Scheme le_subst_ind'' := Minimality for le_subst Sort Prop
    with le_term_ind'' := Minimality for le_term Sort Prop.
  Combined Scheme le_ind' from le_subst_ind'', le_term_ind''.
  move: c; apply: le_ind'; eauto with judgment.
  by split; intro_to wf_subst; inversion; subst; constructor; eauto with judgment.
  {
    intros;
      repeat match goal with H : _ <-> _ |- _ => destruct H end;
      split; inversion; subst; constructor; eauto with judgment.
    give_up (* TODO: this is sim. to issues past*)
    by apply H1.
    
  give_up (*subst term case; hard*).
  {
    intro_to is_true.
    move /(rule_in_wf H).
    by inversion.
  }
  { (*Conv
      Needs to be iff for this case?
      TODOTODOTODOTODO: this case is very bad!
      only hope? show that

*)
 
  
  intro_to wf_term; inversion; subst.
              | constructor]; eauto with judgment.
  {
     subst.
    constructor; eauto with judgment.
      
Add Parametric Morphism l c c' : (flip (wf_subst l c) c')
    with signature subst_sig l c c' ==> impl as wf_subst_mor.
Proof.
  unfold impl.
  intros s1 s2.
  elim; eauto with judgment.
  TODO: must be mutual w/ terms.
  
Add Parametric Morphism l c : (wf_sort l c)
    with signature le_sort l c ==> impl as wf_sort_mor.
Proof.
Add Parametric Morphism l c : (wf_sort l c)
    with signature le_sort l c ==> impl as wf_sort_mor.
Proof.
  unfold impl.
  *)

Lemma sort_subst_mor_Proper
  : forall (l : lang) (c c' : ctx),
       Morphisms.Proper (le_sort l c ==> le le_sort l c') [eta exp_subst s]


Check sort_subst_mor_Proper.



sort_subst_mor = 
fun (l : lang) (c : ctx) (s : subst) => Morphisms.proper_prf
     : forall (l : lang) (c : ctx) (s : subst) (x y : exp),
       le_sort l c x y -> le_sort l c ([eta exp_subst s] x) ([eta exp_subst s] y)

Arguments sort_subst_mor [l c] _ [x y]


Lemma le_preserves_wf l c
  : wf_lang l ->
    (forall s1 s2 c',
        le_subst l c s1 s2 c' -> wf_subst l c s1 c' -> wf_subst l c s2 c')
    /\ (forall e1 e2 t,
        le_term l c e1 e2 t -> wf_term l c e1 t -> wf_term l c e2 t).
Proof.
  Scheme le_subst_ind'' := Minimality for le_subst Sort Prop
    with le_term_ind'' := Minimality for le_term Sort Prop.
  Combined Scheme le_ind' from le_subst_ind'', le_term_ind''.
  intro wfl.
  move: c; apply le_ind'; eauto with judgment.
  by intro_to wf_subst; inversion; subst; constructor; eauto with judgment.
  {
    intros.
    eapply mono_subst_wf_term; auto.
    apply: H2.
    
  }
  intr
  
Lemma le_preserves_wf_sort l c t1 t2
  : wf_lang l -> le_sort l c t1 t2 -> wf_sort l c t1 -> wf_sort l c t2.
Proof.
  intro wfl.
  elim; eauto with judgment.
  {
    intro_to is_true; move /(rule_in_wf wfl).
    inversion; eauto with judgment.
  }
  {
    intros.
    TODO: depends on the same property for substs (which will be mutual w/ terms)
  
Lemma wf_term_sort l c e t : wf_lang l -> wf_term l c e t -> wf_sort l c t.
Proof using .
  intro wfl.
  elim; intros.
  {
    move: H => /is_nth_level_in.
    move /(rule_in_wf wfl).
    inversion; eauto with judgment.  
  }
  {
  
  eauto with judgment.
    by inversion. Qed.
Hint Immediate wf_term_sort : judgment.

Lemma le_term_sort l c e1 e2 t
  : le_term l c e1 e2 t -> wf_sort l c t.
Proof using . by inversion. Qed.
Hint Immediate le_term_sort : judgment.


(* Presuppositions of term well-formedness *)
Lemma le_term_term_l l c e1 e2 t
  : le_term l c e1 e2 t -> wf_term l c e1 t.
Proof using . inversion; try done. Qed.
Hint Immediate le_term_term_l : judgment.

Lemma le_term_term_r l c e1 e2 t
  : le_term l c e1 e2 t -> wf_term l c e2 t.
Proof using . by inversion. Qed.
Hint Immediate le_term_term_r : judgment.


(* Presuppositions of subst well-formedness *)
Lemma le_subst_subst_l l c s1 s2 c'
  : le_subst l c s1 s2 c' -> wf_subst l c s1 c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_subst_l : judgment.

Lemma le_subst_subst_r l c s1 s2 c'
  : le_subst l c s1 s2 c' -> wf_subst l c s2 c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_subst_r : judgment.





(* ==============================
   Context relation transitivity
   ============================= *)



(* manual induction scheme *)
Lemma nat2_mut_ind (Pl Pr : nat -> Prop)
  : Pl 0 ->
    Pr 0 ->
    (forall n, Pl n -> Pr n -> Pr (n.+1)) ->
    (forall n, Pl n -> Pr n -> Pl (n.+1)) ->
    (forall n, Pl n /\ Pr n).
Proof using .
  move => Pl0 Pr0 Plr Prl.
  elim; auto.
  move => n; case => Pln Prn; split; auto.
Qed.

Scheme ctx_refl_ind := Minimality for wf_ctx Sort Prop.


Scheme wf_sort_subst_props_ind := Minimality for wf_sort Sort Prop
  with wf_subst_subst_props_ind := Minimality for wf_subst Sort Prop
  with wf_term_subst_props_ind := Minimality for wf_term Sort Prop.

Combined Scheme subst_props_ind from
         wf_sort_subst_props_ind,
wf_subst_subst_props_ind,
wf_term_subst_props_ind.
(*TODO: will eventually want a library of betterinduction schemes for same reason I wantedparameters*)

      
Lemma wf_is_ws : (forall l c t, wf_sort l c t -> ws_exp (size c) t)
                 /\ (forall l c s c', wf_subst l c s c' -> ws_subst (size c) s)
                 /\ (forall l c e t, wf_term l c e t -> ws_exp (size c) e).
Proof using .
  apply: subst_props_ind; simpl; intros; try apply /andP; auto; try apply: nth_level_size_lt; eauto.
Qed.
Definition wf_is_ws_sort := proj1 wf_is_ws.
Hint Resolve wf_is_ws_sort : judgment.

Definition wf_is_ws_subst := proj1 (proj2 wf_is_ws).
Hint Resolve wf_is_ws_subst : judgment.

Definition wf_is_ws_term := proj2 (proj2 wf_is_ws).
Hint Resolve wf_is_ws_term : judgment.
(*
Lemma wf_subst_conv l c s c' c'' : le_ctx l c' c'' -> wf_subst l c s c' -> wf_subst l c s c''.
Proof.
  elim: c' s c''; intros until s; case: s; intros until c''; case: c'';
      try solve [ eauto with judgment judgment_constructors
                | intro_to le_ctx; inversion
                | intro_to wf_subst; inversion].
  intro_to le_ctx; inversion; inversion; subst.
  suff: wf_subst l c l1 l2; [move => wfs | by apply: H; eauto with judgment].
  econstructor; try by eauto with judgment.
  suff: le_sort l c c a[/l1/] a1[/l1/].
  eauto with judgment_constructors judgment.
  eapply le_sort_subst; 
    eauto with judgment_constructors judgment.
  by apply: le_ctx_refl.
  inversion H8; subst.
  suff: le_subst l c c l1 l1 
  2:{
    
    need to go from a < a1 to a[/l1/] < ...
  econstructor; auto.
  auto with judgment judgment_constructors.
  TODO: is this true?

  
Lemma le_sort_subst l c1 c2 t1 t2 : wf_subst c s c1 -> le_sort l c1 c2 t1 t2 -> le_sort l c c t1[/l1/] t2[/l1/].


TODO: do I need to mix in something about relatedness below?
 *)

Lemma wf_ctx_suffix l c' c : wf_ctx l (c' ++ c) -> wf_ctx l c.
Proof using .
  elim: c'; auto; simpl.
  intro_to wf_ctx; inversion; eauto.
Qed.
Hint Immediate wf_ctx_suffix : judgment.

(*
Lemma wf_subst_conv l c1 s c2 : wf_subst l c1 s c2 -> forall c2', le_ctx l c2' c2 -> wf_subst l c1 s c2'.
Proof.
  elim; eauto with judgment; intros until c2'; inversion.
  eauto with judgment judgment_constructors.
  constructor; eauto with judgment.
  subst.
  eapply wf_term_conv; eauto with judgment.
  TODO: needs to be in the mutualbelow?*)





Scheme le_sort_mono_ctx_ind := Minimality for le_sort Sort Prop
  with le_subst_mono_ctx_ind := Minimality for le_subst Sort Prop
  with le_term_mono_ctx_ind := Minimality for le_term Sort Prop
  with wf_sort_mono_ctx_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ctx_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_ctx_ind := Minimality for wf_term Sort Prop.

Combined Scheme mono_ctx_ind from
         le_sort_mono_ctx_ind,
         le_subst_mono_ctx_ind,
         le_term_mono_ctx_ind,
         wf_sort_mono_ctx_ind,
         wf_subst_mono_ctx_ind,
         wf_term_mono_ctx_ind.

(*
Lemma wf_id_subst l c c' :  wf_ctx l (c'++c) -> wf_subst l (c' ++ c) (id_subst (size c)) c.
Proof with eauto with judgment judgment_constructors.
  elim: c c'; simpl...
  intros; constructor...
  move: H0; rewrite -!cat_rcons; by eauto.
  apply wf_ctx_suffix in H0; by inversion H0.
  rewrite id_subst_identity id_subst_size.
  constructor...
  {
    elim: c' H0; simpl.
    - inversion.
  
  idtac...
  Search _ id_subst.
  Search _ (wf_ctx _ (_++_)).
  *)

Lemma is_nth_level_cat {A : eqType} l (a : A) l' : is_nth_level (l ++ a :: l') (size l') a.
Proof using .
  unfold is_nth_level.
  apply /andP; split;
  rewrite size_cat; simpl.
  apply: ltn_addl; auto.
  rewrite addnC; rewrite add_sub.
  elim: l; simpl; auto.
Qed.

(* manual induction scheme *)
Lemma nat3_mut_ind' (Pl Pr1 Pr2 : nat -> Prop)
  : Pl 0 ->
    Pr1 0 ->
    Pr2 0 ->
    (forall n, Pl n -> Pr1 n -> Pr1 (n.+1)) ->
    (forall n, Pl n -> Pr1 n -> Pr2 n -> Pr2 n.+1) ->
    (forall n, Pr1 n -> Pr2 n -> Pl n) ->
    (forall n, Pl n /\ Pr1 n /\ Pr2 n).
Proof using .
  move => Pl0 Pr10 Pr20 Plr1 Plr2 Prl.
  elim; auto.
  move => n; case => Pln Prn; split; eauto.
  apply: Prl.
  apply: Plr1; auto.
  tauto.
  apply: Plr2; auto.
  tauto.
  tauto.
  split.
  apply: Plr1; auto; tauto.
  apply: Plr2; auto.
  tauto.
  tauto.
Qed.

(* TODO: move to utils *)
Ltac rewrite_matching lem c :=
      match goal with [ H : context[c] |- _] =>
                      rewrite lem in H end.


Lemma is_nth_level_suffix {A : eqType} c' c n (t : A) : is_nth_level c n t -> is_nth_level (c'++c) n t.
Proof using .
  elim: c'; simpl; auto using is_nth_level_cons.
Qed.

Lemma mono_ctx'
  : forall n, ((forall (l : lang) c t1 t2,
                              le_sort l c t1 t2 ->
                              n >= (size c).+1 ->
                              forall c', wf_ctx l (c' ++ c) -> le_sort l (c' ++ c) t1 t2)
                          /\ (forall (l : lang) c s1 s2 c',
                                 le_subst l c s1 s2 c' ->
                                 n >= (size c).+1 ->
                                 forall c'', wf_ctx l (c'' ++ c) -> le_subst l  (c'' ++ c) s1 s2 c')
                          /\ (forall (l : lang) c e1 e2 t,
                                 le_term l c e1 e2 t ->
                                 n >= (size c).+1 ->
                                 forall c', wf_ctx l (c' ++ c) ->
                                 le_term l (c' ++ c) e1 e2 t)
                          /\ (forall (l : lang) c t,
                                 wf_sort l c t -> 
                                 n >= (size c).+1 ->
                                 forall c', wf_ctx l (c' ++ c) -> wf_sort l (c' ++ c) t)
                          /\ (forall (l : lang) c s c',
                                 wf_subst l c s c' ->
                                 n >= (size c).+1 -> 
                                 forall c'', wf_ctx l (c'' ++ c) ->
                                             wf_subst l (c'' ++ c) s c')
                          /\ (forall (l : lang) c e t,
                                 wf_term l c e t -> 
                                 n >= (size c).+1 ->
                     forall c', wf_ctx l (c' ++ c) ->
                                wf_term l (c' ++ c) e t))
              /\ (forall l c c', n >= (size c).+1 -> wf_ctx l (c'++c) -> wf_subst l (c' ++ c) (id_subst (size c)) c)
              /\ (forall l c c', n >= (size c).+1 -> wf_ctx l (c'++c) ->
                                 le_subst l (c' ++ c) (id_subst (size c)) (id_subst (size c)) c).
Proof with eauto with judgment using .
  eapply nat3_mut_ind'; simpl; try easy.
  {
    intros until c; elim: c; simpl; intros until c'.
    all: repeat match goal with [ H : _ /\ _ |- _] => destruct H end.
    rewrite !cats0; constructor; by eauto with judgment judgment_constructors.
    rewrite !id_subst_size.
    constructor; eauto with judgment.
    all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
    rewrite -!cat_rcons; by eauto.
    move /wf_ctx_suffix; by inversion.
    rewrite id_subst_identity.
    constructor; eauto with judgment.
    rewrite -cat_rcons.
    match goal with
      H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
    end; eauto with judgment.
    match goal with [ H : context[wf_ctx] |- _] => move: H end.
    move /wf_ctx_suffix; by inversion.
    by rewrite cat_rcons.
    by apply is_nth_level_cat.
  }
  {
    intros until c; elim: c; simpl; intros until c'.
    all: repeat match goal with [ H : _ /\ _ |- _] => destruct H end.
    rewrite !cats0; constructor; by eauto with judgment judgment_constructors.
    rewrite !id_subst_size.
    constructor; eauto with judgment.
    all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
    { (*TODO: streamline; currently copied *)
      constructor; eauto with judgment.
      all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
      rewrite -!cat_rcons; by eauto.
      move /wf_ctx_suffix; by inversion.
      rewrite id_subst_identity.
      constructor; eauto with judgment.
      rewrite -cat_rcons.
      match goal with
        H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
      end; eauto with judgment.
      match goal with [ H : context[wf_ctx] |- _] => move: H end.
      move /wf_ctx_suffix; by inversion.
        by rewrite cat_rcons.
          by apply is_nth_level_cat.
    }
    
    { (*TODO: streamline; currently copied *)
      constructor; eauto with judgment.
      all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
      rewrite -!cat_rcons; by eauto.
      move /wf_ctx_suffix; by inversion.
      rewrite id_subst_identity.
      constructor; eauto with judgment.
      rewrite -cat_rcons.
      match goal with
        H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
      end; eauto with judgment.
      match goal with [ H : context[wf_ctx] |- _] => move: H end.
      move /wf_ctx_suffix; by inversion.
        by rewrite cat_rcons.
          by apply is_nth_level_cat.
    }
    all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
    rewrite -!cat_rcons; by eauto.
    rewrite id_subst_identity.
    intros; eapply le_term_refl; eauto with judgment.
    rewrite -cat_rcons.
    match goal with
      H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
    end; eauto with judgment.
    match goal with [ H : context[wf_ctx] |- _] => move: H end.
    move /wf_ctx_suffix; by inversion.
      by rewrite cat_rcons.
      constructor; eauto with judgment.
      rewrite -cat_rcons.
      match goal with
        H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
      end; eauto with judgment.
      match goal with [ H : context[wf_ctx] |- _] => move: H end.
      move /wf_ctx_suffix; by inversion.
        by rewrite cat_rcons.
          by apply is_nth_level_cat.
  }
  intros.
  apply: mono_ctx_ind; intros.
  all: try by econstructor; eauto with judgment.
  {
    rewrite <-(@id_subst_identity t1 (size c)).
    rewrite <-(@id_subst_identity t2 (size c)).
    apply: le_sort_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment judgment_constructors.
  }
  {
    rewrite <-(@id_subst_identity t1'[/s1/] (size c)).
    rewrite <-(@id_subst_identity t2'[/s2/] (size c)).
    apply: le_sort_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment.
    eapply le_sort_subst; eauto with judgment.
  }
  {
    rewrite <-(@id_subst_identity t (size c)).
    apply: le_sort_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment.
    eapply le_sort_refl; eauto with judgment.
  }
  {
    apply: le_sort_trans; eauto with judgment.
  }
  {
    rewrite <-(@id_subst_identity e1 (size c)).
    rewrite <-(@id_subst_identity e2 (size c)).
    rewrite <-(@id_subst_identity t (size c)).
    apply: le_term_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment.
    eapply le_term_by; eauto with judgment.
  }
  by eauto with judgment judgment_constructors.
  by apply: le_term_trans; eauto with judgment.
  by apply: le_term_conv; eauto with judgment.
  {
    constructor; eauto with judgment.
    by apply: is_nth_level_suffix.
  }
Qed.

Lemma mono_ctx
  : (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 ->
        forall c', wf_ctx l (c' ++ c) -> le_sort l (c' ++ c) t1 t2)
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           forall c'', wf_ctx l (c'' ++ c) -> le_subst l  (c'' ++ c) s1 s2 c')
    /\ (forall (l : lang) c e1 e2 t,
           le_term l c e1 e2 t ->
           forall c', wf_ctx l (c' ++ c) ->
                      le_term l (c' ++ c) e1 e2 t)
    /\ (forall (l : lang) c t,
           wf_sort l c t ->
           forall c', wf_ctx l (c' ++ c) -> wf_sort l (c' ++ c) t)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' ->
           forall c'', wf_ctx l (c'' ++ c) ->
                       wf_subst l (c'' ++ c) s c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t ->
           forall c', wf_ctx l (c' ++ c) ->
                      wf_term l (c' ++ c) e t).
Proof using .
  repeat split; intros; eapply mono_ctx'; eauto.
Qed.

Lemma wf_id_subst l c : wf_ctx l c -> wf_subst l c (id_subst (size c)) c. 
Proof using .
  change c with ([::] ++ c) at 1.
  eapply mono_ctx'; eauto.
Qed.


Scheme wf_sort_mono_subst_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_subst_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_subst_ind := Minimality for wf_term Sort Prop.

Combined Scheme mono_subst_ind from
wf_sort_mono_subst_ind,
wf_subst_mono_subst_ind,
wf_term_mono_subst_ind.


Lemma subst_nil e : e [/[::]/] = e.
Proof using .
  elim: e; auto.
  unfold exp_subst; intros; simpl.
  f_equal.
  elim: l H; simpl; auto.
  intros.
  f_equal; tauto.
Qed.

Lemma subst_strengthen s' s e : ws_exp (size s) e -> e[/s'++s/] = e[/s/].
Proof using .
  elim: e.
  {
    unfold exp_subst; simpl; intros.
    unfold var_lookup.
    unfold nth_level.
    rewrite size_cat H.
    suff: n < size s' + size s => [->|].
    rewrite nth_cat.
    rewrite -addnBA; auto.
    rewrite -ltn_subRL.
    rewrite sub_n_n; simpl.
    by rewrite add_sub.
    by apply ltn_addl.
  }
  {
    intro n; elim; auto.
    unfold exp_subst; simpl.
    intro_to and; case.
    intro_to is_true; case /andP.
    intros; f_equal; f_equal; auto.
    move: (H b b0); case; auto.
  }
Qed.
 
Lemma wf_subst_drop n l c' s c : wf_subst l c' s c -> wf_subst l c' (drop n s) (drop n c).
Proof using .
  elim: n s c; first intros; rewrite ?drop0; auto.
  intros until s; case: s; intros until c; case: c; intro_to wf_subst; inversion; simpl; eauto with judgment.
Qed.
  
Lemma wf_nth l c' s c a b n : n < size c -> wf_subst l c' s c -> wf_term l c' (nth a s n) (nth b c n) [/s/].
Proof using .
  intros.
  erewrite <-(@cat_take_drop n _ s).
  erewrite <-(@cat_take_drop n _ c).
  rewrite !nth_cat.
  suff: n < size s; [ intro nlts | erewrite wf_subst_len_eq; eauto].
  rewrite !size_takel; auto.
  rewrite !ltnn.
  rewrite !sub_n_n !nth0.
  move: H0 => /(@wf_subst_drop n).
  generalize (take n s) as s'.
  elim: n c s H nlts; intros until c; case: c; try easy; intros until s; case: s; try easy.
  {
    intros e s t c; simpl.
    intro_to wf_subst; inversion; subst.
    rewrite -cat_rcons.
    rewrite subst_strengthen; auto.
    erewrite wf_subst_len_eq; eauto with judgment.
  }
  {
    intros.
    simpl.
    eauto with judgment.
  }
Qed.


Lemma ws_exp_mono sz e : ws_exp sz e -> ws_exp sz.+1 e.
Proof using .
  elim: e; simpl; auto.
  intros until l; elim: l; simpl; auto.
  intro_to and; case.
  intro_to is_true; move /andP; case.
  intros; apply /andP; split.
  exact (a0 a1).
  apply: H; auto.
Qed.
  
Lemma ws_ctx_nth l c a n : n < size c -> wf_ctx l c -> ws_exp (size c) (nth a c n).
Proof using .
  elim: n c; intros until c; case: c; try easy.
  all: intro_to wf_ctx; inversion; simpl.
  all: apply: ws_exp_mono; eauto with judgment.
Qed.

Lemma mono_subst
  : (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 ->
        forall c' s1 s2, le_subst l c' s1 s2 c ->
                         le_sort l c' t1[/s1/] t2[/s2/])
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           forall c'' s1' s2', le_subst l c'' s1' s2' c ->
                               le_subst l c'' (subst_cmp s1 s1') (subst_cmp s2 s2') c')
    /\ (forall (l : lang) c t,
           wf_sort l c t -> 
           forall c' s, wf_subst l c' s c ->
                        wf_sort l c' t[/s/])
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> 
           forall c'' s', wf_subst l c'' s' c ->
                          wf_subst l c'' (subst_cmp s s') c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> 
           forall c' s, wf_subst l c' s c ->
                        wf_term l c' e[/s/] t[/s/]).
Proof with eauto with judgment judgment_constructors using .

Scheme le_sort_mono_subst_ind' := Minimality for le_sort Sort Prop
  with le_subst_mono_subst_ind' := Minimality for le_subst Sort Prop
  with wf_sort_mono_subst_ind' := Minimality for wf_sort Sort Prop
  with wf_subst_mono_subst_ind' := Minimality for wf_subst Sort Prop
  with wf_term_mono_subst_ind' := Minimality for wf_term Sort Prop.

Combined Scheme mono_subst_ind' from
         le_sort_mono_subst_ind',
         le_subst_mono_subst_ind',
         wf_sort_mono_subst_ind',
         wf_subst_mono_subst_ind',
         wf_term_mono_subst_ind'.
  apply: mono_subst_ind';intros; simpl.
  all:idtac...
  {
    constructor...
    suff: (ws_exp (size s2) t).
    intro.
    rewrite !sep_subst_cmp; auto.
    move: (H3 c'' s1' (le_subst_subst_l H9)); inversion; subst.
    move: (H5 c'' s2' (le_subst_subst_r H9)); inversion; subst.
    apply: le_term_subst...
    all: rewrite -?sep_subst_cmp; auto.
    idtac...
    apply: wf_term_conv; eauto with judgment.
    apply: le_sort_subst...
    erewrite wf_subst_len_eq; eauto with judgment.
    inversion H1...
  }
  unfold exp_subst; simpl...
  {
    constructor...
    rewrite !sep_subst_cmp; try erewrite wf_subst_len_eq...
  }
   {
    suff: ws_exp (size s) t;[intro|].
    rewrite con_subst_cmp -sep_subst_cmp...
    apply: wf_term_by...
    rewrite sep_subst_cmp...
    erewrite wf_subst_len_eq; eauto.
    apply is_nth_level_in in H3.
    apply rule_in_wf in H3...
    inversion H3...
  }
  {
    apply: wf_term_conv...
    apply: H6.
    apply: le_subst_refl... (*TODO: add to hints*)
  }
  {
    unfold exp_subst at 1; simpl.
    (*TODO: should this be a separate lemma?*)
    unfold var_lookup.
    suff: n < size c;
      [intro nltc | eauto; move: H3 => /andP; tauto].
    suff: n<size s; [intro nlts | erewrite wf_subst_len_eq; eauto].
    erewrite fn_to_is_nth_level in H3; eauto.
    move: H3 H2 => /eqP <-.
    intros.
    unfold nth_level; rewrite nlts nltc; simpl.
    erewrite wf_subst_len_eq; eauto.
    remember (size c - n.+1) as m.
    suff: m < size c.
    2:{
      rewrite Heqm.
      rewrite ltn_subLR ?addSnnS; auto.
      by apply ltn_addl.
    }
    intro mltc.
    suff: m < size s;[intro mtls | erewrite wf_subst_len_eq; eauto].
    clear Heqm nltc nlts; elim: m mltc mtls.    
    case: c H0 H1 H4 H2; first easy; case: s; first easy; intros.
    simpl.
    inversion H4; subst.
    change (a::l0) with ([::a]++l0).
    rewrite subst_strengthen; eauto with judgment.
    erewrite wf_subst_len_eq; eauto with judgment.

    case: c H0 H1 H4 H2; case: s; simpl; try easy; intros.
    change (a::l0) with ([::a]++l0).
    rewrite subst_strengthen; eauto with judgment.
    apply: wf_nth; eauto with judgment.
    by inversion H4.
    inversion H4; subst.
    erewrite wf_subst_len_eq; eauto with judgment.
    instantiate (1:=var n).
    apply: ws_ctx_nth; eauto.
    inversion H13; eauto.
  }
Qed.


(*TODO: how many to add to hint db?*)
Definition le_subst_on_sort := proj1 mono_subst.
Hint Resolve le_subst_on_sort : judgment.

Definition le_subst_on_subst := proj1 (proj2 mono_subst).
Hint Resolve le_subst_on_subst : judgment.
 
Definition wf_subst_on_sort := proj1 (proj2 (proj2 mono_subst)).
Hint Resolve wf_subst_on_sort : judgment.
 
Definition wf_subst_on_subst := proj1 (proj2 (proj2 (proj2 mono_subst))).
Hint Resolve wf_subst_on_subst : judgment.

Definition wf_subst_on_term  := proj2 (proj2 (proj2 (proj2 mono_subst))).
Hint Resolve wf_subst_on_term : judgment.

    
(* minimal constructors *)
(* we add these as hints rather than the actual constructors
   since they require fewer hypotheses *)

Lemma wf_sort_by' : forall l c n s c',
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (con n s).
Proof using .
   eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_sort_by' : judgment.

Lemma le_sort_by' : forall l c t1 t2,
    wf_lang l ->
    ({< c |- t1 <# t2}) \in l ->
    le_sort l c t1 t2.
Proof using .
  intros.
  pose rwf := rule_in_wf H H0; inversion rwf.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_by' : judgment.

Lemma le_sort_subst' : forall l c s1 s2 c' t1 t2,
    le_subst l c s1 s2 c' ->
    le_sort l c' t1 t2 ->
    le_sort l c t1[/s1/] t2[/s2/].
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_subst' : judgment.

Lemma le_sort_refl' : forall l c t,
    wf_sort l c t ->
    le_sort l c t t.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_refl' : judgment.
  
Lemma le_sort_trans' : forall l c t1 t12 t2,
    le_sort l c t1 t12 ->
    le_sort l c t12 t2 ->
    le_sort l c t1 t2.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_trans' : judgment.

Lemma wf_term_by' : forall l c n s c' t,
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/].
Proof with (eauto with judgment judgment_constructors) using .
  intros.
  suff: wf_lang l...
  intro H1.
  suff: ({|c' |- t}) \in l.
  intro H2.
  pose rwf := rule_in_wf H1 H2.
  econstructor...
  apply: wf_subst_on_sort...
  by inversion rwf.
  eapply is_nth_level_in; eauto.
Qed.
Hint Resolve wf_term_by' : judgment.

Lemma wf_term_conv' : forall l c e t t',
    wf_term l c e t ->
    le_sort l c t t' ->
    wf_term l c e t'.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_term_conv' : judgment.

(* TODO:put somewhere better*)
Lemma wf_ctx_in l c t : wf_ctx l c -> t \in c -> wf_sort l c t.
Proof using .
  elim: c; simpl; intro_to is_true; try by compute.
  rewrite in_cons.
  inversion H0; subst.
  move /orP; case.
  move /eqP ->.
  all: intros; change (a::l0) with ([::a]++l0);
  eapply mono_ctx;
  eauto with judgment.
Qed.

Lemma wf_term_var' : forall l c n t,
    wf_ctx l c ->
    is_nth_level c n t ->
    wf_term l c (var n) t.
Proof with (eauto with judgment) using .
  intros.
  suff: wf_sort l c t; eauto using wf_term_var with judgment.
  suff: t \in c; eauto using is_nth_level_in.
  eauto using wf_ctx_in.
Qed.
Hint Resolve wf_term_var' : judgment.

Lemma le_term_by' : forall l c e1 e2 t,
    wf_lang l ->
    ({< c |- e1 <# e2 .: t}) \in l ->
    le_term l c e1 e2 t.
Proof using .
  intros.
  move: (rule_in_wf H H0).
  inversion;
  eauto using le_term_by with judgment.
Qed.
Hint Resolve le_term_by' : judgment.

Lemma le_term_subst' : forall l c s1 s2 c' e1 e2 t,
    le_subst l c s1 s2 c' ->
    le_term l c' e1 e2 t ->
    le_term l c e1[/s1/] e2[/s2/] t[/s2/].
Proof using.
  intros; apply: le_term_subst; eauto with judgment.
Qed.
Hint Resolve le_term_subst' : judgment.

Lemma le_term_refl' : forall l c e t,
    wf_term l c e t ->
    le_term l c e e t.
Proof using.
  intros; apply: le_term_refl; eauto with judgment.
Qed.
Hint Resolve le_term_refl' : judgment.
  
Lemma le_term_trans' : forall l c e1 e12 e2 t,
    le_term l c e1 e12 t ->
    le_term l c e12 e2 t ->
    le_term l c e1 e2 t.
Proof using.
  intros; apply: le_term_trans; eauto with judgment.
Qed.
Hint Resolve le_term_trans' : judgment.

Lemma le_term_conv' : forall l c e1 e2 t t',
    le_term l c e1 e2 t ->
    le_sort l c t t' ->
    le_term l c e1 e2 t'.
Proof using.
  intros; apply: le_term_conv; eauto with judgment.
Qed.
Hint Resolve le_term_conv' : judgment.

Lemma wf_subst_nil' : forall l c,
    wf_ctx l c ->
    wf_subst l c [::] [::].
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_subst_nil' : judgment.

Lemma wf_subst_cons' : forall l c s c' e t,
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c').
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_subst_cons' : judgment.

Lemma le_subst_nil' : forall l c,
    wf_ctx l c ->
    le_subst l c [::] [::] [::].
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_subst_nil' : judgment.

Lemma le_subst_cons' : forall l c s1 s2 c' e1 e2 t,
    wf_subst l c (e1::s1) (t::c') -> (*TODO: can we reduce the assumptions?*)
    le_subst l c s1 s2 c' ->
    le_term l c e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (e1::s1) (e2::s2) (t::c').
Proof using.
  intros; apply: le_subst_cons; eauto with judgment judgment_constructors.
  inversion H; eauto with judgment.
Qed.
Hint Resolve le_subst_cons' : judgment.

Hint Resolve wf_ctx_nil : judgment.

Lemma wf_ctx_cons' : forall l c v,
    wf_sort l c v ->
    wf_ctx l (v::c).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_ctx_cons' : judgment.

Lemma wf_sort_rule' : forall l c,
    wf_ctx l c ->
    wf_rule l ({| c |- sort}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_sort_rule' : judgment.

Lemma wf_term_rule' : forall l c t,
    wf_sort l c t ->
    wf_rule l ({| c |- t}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_term_rule' : judgment.

Lemma le_sort_rule' : forall l c t1 t2,
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l ({< c |- t1 <# t2}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_rule' : judgment.

Lemma le_term_rule' : forall l c e1 e2 t,
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l ({< c |- e1 <# e2 .: t}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_term_rule' : judgment.

Hint Resolve wf_lang_nil : judgment.

Lemma wf_lang_cons' : forall l r, wf_rule l r -> wf_lang (r::l).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_lang_cons' : judgment.



Lemma mono_n l'
  :  (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 -> wf_lang (l' ++ l) ->
        le_sort (l'++l) c t1 t2)
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           wf_lang (l' ++ l) ->
           le_subst (l'++l) c s1 s2 c')
    /\ (forall (l : lang) c e1 e2 t,
           le_term l c e1 e2 t ->
           wf_lang (l' ++ l) ->
           le_term (l'++l) c e1 e2 t)
    /\ (forall (l : lang) c t,
           wf_sort l c t -> wf_lang (l' ++ l) -> wf_sort (l'++l) c t)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> wf_lang (l' ++ l) -> wf_subst (l'++l) c s c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> wf_lang (l' ++ l) -> wf_term (l'++l) c e t)
    /\ (forall (l : lang) c,
           wf_ctx l c -> wf_lang (l' ++ l) ->  wf_ctx (l'++l) c).
Proof using .
  elim: l'; simpl;
    try by repeat match goal with |- _/\_ => split end;
    intros; rewrite ?constr_shift0 ?map_constr_shift0.
  intros.
  repeat match goal with |- _/\_ => split end;
    intros.
  all: by eapply mono;
  [eapply H; auto; inversion H1; apply: wf_rule_lang; eauto|
    by inversion H1].
Qed.

   
Scheme wf_rule_lang_ind := Induction for wf_rule Sort Prop
  with wf_lang_lang_ind := Induction for wf_lang Sort Prop.



Ltac suff_to_use H :=
   match goal with
    | |- ?T =>
      let T' := type of H in
      suff: T = T' => [-> //|]; f_equal
   end.


Lemma add_inj_left a b c : c + a = c + b -> a = b.
Proof.
  elim: c => //; eauto.
Qed.

Lemma inj_constr_shift e e' n : e %! n == e' %! n -> e == e'.
Proof.
  elim: e e' n; intros until e'; case: e'; simpl; auto.
  intro_to is_true.
  case /eqP.
  move /add_inj_left => ->.
  elim: l H l0; intros until l0; case: l0; simpl; auto.
  - move => a l; inversion.
  - inversion.
  - move: H0; simpl; case => H00 H01.
    move => a0 l0; inversion.
    apply /eqP; f_equal.
    f_equal.
    apply /eqP.
    apply: H00.
    apply /eqP; eauto.
    suff: (con n0 l == con n0 l0); [by case /eqP|].
    apply: H; eauto.
Qed.

Lemma inj_map_constr_shift c c' n : c::%! n == c' ::%! n -> c == c'.
Proof using .
  elim: c c'; intros until c'; case: c'; simpl; auto.
  intro_to is_true.
  case /eqP => /eqP => aeq /eqP => leq.
  apply /eqP; f_equal; apply /eqP.
  apply: inj_constr_shift; eauto.
  eauto.
Qed.

Ltac solve_subpar_eq_surjective :=
  match goal with
      | |- ?c ::%! _ = ?c' ::%! _ => 
        suff: c = c' => [-> //|]
      | |- ?e %! _ = ?e'%! _ => 
        suff: e = e' => [-> //|]
      end;
      apply /eqP;
      first[ apply: inj_map_constr_shift | apply: inj_constr_shift];
      apply /eqP;
      repeat match goal with H : _ = _ |- _ => move: H end;
      rewrite ?map_constr_shift_shift ?constr_shift_shift; eauto.


Lemma first_rule_wf l a : wf_lang (a :: l) -> wf_rule (a :: l) a.
Proof using .
  inversion. eapply mono_rule; eauto with judgment.
Qed.


(*TODO: will eventually want a library of better induction schemes for same reason I wanted parameters*)

(* TODO: move to utils*)
Lemma nth_error_size_lt {A} (l : seq A) n e : List.nth_error l n = Some e -> n < size l.
Proof.
  elim: n l => [| n IH];case; simpl; auto; try done.
Qed.

  
Ltac wf_to_ctx_from_rule :=
  intro_to is_true;
  move /rule_in_wf;
  let H := fresh in
  move => H;
  match goal with
    H : ?E, H' : ?E -> _ |- _ =>
    specialize (H' H)
  end;
  inversion H.
