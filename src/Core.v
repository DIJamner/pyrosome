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


Lemma list_downshift_inj n l l' : Some l' = try_map (constr_downshift n) l -> l' ::%!n = l.
Proof.
  elim: l l'; intros until l'; case: l' => //=.
  - on_bind_do (fun x => case: x => //=).
    on_bind_do (fun x => case: x => //=).
  - move => a0 l0.
    on_bind_do (fun x => case b1: x => //=).
    on_bind_do (fun x => case b2: x => //=).
    case => -> ->.
    simpl; f_equal.
    by apply: downshift_inj.
    by apply: H.
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
   TODO: review presuppositions
 *)
Inductive wf_sort : lang -> ctx -> exp -> Prop :=
| wf_sort_by : forall l c n s c',
    wf_lang l ->
    wf_ctx l c ->
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (con n s)
with le_sort : lang -> ctx -> exp -> exp -> Prop :=
| le_sort_by : forall l c t1 t2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    ({< c |- t1 <# t2}) \in l ->(*TODO: reverse <# notation?*)
    le_sort l c t1 t2
| le_sort_subst : forall l c s1 s2 c' t1' t2',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1'[/s1/] ->
    wf_sort l c t2'[/s2/] ->
    le_subst l c s1 s2 c' ->
    le_sort l c' t1' t2' ->
    le_sort l c t1'[/s1/] t2'[/s2/]
| le_sort_refl : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    le_sort l c t t
| le_sort_trans : forall l c t1 t12 t2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    le_sort l c t1 t12 ->
    le_sort l c t12 t2 ->
    le_sort l c t1 t2
with wf_term : lang -> ctx -> exp -> exp -> Prop :=
| wf_term_by : forall l c n s c' t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s/] ->
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| wf_term_conv : forall l c e t t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c e t ->
    le_sort l c t t' ->
    wf_term l c e t'
| wf_term_var : forall l c n t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    is_nth_level c n t ->
    wf_term l c (var n) t
with le_term : lang -> ctx -> exp -> exp -> exp -> Prop :=
| le_term_subst : forall l c s1 s2 c' e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s2/] ->
    wf_term l c e1[/s1/] t[/s2/] ->
    wf_term l c e2[/s2/] t[/s2/] ->
    le_subst l c s1 s2 c' ->
    le_term l c' e1 e2 t ->
    le_term l c e1[/s1/] e2[/s2/] t[/s2/]
    (*choosing s1 would be a strictly stronger conclusion.
      However, e2[/s2/] may not always have that type, so we must choose s2 *)
| le_term_by : forall l c e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    ({< c |- e1 <# e2 .: t}) \in l ->
    le_term l c e1 e2 t
| le_term_refl : forall l c e t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e t ->
    le_term l c e e t
| le_term_trans : forall l c e1 e12 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    le_term l c e1 e12 t ->
    le_term l c e12 e2 t ->
    le_term l c e1 e2 t
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv : forall l c e1 e2 t t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c e1 t' ->
    wf_term l c e2 t' ->
    le_term l c e1 e2 t ->
    le_sort l c t t' ->
    le_term l c e1 e2 t'
with wf_subst : lang -> ctx -> subst -> ctx -> Prop :=
| wf_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::]
| wf_subst_cons : forall l c s c' e t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c')
with le_subst : lang -> ctx -> subst -> subst -> ctx -> Prop :=
| le_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::] ->
    le_subst l c [::] [::] [::]
| le_subst_cons : forall l c s1 s2 c' e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c (e1::s1) (t::c') ->
    wf_subst l c (e2::s2) (t::c') ->
    le_subst l c s1 s2 c' ->
    le_term l c e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (e1::s1) (e2::s2) (t::c')
with wf_ctx : lang -> ctx -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c)
(* TODO: add as auxilliary judgment
with le_ctx : lang -> ctx -> ctx -> Prop :=
| le_ctx_nil : forall l,
    wf_lang l ->
    wf_ctx l [::] ->
    le_ctx l [::] [::]
| le_ctx_cons : forall l c1 c2 v1 v2,
    wf_lang l ->
    wf_ctx l (v1::c1) ->
    wf_ctx l (v2::c2) ->
    le_sort l c2 c1 v2 v1 ->
    le_ctx l (v1::c1) (v2::c2) *)
with wf_rule : lang -> rule -> Prop :=
| wf_sort_rule : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_rule l ({| c |- sort})
| wf_term_rule : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l ({| c |- t})
| le_sort_rule : forall l c t1 t2,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l ({< c |- t1 <# t2})
| le_term_rule : forall l c e1 e2 t,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l ({< c |- e1 <# e2 .: t})
with wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).

(* database of constructor hints. In general, this should be avoided 
   in favor of the databse below of related lemmas with fewer hypotheses *)
Create HintDb judgment_constructors discriminated.
Hint Constructors wf_sort le_sort
     wf_term le_term
     wf_subst le_subst
     wf_ctx wf_rule wf_lang : judgment_constructors.


(* build a database of presuppositions and judgment facts *)
Create HintDb judgment discriminated.

(* Presuppositions of language well-formedness *)
Lemma wf_sort_lang l c t : wf_sort l c t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_sort_lang : judgment.

Lemma le_sort_lang l c t1 t2 : le_sort l c t1 t2 -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_sort_lang : judgment.

Lemma wf_term_lang l c e t : wf_term l c e t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_term_lang : judgment.

Lemma le_term_lang l c e1 e2 t
  : le_term l c e1 e2 t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_term_lang : judgment.

Lemma wf_subst_lang l c s c' : wf_subst l c s c' -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_lang : judgment.

Lemma le_subst_lang l c s1 s2 c'
  : le_subst l c s1 s2 c' -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_subst_lang : judgment.

Lemma wf_ctx_lang l c : wf_ctx l c -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_ctx_lang : judgment.

Lemma wf_rule_lang l r : wf_ctx l r -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_rule_lang : judgment.


(* Presuppositions of context well-formedness *)
Lemma wf_sort_ctx l c t : wf_sort l c t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_sort_ctx : judgment.

Lemma le_sort_ctx l c t1 t2
  : le_sort l c t1 t2 -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_sort_ctx : judgment.

Lemma wf_term_ctx l c e t : wf_term l c e t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_term_ctx : judgment.

Lemma le_term_ctx l c e1 e2 t
  : le_term l c e1 e2 t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_term_ctx : judgment.

Lemma wf_subst_ctx_in l c s c' : wf_subst l c s c' -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_in : judgment.

Lemma wf_subst_ctx_out l c s c' : wf_subst l c s c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_out : judgment.

Lemma le_subst_ctx_in l c s1 s2 c'
  : le_subst l c s1 s2 c' -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_subst_ctx_in : judgment.

Lemma le_subst_ctx_out l c s1 s2 c'
  : le_subst l c s1 s2 c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_ctx_out : judgment.


(* Presuppositions of sort well-formedness *)
Lemma le_sort_sort_l l c t1 t2
  : le_sort l c t1 t2 -> wf_sort l c t1.
Proof using . by inversion. Qed.
Hint Immediate le_sort_sort_l : judgment.

Lemma le_sort_sort_r l c t1 t2
  : le_sort l c t1 t2 -> wf_sort l c t2.
Proof using . by inversion. Qed.
Hint Immediate le_sort_sort_r : judgment.

Lemma wf_term_sort l c e t : wf_term l c e t -> wf_sort l c t.
Proof using . by inversion. Qed.
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


Scheme le_sort_mono_ind := Minimality for le_sort Sort Prop
  with le_subst_mono_ind := Minimality for le_subst Sort Prop
  with le_term_mono_ind := Minimality for le_term Sort Prop
  with wf_sort_mono_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_ind := Minimality for wf_term Sort Prop
  with wf_ctx_mono_ind := Minimality for wf_ctx Sort Prop.

Combined Scheme mono_ind from
         le_sort_mono_ind,
         le_subst_mono_ind,
         le_term_mono_ind,
         wf_sort_mono_ind,
         wf_subst_mono_ind,
         wf_term_mono_ind,
         wf_ctx_mono_ind.

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


Lemma is_nth_level_cons {A : eqType} l n t (r : A) : is_nth_level l n t -> is_nth_level (r::l) n t.
Proof using .  
  unfold is_nth_level.
  move /andP => [nlts] /eqP <-.
  simpl.
  apply /andP; split.
  auto.
  rewrite subSn; auto.
Qed.

Lemma mono r
  : (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 -> wf_rule l r ->
        le_sort (r::l) c t1 t2)
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           wf_rule l r ->
           le_subst (r::l) c s1 s2 c')
    /\ (forall (l : lang) c e1 e2 t,
           le_term l c e1 e2 t ->
           wf_rule l r ->
           le_term (r::l) c e1 e2 t)
    /\ (forall (l : lang) c t,
           wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> wf_rule l r ->  wf_term (r::l) c e t)
    /\ (forall (l : lang) c,
           wf_ctx l c -> wf_rule l r ->  wf_ctx (r::l) c).
Proof using .
  apply: mono_ind; intros; eauto with judgment judgment_constructors.
  all: try solve[ constructor; move: rule_in_mono; eauto with judgment_constructors
                | rewrite !constr_shift_subst_comm; eauto with judgment_constructors
                | simpl; constructor; eauto with judgment_constructors;
                  rewrite -!constr_shift_subst_comm; auto with judgment_constructors
                | apply: le_term_conv; eauto with judgment_constructors].
  all: try by econstructor; eauto with judgment_constructors; rewrite in_cons; apply /orP; auto.
  all: try by econstructor; eauto with judgment_constructors; apply is_nth_level_cons.
Qed.
(* TODO: add as hint? *)

Lemma mono_rule l r r' : wf_rule l r -> wf_rule l r' -> wf_rule (r::l) r'.
Proof using .
  move => wfr.
  inversion; constructor; try by constructor; auto.
  all: try by eapply mono; eauto.
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
 rewrite in_cons; case /orP; first move /eqP ->; eauto using mono_rule.
Qed.
Hint Resolve rule_in_wf : judgment.


(* ==============================
   Context relation transitivity
   ============================= *)

(* TODO: move to utils*)
Lemma nth_level_size_lt {A:eqType} l n e : @is_nth_level A l n e -> n < size l.
Proof using .
  unfold is_nth_level.
  move /andP; tauto.
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

Lemma le_subst_refl l c s c' : wf_subst l c s c' -> le_subst l c s s c'.
Proof using .
  elim; econstructor; eauto with judgment judgment_constructors.
Qed.



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

Lemma mono_subst
  : (forall (l : lang) c1 c2 t1' t2',
        le_sort l c1 c2 t1' t2' ->
        forall c1' c2' s1 s2, le_subst l c1' c2' s1 s2 c1 c2 ->
                              le_sort l c1' c2' t1'[/s1/] t2'[/s2/])
    /\ (forall (l : lang) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           forall c1'' c2'' s1' s2', le_subst l c1'' c2'' s1' s2' c1 c2 ->
                                     le_subst l c1'' c2'' (subst_cmp s1 s1') (subst_cmp s2 s2') c1' c2')
    /\ (forall (l : lang) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 ->
           forall c1' c2' s1 s2, le_subst l c1' c2' s1 s2 c1 c2 ->
                                 le_term l c1' c2' e1[/s1/] e2[/s2/] t1[/s1/] t2[/s2/])
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
  apply: mono_ctx_ind.
  1-5: idtac...
  {
    intros; simpl;
      constructor...
    rewrite !sep_subst_cmp; try erewrite wf_subst_len_eq...
  }
  all: try (intros; match goal with
         |- le_term _ _ _ _ _ _ _ =>
         eapply le_term_subst;
           eauto with judgment
                    end).
  1-2:idtac...
  eapply le_term_trans...
  eapply le_term_conv...
  {
    intros; rewrite con_subst_cmp...
  }
  idtac...
  {
    intros.
    simpl.
    constructor...
    rewrite !sep_subst_cmp; try erewrite wf_subst_len_eq...
  }
  {
    intros.
    rewrite -sep_subst_cmp.
    rewrite con_subst_cmp.
    econstructor...
    rewrite sep_subst_cmp...
    all: 
    apply is_nth_level_in in H3;
    apply rule_in_wf in H3; eauto with judgment;
      inversion H3; subst; erewrite wf_subst_len_eq...
  }
  {
    intros.
    (*
      necessary steps:
      use le_subst_refl
     *)
    suff: le_ctx l c' c; [intro | eauto with judgment].
    suff: wf_subst l c'0 s c.
    intro; eapply wf_term_conv; eauto with judgment.
    apply H6.
    apply le_subst
    
    
    give_up.
    apply H6.
    
    eassumption.
    4:{
      apply H6.
      
    4: eauto.
    auto.
    done.
    3:{
      apply: H4; eauto with judgment.
      instantiate (1:=c'0).
      TODO: issue: subst is wf under lesser ctxs;
    are subst outputs contravariant?
      
  2:idtac...
  idtac...
  idtac...
  - intros.
    Print subst_cmp.
    simpl.
    
  - idtac...
  
  all: try by econstructor; eauto with judgment_constructors.



Lemma wf_subst_unequal_ctx l c1 s c2 : wf_subst l c1 s c2 -> forall c2', le_ctx l c2 c2' -> wf_subst l c1 s c2'.
Proof with eauto with judgment using .
  elim; intro_to le_ctx; inversion; subst; constructor...
  
  by eauto with judgment_constructors.
  constructor...
  
  idtac.

Lemma le_subst_unequal_ctx l c1 s c2 c2' : wf_subst l c1 s c2 -> le_ctx l c2 c2' -> le_subst l c1 c1 s s c2 c2'.
Proof with eauto with judgment using .
  elim; intro_to le_ctx; inversion; constructor...
  1-4: by eauto with judgment_constructors.
  constructor...
  
  idtac.
  
  Lemma subst_conv'
  : (forall (l : lang) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           forall c1'' c2'', le_ctx l c1'' c2'' ->
                             le_ctx l c1' c1'' ->
                             le_ctx l c2' c2'' ->
                             le_subst l c1 c2 s1 s2 c1'' c2'')
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> 
           forall c'', le_ctx l c' c'' ->
                       wf_subst l c s c'').
Proof with eauto with judgment judgment_constructors using .
  Scheme le_ind := Induction for le_subst Sort Prop
    with wf_ind := Induction for wf_subst Sort Prop.
  Combined Scheme ind from le_ind, wf_ind.
  apply: ind.
  intros until c1''; case: c1''; intros until c2''; case: c2''; try easy...
  give_up.
(*  {
    intros until c1''; case: c1''; first easy.
    intros t1'' c1'' c2''; case: c2''; first easy.
    intros t2'' c2''.
    constructor; eauto with judgment.
    - eapply H7.
 *)
  all: intros until c''; case: c''; try easy.
  idtac...
  intros t'' c''; inversion; constructor...
  TODO: needs to be mutual w/below?
  
Lemma lift_subst_wf l c' c : wf_ctx l (c'++c) -> wf_subst l (c'++c) (lift_subst (size c) (size c')) c.
Proof.
  suff: (c' = rev (rev c')); [| by rewrite revK]; move ->.
  generalize (rev c') as c'' => c''.
  clear c'.
  rewrite size_rev.
  elim: c c'';[| intros t c IH]; intro c'.
  - eauto with judgment judgment_constructors.
  - simpl.
    econstructor; eauto with judgment judgment_constructors.
    + rewrite -cat_rcons -rev_cons.
      apply: IH.
      by rewrite rev_cons cat_rcons.
    + apply wf_ctx_suffix in H; by inversion H.
    + econstructor; eauto with judgment.
      * suff: (wf_sort l c t); [ intro wft | apply wf_ctx_suffix in H; by inversion H].
        TODO: needs monoctx
        econstructor; eauto with judgment.
    simpl; auto.
    Search
    change (size c').+1 with (size (c'++[::t])).
    Search _ (_++ _::_).

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

Lemma mono_ctx
  : (forall (l : lang) c1 c2 t1' t2',
        le_sort l c1 c2 t1' t2' ->
        forall t1 t2, le_sort l c1 c2 t1 t2 ->
                      le_sort l (t1::c1) (t2::c2) t1'^!1 t2'^!1)
    /\ (forall (l : lang) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           forall t1 t2, le_sort l c1 c2 t1 t2 ->
                         le_subst l (t1::c1) (t2::c2) s1^!!1 s2^!!1 c1' c2')
    /\ (forall (l : lang) c1 c2 e1 e2 t1' t2',
           le_term l c1 c2 e1 e2 t1' t2' ->
           forall t1 t2, le_sort l c1 c2 t1 t2 ->
                         le_term l (t1::c1) (t2::c2) e1^!1 e2^!1 t1'^!1 t2'^!1)
    /\ (forall (l : lang) c t',
           wf_sort l c t' -> 
           forall t, wf_sort l c t -> wf_sort l (t::c) t'^!1)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> 
           forall t, wf_sort l c t -> wf_subst l (t::c) s^!!1 c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> 
           forall t, wf_sort l c t -> wf_term l (t::c) e^!1 t^!1).
Proof using .
  apply: mono_ctx_ind; intros; eauto with judgment_constructors; simpl.
  all: try by econstructor; eauto with judgment_constructors. (*rewrite in_cons; apply /orP; auto. *)
  erewrite !lift_is_subst; eauto with judgment.
  eapply le_sort_subst;
    try solve [ erewrite <- !lift_is_subst; eauto with judgment
              | eauto with judgment judgment_constructors].
  
  econstructor.
  give_up.
  erewrite <- !lift_is_subst.
  apply: le_subst_refl.

  
Lemma wf_subst_props c s
  : (forall l c' t, wf_sort l c' t -> wf_subst l c s c' -> wf_sort l c t[/s/])
    /\ (forall l c' s2 c2', wf_subst l c' s2 c2' -> wf_subst l c s c' -> wf_subst l c (subst_cmp s2 s) c2')
    /\ (forall l c' e t, wf_term l c' e t -> wf_subst l c s c' -> wf_term l c e[/s/] t[/s/]).
Proof.
  apply: subst_props_ind;intros; simpl.
  all: rewrite ?con_subst_cmp.
  1-2: by eauto with judgment judgment_constructors.
  {
    econstructor; rewrite ?sep_subst_cmp;
      eauto  with judgment judgment_constructors.
    eapply wf_is_ws in H4.
    erewrite wf_subst_len_eq; eauto with judgment.
  }
  {
    suff: wf_rule l ({|c' |- t}).
    2: apply is_nth_level_in in H3;
    apply rule_in_wf in H3; eauto with judgment.
    inversion; subst.
    rewrite -sep_subst_cmp.
    eapply wf_term_by; eauto with judgment.
    rewrite sep_subst_cmp; eauto with judgment.
    all: erewrite wf_subst_len_eq; eauto with judgment; by eapply wf_is_ws in H13.
  }
  {
    suff: wf_term l c' e t'; [ move => wft | by eauto with judgment judgment_constructors].
    pose H7 := H2 H6.
    (*should have IH?*)
    eapply wf_term_conv; eauto with judgment.
    apply: H4.
Admitted.

Definition wf_subst_on_sort c s := proj1 (wf_subst_props c s).
Hint Resolve wf_subst_on_sort : judgment.

Definition wf_subst_cmp c s := proj1 (proj2 (wf_subst_props c s)).
Hint Resolve wf_subst_cmp : judgment.

Definition wf_subst_on_term c s := proj2 (proj2 (wf_subst_props c s)).
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

Lemma le_sort_by' : forall l c1 c2 t1 t2,
    wf_lang l ->
    ({< c1 <# c2 |- t1 <# t2}) \in l ->
    le_sort l c1 c2 t1 t2.
Proof using .
  intros.
  pose rwf := rule_in_wf H H0; inversion rwf.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_by' : judgment.

Lemma le_sort_subst' : forall l c1 c2 s1 s2 c1' c2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1' t2' ->
    le_sort l c1 c2 t1'[/s1/] t2'[/s2/].
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_subst' : judgment.

Lemma le_sort_refl' : forall l c t,
    wf_sort l c t ->
    le_sort l c c t t.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_refl' : judgment.
  
Lemma le_sort_trans' : forall l c1 c12 c2 t1 t12 t2,
    le_ctx l c1 c2 ->
    le_sort l c1 c12 t1 t12 ->
    le_sort l c12 c2 t12 t2 ->
    le_sort l c1 c2 t1 t2.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_trans' : judgment.

Lemma wf_term_by' : forall l c n s c' t,
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/].
Proof with (eauto with judgment judgment_constructors) using .
  (* TODO: get judgment db setup to handle this proof*)
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

Lemma wf_term_conv' : forall l c e t c' t',
    wf_term l c e t ->
    le_sort l c c' t t' ->
    wf_term l c' e t'.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_term_conv' : judgment.

Lemma wf_term_var' : forall l c n t,
    wf_ctx l c ->
    List.nth_error c n = Some t ->
    wf_term l c (var n) t.
Proof with (eauto with judgment judgment_constructors) using .
  intros.
  suff: wf_sort l c t...
  suff: t \in c.
Qed.
Hint Resolve wf_term_var' : judgment.


with le_term : lang ->
               ctx -> ctx ->
               exp -> exp ->
               exp -> exp -> Prop :=
| le_term_by : forall l c1 c2 e1 e2 t1 t2,
    wf_lang l ->
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    le_sort l c1 c2 t1 t2 ->
    wf_term l c1 e1 t1 ->
    wf_term l c2 e2 t2 ->
    ({< c1 <# c2|- e1 <# e2 .: t1 <# t2}) \in l ->
    le_term l c1 c2 e1 e2 t1 t2
| le_term_subst : forall l c1 c2 s1 s2 c1' c2' e1' e2' t1' t2',
    wf_lang l ->
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_sort l c1 t1'[/s1/] ->
    wf_sort l c2 t2'[/s2/] ->
    le_sort l c1 c2 t1'[/s1/] t2'[/s2/] ->
    wf_term l c1 e1'[/s1/] t1'[/s1/] ->
    wf_term l c2 e2'[/s2/] t2'[/s2/] ->
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1' c2' e1' e2' t1' t2' ->
    le_term l c1 c2 e1'[/s1/] e2'[/s2/] t1'[/s1/] t2'[/s2/]
| le_term_refl : forall l c e t,
    wf_lang l ->
    wf_ctx l c ->
    le_ctx l c c ->
    wf_sort l c t ->
    le_sort l c c t t ->
    wf_term l c e t ->
    le_term l c c e e t t
| le_term_trans : forall l c1 c12 c2 e1 e12 e2 t1 t12 t2,
    wf_lang l ->
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    le_sort l c1 c2 t1 t2 ->
    wf_term l c1 e1 t1 ->
    wf_term l c2 e2 t2 ->
    le_term l c1 c12 e1 e12 t1 t12 ->
    le_term l c12 c2 e12 e2 t12 t2 ->
    le_term l c1 c2 e1 e2 t1 t2
(* Conversion:

c1  < c2  |- e1 < e2 : t1  < t2   ||
/\    /\               /\    /\   ||
c1' < c2' |- e1 < e2 : t1' < t2'  \/
*)
| le_term_conv : forall l c1 c2 e1 e2 t1 t2 c1' c2' t1' t2',
    wf_lang l ->
    wf_ctx l c1' ->
    wf_ctx l c2' ->
    le_ctx l c1' c2' ->
    wf_sort l c1' t1' ->
    wf_sort l c2' t2' ->
    le_sort l c1' c2' t1' t2' ->
    wf_term l c1' e1 t1' ->
    wf_term l c2' e2 t2' ->
    le_term l c1 c2 e1 e2 t1 t2 ->
    le_sort l c1 c1' t1 t1' ->
    le_sort l c2 c2' t2 t2' ->
    le_term l c1' c2' e1 e2 t1' t2'
with wf_subst : lang -> ctx -> subst -> ctx -> Prop :=
| wf_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::]
| wf_subst_cons : forall l c s c' e t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c')
with le_subst : lang ->
                ctx -> ctx ->
                subst -> subst ->
                ctx -> ctx -> Prop :=
| le_subst_nil : forall l c1 c2,
    wf_lang l ->
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_ctx l [::] ->
    le_ctx l [::] [::] ->
    wf_subst l c1 [::] [::] ->
    wf_subst l c1 [::] [::] ->
    le_subst l c1 c2 [::] [::] [::] [::]
| le_subst_cons : forall l c1 c2 s1 s2 c1' c2' e1 e2 t1 t2,
    wf_lang l ->
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_ctx l (t1::c1') ->
    wf_ctx l (t2::c2') ->
    le_ctx l (t1::c1') (t2::c2') ->
    wf_subst l c1 (e1::s1) (t1::c1') ->
    wf_subst l c2 (e2::s2) (t2::c2') ->
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1 t2 ->
    le_term l c1 c2 e1 e2 t1[/s1/] t2[/s2/] ->
    le_subst l c1 c2 (e1::s1) (e2::s2) (t1::c1') (t2 :: c2')
with wf_ctx : lang -> ctx -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c)
with le_ctx : lang -> ctx -> ctx -> Prop :=
| le_ctx_nil : forall l,
    wf_lang l ->
    wf_ctx l [::] ->
    le_ctx l [::] [::]
| le_ctx_cons : forall l c1 c2 v1 v2,
    wf_lang l ->
    wf_ctx l (v1::c1) ->
    wf_ctx l (v2::c2) -> 
    le_sort l c1 c2 v1 v2 ->
    le_ctx l (v1::c1) (v2::c2)
with wf_rule : lang -> rule -> Prop :=
| wf_sort_rule : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_rule l ({| c |- sort})
| wf_term_rule : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l ({| c |- t})
| le_sort_rule : forall l c1 c2 t1 t2,
    wf_lang l -> 
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    wf_rule l ({< c1 <# c2 |- t1 <# t2})
| le_term_rule : forall l c1 c2 e1 e2 t1 t2,
    wf_lang l -> 
    wf_ctx l c1 ->
    wf_ctx l c2 ->
    le_ctx l c1 c2 ->
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    le_sort l c1 c2 t1 t2 ->
    wf_term l c1 e1 t1 ->
    wf_term l c2 e2 t2 ->
    wf_rule l ({< c1 <# c2 |- e1 <# e2 .: t1 <# t2})
with wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).


*)




Lemma mono_n l'
  : (forall (l : lang) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_lang (l' ++ l) ->
        le_sort (l' ++ l) c1 c2 t1 t2)
    /\ (forall (l : lang) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           wf_lang (l' ++ l) ->
           le_subst (l' ++ l) c1 c2 s1 s2 c1' c2')
    /\ (forall (l : lang) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 ->
           wf_lang (l' ++ l) ->
           le_term (l' ++ l) c1 c2 e1 e2 t1 t2)
    /\ (forall (l : lang) c1 c2,
           le_ctx l c1 c2 ->
           wf_lang (l' ++ l) ->
           le_ctx (l' ++ l) c1 c2)
    /\ (forall (l : lang) c t,
           wf_sort l c t -> wf_lang (l' ++ l) -> wf_sort (l' ++ l) c t)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> wf_lang (l' ++ l) -> wf_subst (l' ++ l) c s c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> wf_lang (l' ++ l) -> wf_term (l' ++ l) c e t)
    /\ (forall (l : lang) c,
           wf_ctx l c -> wf_lang (l' ++ l) ->  wf_ctx (l' ++ l) c).
Proof.
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

(*
Lemma le_ctx_mono (l : lang) r c1 c2
                 (wfc : le_ctx l c1 c2)
  : wf_rule l r -> le_ctx (r::l) c1::%!1 c2::%!1.
Proof.
  apply mono; auto.
Qed.
(*Hint Resolve le_ctx_mono. TODO: use DBs *)

Lemma le_sort_mono l r c1 c2 t1 t2
                  (wfs : le_sort l c1 c2 t1 t2)
     : wf_rule l r -> le_sort (r::l) c1::%!1 c2::%!1 t1%!1 t2%!1.
Proof.
  apply mono; auto.
Qed.

Lemma le_subst_mono l r c1 c2 s1 s2 c1' c2'
                   (wfsb : le_subst l c1 c2 s1 s2 c1' c2')
     : wf_rule l r -> le_subst (r::l) c1::%!1 c2::%!1 s1::%!1 s2::%!1 c1'::%!1 c2'::%!1.
Proof.
  apply mono; auto.
Qed.

Lemma le_term_mono l r c1 c2 e1 e2 t1 t2
                  (wft :  le_term l c1 c2 e1 e2 t1 t2)
  : wf_rule l r -> le_term (r::l) c1::%!1 c2::%!1 e1%!1 e2%!1 t1%!1 t2%!1.
Proof.
  apply mono; auto.
Qed.

Lemma wf_sort_mono {p} (l : lang p) r c t : wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_sort_mono.
      
Lemma wf_subst_mono {p} (l : lang p) r c s c'
  : wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c'.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_subst_mono.

Lemma wf_term_mono {p} (l : lang p) r c e t
  : wf_term l c e t -> wf_rule l r -> wf_term (r::l) c e t.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_term_mono.

Lemma wf_ctx_mono {p} (l : lang p) r c : wf_ctx l c -> wf_rule l r -> wf_ctx (r::l) c.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_ctx_mono.

Lemma wf_rule_mono {p} (l : lang p) r r'
  : wf_rule l r' -> wf_rule l r -> wf_rule (r::l) r'.
Proof. 
  elim; auto.
Qed.
Hint Resolve wf_rule_mono.
 *)



   
Scheme wf_rule_lang_ind := Induction for wf_rule Sort Prop
  with wf_lang_lang_ind := Induction for wf_lang Sort Prop.



(*
Lemma is_nth_list_split m r l n
  : shifted_is_nth m r l n ->
    exists l1 r' l2, l = l1 ++ (r':: l2) /\ r = r'%%!(m + n) /\ n = (size l1).
Proof.
  elim: n l m.
  - case; simpl;
      intro_to is_true;
      [intro_to is_true; inversion|].
    rewrite addn0.
    move /eqP; intros;
    exists [::]; simpl; eauto.
  - intro_to seq.
    case; simpl; [intro_to is_true; inversion|].
    intros.
    rewrite addnS. 
    change (m + n).+1 with (m.+1 + n).
    case: (H l m.+1 H0) => l1 [r' [l2[[]]]] -> [] -> neq.
    exists (a::l1).
    exists r'.
    exists l2.
    rewrite {3}neq.
    eauto.
Qed.
*)


Lemma rule_constr_shift_0_id r : r%%!0 = r.
Proof.
  case: r => //; simpl; intros;
  by rewrite ?map_constr_shift0 ?constr_shift0.
Qed.  

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
Proof.
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

Lemma surjective_rule_shift r r' n : r %%! n == r' %%! n -> r == r'.
Proof.
  elim: n; simpl.
  - by rewrite !rule_constr_shift_0_id.
  - case: r; case: r'; simpl; auto;
      intro_to is_true;
      case /eqP;
      change (n.+1) with (1 + n);
      rewrite ![1 + _]addnC;
      rewrite -?map_constr_shift_shift -?constr_shift_shift;
      intros;   
      apply: H;
      apply /eqP; f_equal;
      solve_subpar_eq_surjective.
Qed.    

Lemma first_rule_wf l a : wf_lang (a :: l) -> wf_rule (a :: l) a.
Proof.
  inversion.
  inversion H1; subst; constructor; eapply mono; auto.
Qed.


Scheme wf_sort_subst_props_ind := Minimality for wf_sort Sort Prop
  with wf_subst_subst_props_ind := Minimality for wf_subst Sort Prop
  with wf_term_subst_props_ind := Minimality for wf_term Sort Prop.

Combined Scheme subst_props_ind from
         wf_sort_subst_props_ind,
wf_subst_subst_props_ind,
wf_term_subst_props_ind.
(*TODO: will eventually want a library of betterinduction schemes for same reason I wantedparameters*)

(* TODO: move to utils*)
Lemma nth_error_size_lt {A} (l : seq A) n e : List.nth_error l n = Some e -> n < size l.
Proof.
  elim: n l => [| n IH];case; simpl; auto; try done.
Qed.

Lemma le_ctx_len_eq  l c c' : le_ctx l c c' -> size c = size c'
with le_sort_ctx_len_eq l c c' t t' : le_sort l c c' t t' -> size c = size c'.
Proof.
  case; simpl; auto; intros; f_equal.
  apply: le_sort_ctx_len_eq; eauto.
  intro les.
  eapply wf_to_ctx in les.
  apply: le_ctx_len_eq; eauto.
TODO: get a nicer induction w/ presuppositions
  
Lemma wf_is_ws : (forall l c t, wf_sort l c t -> ws_exp (size c) t)
                 /\ (forall l c s c', wf_subst l c s c' -> ws_subst (size c) s)
                 /\ (forall l c e t, wf_term l c e t -> ws_exp (size c) e).
Proof.
  apply: subst_props_ind; simpl; intros; try apply /andP; auto; try apply: nth_error_size_lt; eauto.
  eapply wf_to_ctx in H1.
  TODO: show cssame size
Qed.


Lemma wf_subst_props c s
  : (forall l c' t, wf_sort l c' t -> wf_subst l c s c' -> wf_sort l c t[/s/])
    /\ (forall l c' s2 c2', wf_subst l c' s2 c2' -> wf_subst l c s c' -> wf_subst l c (subst_cmp s2 s) c2')
    /\ (forall l c' e t, wf_term l c' e t -> wf_subst l c s c' -> wf_term l c e[/s/] t[/s/]).
Proof.
  apply: subst_props_ind.
  {  
    intros.
    rewrite con_subst_cmp.
    eauto.
  }
  {
    intros; simpl; constructor.
    by apply wf_to_ctx in H0.
  }
  {
    intros; simpl; constructor; eauto.
    rewrite sep_subst_cmp.
    auto.
    Search _ ws_subst.
    TODO: need wf ->ws

Lemma wf_sort_subst l c s c' t : wf_sort l c' t -> wf_subst l c s c' -> wf_sort l c t[/s/].
Proof.
  inversion; subst; unfold exp_subst; simpl.
  econstructor; eauto.
  
  Print subst_cmp.

Lemma le_ctx_wf_l l c1 c2 : le_ctx l c1 c2 -> wf_ctx l c1
with le_sort_wf_l l c1 c2 t1 t2 : le_sort l c1 c2 t1 t2 -> wf_sort l c1 t1
with le_term_wf_l l c1 c2 e1 e2 t1 t2 : le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c1 e1 t1
with le_subst_wf_l l c1 c2 s1 s2 c1' c2' : le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c1 s1 c1'.
Proof.
  {
    case: c1 c2.
    case => //=; intro_to le_ctx; inversion; auto.
    intros until c2.
    case: c2; intro_to le_ctx; inversion; eauto.
  }
  {
    case.
    intros; apply rule_in_wf in i; by inversion i.
    intros until t2'; move /le_subst_wf_l => wfsub /le_sort_wf_l => wfs.
    eapply wf_sort_subst.

    
(*
Lemma rule_in_wf l : wf_lang l ->
                     forall r m n, shifted_rule_in n r%%!(m+n) l -> wf_rule l r%%!m%%!1.
Proof.
  elim: l => //=.
  intro_to is_true.
  case /orP.
  - rewrite -!rule_constr_shift_shift.
    move /surjective_rule_shift /eqP <-.
    by apply: first_rule_wf.
  - Search _ shifted_rule_in.
    case: a H0; eauto.
    (*eapply mono_rule.*)

Lemma rule_in_wf n r l : wf_lang l -> rule_in r%%!n l -> wf_rule l r%%!n.
Proof.
  elim: l n => //.
  move => a l IH n wfl.
  unfold rule_in.
  simpl; case /orP.
  1:{
    case: n.
    - rewrite rule_constr_shift_0_id.
      move /eqP <-.
      by apply: first_rule_wf.
    - move => n.
      change (n.+1) with (1+n).
      rewrite addnC.
      rewrite -rule_constr_shift_shift.
      move /surjective_rule_shift => /eqP <-.
      by apply: first_rule_wf.
  }
  
  Search _ shifted_rule_in. TODO: lemma to cancel n? (should it already be cancelled?)
  compute.
  move
  Search _ (_%%! _).
  2: {
  inversion wfl.
  move: H0.
  move /wf_rule_lang => /IH => IH'.
  move /IH'.
  apply wf_rule_lang in H0.
  move: 
  eapply IH in H0; eauto
  eauto.
  simpl. TODO: needs to be more general, encorporate shift
Admitted.
*)
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



Lemma wf_to_ctx
  : (forall l c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> le_ctx l c1 c2)
    /\ (forall l c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> le_ctx l c1 c2)
    /\ (forall l c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> le_ctx l c1 c2)
    /\ (forall l c1 c2,  le_ctx l c1 c2 -> wf_ctx l c1 /\ wf)
    /\ (forall l c t, wf_sort l c t -> wf_ctx l c)
    /\ (forall l c s c', wf_subst l c s c' -> wf_ctx l c)
    /\ (forall l c e t,  wf_term l c e t -> wf_ctx l c).
Proof.
  apply: mono_ind; eauto.
  by wf_to_ctx_from_rule.
Admitted.

Lemma wf_term_sort l c t s : wf_term l c t s -> wf_sort l c s.
Proof.
Admitted.
    

(*
Lemma rule_in_wf r l : wf_lang l -> forall n, is_nth r l n -> wf_rule l r.
Proof.
  case: r => [c e | c e t | c1 c2 t1 t2 | c1 c2 e1 e2 t1 t2] n.
  - constructor.
    move: H => /is_nth_list_split.
    change (0+n) with n.
    case => l1 [r'[l2 []]] leq [req neq].
    subst.
    case: r' e req; intro_to (@eq rule); simpl; try by top_inversion.
    case => ->.
    elim: l1 e; simpl.
    + rewrite map_constr_shift0.
      give_up.
    +intros.
  
  
  Lemma is_nth_list_split : is_nth r l n -> exists l1 r' l2, l = l1 ++ [:: r'] ++ l2 /\ r'%%!n = r.
  eapply mono_n.
  elim: l lin wfl => //= => r l IH.
  (case => [->| linl]; top_inversion;
       do [ apply: wf_ctx_mono => //=
           | apply: wf_sort_mono => //=
           | apply: wf_term_mono => //=
           | apply: le_ctx_mono => //=
           | apply: le_sort_mono => //=
           | apply: le_term_mono => //=];
       [ by inversion H1
       | apply: IH => //=;
         apply: wf_rule_lang; eauto]).
Qed.


Scheme le_wf_ctx_ind := Minimality for le_ctx Sort Prop
  with le_wf_sort_ind := Minimality for le_sort Sort Prop
  with le_wf_subst_ind := Minimality for le_subst Sort Prop
  with le_wf_term_ind := Minimality for le_term Sort Prop.
Combined Scheme le_wf_ind from
         le_wf_sort_ind,
         le_wf_subst_ind,
         le_wf_term_ind,
         le_wf_ctx_ind.


Lemma le_wf_l {p}
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_sort l c1 t1)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c1 s1 c1')
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c1 e1 t1)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> wf_ctx l c1).
Proof.
  apply: le_wf_ind; eauto; repeat intro_term;
    move => wfl /rule_in_wf rin;
     apply rin in wfl;
     by inversion wfl.
Qed.

Lemma le_wf_r {p}
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_sort l c2 t2)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c2 s2 c2')
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c2 e2 t2)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> wf_ctx l c2).
Proof.
  apply: le_wf_ind; eauto; repeat intro_term;
    move => wfl /rule_in_wf rin;
     apply rin in wfl;
       by inversion wfl.
Qed.
 
Lemma le_ctx_wf_l  {p} (l : lang p) c1 c2 : le_ctx l c1 c2 -> wf_ctx l c1.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_ctx_wf_l. 
Lemma le_ctx_wf_r  {p} (l : lang p) c1 c2 : le_ctx l c1 c2 -> wf_ctx l c2.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_ctx_wf_r.
Lemma le_sort_wf_l  {p} (l : lang p) c1 c2 t1 t2 : le_sort l c1 c2 t1 t2 -> wf_sort l c1 t1.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_sort_wf_l.
Lemma le_sort_wf_r  {p} (l : lang p) c1 c2 t1 t2 : le_sort l c1 c2 t1 t2 -> wf_sort l c2 t2.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_sort_wf_r.
Lemma le_term_wf_l  {p} (l : lang p) c1 c2 e1 e2 t1 t2
  : le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c1 e1 t1.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_term_wf_l.
Lemma le_term_wf_r  {p} (l : lang p) c1 c2 e1 e2 t1 t2
  : le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c2 e2 t2.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_term_wf_r.
Lemma le_subst_wf_l  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
  : le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c1 s1 c1'.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_subst_wf_l.
Lemma le_subst_wf_r  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
  : le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c2 s2 c2'.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_subst_wf_r.

(* TODO: finish the proof
Lemma wf_to_ctx {p}
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2 v1 v2,
           le_ctx_var l c1 c2 v1 v2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c t, wf_sort l c t -> wf_ctx l c)
    /\ (forall (l : lang p) c s c', wf_subst l c s c' -> wf_ctx l c)
    /\ (forall (l : lang p) c e t,  wf_term l c e t -> wf_ctx l c)
    /\ (forall (l : lang p) c,  wf_ctx l c -> wf_ctx l c)
    /\ (forall (l : lang p) c v,  wf_ctx_var l c v -> wf_ctx l c).
Proof.
  apply: mono_ind;
    eauto;
    repeat intro_term;
    move => wfl /rule_in_wf => riwf;
    apply riwf in wfl;
    try by inversion wfl.
  - inversion wfl.
    give_up. (*TODO: need IH for sort here *)
  - apply: le_ctx_refl.
      by inversion wfl.
Fail Qed.
*)

(* constructor conversion lemmas *)

Ltac rewrite_constr_eqs :=
  repeat match goal with
  | [ |- _ = _ -> _] => move => ->
  | _ => intro
  end.

(* TODO: useful or no?
Lemma wf_ctx_iff_variant {p} (l : lang p) c : wf_ctx l c <-> wf_ctx_ l c.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_ctx_from_variant p (l : lang p) c := iffRL (wf_ctx_iff_variant l c).

Lemma wf_ctx_var_iff_variant {p} (l : lang p) c v : wf_ctx_var l c v <-> wf_ctx_var_ l c v.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_ctx_var_from_variant p (l : lang p) c v := iffRL (wf_ctx_var_iff_variant l c v).

Lemma wf_sort_iff_variant {p} (l : lang p) c t : wf_sort l c t <-> wf_sort_ l c t.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_sort_from_variant p (l : lang p) c t := iffRL (wf_sort_iff_variant l c t).

Lemma wf_subst_iff_variant {p} (l : lang p) c s c' : wf_subst l c s c' <-> wf_subst_ l c s c'.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_subst_from_variant p (l : lang p) c s c' := iffRL (wf_subst_iff_variant l c s c').

(* TODO: why does this one fail?
Lemma wf_term_iff_variant {p} (l : lang p) c e t : wf_term l c e t <-> wf_term_ l c e t.
Proof.
  split;case; rewrite_constr_eqs; eauto.
Fail Qed.
Coercion wf_term_from_variant p (l : lang p) c e t := iffRL (wf_term_iff_variant l c e t).
*)

Lemma le_ctx_iff_variant {p} (l : lang p) c1 c2 : le_ctx l c1 c2 <-> le_ctx_ l c1 c2.
Proof.
  split;case; rewrite_constr_eqs; eauto;
    (* TODO: why doesn't eauto handle this?*)
    by constructor.    
Qed.
Coercion le_ctx_from_variant p (l : lang p) c1 c2 := iffRL (le_ctx_iff_variant l c1 c2).

Lemma le_ctx_var_iff_variant {p} (l : lang p) c1 c2 v1 v2
  : le_ctx_var l c1 c2 v1 v2 <-> le_ctx_var_ l c1 c2 v1 v2.
Proof.
  split;case; rewrite_constr_eqs;  eauto.
Qed.
Coercion e_ctx_var_from_variant p (l : lang p) c1 c2 v1 v2 :=
  iffRL (le_ctx_var_iff_variant l c1 c2 v1 v2).

Lemma le_sort_iff_variant {p} (l : lang p) c1 c2 t1 t2
  : le_sort l c1 c2 t1 t2 <-> le_sort_ l c1 c2 t1 t2.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion le_sort_from_variant p (l : lang p) c1 c2 t1 t2 :=
  iffRL (le_sort_iff_variant l c1 c2 t1 t2).

Lemma le_subst_iff_variant {p} (l : lang p) c1 c2 s1 s2 c1' c2'
  : le_subst l c1 c2 s1 s2 c1' c2' <-> le_subst_ l c1 c2 s1 s2 c1' c2'.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion le_subst_from_variant p (l : lang p) c1 c2 s1 s2 c1' c2' :=
  iffRL (le_subst_iff_variant l c1 c2 s1 s2 c1' c2').

Lemma le_term_iff_variant {p} (l : lang p) c1 c2 e1 e2 t1 t2
  : le_subst l c1 c2 e1 e2 t1 t2 <-> le_subst_ l c1 c2 e1 e2 t1 t2.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion le_term_from_variant p (l : lang p) c1 c2 e1 e2 t1 t2 :=
  iffRL (le_term_iff_variant l c1 c2 e1 e2 t1 t2).
*)

Lemma wf_shift_subst {p} (l : lang p) c c'
  : wf_ctx l (c' ++ c) -> wf_subst l (c' ++ c) (shift_subst (size c) (size c')) c.
Proof.
  elim: c c'.
  - move => c';
    rewrite cats0;
      simpl;
      auto.
  - intros.
    simpl.
    constructor;
    move: H0;
      change (a :: l0) with ([::a]++ l0);
      suff: size (c'++[::a]) = (size c').+1;
      try (by elim: c'; simpl; auto);
      move <-.
    + rewrite catA;
        by apply H.
    + move=> wfc.
      rewrite extract_var_shift.
      erewrite <-shift_subst_shift.
      instantiate(1:=1).
      (*TODO: is there a place I'm missing shifts in the defs?*)
      (* posible since Jon Sterling doesn't use debruijn *)
      (*TODO: strengthen? e.g. n <= size c'?*)
      eapply wf_term_subst.
      change (size c') with (0+(size c')).
      erewrite <-lookup_in_shift_subst; eauto.
      eapply wf_term_subst.
 
    
    
Lemma wf_sort_weaken {p} (l : lang p) c s
  : wf_sort l c s -> forall v, wf_ctx_var l c v -> wf_sort l (v::c) s^!1.
Proof.
  intros.
  suff: ws_exp (size c) s => [wse|].
  erewrite <-shift_subst_shift; eauto.
  apply: wf_sort_subst; eauto.
  give_up. (* need to prove that shift_substs are well-typed *)
  give_up. (* need to prove that well-typed terms are well-scoped*)
*)
    
