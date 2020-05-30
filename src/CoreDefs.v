
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

(*Todo: whichs more useful?*)
Definition nth_level {A} l n : option A :=
  if n <= size l then List.nth_error l (size l - n) else None.
Definition is_nth_level {A:eqType} (l : seq A) n x : bool :=
   (n <= size l) && (List.nth_error l (size l - n) == Some x).

Lemma nth_level_confluent {A:eqType} (l : seq A) n x
  : (nth_level l n == Some x) = is_nth_level l n x.
Proof.
  unfold nth_level; unfold is_nth_level.
  case: (n <= size l);
    by simpl.
Qed.    
  
(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   Expression constructors contain the level of the sort/term rule that proves them wf.
   This is a deruijn version of how Jon Sterling does it
   TODO: review presuppositions
 *)
Inductive wf_sort : lang -> ctx -> exp -> Prop :=
| wf_sort_by : forall l c n s c',
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (con n s)
with le_sort : lang -> ctx -> ctx -> exp -> exp -> Prop :=
| le_sort_by : forall l c1 c2 t1 t2,
    wf_lang l ->
    ({< c1 <# c2 |- t1 <# t2}) \in l ->
    le_sort l c1 c2 t1 t2
| le_sort_subst : forall l c1 c2 s1 s2 c1' c2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1' t2' ->
    le_sort l c1 c2 t1'[/s1/] t2'[/s2/]
| le_sort_refl : forall l c t,
    wf_sort l c t ->
    le_sort l c c t t
| le_sort_trans : forall l c1 c12 c2 t1 t12 t2,
    le_sort l c1 c12 t1 t12 ->
    le_sort l c12 c2 t12 t2 ->
    le_sort l c1 c2 t1 t2
with wf_term : lang -> ctx -> exp -> exp -> Prop :=
| wf_term_by : forall l c n s c' t,
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| wf_term_conv : forall l c e t c' t',
    wf_term l c e t ->
    le_sort l c c' t t' ->
    wf_term l c' e t'
| wf_term_var : forall l c n t,
    wf_ctx l c ->
    List.nth_error c n = Some t ->
    wf_term l c (var n) t
with le_term : lang ->
               ctx -> ctx ->
               exp -> exp ->
               exp -> exp -> Prop :=
| le_term_by : forall l c1 c2 e1 e2 t1 t2,
    wf_lang l ->
    ({< c1 <# c2|- e1 <# e2 .: t1 <# t2}) \in l ->
    le_term l c1 c2 e1 e2 t1 t2
| le_term_subst : forall l c1 c2 s1 s2 c1' c2' e1' e2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1' c2' e1' e2' t1' t2' ->
    le_term l c1 c2 e1'[/s1/] e2'[/s2/] t1'[/s1/] t2'[/s2/]
| le_term_refl : forall l c e t,
    wf_term l c e t ->
    le_term l c c e e t t
| le_term_trans : forall l c1 c12 c2 e1 e12 e2 t1 t12 t2,
    le_term l c1 c12 e1 e12 t1 t12 ->
    le_term l c12 c2 e12 e2 t12 t2 ->
    le_term l c1 c2 e1 e2 t1 t2
(* Conversion:

c1  < c2  |- e1 < e2 : t1  < t2   ||
/\    /\               /\    /\   ||
c1' < c2' |- e1 < e2 : t1' < t2'  \/
*)
| le_term_conv : forall l c1 c2 e1 e2 t1 t2 c1' c2' t1' t2',
    le_sort l c1' c2' t1' t2' ->
    le_term l c1 c2 e1 e2 t1 t2 ->
    le_sort l c1 c1' t1 t1' ->
    le_sort l c2 c2' t2 t2' ->
    le_term l c1' c2' e1 e2 t1' t2'
with wf_subst : lang -> ctx -> subst -> ctx -> Prop :=
| wf_subst_nil : forall l c,
    wf_ctx l c ->
    wf_subst l c [::] [::]
| wf_subst_cons : forall l c s c' e t,
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c')
with le_subst : lang ->
                ctx -> ctx ->
                subst -> subst ->
                ctx -> ctx -> Prop :=
| le_subst_nil : forall l c1 c2,
    le_ctx l c1 c2 ->
    le_subst l c1 c2 [::] [::] [::] [::]
| le_subst_cons : forall l c1 c2 s1 s2 c1' c2' e1 e2 t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1 t2 ->
    le_term l c1 c2 e1 e2 t1[/s1/] t2[/s2/] ->
    le_subst l c1 c2 (e1::s1) (e2::s2) (t1::c1') (t2 :: c2')
with wf_ctx : lang -> ctx -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_sort l c v ->
    wf_ctx l (v::c)
with le_ctx : lang -> ctx -> ctx -> Prop :=
| le_ctx_nil : forall l, wf_lang l -> le_ctx l [::] [::]
| le_ctx_cons : forall l c1 c2 v1 v2,
    le_ctx l c1 c2 ->
    le_sort l c1 c2 v1 v2 ->
    le_ctx l (v1::c1) (v2::c2)
with wf_rule : lang -> rule -> Prop :=
| wf_sort_rule : forall l c,
    wf_ctx l c ->
    wf_rule l ({| c |- sort})
| wf_term_rule : forall l c t,
    wf_sort l c t ->
    wf_rule l ({| c |- t})
| le_sort_rule : forall l c1 c2 t1 t2,
    le_ctx l c1 c2 ->
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    wf_rule l ({< c1 <# c2 |- t1 <# t2})
| le_term_rule : forall l c1 c2 e1 e2 t1 t2,
    le_sort l c1 c2 t1 t2 ->
    wf_term l c1 e1 t1 ->
    wf_term l c2 e2 t2 ->
    wf_rule l ({< c1 <# c2 |- e1 <# e2 .: t1 <# t2})
with wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_rule l r -> wf_lang (r::l).
Hint Constructors wf_sort.
Hint Constructors le_sort.
Hint Constructors wf_term.
Hint Constructors le_term.
Hint Constructors wf_subst.
Hint Constructors le_subst.
Hint Constructors wf_ctx.
Hint Constructors le_ctx.
Hint Constructors wf_rule.
Hint Constructors wf_lang.

(* Judgment manipulation tactics
   These tactics are designed to generate reasdable subterms,
   particularly for use when the proof must be inspected for well-foundedness
 *)

(* tac_map tactics push under "wf : (wf_X ...) |- ... -> (wf_X ...)" goals to the subterms 
   These tactics are meant to generate readable proof terms
*)
Ltac tac_map_wf_sort wf :=
  refine (match wf with
           | wf_sort_by _ _ _ _ _ _ _ => _ (*TODO*)
            end);
  intros; eapply wf_sort_by.


Ltac tac_map_le_sort :=
  refine (fun wfs =>
            match wfs with
           | le_sort_by _ _ _ _ _ _ _ => _
           | le_sort_subst _ _ _ _ _ _ _ _ _ _ _ => _
           | le_sort_refl _ _ _ _ => _
           | le_sort_trans _ _ _ _ _ _ _ _ _ => _
            end).
