
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule.


(* grouped right with the fixpoint so that eq_exp goes through*)
Definition all2 := 
fun (S T : Type) (r : S -> T -> bool) =>
fix all2 (s : seq S) (t : seq T) {struct s} : bool :=
  match s, t with
  | [::], [::] => true
  | x :: s0, y::t0 => r x y && all2 s0 t0
  | _,_ => false
  end.

(* TODO: I have to inline all2 to get this accepted *)
Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => x == y
  | con n1 l1, con n2 l2 =>
    (n1 == n2) && (all2 eq_exp l1 l2)
  | _,_ => false
  end.

Lemma all2P {T} eqb (l1 l2 : seq T)
  : (forall e1 e2, reflect (e1 = e2) (eqb e1 e2)) ->
    reflect (l1 = l2) (all2 eqb l1 l2).
Proof.
  move => eqbP.
  elim: l1 l2.
  - case; simpl; [by constructor|].
    intros.
    constructor; eauto.
    move => H; inversion H.
  - move => a l IH.
    case; simpl.
    constructor; move => H; inversion H.
    intros.
    move: (eqbP a a0).
    case (eqb a a0); simpl.
    move: (IH l0); case:(all2 eqb l l0); simpl.
    + constructor.
      inversion IH0; inversion eqbP0; by subst.
    + constructor.
      move => lfl.
      inversion lfl.
      inversion IH0; eauto.
    + constructor; move => lfl.
      inversion lfl; inversion eqbP0; auto.
Qed.

Lemma exp2_ind (P : exp -> exp -> Set)
  : (forall n m, P (var n) (var m)) ->
    (forall n c l, P (var n) (con c l)) ->
    (forall n c l, P (con c l) (var n)) ->
    (forall c1 c2, P (con c1 [::]) (con c2 [::])) ->
    (forall c1 c2 a l, P (con c1 [::]) (con c2 (a::l))) ->
    (forall c1 c2 a l, P (con c1 (a::l)) (con c2 [::])) ->
    (forall c1 c2 a1 a2 l1 l2,
        P a1 a2 ->
        P (con c1 l1) (con c2 l2) ->
        P (con c1 (a1::l1)) (con c2 (a2::l2))) ->
    forall e1 e2, P e1 e2.
Proof.
  intro_to exp.
  elim.
  - intro_to exp; case; auto.
  - intro_to exp.
    case; auto.
    move => n0.
    elim: l X.
    + move => _; case; auto.
    + move => a l IH.
      simpl; case => pa fld.
      case; auto.
Qed.      

(*TODO: case neq does not use the right name*)
Tactic Notation "case_on_eqb" ident(a) ident(b) :=
  let neq := fresh "neq" in
  case neq: (a == b); constructor;
  [f_equal; apply /eqP
  | case => /eqP; rewrite neq].
  

Lemma eq_exp_refl : forall e, eq_exp e e.
Proof.
  elim; simpl; auto.
  move => n.
  suff: n == n.
  move ->; simpl.
  elim; simpl; auto.
  intro_to and.
  case => eqaa fld.
  apply /andP.
  split; auto.
  elim: n; simpl; auto.
Qed.

Lemma all2_eq_exp_refl : forall l, all2 eq_exp l l.
  pose eqer := eq_exp_refl.
  elim; simpl; auto.
  intros; apply /andP; split; auto.
Qed.

Lemma eq_expP : forall e1 e2, reflect (e1 = e2) (eq_exp e1 e2).
Proof.
  elim.
  - intro_to exp; case; simpl.
    + move => n0.
        by case_on_eqb n n0.
    + constructor; by case.
  - intro_to exp; case; simpl.
    + constructor; by case.
    + intros.
      case neq: (n == n0); simpl.
      * case alleq: (all2 eq_exp l l0).
        --constructor.
          f_equal.
            by apply /eqP; rewrite neq.
            elim: l X l0 alleq.
          ++ simpl; move => _; case; by auto.
          ++ simpl; move => a l IH.
             case => refla fld.
             case; try by auto.
             move => a0 l0.
             case /andP.
             move /refla => -> all2l.
             f_equal.
             eauto.
        -- constructor.
           case => _.
           elim: l X l0 alleq.
           ++ simpl; move => _; case; by auto.
          ++ simpl; move => a l IH.
             case => refla fld.
             case; try by auto.
             move => a0 l0.
             move /andP => oneof.
             case => aeq leq.
             apply oneof.
             split.
             rewrite aeq.
             apply: eq_exp_refl.
             rewrite leq.
             apply: all2_eq_exp_refl.
      * constructor.
        case; move /eqP; by rewrite neq.
Qed.

Definition exp_eqMixin := Equality.Mixin eq_expP.

Canonical exp_eqType := @Equality.Pack exp exp_eqMixin.

Definition eq_rule r1 r2 : bool :=
  match r1, r2 with
  | {| c1 |- sort }, {| c2 |- sort } => c1 == c2
  | {| c1 |- t1 }, {| c2 |- t2 } => (c1 == c2) && (t1 == t2)
  | {< c1 <# c2 |- t1 <# t2 },{< c1' <# c2' |- t1' <# t2' } =>
    (c1 == c1') && (t1 == t1') && (c2 == c2') && (t2 == t2')
  | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 },{< c1' <# c2' |- e1' <# e2' .: t1' <# t2' } =>
    (c1 == c1') && (e1 == e1') && (t1 == t1') && (c2 == c2')  && (e2 == e2') && (t2 == t2')
  | _,_ => false
  end.

Tactic Notation "inversion" :=
  let H := fresh in
  move => H; inversion H.

Lemma eq_ruleP r1 r2 : reflect (r1 = r2) (eq_rule r1 r2).
Proof.
  case: r1 r2; intro_to rule; case; intros; simpl; eauto;
  try match goal with
  | |- reflect _ false => constructor; by inversion
  | |- reflect _ (?A == ?B) =>
    case eqcase: (A == B); constructor;
      solve [ by f_equal; apply /eqP
            | by case; move /eqP; rewrite eqcase]
      end.
  - match goal with
    | |- reflect _ (?E && _) => case and1: E; simpl
    end.
    match goal with
    | |- reflect _ false => constructor; by inversion
    | |- reflect _ (?A == ?B) =>
      case eqcase: (A == B); constructor;
        try solve [ by f_equal; apply /eqP
                  | by case; move /eqP; rewrite eqcase]
    end.
    case => _ => /eqP.
    by rewrite eqcase.
    constructor.
    case  => /eqP.
      by rewrite and1.
  - case ccs: (c == c1); simpl.
    case ecs: (e == e1); simpl.
    case c0cs: (c0 == c2); simpl.
    case e0cs: (e0 == e2); simpl.
    constructor; f_equal; by apply /eqP.
    constructor; case => _ _ _ /eqP; by rewrite e0cs.
    constructor; case => _ /eqP; by rewrite c0cs.
    constructor; case => _ _ /eqP; by rewrite ecs.
    constructor; case => /eqP; by rewrite ccs.
  - case ccs: (c == c1); simpl.
    case ecs: (e == e3); simpl.
    case e1cs: (e1 == e5); simpl.
    case c0cs: (c0 == c2); simpl.
    case e0cs: (e0 == e4); simpl.
    case e2cs: (e2 == e6); simpl.
    constructor; f_equal; by apply /eqP.
    constructor; case => _ _ _ _ _ /eqP; by rewrite e2cs.
    constructor; case => _ _ _ /eqP; by rewrite e0cs.
    constructor; case => _ /eqP; by rewrite c0cs.
    constructor; case => _ _ _ _ /eqP; by rewrite e1cs.
    constructor; case => _ _ /eqP; by rewrite ecs.
    constructor; case => /eqP; by rewrite ccs.
Qed.

Definition rule_eqMixin := Equality.Mixin eq_ruleP.

Canonical rule_eqType := @Equality.Pack rule rule_eqMixin.


(*TODO: move these to Exp*)
Fixpoint constr_shift n e :=
  match e with
  | var x => var x
  | con m l => con (n + m) (map (constr_shift n) l)
  end.


Notation "e %! n" := (constr_shift n e) (at level 7).

Notation "e ::%! n" := (map (constr_shift n) e) (at level 7).

Lemma constr_shift0 e : e%!0 = e.
Proof.
  elim: e => //.
  intros; simpl.
  f_equal.
  elim: l H => //.
  simpl; intros.
  case: H0 => H01 H02; f_equal; auto.
Qed.

Lemma map_constr_shift0 s : s::%!0 = s.
  elim: s => //.
  intros; simpl; f_equal; move: constr_shift0; auto.
Qed.
  
Lemma constr_shift_shift e n m : e%!n %!m = e%!(n + m).
Proof.
  elim: e => //.
  intros;
    simpl;
    f_equal.
  - ring.
  - elim: l H => //; simpl; intros.
    rewrite -> H;
      case: H0; intros.
    f_equal; auto.
    auto.
Qed.

Definition rule_constr_shift n r :=
  match r with
  | {| c |- sort } => {| map (constr_shift n) c |- sort}
  | {| c |- t } => {| map (constr_shift n) c |- constr_shift n t}
  | {< c1 <# c2 |- t1 <# t2 } =>
    {< map (constr_shift n) c1 <# map (constr_shift n) c2
     |- constr_shift n t1 <# constr_shift n t2 }
  | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 } =>
    {< map (constr_shift n) c1 <# map (constr_shift n) c2
     |- constr_shift n e1 <# constr_shift n e2
                     .: constr_shift n t1 <# constr_shift n t2}
  end.

Notation "r %%! n" := (rule_constr_shift n r) (at level 7).

(*TODO: should be mutually recursive w/ last lemma *)
Lemma map_constr_shift_shift l n m
  : l ::%! n ::%! m = l::%!(n+m).
Proof.
  elim: l => //.
  simpl.
  move => a l ->.
  f_equal; move: constr_shift_shift; auto.
Qed.

Lemma rule_constr_shift_shift r n m : r%%!n %%!m = r%%!(n+m).
Proof.
  case: r; simpl; intros; f_equal;
    move: constr_shift_shift map_constr_shift_shift;
  auto.
Qed.

Lemma constr_shift_subst_comm e s n : e[/s/]%!n = e%!n[/s::%!n/].
Proof.
  elim: e s n.
  - elim ;intro_to subst; case => //.
  - intros; simpl;
      unfold exp_subst;
      unfold exp_var_map;
      fold exp_var_map;
      fold exp_subst.
    f_equal.
    fold exp_subst.
    elim: l H => //.
    simpl; intro_to and.
    case; intros.
    f_equal; eauto.
Qed.

(* determines whether a given language contains the appropriate axiom.
   Uses constructor shifts to get the right debruijn indices
 *)
Fixpoint shifted_rule_in n (r : rule) (l : lang) : bool :=
  match l with
  | [::] => false
  | r' :: l' => ( r' %%! n == r) || (shifted_rule_in (n.+1) r l')
  end.

Lemma shifted_rule_in_cons n r l
  : shifted_rule_in n.+1 r l -> forall r', shifted_rule_in n r (r'::l).
Proof.
  intros; by apply /orP; auto.
Qed.

Lemma unshift_rule_in_cons n r l
  : shifted_rule_in n r l -> forall m, shifted_rule_in (n + m) r%%!m l.
Proof.
  elim: l n => //.
  intro_to is_true.
  case /orP => [ /eqP <- |].
  - move => m; rewrite rule_constr_shift_shift.
    simpl.
    apply /orP; left; by apply /eqP.
  - fold shifted_rule_in.
    intros; simpl.
    apply /orP; right.
    change (n+m).+1 with (n.+1 + m).
    auto.
Qed.

Lemma rule_in_mono n r l
  : shifted_rule_in n r l -> forall r', shifted_rule_in n r%%!1 (r'::l).
Proof.
  intros.
  apply: shifted_rule_in_cons.
  change n.+1 with (1+n).
  rewrite addnC.
  by apply: unshift_rule_in_cons.
Qed.

Definition rule_in r (l : lang) : bool := shifted_rule_in 1 r l.
Hint Unfold rule_in.

Fixpoint shifted_is_nth n (r : rule) l m : bool :=
  match m, l with
  | _, [::] => false
  | 0, r'::l' => (rule_constr_shift n r' == r)
  | m'.+1, _::l' => shifted_is_nth n.+1 r l' m'
  end.

Lemma unshift_is_nth_cons n r l m
  : shifted_is_nth n r l m -> forall n', shifted_is_nth (n + n') r%%!n' l m.
Proof.
  elim: m l n => //.
  - case; simpl; auto.
    intro_to is_true.
    move /eqP <- => n'.
    by rewrite rule_constr_shift_shift.
  - intro_to seq.
    case; simpl; auto.
    intros.
    change (n0 + n').+1 with (n0.+1 + n').
    auto.
Qed.

Definition is_nth r l m := shifted_is_nth 1 r l m.
Hint Unfold is_nth.
  

(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   Expression constructors contain the index of the sort/term rule that proves them wf.
   This is a deruijn version of how Jon Sterling does it
 *)
Print List.
Inductive wf_sort : lang -> ctx -> exp -> Prop :=
| wf_sort_by : forall l c n s c',
    is_nth ({| c' |- sort}) l n ->
    wf_subst l c s c' ->
    wf_sort l c (con n s)
with le_sort : lang -> ctx -> ctx -> exp -> exp -> Prop :=
(*TODO: constructor indices!!!
 get right! should these get shifted?
 answer: I think so, in every case where
*)
| le_sort_by : forall l c1 c2 t1 t2,
    wf_lang l ->
    rule_in ({< c1 <# c2 |- t1 <# t2}) l ->
    le_sort l c1 c2 t1 t2
| le_sort_subst : forall l c1 c2 s1 s2 c1' c2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1' t2' ->
    le_sort l c1 c2 t1'[/s1/] t2'[/s2/]
| le_sort_refl : forall l c t,
    wf_lang l ->
    wf_sort l c t ->
    le_sort l c c t t
| le_sort_trans : forall l c1 c12 c2 t1 t12 t2,
    le_sort l c1 c12 t1 t12 ->
    le_sort l c12 c2 t12 t2 ->
    le_sort l c1 c2 t1 t2
with wf_term : lang -> ctx -> exp -> exp -> Prop :=
| wf_term_by : forall l c n s c' t,
    is_nth ({| c' |- t}) l n ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around
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
    rule_in ({< c1 <# c2|- e1 <# e2 .: t1 <# t2}) l ->
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
           | le_sort_refl _ _ _ _ _ => _
           | le_sort_trans _ _ _ _ _ _ _ _ _ => _
            end).



(* =================================
   Inductives with better parameters
   =================================
These can't all be mutually inductive since they have different parameters,
so they are just defined by reference to the core datatypes
 *)

(*
(*TODO: out of date wrt vars. Are these really worth it? *)
Variant wf_sort_ {p} (l : lang p) c t : Prop :=
| wf_sort_by_ :  wf_lang l ->  List.In ({| c|- t})%rule l -> wf_sort_ l c t
| wf_sort_subst_ : forall s c' t',
    t = t'[/s/] ->
    wf_subst l c s c' ->
    wf_sort l c' t' ->
    wf_sort_ l c t.
Hint Constructors wf_sort_.

Variant le_sort_ {p} (l : lang p) c1 c2 t1 t2 : Prop :=
| le_sort_by_ :
    wf_lang l ->
    List.In ({< c1 <# c2 |- t1 <# t2})%rule l ->
    le_sort_ l c1 c2 t1 t2
| le_sort_subst_ : forall s1 s2 c1' c2' t1' t2',
    t1 = t1'[/s1/] ->
    t2 = t2'[/s2/] ->
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1' t2' ->
    le_sort_ l c1 c2 t1 t2
| le_sort_refl_ :
    c1 = c2 ->
    t1 = t2 ->
    wf_lang l ->
    wf_sort l c1 t1 ->
    le_sort_ l c1 c2 t1 t2
| le_sort_trans_ : forall c12 t12,
    le_sort l c1 c12 t1 t12 ->
    le_sort l c12 c2 t12 t2 ->
    le_sort_ l c1 c2 t1 t2.
Hint Constructors le_sort_.

Variant wf_term_ {p} (l : lang p) c e t : Prop :=
| wf_term_by_ :
    wf_lang l ->
    List.In ({| c |- e .: t})%rule l ->
    wf_term_ l c e t
| wf_term_subst_ : forall s c' e' t',
    e = e'[/s/] ->
    t = t'[/s/] ->
    wf_subst l c s c' ->
    wf_term l c' e' t' ->
    wf_term_ l c e t
| wf_term_conv_ : forall c' t',
    wf_term l c' e t' ->
    le_sort l c' c t' t ->
    wf_term_ l c e t.
Hint Constructors wf_term_.

Variant le_term_ {p} (l : lang p) c1 c2 e1 e2 t1 t2 : Prop :=
| le_term_by_ :
    wf_lang l ->
    List.In ({< c1 <# c2|- e1 <# e2 .: t1 <# t2}) l ->
    le_term_ l c1 c2 e1 e2 t1 t2
| le_term_subst_ : forall s1 s2 c1' c2' e1' e2' t1' t2',
    e1 = e1'[/s1/] ->
    e2 = e2'[/s2/] ->
    t1 = t1'[/s1/] ->
    t2 = t2'[/s2/] ->
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1' c2' e1' e2' t1' t2' ->
    le_term_ l c1 c2 e1 e2 t1 t2
| le_term_refl_ :
    c1 = c2 ->
    e1 = e2 ->
    t1 = t2 ->
    wf_lang l ->
    wf_term l c1 e1 t1 ->
    le_term_ l c1 c2 e1 e2 t1 t2
| le_term_trans_ : forall c12 e12 t12,
    le_term l c1 c12 e1 e12 t1 t12 ->
    le_term l c12 c2 e12 e2 t12 t2 ->
    le_term_ l c1 c2 e1 e2 t1 t2
| le_term_conv_ : forall c1' c2' t1' t2',
    le_sort l c1 c2 t1 t2 ->
    le_term l c1' c2' e1 e2 t1' t2' ->
    le_sort l c1' c1 t1' t1 ->
    le_sort l c2' c2 t2' t2 ->
    le_term_ l c1 c2 e1 e2 t1 t2.
Hint Constructors le_term_.
            
Variant wf_subst_ {p} (l : lang p) c : subst p -> ctx p -> Prop :=
| wf_subst_nil_ : wf_ctx l c -> wf_subst_ l c [::] [::]
| wf_subst_sort_ : forall s c' t,
    wf_subst l c s c' ->
    wf_sort l c t ->
    wf_subst_ l c (t::s) (sort_var::c')
| wf_subst_term_ : forall s c' e t,
    wf_subst l c s c' ->
    wf_term l c e t[/s/] ->
    wf_subst_ l c (e::s) (term_var t::c').
Hint Constructors wf_subst_.

Variant le_subst_ {p} (l : lang p) c1 c2
  : subst p -> subst p ->
    ctx p -> ctx p -> Prop :=
| le_subst_nil_ : le_ctx l c1 c2 ->
                  le_subst_ l c1 c2 [::] [::] [::] [::]
| le_subst_sort_ : forall s1 s2 c1' c2' t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1 c2 t1 t2 ->
    le_subst_ l c1 c2 (t1::s1) (t2::s2) (sort_var::c1') (sort_var::c2')
| le_subst_term_ : forall s1 s2 c1' c2' e1 e2 t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1 c2 e1 e2 t1[/s1/] t2[/s2/] ->
    le_subst_ l c1 c2 (e1::s1) (e2::s2) (term_var t1::c1') (term_var t2 :: c2').
Hint Constructors le_subst_.

Variant wf_ctx_var_ {p} (l : lang p) c : ctx_var p -> Prop :=
| wf_ctx_var_sort_ :  wf_ctx l c ->  wf_ctx_var_ l c sort_var
| wf_ctx_var_term_ : forall t, wf_sort l c t -> wf_ctx_var_ l c (term_var t).
Hint Constructors wf_ctx_var_.

Variant le_ctx_var_ {p} (l : lang p) c1 c2 : ctx_var p -> ctx_var p -> Prop :=
| le_sort_var_ : 
    le_ctx l c1 c2 ->
    le_ctx_var_ l c1 c2 sort_var sort_var
| le_term_var_ : forall t1 t2,
    le_sort l c1 c2 t1 t2 ->
    le_ctx_var_ l c1 c2 (term_var t1) (term_var t2).
Hint Constructors le_ctx_var_.

Variant wf_ctx_ {p} (l : lang p) : ctx p -> Prop :=
| wf_ctx_nil_ : wf_lang l -> wf_ctx_ l [::]
| wf_ctx_cons_ : forall c v,
    wf_ctx_var l c v ->
    wf_ctx_ l (v::c).
Hint Constructors wf_ctx_.

Variant le_ctx_ {p} (l : lang p) : ctx p -> ctx p -> Prop :=
| le_ctx_nil_ : wf_lang l -> le_ctx_ l [::] [::]
| le_ctx_cons_ : forall c1 c2 v1 v2,
    le_ctx_var l c1 c2 v1 v2 ->
    le_ctx_ l (v1::c1) (v2::c2).
Hint Constructors wf_ctx_.

Variant wf_rule_ {p} (l : lang p) : rule p -> Prop :=
| wf_sort_rule_ : forall c t,
    wf_ctx_ l c ->
    wf_rule_ l ({| c |- t})
| wf_term_rule_ : forall c e t,
    wf_ctx_ l c ->
    wf_sort_ l c t ->
    wf_rule_ l ({| c |- e .: t})
| le_sort_rule_ : forall c1 c2 t1 t2,
    le_ctx l c1 c2 ->
    wf_sort_ l c1 t1 ->
    wf_sort_ l c2 t2 ->
    wf_rule_ l ({< c1 <# c2 |- t1 <# t2})
| le_term_rule_ : forall c1 c2 e1 e2 t1 t2,
    le_sort l c1 c2 t1 t2 ->
    wf_term_ l c1 e1 t1 ->
    wf_term_ l c2 e2 t2 ->
    wf_rule_ l ({< c1 <# c2 |- e1 <# e2 .: t1 <# t2}).
Hint Constructors wf_rule_.
*)

