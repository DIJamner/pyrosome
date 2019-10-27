
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* TODO: change from loads to imports*)
From excomp Require Import Exp.

(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   Some constructors take in more presuppositions than strictly necessary
   (i.e. they can be derived from other arguments). This is a conscious design choice.
   It is easier to devise secondary "constructor" functions that perform these
   derivations than to do the mutually inductive proof that such derivations exist.
 *)
Inductive wf_sort {p} : lang p -> ctx p -> exp p -> Prop :=
| wf_sort_by : forall l c t,
    wf_lang l ->
    List.In ({| c|- t}) l ->
    wf_sort l c t
| wf_sort_subst : forall l c s c' t',
    wf_subst l c s c' ->
    wf_sort l c' t' ->
    wf_sort l c t'[/s/]
with le_sort {p} : lang p -> ctx p -> ctx p -> exp p -> exp p -> Prop :=
| le_sort_by : forall l c1 c2 t1 t2,
    wf_lang l ->
    List.In ({< c1 <# c2 |- t1 <# t2}) l ->
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
with wf_term {p} : lang p -> ctx p -> exp p -> exp p -> Prop :=
| wf_term_by : forall l c e t,
    wf_lang l ->
    List.In ({| c |- e .: t}) l ->
    wf_term l c e t
| wf_term_subst : forall l c s c' e' t',
    wf_subst l c s c' ->
    wf_term l c' e' t' ->
    wf_term l c e'[/s/] t'[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around
 *)
| wf_term_conv : forall l c e t c' t',
    wf_term l c e t ->
    le_sort l c c' t t' ->
    wf_term l c' e t'
with le_term {p} : lang p ->
                   ctx p -> ctx p ->
                   exp p -> exp p ->
                   exp p -> exp p -> Prop :=
| le_term_by : forall l c1 c2 e1 e2 t1 t2,
    wf_lang l ->
    List.In ({< c1 <# c2|- e1 <# e2 .: t1 <# t2})%rule l ->
    le_term l c1 c2 e1 e2 t1 t2
| le_term_subst : forall l c1 c2 s1 s2 c1' c2' e1' e2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1' c2' e1' e2' t1' t2' ->
    le_term l c1 c2 e1'[/s1/] e2'[/s2/] t1'[/s1/] t2'[/s2/]
| le_term_refl : forall l c e t,
    wf_lang l ->
    List.In ({| c |- e .: t })%rule l ->
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
with wf_subst {p} : lang p -> ctx p -> subst p ->  ctx p -> Prop :=
| wf_subst_nil : forall l c,
    wf_ctx l c ->
    wf_subst l c [::] [::]
| wf_subst_sort : forall l c s c' t,
    wf_subst l c s c' ->
    wf_sort l c t ->
    wf_subst l c (t::s) (sort_var :: c')
| wf_subst_term : forall l c s c' e t,
    wf_subst l c s c' ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (term_var t::c')
with le_subst {p} : lang p ->
                    ctx p -> ctx p ->
                    subst p -> subst p ->
                    ctx p -> ctx p -> Prop :=
| le_subst_nil : forall l c1 c2,
    le_ctx l c1 c2 ->
    le_subst l c1 c2 [::] [::] [::] [::]
| le_subst_sort : forall l c1 c2 s1 s2 c1' c2' t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1 c2 t1 t2 ->
    le_subst l c1 c2 (t1::s1) (t2::s2) (sort_var::c1') (sort_var::c2')
| le_subst_term : forall l c1 c2 s1 s2 c1' c2' e1 e2 t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1 c2 e1 e2 t1[/s1/] t2[/s2/] ->
    le_subst l c1 c2 (e1::s1) (e2::s2) (term_var t1::c1') (term_var t2 :: c2')
with wf_ctx_var {p} : lang p -> ctx p -> ctx_var p -> Prop :=
| wf_sort_var : forall l c,
    wf_ctx l c ->
    wf_ctx_var l c sort_var
| wf_term_var : forall l c t,
    wf_sort l c t ->
    wf_ctx_var l c (term_var t)
with le_ctx_var {p} : lang p -> ctx p -> ctx p -> ctx_var p -> ctx_var p -> Prop :=
| le_sort_var : forall l c1 c2,
    le_ctx l c1 c2 ->
    le_ctx_var l c1 c2 sort_var sort_var
| le_term_var : forall l c1 c2 t1 t2,
    le_sort l c1 c2 t1 t2 ->
    le_ctx_var l c1 c2 (term_var t1) (term_var t2)
with wf_ctx {p} : lang p -> ctx p -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_ctx_var l c v ->
    wf_ctx l (v::c)
with le_ctx {p} : lang p -> ctx p -> ctx p -> Prop :=
| le_ctx_nil : forall l, wf_lang l -> le_ctx l [::] [::]
| le_ctx_cons : forall l c1 c2 v1 v2,
    le_ctx_var l c1 c2 v1 v2 ->
    le_ctx l (v1::c1) (v2::c2)
with wf_rule {p} : lang p -> rule p -> Prop :=
| wf_sort_rule : forall l c t,
    wf_ctx l c ->
    (* TODO: require t (prefix) not in thy? interferes with monotonicity *)
    wf_rule l ({| c |- t})
| wf_term_rule : forall l c e t,
    wf_ctx l c ->
    wf_sort l c t ->
    (* TODO: require e (prefix) not in thy? interferes with monotonicity *)
    wf_rule l ({| c |- e .: t})
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
with wf_lang {p} : lang p -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_rule l r -> wf_lang (r::l).
Hint Constructors wf_sort.
Hint Constructors le_sort.
Hint Constructors wf_term.
Hint Constructors le_term.
Hint Constructors wf_subst.
Hint Constructors le_subst.
Hint Constructors wf_ctx_var.
Hint Constructors le_ctx_var.
Hint Constructors wf_ctx.
Hint Constructors le_ctx.
Hint Constructors wf_rule.
Hint Constructors wf_lang.

(* Judgment manipulation tactics
   These tactics are designed to generate reasdable subterms,
   particularly for use when the proof must be inspected for well-foundedness
 *)

Ltac get_polynomial :=
  match goal with
    p : polynomial |- _ => p
  end.

(* tac_map tactics push under "wf : (wf_X ...) |- ... -> (wf_X ...)" goals to the subterms 
   These tactics are meant to generate readable proof terms
*)
Ltac tac_map_wf_sort wf :=
  refine (match wf with
           | wf_sort_by _ _ _ _ _ => _ (*TODO*)
           | wf_sort_subst _ _ _ _ _ _ _ => _
            end);
  [ intros; eapply wf_sort_by
  | intros; eapply wf_sort_subst].


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
| wf_sort_var_ :  wf_ctx l c ->  wf_ctx_var_ l c sort_var
| wf_term_var_ : forall t, wf_sort l c t -> wf_ctx_var_ l c (term_var t).
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


