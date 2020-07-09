Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Syntax.


Inductive wf_sort : lang -> ctx -> sort -> Prop :=
| wf_sort_by : forall l c n s c',
    wf_lang l ->
    wf_ctx l c ->
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (srt n s)
with le_sort : lang -> ctx -> sort_le -> sort -> sort -> Prop :=
| le_sort_by : forall l c n c' t1 t2 ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1[/s1/] ->
    wf_sort l c t2[/s2/] ->
    is_nth_level l n (sort_le_rule c' t1 t2) ->
    le_subst l c ps s1 s2 c' ->
    le_sort l c (sle_by n ps) t1[/s1/] t2[/s2/]
| le_sort_refl : forall l c n c' ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c (srt n s1) ->
    wf_sort l c (srt n s2) ->    
    is_nth_level l n (sort_rule c') ->
    le_subst l c ps s1 s2 c' ->    
    le_sort l c (sle_refl n ps) (srt n s1) (srt n s2)
| le_sort_trans : forall l sp1 sp2 c t1 t12 t2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    le_sort l c sp1 t1 t12 ->
    le_sort l c sp2 t12 t2 ->
    le_sort l c (sle_trans sp1 sp2) t1 t2
with wf_term : lang -> ctx -> term -> sort -> Prop :=
| wf_term_by : forall l c n s c' t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s/] ->
    is_nth_level l n (term_rule c' t) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction from le to ge? might be more intuitive
 *)
| wf_term_conv : forall l c e t pf t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c e t ->
    le_sort l c pf t t' ->
    wf_term l c (conv pf e) t'
| wf_term_var : forall l c n t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    is_nth_level c n t ->
    wf_term l c (var n) t
with le_term : lang -> ctx -> term_le -> term -> term -> sort -> Prop :=
| le_term_by : forall l c n c' e1 e2 t ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s2/] ->
    wf_term l c e1[/s1/] t[/s1/] ->
    wf_term l c e2[/s2/] t[/s2/] ->
    is_nth_level l n (term_le_rule c' e1 e2 t) ->
    le_subst l c ps s1 s2 c' ->
    le_term l c (tle_by n ps) e1[/s1/] e2[/s2/] t[/s2/]
| le_term_refl_var : forall l c x t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c (var x) t ->
    is_nth_level c x t ->
    le_term l c (tle_refl_var x) (var x) (var x) t
| le_term_refl_con : forall l c n c' t ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s2/] ->
    wf_term l c (con n s1) t[/s2/] ->
    wf_term l c (con n s2) t[/s2/] ->    
    is_nth_level l n (term_rule c' t) ->
    le_subst l c ps s1 s2 c' ->    
    le_term l c (tle_refl_con n ps) (con n s1) (con n s2) t[/s2/]
| le_term_trans : forall l p1 p2 c e1 e12 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    le_term l c p1 e1 e12 t ->
    le_term l c p2 e12 e2 t ->
    le_term l c (tle_trans p1 p2) e1 e2 t
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv : forall l sp p c e1 e2 t t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c (conv sp e1) t' ->
    wf_term l c (conv sp e2) t' ->
    le_term l c p e1 e2 t ->
    le_sort l c sp t t' ->
    le_term l c (tle_conv sp p) (conv sp e1) (conv sp e2) t'
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
with le_subst : lang -> ctx -> subst_le -> subst -> subst -> ctx -> Prop :=
| le_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::] ->
    le_subst l c [::] [::] [::] [::]
| le_subst_cons : forall l pf pfs c s1 s2 c' e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c (e1::s1) (t::c') ->
    wf_subst l c (e2::s2) (t::c') ->
    le_subst l c pfs s1 s2 c' ->
    le_term l c pf e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (pf::pfs) (e1::s1) (e2::s2) (t::c')
with wf_ctx : lang -> ctx -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c)
with wf_rule : lang -> rule -> Prop :=
| wf_sort_rule : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_rule l (sort_rule c)
| wf_term_rule : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l (term_rule c t)
| le_sort_rule : forall l c t1 t2,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l (sort_le_rule c t1 t2)
| le_term_rule : forall l c e1 e2 t,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l (term_le_rule c e1 e2 t)
with wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).
