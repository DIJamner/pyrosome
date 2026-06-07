(* WIP prototype: the mutual fundamental lemma for the OTT reduction-on-syntax
   LR (file 4/5).  One `RedTy_rect`, motive = escape_ty * escape_tm * reflect.

   Goal here: validate the motive (with `elt_sort` supplying the canonical
   member sort), prove the three LEAF cases, and stage the Pi case.  Once green
   + axiom-free (modulo egraph_sound) this ports into FundamentalLemma.v. *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Tools Require Import Matches.
From Pyrosome.Lang.OTT Require Import Base Nat Pi.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral LogicalRelation FundamentalLemma.
Import Core.Notations.

(* The canonical element sort of a reducible type, read off the constructor.
   reflect / escape_tm are stated at this sort. *)
Definition elt_sort {G A B} (r : RedTy ott G A B) : osort :=
  match projT2 r with
  | rtt_nat _ G _ _ _ _ => nat_sort G
  | rtt_empty _ G _ _ _ _ => empty_sort G
  | rtt_ne _ G _ _ na _ rN lN _ _ _ => el_sort rN lN G na
  | rtt_pi _ G _ _ rF lF lG F C _ _ _ _ _ _ _ _ =>
      s_exp G (term_info orel lG) (oEl orel lG G (oPi_rel rF lF lG F C G))
  end.

(* sanity: elt_sort computes on the smart constructors *)
Lemma elt_sort_nat (G A B : tm) (ra : RNat ott G A) (rb : RNat ott G B)
  : elt_sort (RedTy_nat ott ra rb) = nat_sort G.
Proof. reflexivity. Qed.

Lemma elt_sort_empty (G A B : tm) (ra : REmpty ott G A) (rb : REmpty ott G B)
  : elt_sort (RedTy_empty ott ra rb) = empty_sort G.
Proof. reflexivity. Qed.

Lemma elt_sort_ne (G A B na nb rN lN : tm) (ra : reds string ott ott_pa A na)
  (rb : reds string ott ott_pa B nb)
  (h : ne_eq string ott ott_pa (code_sort rN lN G) na nb)
  : elt_sort (@RedTy_ne ott G A B na nb rN lN ra rb h) = el_sort rN lN G na.
Proof. reflexivity. Qed.

(* ---- the three components of the motive ---- *)
Definition esc_ty {G A B} (r : RedTy ott G A B) : Prop :=
  forall S, wf_term ott [] A S -> wf_term ott [] B S -> eq_term ott [] S A B.

Definition esc_tm {G A B} (r : RedTy ott G A B) : Prop :=
  forall a b, RedTy_R ott r a b ->
    wf_term ott [] a (elt_sort r) -> wf_term ott [] b (elt_sort r) ->
    eq_term ott [] (elt_sort r) a b.

Definition reflect_at {G A B} (r : RedTy ott G A B) : Type :=
  forall a b, neutral ott_pa a -> neutral ott_pa b ->
    wf_term ott [] a (elt_sort r) -> wf_term ott [] b (elt_sort r) ->
    eq_term ott [] (elt_sort r) a b -> RedTy_R ott r a b.

Definition Pmot (G A B : tm) (r : RedTy ott G A B) : Type :=
  (esc_ty r * esc_tm r * reflect_at r)%type.

(* ---- LEAF: Nat ---- *)
Lemma leaf_nat (G A B : tm) (ra : RNat ott G A) (rb : RNat ott G B)
  : Pmot G A B (RedTy_nat ott ra rb).
Proof.
  unfold Pmot, esc_ty, esc_tm, reflect_at; rewrite !elt_sort_nat.
  repeat split.
  - (* escape_ty *) intros S HA HB. eapply RedTy_Nat_sound; eassumption.
  - (* escape_tm *) intros a b Hm Ha Hb.
    change (RedTy_R ott (RedTy_nat ott ra rb) a b) with (RedNatMem ott G a b) in Hm.
    eapply RedNatMem_sound; eassumption.
  - (* reflect *) intros a b Hna Hnb Ha Hb Heq.
    change (RedTy_R ott (RedTy_nat ott ra rb) a b) with (RedNatMem ott G a b).
    apply RedNatMem_reflect; repeat split; eassumption.
Qed.

(* ---- LEAF: Empty ---- *)
Lemma leaf_empty (G A B : tm) (ra : REmpty ott G A) (rb : REmpty ott G B)
  : Pmot G A B (RedTy_empty ott ra rb).
Proof.
  unfold Pmot, esc_ty, esc_tm, reflect_at; rewrite !elt_sort_empty.
  repeat split.
  - intros S HA HB. eapply RedTy_Empty_sound; eassumption.
  - intros a b Hm Ha Hb.
    change (RedTy_R ott (RedTy_empty ott ra rb) a b) with (RedNe ott (empty_sort G) a b) in Hm.
    eapply RedNe_sound_at; eassumption.
  - intros a b Hna Hnb Ha Hb Heq.
    change (RedTy_R ott (RedTy_empty ott ra rb) a b) with (RedNe ott (empty_sort G) a b).
    apply RedNe_reflect; repeat split; eassumption.
Qed.

(* ---- LEAF: neutral code ---- *)
Lemma leaf_ne (G A B na nb rN lN : tm) (ra : reds string ott ott_pa A na)
  (rb : reds string ott ott_pa B nb)
  (h : ne_eq string ott ott_pa (code_sort rN lN G) na nb)
  : Pmot G A B (@RedTy_ne ott G A B na nb rN lN ra rb h).
Proof.
  unfold Pmot, esc_ty, esc_tm, reflect_at; rewrite !elt_sort_ne.
  repeat split.
  - (* escape_ty: type codes A,B reduce to ne_eq codes na,nb at the U code-sort *)
    intros S HA HB. eapply RedNe_sound_at with (t:=code_sort rN lN G);
      [ eapply red_ne; eassumption | eassumption | eassumption ].
  - (* escape_tm: members reduce to ne_eq neutrals at El na *)
    intros a b Hm Ha Hb.
    change (RedTy_R ott (@RedTy_ne ott G A B na nb rN lN ra rb h) a b)
      with (RedNe ott (el_sort rN lN G na) a b) in Hm.
    eapply RedNe_sound_at; eassumption.
  - (* reflect: a neutral pair at El na is a neutral member *)
    intros a b Hna Hnb Ha Hb Heq.
    change (RedTy_R ott (@RedTy_ne ott G A B na nb rN lN ra rb h) a b)
      with (RedNe ott (el_sort rN lN G na) a b).
    apply RedNe_reflect; repeat split; eassumption.
Qed.
