Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

From Coq Require Import Bool Lists.List Classes.DecidableClass.
Import ListNotations.
Import BoolNotations.
Open Scope list.

(*
Require Import Utils.Base Utils.Booleans Utils.Eqb.
*)
Require Import Utils (*TODO: temp*).

(* Propositions that have Boolean computational behavior where possible *)
Variant cProp : Type := cTrue | cFalse | cEmbed (P : Prop).

Definition interp (P : cProp) : Prop :=
  match P with
  | cTrue => True
  | cFalse => False
  | cEmbed P => P
  end.

Definition cCorresponds cA A := (interp cA) <-> A.
Existing Class cCorresponds.

Ltac solve_corresponds :=
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp |- _] => destruct P;try clear P end;
  cbn in *; intuition fail.

(* Note: this hint needs to be last; make sure it works right *)
Definition cembed_corresponds A : cCorresponds (cEmbed A) A.
Proof. solve_corresponds. Qed.
#[export] Hint Extern 100 (cCorresponds _ ?A) => apply cembed_corresponds : typeclass_instances.


#[export] Instance ctrue_corresponds : cCorresponds cTrue True.
Proof. solve_corresponds. Qed.

#[export] Instance cfalse_corresponds : cCorresponds cFalse False.
Proof. solve_corresponds. Qed.

Lemma cProp_intro cA A `{c_Corr : cCorresponds cA A} : interp cA -> A.
Proof. apply c_Corr. Qed.
Arguments cProp_intro {cA}%type_scope {A}%type_scope {c_Corr} _.


Lemma cProp_ex cA A `{c_Corr : cCorresponds cA A} : A -> interp cA.
Proof. apply c_Corr. Qed.
Arguments cProp_ex {cA} {A}%type_scope {c_Corr} _.


Definition cand (a b : cProp) :=
  match a, b with
  | cTrue, _ => b
  | cFalse, _ => cFalse
  | cEmbed P, cTrue => cEmbed P
  | cEmbed P, cFalse => cFalse
  | cEmbed P1, cEmbed P2 => cEmbed (P1 /\ P2)
  end.

Definition cor (a b : cProp) :=
  match a, b with
  | cTrue, _ => cTrue
  | cFalse, _ => b
  | cEmbed P, cTrue => cTrue
  | cEmbed P, cFalse => cEmbed P
  | cEmbed P1, cEmbed P2 => cEmbed (P1 \/ P2)
  end.

Definition cneg (a : cProp) :=
  match a with
  | cTrue => cFalse
  | cFalse => cTrue
  | cEmbed P => cEmbed (~ P)
  end.

Definition cimpl (a b : cProp) :=
  match a, b with
  | cTrue, _ => b
  | cFalse, _ => cTrue
  | cEmbed P, cTrue => cTrue
  | cEmbed P, cFalse => cEmbed (~ P)
  | cEmbed P1, cEmbed P2 => cEmbed (P1 -> P2)
  end.


Definition ciff (a b : cProp) :=
  match a, b with
  | cTrue, cTrue
  | cFalse, cFalse => cTrue
  | cTrue, cFalse 
  | cFalse, cTrue => cFalse
  | cEmbed P, cTrue
  | cTrue, cEmbed P => cEmbed P
  | cEmbed P, cFalse
  | cFalse, cEmbed P => cEmbed (~ P)
  | cEmbed P1, cEmbed P2 => cEmbed (P1 <-> P2)
  end.

Section WithParams.
  Context (cA cB : cProp) (A B : Prop)
    (A_corr : cCorresponds cA A)
    (B_corr : cCorresponds cB B).
 

#[export] Instance cand_corresponds : cCorresponds (cand cA cB) (A /\ B).
Proof. solve_corresponds. Qed.

#[export] Instance cor_corresponds : cCorresponds (cor cA cB) (A \/ B).
Proof. solve_corresponds. Qed.

#[export] Instance cneg_corresponds : cCorresponds (cneg cA) (~A).
Proof. solve_corresponds. Qed.

#[export] Instance cimpl_corresponds : cCorresponds (cimpl cA cB) (A -> B).
Proof. solve_corresponds. Qed.

#[export] Instance ciff_corresponds : cCorresponds (ciff cA cB) (A <-> B).
Proof. solve_corresponds. Qed.

End WithParams.


(* Propositions that have Boolean computational behavior where possible *)
Inductive qcProp : Type :=
| qcTrue
| qcFalse
| qcforall (A : Type) (cP : A -> qcProp)
| qcexists (A : Type) (cP : A -> qcProp)
| qcEmbed (P : Prop).



Definition qcand_body qcand_l qcand_r (a b : qcProp) :=
  match a, b with
  | qcTrue, _ => b
  | qcFalse, _ => qcFalse
  | qcEmbed P, qcTrue => qcEmbed P
  | qcEmbed P, qcFalse => qcFalse
  | qcEmbed P1, qcEmbed P2 => qcEmbed (P1 /\ P2)

  | _, qcforall cP =>
      qcforall (fun x => qcand_l a (cP x))
  | qcforall cP, _ =>
      qcforall (fun x => qcand_r (cP x) b)
  | _, qcexists cP =>
      qcexists (fun x => qcand_l a (cP x))
  | qcexists cP, _ =>
      qcexists (fun x => qcand_r (cP x) b)
  end.

TODO: to handle quantifiers properly, feels like I need a telescope
Question: do I need a type of telescopes or only specific tele types?                                          

Fixpoint qcand a b {struct a} :=  qcand_body qcand qcand_r a b
with qcand_r a b :=  qcand_body qcand qcand_r a b.


Definition interp (P : cProp) : Prop :=
  match P with
  | cTrue => True
  | cFalse => False
  | cEmbed P => P
  end.


(*
Record qcProp :=
  {
    U : Type;
    E : U -> Type;
    ex : forall univ : U, E univ;
    body : forall univ : U, E univ -> cProp;
  }.

Record qcProp' (U : Type) (E : U -> Type) :=
  {
    U' : forall (univ1 : U) (ex1 : E univ1), Type;
    E' : forall (univ1 : U) (ex1 : E univ1), U' univ1 ex1 -> Type;
    ex : forall (univ1 : U) (ex1 : E univ1) (univ : U univ1 ex1), E univ;
    body : forall univ : U, E univ -> cProp;
  }.

(*TODO: can't have U depend on A*)
Definition qcforall A (cB : A -> qcProp) :=
  
  let (U,E, ex, body) := cB in
                 

(* TODO: current lemmas don't work under/around binders *)
#[export] Instance cforall_corresponds : cCorresponds (cforall A cB) (forall x : A, B x).
Proof. solve_corresponds. Qed.
*)

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C).
Proof.
  intros.
  eapply cProp_intro.
  eapply cProp_ex in H.
  cbn in *.
  tauto.
Abort.

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C).
Proof.
  intros A B C.
  cbn in *.
  tauto.
Abort.

(* Deals w/ top-level forall only *)
Lemma under_forall A R Q
  :(forall (x : A), Q x) -> (forall x, Q x -> R x)  -> forall (x : A), R x.
Proof.
  firstorder.
Qed.

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C) -> False.
Proof.
  intros.
  epose proof (under_forall _ _ H).

  eapply under_forall in H.
  
  eapply cProp_ex in H.
  intros A B C.
  cbn in *.
  tauto.
Abort.


Definition cIs_true (b : bool) := if b then cTrue else cFalse.

#[export] Instance cIstrue_corresponds b : cCorresponds (cIs_true b) (Is_true b).
Proof. destruct b; solve_corresponds. Qed.

Section WithDecidable.

  Context (P : Prop)
    `{Decidable P}.

  Definition cEmbed_dec := cIs_true Decidable_witness.
  
  #[export] Instance cEmbed_dec_corresponds : cCorresponds cEmbed_dec P.
  Proof.
    unfold cEmbed_dec, DecidableClass.Decidable_witness.
    destruct H.
    clear H.
    unfold cCorresponds.
    rewrite <- Decidable_spec.
    destruct Decidable_witness; simpl;
      intuition congruence.
  Qed.

End WithDecidable.


Fixpoint call {A} (R : A -> cProp) l : cProp :=
  match l with
  | []=> cTrue
  | a::l => cand (R a) (call R l)
  end.

Instance call_corresponds {A} cR (R : A -> Prop)
  `{forall a, cCorresponds (cR a) (R a)}
  l
  : cCorresponds (call cR l) (all R l).
Proof.
  induction l; basic_goal_prep; typeclasses eauto.
Qed.


Fixpoint call2 {A B} (R : A -> B -> cProp) l1 l2 : cProp :=
  match l1, l2 with
  | [], [] => cTrue
  | a::l1, b::l2 => cand (R a b) (call2 R l1 l2)
  | _, _ => cFalse
  end.


Instance call2_corresponds {A B} cR (R : A -> B -> Prop)
  `{forall a b, cCorresponds (cR a b) (R a b)}
  l1 l2
  : cCorresponds (call2 cR l1 l2) (Forall2 R l1 l2).
Proof.
  revert l2;
    induction l1; destruct l2; basic_goal_prep.
  1-3:cbv; intuition eauto; safe_invert H0.
  {
    assert (Forall2 R (a :: l1) (b :: l2) <-> R a b /\ Forall2 R l1 l2).
    {
      intuition eauto;safe_invert H0; tauto.
    }
    unfold cCorresponds.
    rewrite H0.
    change (cCorresponds (cand (cR a b) (call2 cR l1 l2)) (R a b /\ Forall2 R l1 l2)).
    typeclasses eauto.
  }
Qed.



Instance list_eq_corresponds {A} cEq
  `{forall a b, cCorresponds (cEq a b) (a = b)}
  (l1 l2 : list A)
  : cCorresponds (call2 cEq l1 l2) (l1 = l2).
Proof.
  revert l2;
    induction l1; destruct l2; basic_goal_prep.
  1-3:cbv; intuition eauto; safe_invert H0.
  {
    assert (a :: l1 = a0 :: l2 <-> a = a0 /\ l1 = l2).
    {
      intuition eauto; subst; auto; try (safe_invert H0; subst; eauto).
    }
    unfold cCorresponds.
    rewrite H0.
    change (cCorresponds (cand (cEq a a0) (call2 cEq l1 l2)) (a = a0 /\ l1 = l2)).
    typeclasses eauto.
  }
Qed.
  

Goal forall A B C : Type, [A; A; C] = [A; B; C].
Proof.
  intros.
  eapply cProp_intro.
  (*TODO: do I want to try to handle A=A? probably not? but would be good
    alt: could use both this and existing rewrites so that existing rules fire less,
    but that would be a bit disappointing
    related: am I rebuilding something related to itauto?
    -Doesn't seem exactly the same b/c of e.g. call2 for equality
    -can the 2 be separated into 2 phases?
         +If so, what's the analogue to call2 R corresponds?

   Should probably separate out computational equality first, then do props?
   but if I'm always doing both, may as well have 1 step

   on the other hand, computational equality lemmas might make it into stdlib
   - can still use lemmas in proofs here
   *)

(*TODO: move to eqb*)
#[export, refine]
Instance eqb_decidable {A} `{Eqb_ok A} (a b : A) : Decidable (a = b) :=
  {|
    Decidable_witness := eqb a b;
  |}.
Proof.
  pose proof (eqb_prop_iff a b).
  destruct (eqb a b); simpl in *; intuition congruence.
Defined.


