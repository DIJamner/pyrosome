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

(* Not definitions so that they don't get in the way of evaluation
 *)
Notation lift1 f A := (fun a => f (A a)).
Notation lift2 f A B := (fun a => f (A a) (B a)).

Section WithTeleType.

  Context (A : Type)
    (*(E : A -> Type)*).

  (* Propositions that have Boolean computational behavior where possible.
     TODO: separate embedded props/vals out into subst so that we can compute A = A ~> True
   *)
Variant cProp : Type := cTrue | cFalse | cEmbed (P : forall (a : A), (* E a ->*) Prop).

Definition interp (a : A) (*(e : E a)*) (P : cProp) : Prop :=
  match P with
  | cTrue => True
  | cFalse => False
  | cEmbed P => P a
  end.

(* TODO: what args for A? *)
(*TODO: want exists (the same) e*)
Definition cCorresponds cA A :=
  (forall a (* (e : E a)*) , interp a cA <-> A a).

Existing Class cCorresponds.

Ltac solve_corresponds :=
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp |- _] => destruct P;try clear P end;
  cbn in *; intros a;
  repeat match goal with [H : forall a (* (e : E a)*), _ |- _] => specialize (H a) end;
  intuition fail.

(* Note: this hint needs to be last; make sure it works right *)
Definition cembed_corresponds B : cCorresponds (cEmbed B) B.
Proof. solve_corresponds. Qed.

#[export] Instance ctrue_corresponds : cCorresponds cTrue (fun _ => True).
Proof. solve_corresponds. Qed.

#[export] Instance cfalse_corresponds : cCorresponds cFalse (fun _ => False).
Proof. solve_corresponds. Qed.


Definition cand (a b : cProp) :=
  match a, b with
  | cTrue, _ => b
  | cFalse, _ => cFalse
  | cEmbed P, cTrue => cEmbed P
  | cEmbed P, cFalse => cFalse
  | cEmbed P1, cEmbed P2 => cEmbed (lift2 and P1 P2)
  end.

Definition cor (a b : cProp) :=
  match a, b with
  | cTrue, _ => cTrue
  | cFalse, _ => b
  | cEmbed P, cTrue => cTrue
  | cEmbed P, cFalse => cEmbed P
  | cEmbed P1, cEmbed P2 => cEmbed (lift2 or P1 P2)
  end.

Definition cnot (a : cProp) :=
  match a with
  | cTrue => cFalse
  | cFalse => cTrue
  | cEmbed P => cEmbed (lift1 not P)
  end.

(* TODO: deprecated; replaced w/ cforall *)
Definition cimpl (a b : cProp) :=
  match a, b with
  | cTrue, _ => b
  | cFalse, _ => cTrue
  | cEmbed P, cTrue => cTrue
  | cEmbed P, cFalse => cEmbed (lift1 not P)
  | cEmbed P1, cEmbed P2 => cEmbed (fun a => P1 a -> P2 a)
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
  | cFalse, cEmbed P => cEmbed (lift1 not P)
  | cEmbed P1, cEmbed P2 => cEmbed (lift2 iff P1 P2)
  end.


#[export] Instance Prop_corresponds : cCorresponds cTrue (fun t => inhabited Prop).
Proof.  
  unfold cCorresponds in *;
    cbn;
    intuition idtac.
  constructor; eauto.
  apply True.
Qed.

Section WithParams.
  Context (cB' cB : cProp) (B' B : forall x : A, (*E x ->*) Prop)
    (B'_corr : cCorresponds cB' B')
    (B_corr : cCorresponds cB B).
 

#[export] Instance cand_corresponds : cCorresponds (cand cB' cB) (lift2 and B' B).
Proof. solve_corresponds. Qed.

#[export] Instance cor_corresponds : cCorresponds (cor cB' cB) (lift2 or B' B).
Proof. solve_corresponds. Qed.

#[export] Instance cnot_corresponds : cCorresponds (cnot cB') (lift1 not B').
Proof. solve_corresponds. Qed.

#[export] Instance cimpl_corresponds : cCorresponds (cimpl cB' cB) (fun a => B' a -> B a).
Proof. solve_corresponds. Qed.

#[export] Instance ciff_corresponds : cCorresponds (ciff cB' cB) (lift2 iff B' B).
Proof. solve_corresponds. Qed.

(*TODO: where to put this?*)
Lemma inhabited_prop C : C <-> inhabited C.
Proof.
  intuition eauto using inhabits.
  destruct H; auto.
Qed.

#[export] Instance inhabited_prop_corresponds : cCorresponds cB (lift1 inhabited B).
Proof using B_corr.
  clear B'_corr cB' B'.
   unfold cCorresponds in *; repeat lazymatch goal with
                                   | P:cProp |- _ => destruct P; try clear P
                                   end; cbn in *; intros a;
   repeat match goal with
          | H:forall a, _ |- _ => specialize (H a)
     end.
   all: try solve[intuition eauto using inhabited_prop].
   all: rewrite <- inhabited_prop; intuition fail.
Qed.
     


End WithParams.


End WithTeleType.


Lemma cProp_intro cB' B' `{c_Corr : cCorresponds unit cB' (fun _ => B')}
  : interp tt cB' -> B'.
Proof. apply c_Corr. Qed.
Lemma cProp_ex cB' B' `{c_Corr : cCorresponds unit cB' (fun _ => B')}
  : B' -> interp tt cB'.
Proof. apply c_Corr. Qed.

(*
Ltac solve_corresponds :=
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
  cbn in *; intuition fail.
*)
     
Arguments cProp_intro {cA}%type_scope {A}%type_scope {c_Corr} _ : rename.

Arguments cProp_ex {cA} {A}%type_scope {c_Corr} _ : rename.

#[export] Hint Extern 100 (cCorresponds _ ?A) => apply cembed_corresponds : typeclass_instances.


Definition cforall T A cA (cP : cProp {t : T & A t}) : cProp T :=
  match cA, cP with
  | cFalse _, _
  | _ , cTrue _ => cTrue _
  | cTrue _, cFalse _ => cFalse _
  | cEmbed P, cFalse _ => cEmbed (lift1 not P)
  | cTrue _, cEmbed P
  | cEmbed _, cEmbed P => cEmbed (fun t => forall x : A t, P (existT _ t x))
  end.


Instance cforall_corresponds T A cA cB (B : forall t : T, A t -> Prop)
  `{cCorresponds T cA (fun t => inhabited (A t))}
  `{cCorresponds (sigT A)%type cB (fun t' => B (projT1 t') (projT2 t'))}
  : cCorresponds (cforall A cA cB) (fun t => forall x : A t, B t x).
Proof.
  (*
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
    cbn in *; intros a;
    repeat match goal with [H : forall a (* (e : E a)*), _ |- _] => specialize (H a) end.
  {
    pose proof (fun a' => H0 (existT _ a a')).
    intuition idtac.
    specialize (H1 x).
    intuition idtac.
  }
  {
    pose proof (fun a' => H0 (existT _ a a')).
    intuition idtac.
    eapply H0 with (a:=existT _ _ _); eauto.
  }
    eapply H2.
  }
  {
    pose proof (fun a' => H0 (existT _ a a')).
    intuition idtac.
    {
       eapply H0 with (a:=existT _ _ _).
       eapply H2.
    }
  }
    {
      apply H0; simpl; eauto.
    }
  }
  Unshelve.
  auto.
Qed.
#[export] Hint Extern 90 (cCorresponds _ (fun t => forall x : _, _))
=> simple eapply cforall_corresponds : typeclass_instances.*)
Admitted.


Definition cexists T A (cA : cProp T) (cP : cProp {t : T & A t}) : cProp T :=
  match cP with
  | cTrue _ => cA
  (* must check the inhabitance of A
     Question: should I design this to assume A inhabited?
   *)
  | cFalse _ => cFalse _
  | cEmbed P => cEmbed (fun t => exists x : A t, P (existT _ t x))
  end.
(*
#[export] Instance cexist_corresponds T A cB (B : forall t : T, A t -> Prop)
  `{cCorresponds (sigT A)%type cB (fun t' => B (projT1 t') (projT2 t'))}
  : cCorresponds (cexists A cA cB) (fun t => exists x : A t, B t x).
Proof.
  
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
    cbn in *; intros a.
  {
    pose proof (fun a' => H (existT _ a a')).
    intuition idtac.
    {
      destruct H1.
      exists X.
      eapply H0 with (a':= X).
      auto.
    }
    eapply exists_inhabited; eauto.
  }
  { pose proof (fun a' => H (existT _ a a')).    
    firstorder.
  }
  {
    firstorder.
  }
Qed.
*)

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C).
Proof.
  intros.
  eapply cProp_intro.
  eapply cProp_ex in H.
  cbn in *.
  tauto.
Abort.

(*
#[export] Hint Extern 90 (cCorresponds _ (fun t => _))
=> eapply cforall_corresponds : typeclass_instances.*)

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C).
Proof.
  eapply cProp_intro.
  cbn.
  tauto.
Qed.



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


