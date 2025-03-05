Require Import Utils.Base Datatypes.Bool Datatypes.String Uint63.
Require Export coqutil.Eqb.


Section __.
  Context (A : Type).

  (* TODO: is the no-record version worth it here to avoid firstorder trouble? *)
  Class DecidableEq :=
    {
      dec : forall (s1 s2 : A), {s1 = s2} + {s1 <> s2}
    }.

  Context `{DecidableEq}.
  
  (* Note: do not export. Should be declared as an instance only when no boolean implementation yet exists since it will likely have poor performance.   
   *)
  Instance eqb_from_decidable : Eqb A :=
    fun a b => if dec a b then true else false.

  
  Instance eqb_from_decidable_ok `{DecidableEq} : Eqb_ok eqb_from_decidable.
  Proof.
    intros a b.
    unfold eqb, eqb_from_decidable.
    destruct (dec a b); auto.
  Qed.


  Context `{@Eqb_ok _ eqb_from_decidable}.
  
  (* Note: do not export. This instance should not be expected to compute, since it depends on a lemma
     that is probably defined with Qed. To emphasize this, we define this instance with Qed as well.
     Thus, it should be used with caution.
   *)
  Instance decidable_from_eqb_ok : DecidableEq.
  Proof.
    constructor; intros.
    specialize (H0 s1 s2).
    revert H0.
    case_match;
      intros; subst; eauto.
  Qed.

End __.

Arguments dec {A}%type_scope {DecidableEq} s1 s2.

  
(*TODO: also account for _=_->False *)
#[export] Hint Rewrite eqb_ineq_false
  using (try typeclasses eauto; (left || right); assumption) : bool.
