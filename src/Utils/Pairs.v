Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Bool.
Import BoolNotations.

From Utils Require Import Base Booleans Eqb Default.

Section __.
  Context (A B : Type)
    `{Eqb_ok A}
    `{Eqb_ok B}
    `{WithDefault A}
    `{WithDefault B}.
  
  Hint Rewrite pair_equal_spec : utils.

  #[export] Instance pair_eqb : Eqb (A * B) :=
    fun a b =>
      andb (eqb (fst a) (fst b))
        (eqb (snd a) (snd b)).

  #[export] Instance pair_eqb_ok : Eqb_ok pair_eqb.
  Proof.
    unfold Eqb_ok, eqb, pair_eqb.
    intros a b;
      specialize (H0 (fst a) (fst b));
      specialize (H2 (snd a) (snd b)).
    revert H0 H2;
      case_match; case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  #[export] Instance pair_default : WithDefault (A * B) := (default, default).

  

  Definition pair_map_snd {C} (f : B -> C) (p : A * B) :=
    let (a,b) := p in (a, f b).
  
End __.


Arguments pair_eqb {A B}%type_scope {Eqb_A Eqb_B} _ _ : rename.

Arguments pair_default {A B}%type_scope {Default_A Default_B} : rename.

Arguments pair_map_snd {A B C} f !p/.

#[export] Hint Rewrite pair_equal_spec : utils.
