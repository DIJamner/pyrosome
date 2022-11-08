Require Import ZArith Lia.

From Utils Require Import Utils Natlike.

(*TODO: decouple Eqb from Eqb_ok*)
#[global] Instance eqb_positive : Eqb positive :=
  {
    eqb := Pos.eqb;
    eqb_eq := Pos.eqb_eq;
    eqb_neq := Pos.eqb_neq;
    eqb_refl := Pos.eqb_refl;
    Eqb_dec := Pos.eq_dec;
  }.

#[global] Instance natlike_positive : Natlike positive :=
  {
    natlike_eqb := eqb_positive;
    ltb := Pos.ltb;
    leb := Pos.leb;
    zero := xH;
    succ n := (n + 1)%positive;
    is_top _ := false;
    iter _ b f := Pos.iter f b;
  }.

(* TODO: prove natlike_ok *)
