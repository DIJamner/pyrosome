(* P1c alternative: member relation as a MUTUAL INDEX (no output-Sig).        *)
(* RedTyIn G A B S : Prop  +  RedTmIn G A B S a b : Prop, MUTUALLY inductive.  *)
(* This AVOIDS both the choice problem (no existentially-chosen R to thread)   *)
(* AND the funext problem (no member-relation index to transport).  The only   *)
(* risk is POSITIVITY: RedTmIn appears in a hypothesis position of the Pi      *)
(* codomain clause (`raa' : RedTmIn .. -> ..`), the standard logrel mutual     *)
(* encoding.  This file TESTS positivity. *)
(* RESULT: FAILS POSITIVITY.  `RedTmIn` occurs non-strictly-positively in    *)
(* `in_pi`'s codomain clause: `RedTmIn .. a a' -> RedTyIn ..` puts the member *)
(* relation to the LEFT of an arrow whose head is the mutual type.  This is   *)
(* the exact reason metamltt/LogRel2 carry the member relation as a Type      *)
(* Record-of-functions (PolyRedPack) + adequacy split, NOT a Prop index.      *)
(* The Prop mutual encoding is therefore NOT available.  See z26 QUESTION.    *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral LogicalRelation.
Import Core.Notations.
Notation tm := (@Term.term string).
Notation osort := (@Term.sort string).
Open Scope string.

Section T.
Context (l : Rule.lang string).
Notation osub := (osub l).
Notation reds := (reds string l ott_pa "hd").
Notation ne_eq := (ne_eq string l ott_pa "hd").

Inductive RedTyIn : tm -> tm -> tm -> osort -> Prop :=
| in_nat : forall G A B,
    RNat l G A -> RNat l G B -> RedTyIn G A B (nat_sort G)
| in_empty : forall G A B,
    REmpty l G A -> REmpty l G B -> RedTyIn G A B (empty_sort G)
| in_ne : forall G A B na nb rN lN,
    reds A na -> reds B nb -> ne_eq (code_sort rN lN G) na nb ->
    RedTyIn G A B (el_sort rN lN G na)
| in_pi : forall G A B rF lF lG F C F' C',
    reds A (oPi_rel rF lF lG F C G) ->
    reds B (oPi_rel rF lF lG F' C' G) ->
    (forall D g (os : osub G D g),
        RedTyIn D (act_code rF lF g G D F) (act_code rF lF g G D F')
                  (el_sort rF lF D (act_code rF lF g G D F))) ->
    (forall D g (os : osub G D g) a a',
        RedTmIn D (act_code rF lF g G D F) (act_code rF lF g G D F')
                  (el_sort rF lF D (act_code rF lF g G D F)) a a' ->
        RedTyIn D (cod_at rF lF lG g G D F C a) (cod_at rF lF lG g G D F' C' a')
                  (el_sort orel lG D (cod_at rF lF lG g G D F C a))) ->
    RedTyIn G A B (el_sort orel lG G (oPi_rel rF lF lG F C G))
with RedTmIn : tm -> tm -> tm -> osort -> tm -> tm -> Prop :=
| inm_nat_zero : forall G A B a b,
    RNat l G A -> RNat l G B ->
    reds a (ozero G) -> reds b (ozero G) ->
    RedTmIn G A B (nat_sort G) a b
| inm_nat_suc : forall G A B a b a' b',
    RNat l G A -> RNat l G B ->
    reds a (osuc G a') -> reds b (osuc G b') ->
    RedTmIn G A B (nat_sort G) a' b' ->
    RedTmIn G A B (nat_sort G) a b
| inm_ne : forall G A B S a b na nb,
    (* generic neutral member at ANY sort S whose type reduces to a neutral
       code / Nat / Empty.  Carries the reds + ne_eq directly. *)
    reds a na -> reds b nb -> ne_eq S na nb ->
    RedTmIn G A B S a b
| inm_pi : forall G A B rF lF lG F C F' C' t u,
    reds A (oPi_rel rF lF lG F C G) ->
    reds B (oPi_rel rF lF lG F' C' G) ->
    (forall D g (os : osub G D g) a a'
        (raa' : RedTmIn D (act_code rF lF g G D F) (act_code rF lF g G D F')
                  (el_sort rF lF D (act_code rF lF g G D F)) a a'),
        wf_term l [] a  (el_sort rF lF D (act_code rF lF g G D F)) ->
        wf_term l [] a' (el_sort rF lF D (act_code rF lF g G D F)) ->
        RedTmIn D (cod_at rF lF lG g G D F C a) (cod_at rF lF lG g G D F' C' a')
                  (el_sort orel lG D (cod_at rF lF lG g G D F C a))
                  (mapp rF lF lG g G D F C t a)
                  (mapp rF lF lG g G D F' C' u a')) ->
    RedTmIn G A B (el_sort orel lG G (oPi_rel rF lF lG F C G)) t u.

End T.
