(* Prototype 3 (staged reference): the CONCRETE OTT substrate for instantiating
   the Kripke RedTy in src/.../Pi/LogicalRelation.v.  Verified con builders
   (memory ott-con-arg-orders), the `ott_pa` selector, and the base recognizers
   RNat/RPi/osub (which DO instantiate the generic interface cleanly).

   DESIGN FINDING (2026-06-07): the generic interface's `act`/`cod`/`mapp`
   operations (term->term->term in the committed LogicalRelation.v RedTyDef) are
   TOO THIN to instantiate for OTT.  OTT explicit substitutions carry full type
   annotations -- `exp_subst` = [v; A; i; g; src; tgt] needs the SOURCE/TARGET
   envs AND the substituted code's type `A`=U_{rF,lF} and info `i`=info rel
   (next lF).  Those (G/D/g and the Pi telescope rF/lF/lG) live ONLY inside the
   rtt_pi constructor.  So the truly-concrete RedTy must EITHER (a) thread the
   telescope+envs through richer operation signatures, OR (b) be written fully
   OTT-concrete with the builders inlined and rF/lF/lG/G/D carried in rtt_pi.
   RECOMMENDATION: (b) -- the operations diverge anyway (act-on-code vs
   act-on-member use different type annotations), so a generic interface buys
   little.  Next session: rewrite RedTy_tot OTT-concrete using the builders
   below, carrying rF lF lG in rtt_pi. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral LogicalRelation.
Import Core.Notations.
Open Scope string.

(* OTT principal-argument selector (verified indices). *)
Definition ott_pa (n : string) : option nat :=
  if eqb n "app_rel" then Some 1
  else if eqb n "app_irr" then Some 1
  else if eqb n "Emptyrec" then Some 0
  else if eqb n "exp_subst" then Some 0
  else if eqb n "ty_subst" then Some 0
  else None.

Notation tm := (@Term.term string).

(* ---- info / universe / decode ---- *)
Definition orel : tm := con "rel" [].
Definition oirr : tm := con "irr" [].
Definition oL0  : tm := con "L0" [].
Definition onext (l : tm) : tm := con "next" [l].
Definition oiota (l : tm) : tm := con "iota" [l].
Definition oinfo (r l : tm) : tm := con "info" [l; r].
Definition oU (r l G : tm) : tm := con "U" [l; r; G].
Definition oEl (r l G e : tm) : tm := con "El" [e; l; r; G].

(* a CODE F : exp G (U r l) has info [rel, next l] and inhabits type U r l. *)
Definition code_info (l : tm) : tm := oinfo orel (onext l).
Definition code_ty (r l G : tm) : tm := oU r l G.

(* ---- substitution calculus ---- *)
Definition oid (G : tm) : tm := con "id" [G].
Definition oext (A i G : tm) : tm := con "ext" [A; i; G].
Definition owkn (A i G : tm) : tm := con "wkn" [A; i; G].
Definition ohd  (A i G : tm) : tm := con "hd"  [A; i; G].
(* exp_subst (g : sub src tgt)(v : exp src A) : exp tgt A[g]. *)
Definition oexp_subst (v A i g src tgt : tm) : tm :=
  con "exp_subst" [v; A; i; g; src; tgt].
Definition osnoc (v A i g src tgt : tm) : tm := con "snoc" [v; A; i; g; src; tgt].

(* ---- type/term formers ---- *)
Definition oNat (G : tm) : tm := con "Nat" [G].
Definition oEmpty (G : tm) : tm := con "Empty" [G].
Definition oPi_rel (rF lF lG F B G : tm) : tm := con "Pi_rel" [B; F; lG; lF; rF; G].
Definition oapp_rel (rF lF lG F B G f a : tm) : tm :=
  con "app_rel" [a; f; B; F; lG; lF; rF; G].

Section Recognizers.
  Context (l : Rule.lang string).
  Notation reds := (reds string l ott_pa).

  (* A reduces to the Nat code in env G. *)
  Definition RNat (G A : tm) : Prop := reds A (oNat G).
  (* A reduces to a proof-relevant Pi code with domain code F, codomain code C,
     in env G (levels/relevance recovered existentially). *)
  Definition RPi (G A F C : tm) : Prop :=
    exists rF lF lG, reds A (oPi_rel rF lF lG F C G).
  (* object substitution g : sub G D. *)
  Definition osub (G D g : tm) : Prop := wf_term l [] g (scon "sub" [G; D]).
End Recognizers.
