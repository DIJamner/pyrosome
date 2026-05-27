Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain.
Import Core.Notations.

(* Normalizing the object environment, per the design: the normal form of an env
   is a telescope of [ext]s on a base ([emp], or an abstract metavar). That
   telescope IS the reflecting semantic environment used to evaluate open terms:
   one fresh neutral variable ([hd]) per [ext], with the inner variables WEAKENED
   (shifted by [wkn]) as we go under each extension. A bare base ([emp]/metavar)
   contributes no accessible object variables (it is opaque), so its reflecting
   env is empty.

   [weaken_val]/[weaken_ty] are the renaming (Kripke) action on values: they push
   a [wkn] onto every neutral leaf. NOTE the [wkn]/[exp_subst] annotation slots
   here use a placeholder [_ann]; [eval] ignores annotations, but faithful
   annotations are needed for the reify/soundness direction (TODO). *)
Section Env.
  Notation term := (@term string).

  Definition ann : term := con "_ann" [].

  (* push a weakening onto a neutral term:  e  |->  exp_subst wkn e *)
  Definition wk_term (e : term) : term :=
    con "exp_subst" [e; ann; ann; con "wkn" [ann; ann; ann]; ann; ann].

  Fixpoint weaken_val (v : sval) : sval :=
    match v with
    | vNe e => vNe (wk_term e)
    | vZero => vZero
    | vSuc v' => vSuc (weaken_val v')
    | vPair v1 v2 => vPair (weaken_val v1) (weaken_val v2)
    | vLam env body => vLam (map weaken_val env) body
    | vCode T => vCode (weaken_ty T)
    end
  with weaken_ty (T : svalty) : svalty :=
    match T with
    | dNe e => dNe (wk_term e)
    | dNat => dNat
    | dEmpty => dEmpty
    | dU r l => dU r l
    | dPi dom cenv cbody => dPi (weaken_ty dom) (map weaken_val cenv) cbody
    | dSig d1 denv dbody => dSig (weaken_ty d1) (map weaken_val denv) dbody
    end.

  (* Reflecting environment of a context term: a fresh neutral [hd] per [ext],
     with the already-built inner variables weakened.  Base ([emp]/metavar): []. *)
  Fixpoint eval_env (G : term) : senv :=
    match G with
    | con "ext" [A; i; G'] =>
        vNe (con "hd" [A; i; G']) :: map weaken_val (eval_env G')
    | _ => []
    end.

End Env.
