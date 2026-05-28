Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(* Semantic value domain for the cast-free OTT NbE / gluing model.

   ENVIRONMENT-FREE evaluation (see EvalRel.v): evaluation does NOT carry an ambient
   substitution.  An object variable reflects directly to a neutral with a de Bruijn
   INDEX head (index 0 = innermost binding), and an explicit substitution [exp_subst
   g e] is realised by [apply]ing the semantic substitution [eval_sub g] (an [ssub])
   to the value [eval_rel e].  Because values are thus *absolute* (not relative to an
   environment), term congruence is plain value-equality and substitution congruence
   follows from [apply] respecting equality.

   Neutrals carry only SEMANTIC data — an index, or a spine of eliminators over
   semantic motives — never raw syntax, so congruent arguments build equal neutrals.

   The Tarski universe is handled UNIFORMLY: a semantic type [svalty] is either the
   universe [dU] or [dEl e] = [El] of a code-value [e : sval] (Nat/Empty are codes,
   [vNat]/[vEmpty]; a stuck type is [dEl] of a neutral [vNe]).  Because [dEl] wraps an
   arbitrary code without inspecting its shape, [El]-formation is a plain congruence and
   [El]-substitution computes definitionally ([apply_ty s (dEl e) = dEl (apply_val s e)]).
   Pi/Sig/pairs (binders) are deferred — re-add their value forms with the binder
   fragment. *)
Section Domain.
  Notation term := (@term string).

  Unset Elimination Schemes.
  Inductive svalty : Type :=
  | dU    (r l : term)                   (* universe U_{r,l}; r,l are nf_info-normal *)
  | dEl   (e : sval)                     (* El of a code-value (typically a neutral) *)
  with sval : Type :=
  | vNe   (n : neutral)                  (* neutral value *)
  | vZero
  | vSuc  (v : sval)
  | vNat                                 (* the code [Nat] (element of U) *)
  | vEmpty                               (* the code [Empty] (element of U) *)
  with neutral : Type :=
  | nVar  (k : nat)                      (* de Bruijn index (0 = innermost) *)
  | nEmptyrec (rA lA : term) (A : sval) (scrut : neutral).
  Set Elimination Schemes.

  (* A semantic SUBSTITUTION: the values to substitute for the in-scope variables
     (the denotation of a [sub] term; produced by [eval_sub], consumed by [apply]). *)
  Definition ssub := list sval.

  (* A semantic ENVIRONMENT: the (semantic) TYPES of an object context's variables
     (the denotation of an [env]/context; produced by [eval_env]). *)
  Definition senv := list svalty.

  (* Renaming for context extension: index 0 is innermost, so adding [d] binders
     shifts every index up by [d].  (Used for [wkn] and to weaken carried-over
     variables/types when normalizing an [ext].) *)
  Fixpoint shift_ty (d : nat) (T : svalty) : svalty :=
    match T with
    | dU r l => dU r l
    | dEl e => dEl (shift_val d e)
    end
  with shift_val (d : nat) (v : sval) : sval :=
    match v with
    | vNe n => vNe (shift_ne d n)
    | vZero => vZero
    | vSuc v' => vSuc (shift_val d v')
    | vNat => vNat
    | vEmpty => vEmpty
    end
  with shift_ne (d : nat) (n : neutral) : neutral :=
    match n with
    | nVar k => nVar (k + d)
    | nEmptyrec rA lA A s => nEmptyrec rA lA (shift_val d A) (shift_ne d s)
    end.

  (* Apply a semantic substitution to a value/type/neutral (NbE substitution into
     normal forms).  A variable picks its replacement out of [σ]; [dEl] pushes the
     substitution into its code (if that code was a neutral that becomes concrete, the
     type is just [dEl] of the new code — no re-decode needed); the [Emptyrec] spine
     re-substitutes its motive and recurses on its (still-neutral) scrutinee. *)
  Fixpoint apply_ty (s : ssub) (T : svalty) : svalty :=
    match T with
    | dU r l => dU r l
    | dEl e => dEl (apply_val s e)
    end
  with apply_val (s : ssub) (v : sval) : sval :=
    match v with
    | vNe n => apply_ne s n
    | vZero => vZero
    | vSuc v' => vSuc (apply_val s v')
    | vNat => vNat
    | vEmpty => vEmpty
    end
  with apply_ne (s : ssub) (n : neutral) : sval :=
    match n with
    | nVar k => nth_default (vNe (nVar k)) s k
    | nEmptyrec rA lA A scrut =>
        match apply_ne s scrut with
        | vNe scrut' => vNe (nEmptyrec rA lA (apply_val s A) scrut')
        | _ => vNe (nEmptyrec rA lA (apply_val s A) scrut)
        end
    end.

End Domain.

(* Mutual induction principle for the value domain. *)
Scheme svalty_rect := Induction for svalty Sort Type
  with sval_rect   := Induction for sval   Sort Type
  with neutral_rect := Induction for neutral Sort Type.
Combined Scheme sval_mutind from svalty_rect, sval_rect, neutral_rect.
