Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(* Normal/neutral forms for the cast-free OTT fragment, as a *boolean* predicate
   over the existing [term] type (representation decision 1: computable — pairs
   with [eqb] for decidability of conversion — and avoids the embedding machinery
   of a separate normal-form type/language).

   - [is_neutral e]: e is a variable / [hd] head under a spine of eliminators
     (app_rel / app_irr / fst / snd / Emptyrec) whose arguments are all normal.
   - [is_normal e]: e is neutral, or a canonical former (U / El / Nat / zero / suc
     / Empty / Pi_rel / Pi_irr / lam_rel / lam_irr / Sig / pair) with normal args.

   Eliminator arities are fixed (app_rel 8, app_irr 7, fst/snd 4, Emptyrec 5);
   canonical formers are handled by the inner [all_normal] so their arity is
   irrelevant.

   TODO (refinement, once the glue's reify is fixed): the explicit-substitution
   variable encoding ([hd] under weakening stacks via [exp_subst]/[wkn]) and the
   exclusion of σ-redexes are not yet characterized here. *)
Section OTT_Values.
  Notation term := (@term string).

  Fixpoint is_neutral (e : term) : bool :=
    match e with
    | var _ => true
    | con n args =>
        let fix all_normal (es : list term) : bool :=
          match es with
          | [] => true
          | e' :: es' => (is_normal e' && all_normal es')%bool
          end in
        if eqb n "hd" then true
        else if eqb n "app_rel"
             then match args with
                  | [_;_;_;_;_;_;f;_] => (is_neutral f && all_normal args)%bool
                  | _ => false end
        else if eqb n "app_irr"
             then match args with
                  | [_;_;_;_;_;f;_] => (is_neutral f && all_normal args)%bool
                  | _ => false end
        else if eqb n "fst"
             then match args with
                  | [_;_;_;e'] => (is_neutral e' && all_normal args)%bool
                  | _ => false end
        else if eqb n "snd"
             then match args with
                  | [_;_;_;e'] => (is_neutral e' && all_normal args)%bool
                  | _ => false end
        else if eqb n "Emptyrec"
             then match args with
                  | [_;_;_;_;e'] => (is_neutral e' && all_normal args)%bool
                  | _ => false end
        else false
    end
  with is_normal (e : term) : bool :=
    match e with
    | var _ => true
    | con n args =>
        let fix all_normal (es : list term) : bool :=
          match es with
          | [] => true
          | e' :: es' => (is_normal e' && all_normal es')%bool
          end in
        if eqb n "hd" then true
        else if eqb n "app_rel"
             then match args with
                  | [_;_;_;_;_;_;f;_] => (is_neutral f && all_normal args)%bool
                  | _ => false end
        else if eqb n "app_irr"
             then match args with
                  | [_;_;_;_;_;f;_] => (is_neutral f && all_normal args)%bool
                  | _ => false end
        else if eqb n "fst"
             then match args with
                  | [_;_;_;e'] => (is_neutral e' && all_normal args)%bool
                  | _ => false end
        else if eqb n "snd"
             then match args with
                  | [_;_;_;e'] => (is_neutral e' && all_normal args)%bool
                  | _ => false end
        else if eqb n "Emptyrec"
             then match args with
                  | [_;_;_;_;e'] => (is_neutral e' && all_normal args)%bool
                  | _ => false end
        else if (eqb n "U" || eqb n "El" || eqb n "Nat" || eqb n "zero"
                 || eqb n "suc" || eqb n "Empty" || eqb n "Pi_rel" || eqb n "Pi_irr"
                 || eqb n "lam_rel" || eqb n "lam_irr" || eqb n "Sig" || eqb n "pair")%bool
             then all_normal args
        else false
    end.

  (* External list version (non-mutual; [is_normal] is already defined). *)
  Fixpoint all_normal (es : list term) : bool :=
    match es with
    | [] => true
    | e :: es' => (is_normal e && all_normal es')%bool
    end.

  Definition normal (e : term) : Prop := Is_true (is_normal e).
  Definition neutral (e : term) : Prop := Is_true (is_neutral e).

End OTT_Values.
