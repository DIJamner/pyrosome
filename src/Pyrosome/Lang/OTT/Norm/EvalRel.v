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

(* ENVIRONMENT-FREE relational evaluator for the cast-free OTT NbE model (first-order
   fragment: substitution calculus + U/El + Nat/Empty).

     eval_sub  : term -> ssub   -> Type   (a [sub] term denotes a semantic subst)
     eval_ty   : term -> svalty -> Type
     eval_rel  : term -> sval   -> Type
     eval_env  : term -> senv   -> Type   (a context denotes its variables' types)

   There is NO ambient substitution argument: a variable [hd] reflects straight to
   [vNe (nVar 0)], and an explicit substitution [exp_subst g e] is realised by
   [apply (eval_sub g) (eval_rel e)].  [id]/[wkn] denote the identity/shift over a
   context of [ctx_len] variables; [snoc] conses; [cmp] composes by [apply].  This is
   what makes substitution-congruence hold (values are absolute).  There are NO
   Pyrosome metavariables, hence no [var] cases.  Totality on well-typed terms comes
   from the generic pf-eval, not from these relations. *)
Section EvalRel.
  Notation term := (@term string).

  (* Number of [ext]s in a context telescope (its variable count). *)
  Fixpoint ctx_len (G : term) : nat :=
    match G with
    | con n args =>
        if eqb n "ext"
        then match args with _ :: _ :: G' :: nil => S (ctx_len G') | _ => 0 end
        else 0
    | var _ => 0
    end.

  (* The identity / weakening substitutions over an [n]-variable context. *)
  Definition id_list  (n : nat) : ssub := map (fun k => vNe (nVar k)) (seq 0 n).
  Definition wkn_list (n : nat) : ssub := map (fun k => vNe (nVar (S k))) (seq 0 n).

  (* Normal form of the static info fragment (relevance/lvl/tlvl/tyinfo): the only
     computation is next0/next1 ([next L0 = iota L1], [next L1 = inf]).  Used so that
     value annotations ([dU], [nEmptyrec]) are normalized, making the congruences for
     U/Nat/Empty/Emptyrec go through (the info-soundness fix, now in the value world).
     Inner [let fix] over the arg list per the [term] recursion idiom. *)
  Fixpoint nf_info (e : term) : term :=
    match e with
    | var x => var x
    | con n args =>
        let args' :=
          (fix nf_list (l : list term) : list term :=
             match l with
             | [] => []
             | x :: xs => nf_info x :: nf_list xs
             end) args in
        if eqb n "next"
        then match args' with
             | [l'] =>
                 match l' with
                 | con m [] =>
                     if eqb m "L0" then con "iota" [con "L1" []]
                     else if eqb m "L1" then con "inf" []
                     else con "next" [l']
                 | _ => con "next" [l']
                 end
             | _ => con n args'
             end
        else con n args'
    end.

  Inductive eval_sub : term -> ssub -> Type :=
  | ev_id   : forall G, eval_sub (con "id" [G]) (id_list (ctx_len G))
  | ev_wkn  : forall A i G, eval_sub (con "wkn" [A; i; G]) (wkn_list (ctx_len G))
  | ev_forget : forall G, eval_sub (con "forget" [G]) []
  | ev_cmp  : forall g f G1 G2 G3 sf sg,
      eval_sub f sf -> eval_sub g sg ->
      eval_sub (con "cmp" [g; f; G3; G2; G1]) (map (apply_val sf) sg)
  | ev_snoc : forall v g A i G' G sg vv,
      eval_sub g sg -> eval_rel v vv ->
      eval_sub (con "snoc" [v; g; A; i; G'; G]) (vv :: sg)

  with eval_ty : term -> svalty -> Type :=
  | ev_U    : forall l r G, eval_ty (con "U" [l; r; G]) (dU (nf_info r) (nf_info l))
  | ev_El_code : forall e l r G T,
      eval_rel e (vCode T) -> eval_ty (con "El" [e; l; r; G]) T
  | ev_El_ne : forall e l r G n,
      eval_rel e (vNe n) -> eval_ty (con "El" [e; l; r; G]) (dNe n)
  | ev_ty_subst : forall A i g G' G sg T,
      eval_sub g sg -> eval_ty A T ->
      eval_ty (con "ty_subst" [A; i; g; G'; G]) (apply_ty sg T)

  with eval_rel : term -> sval -> Type :=
  | ev_hd   : forall A i G, eval_rel (con "hd" [A; i; G]) (vNe (nVar 0))
  | ev_exp_subst : forall e A i g G' G sg ve,
      eval_sub g sg -> eval_rel e ve ->
      eval_rel (con "exp_subst" [e; A; i; g; G'; G]) (apply_val sg ve)
  | ev_zero : forall G, eval_rel (con "zero" [G]) vZero
  | ev_suc  : forall n G vn,
      eval_rel n vn -> eval_rel (con "suc" [n; G]) (vSuc vn)
  | ev_Nat  : forall G, eval_rel (con "Nat" [G]) (vCode dNat)
  | ev_Empty : forall G, eval_rel (con "Empty" [G]) (vCode dEmpty)
  | ev_Emptyrec : forall e A lA rA G ne vA,
      eval_rel e (vNe ne) -> eval_rel A vA ->
      eval_rel (con "Emptyrec" [e; A; lA; rA; G])
               (vNe (nEmptyrec (nf_info rA) (nf_info lA) vA ne)).

  (* Environment normalization: a context's list of (semantic) variable types.  Each
     [ext]'s annotation evaluates env-free; extending shifts the carried types up by
     one (index 0 becomes the new variable).  Only base is [emp] (no metavariables). *)
  Inductive eval_env : term -> senv -> Type :=
  | ev_env_emp : eval_env (con "emp" []) []
  | ev_env_ext : forall A i G Genv S,
      eval_env G Genv -> eval_ty A S ->
      eval_env (con "ext" [A; i; G]) (shift_ty 1 S :: map (shift_ty 1) Genv).

End EvalRel.
