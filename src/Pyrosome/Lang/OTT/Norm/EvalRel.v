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

(* TYPED relational evaluator for the cast-free OTT NbE model (first-order
   fragment: substitution calculus + U/El + Nat/Empty).

   Unlike a bare big-step evaluator, each judgment is INDEXED by the semantic
   typing data, so that a derivation simultaneously witnesses evaluation AND
   well-formedness of the result ("preservation is by construction"):

     eval_env :                 term -> senv          -> Type
        a context denotes its variables' types [Ge : senv]
     eval_ty  : senv         -> term -> svalty        -> Type
        in semantic context [Ge], a type-term denotes a semantic type [T]
     eval_rel : senv -> term -> svalty -> sval        -> Type
        in [Ge], a term of (semantic) type [T] denotes a value [v]
     eval_sub : senv -> senv -> term -> ssub          -> Type
        a [sub] term denotes a semantic substitution [sg] from the input
        (domain) [senv] to the output (codomain) [senv]

   Values are still the ENVIRONMENT-FREE/absolute domain of [Domain.v]: a
   neutral [nVar k] is the de Bruijn index [k]; an explicit substitution
   [exp_subst g e] is realised by [apply]ing [eval_sub g] to [eval_rel e].
   The senv/svalty indices simply record the types those absolute indices
   carry, exactly as in [Typing.v]'s [has_svalty]/[wf_ssub].

   Convention for [eval_sub Gin Gout g sg]: [Gin] is the DOMAIN env (one entry
   per variable that [sg] substitutes; [length sg = length Gin]) and [Gout] is
   the CODOMAIN env (the values in [sg] live there).  This matches
   [wf_ssub Gout sg Gin]. *)
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
     value annotations ([dU], [nEmptyrec]) are normalized. *)
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

  Inductive eval_env : term -> senv -> Type :=
  | ev_env_emp : eval_env (con "emp" []) []
  | ev_env_ext : forall A i G Genv S,
      eval_env G Genv -> eval_ty Genv A S ->
      eval_env (con "ext" [A; i; G]) (shift_ty 1 S :: map (shift_ty 1) Genv)

  with eval_ty : senv -> term -> svalty -> Type :=
  | ev_U : forall Ge l r G,
      eval_env G Ge ->
      eval_ty Ge (con "U" [l; r; G]) (dU (nf_info r) (nf_info l))
  | ev_El : forall Ge e l r G ve,
      eval_env G Ge ->
      eval_rel Ge e (dU (nf_info r) (nf_info l)) ve ->
      eval_ty Ge (con "El" [e; l; r; G]) (dEl ve)
  | ev_ty_subst : forall GeD GeC A i g G' G sg T,
      eval_sub GeD GeC g sg -> eval_ty GeD A T ->
      eval_ty GeC (con "ty_subst" [A; i; g; G'; G]) (apply_ty sg T)

  with eval_rel : senv -> term -> svalty -> sval -> Type :=
  | ev_hd : forall A i G Ge S,
      eval_env G Ge -> eval_ty Ge A S ->
      eval_rel (shift_ty 1 S :: map (shift_ty 1) Ge) (con "hd" [A; i; G])
               (shift_ty 1 S) (vNe (nVar 0))
  | ev_exp_subst : forall e A i g G' G GeD GeC sg ve T,
      eval_sub GeD GeC g sg -> eval_rel GeD e T ve ->
      eval_rel GeC (con "exp_subst" [e; A; i; g; G'; G])
               (apply_ty sg T) (apply_val sg ve)
  | ev_zero : forall G Ge,
      eval_env G Ge -> eval_rel Ge (con "zero" [G]) (dEl vNat) vZero
  | ev_suc  : forall n G Ge vn,
      eval_rel Ge n (dEl vNat) vn ->
      eval_rel Ge (con "suc" [n; G]) (dEl vNat) (vSuc vn)
  | ev_Nat  : forall G Ge,
      eval_env G Ge ->
      eval_rel Ge (con "Nat" [G])
               (dU (nf_info (con "rel" [])) (nf_info (con "L0" []))) vNat
  | ev_Empty : forall G Ge,
      eval_env G Ge ->
      eval_rel Ge (con "Empty" [G])
               (dU (nf_info (con "irr" [])) (nf_info (con "L0" []))) vEmpty
  | ev_Emptyrec : forall e A lA rA G Ge ne vA,
      eval_rel Ge e (dEl vEmpty) (vNe ne) ->
      eval_rel Ge A (dU (nf_info rA) (nf_info lA)) vA ->
      eval_rel Ge (con "Emptyrec" [e; A; lA; rA; G])
               (dEl vA) (vNe (nEmptyrec (nf_info rA) (nf_info lA) vA ne))

  with eval_sub : senv -> senv -> term -> ssub -> Type :=
  | ev_id   : forall G Ge,
      eval_env G Ge -> eval_sub Ge Ge (con "id" [G]) (id_list (length Ge))
  | ev_wkn  : forall A i G Ge S,
      eval_env G Ge -> eval_ty Ge A S ->
      eval_sub Ge (shift_ty 1 S :: map (shift_ty 1) Ge) (con "wkn" [A; i; G])
               (wkn_list (length Ge))
  | ev_forget : forall G Ge,
      eval_env G Ge -> eval_sub [] Ge (con "forget" [G]) []
  | ev_cmp  : forall g f G3 G2 G1 Ge1 Ge2 Ge3 sf sg,
      eval_sub Ge2 Ge1 f sf -> eval_sub Ge3 Ge2 g sg ->
      eval_sub Ge3 Ge1 (con "cmp" [g; f; G3; G2; G1]) (map (apply_val sf) sg)
  | ev_snoc : forall v g A i G' G GeD GeC sg vv S,
      eval_sub GeD GeC g sg -> eval_ty GeD A S ->
      eval_rel GeC v (apply_ty sg S) vv ->
      eval_sub (shift_ty 1 S :: map (shift_ty 1) GeD) GeC
               (con "snoc" [v; g; A; i; G'; G]) (vv :: sg).

End EvalRel.

(* Mutual induction principle for the four typed eval judgments.  [Combined
   Scheme] only supports Prop, so we pair the four Type-valued eliminators by
   hand (they share the same motives + 17-constructor method telescope). *)
Scheme eval_env_mind := Induction for eval_env Sort Type
  with eval_ty_mind  := Induction for eval_ty  Sort Type
  with eval_rel_mind := Induction for eval_rel Sort Type
  with eval_sub_mind := Induction for eval_sub Sort Type.

Definition eval_mutind
  (P0 : forall G Ge, eval_env G Ge -> Type)
  (P1 : forall Ge A T, eval_ty Ge A T -> Type)
  (P2 : forall Ge e T v, eval_rel Ge e T v -> Type)
  (P3 : forall Gin Gout g sg, eval_sub Gin Gout g sg -> Type)
  := fun f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero f_suc f_Nat f_Empty
         f_Emptyrec f_id f_wkn f_forget f_cmp f_snoc =>
  ( @eval_env_mind P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_id f_wkn f_forget f_cmp f_snoc
  , @eval_ty_mind  P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_id f_wkn f_forget f_cmp f_snoc
  , @eval_rel_mind P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_id f_wkn f_forget f_cmp f_snoc
  , @eval_sub_mind P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_id f_wkn f_forget f_cmp f_snoc ).
