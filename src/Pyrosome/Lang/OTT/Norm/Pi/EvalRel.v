Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Domain Apply Reflect.
Import Core.Notations.

(* ===================================================================== *)
(* TYPED relational evaluator for the Pi-extended cast-free OTT NbE model. *)
(*                                                                        *)
(* Same shape as the first-order [OTT/Norm/EvalRel.v] (four mutual        *)
(* judgments indexed by the semantic typing data, so a derivation         *)
(* simultaneously witnesses evaluation AND well-formedness of the result) *)
(* but rebuilt over the RELATIONAL [Apply]/[Vapp]/[Reflect] of [Apply.v]/ *)
(* [Reflect.v], since with binders substitution is hereditary and the     *)
(* variable rule [ev_hd] reflects eta-long.                               *)
(*                                                                        *)
(* New since the first-order version:                                     *)
(*   - [ev_hd] reflects [nVar 0] at the variable's type ([Reflect]), so a *)
(*     variable of relevant function type is returned eta-expanded;       *)
(*   - substitution constructors ([ev_ty_subst]/[ev_exp_subst]/[ev_cmp]/  *)
(*     [ev_snoc]) thread relational [Apply_*] instead of the old apply     *)
(*     functions;                                                         *)
(*   - the Pi fragment: [ev_Pi]/[ev_PiI] (codes), [ev_lam]/[ev_lamI]      *)
(*     (lambdas), [ev_app]/[ev_appI] (application via [Vapp], result type  *)
(*     [B[a]] via [Apply_val]). *)
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

  (* Normal form of the static info fragment (relevance/lvl/tlvl/tyinfo). *)
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

  (* Pointwise relational substitution over a list (for [ev_cmp]). *)
  Inductive Apply_list (m : nat) (sf : ssub) : ssub -> ssub -> Type :=
  | al_nil  : Apply_list m sf [] []
  | al_cons : forall v v' vs vs',
      Apply_val m sf v v' -> Apply_list m sf vs vs' ->
      Apply_list m sf (v :: vs) (v' :: vs').

  Inductive eval_env : term -> senv -> Type :=
  | ev_env_emp : eval_env (con "emp" []) []
  | ev_env_ext : forall A i G Genv S,
      eval_env G Genv -> eval_ty Genv A S ->
      eval_env (con "ext" [A; i; G]) (shift_ty 0 1 S :: map (shift_ty 0 1) Genv)

  with eval_ty : senv -> term -> svalty -> Type :=
  | ev_U : forall Ge l r G,
      eval_env G Ge ->
      eval_ty Ge (con "U" [l; r; G]) (dU (nf_info r) (nf_info l))
  | ev_El : forall Ge e l r G ve,
      eval_env G Ge ->
      eval_rel Ge e (dU (nf_info r) (nf_info l)) ve ->
      eval_ty Ge (con "El" [e; l; r; G]) (dEl ve)
  | ev_ty_subst : forall GeD GeC A i g G' G sg T T',
      eval_sub GeD GeC g sg -> eval_ty GeD A T ->
      Apply_ty (length GeC) sg T T' ->
      eval_ty GeC (con "ty_subst" [A; i; g; G'; G]) T'

  with eval_rel : senv -> term -> svalty -> sval -> Type :=
  | ev_hd : forall A i G Ge Sty v,
      eval_env G Ge -> eval_ty Ge A Sty ->
      Reflect (S (length Ge)) (shift_ty 0 1 Sty) (nVar 0) v ->
      eval_rel (shift_ty 0 1 Sty :: map (shift_ty 0 1) Ge) (con "hd" [A; i; G])
               (shift_ty 0 1 Sty) v
  | ev_exp_subst : forall e A i g G' G GeD GeC sg ve T T' v,
      eval_sub GeD GeC g sg -> eval_rel GeD e T ve ->
      Apply_ty (length GeC) sg T T' -> Apply_val (length GeC) sg ve v ->
      eval_rel GeC (con "exp_subst" [e; A; i; g; G'; G]) T' v
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
  | ev_Pi : forall G Ge rF lF lG F B vF vB,
      eval_env G Ge ->
      eval_rel Ge F (dU (nf_info rF) (nf_info lF)) vF ->
      eval_rel (dEl (shift_val 0 1 vF) :: map (shift_ty 0 1) Ge) B
               (dU (nf_info (con "rel" [])) (nf_info lG)) vB ->
      eval_rel Ge (con "Pi_rel" [B; F; lG; lF; rF; G])
               (dU (nf_info (con "rel" [])) (nf_info lG)) (vPi vF vB)
  | ev_PiI : forall G Ge rF lF F B vF vB,
      eval_env G Ge ->
      eval_rel Ge F (dU (nf_info rF) (nf_info lF)) vF ->
      eval_rel (dEl (shift_val 0 1 vF) :: map (shift_ty 0 1) Ge) B
               (dU (nf_info (con "irr" [])) (nf_info (con "L0" []))) vB ->
      eval_rel Ge (con "Pi_irr" [B; F; lF; rF; G])
               (dU (nf_info (con "irr" [])) (nf_info (con "L0" []))) (vPiI vF vB)
  | ev_lam : forall G Ge rF lF lG F B t vF vB vt,
      eval_env G Ge ->
      eval_rel Ge F (dU (nf_info rF) (nf_info lF)) vF ->
      eval_rel (dEl (shift_val 0 1 vF) :: map (shift_ty 0 1) Ge) B
               (dU (nf_info (con "rel" [])) (nf_info lG)) vB ->
      eval_rel (dEl (shift_val 0 1 vF) :: map (shift_ty 0 1) Ge) t (dEl vB) vt ->
      eval_rel Ge (con "lam_rel" [t; B; F; lG; lF; rF; G])
               (dEl (vPi vF vB)) (vLam vt)
  | ev_lamI : forall G Ge rF lF F B t vF vB vt,
      eval_env G Ge ->
      eval_rel Ge F (dU (nf_info rF) (nf_info lF)) vF ->
      eval_rel (dEl (shift_val 0 1 vF) :: map (shift_ty 0 1) Ge) B
               (dU (nf_info (con "irr" [])) (nf_info (con "L0" []))) vB ->
      eval_rel (dEl (shift_val 0 1 vF) :: map (shift_ty 0 1) Ge) t (dEl vB) vt ->
      eval_rel Ge (con "lam_irr" [t; B; F; lF; rF; G])
               (dEl (vPiI vF vB)) (vLamI vt)
  | ev_app : forall G Ge rF lF lG F B f a vF vB vf va v vBa,
      eval_env G Ge ->
      eval_rel Ge f (dEl (vPi vF vB)) vf ->
      eval_rel Ge a (dEl vF) va ->
      Vapp (length Ge) vF vB vf va v ->
      Apply_val (length Ge) (va :: id_list (length Ge)) vB vBa ->
      eval_rel Ge (con "app_rel" [a; f; B; F; lG; lF; rF; G]) (dEl vBa) v
  | ev_appI : forall G Ge rF lF F B f a vF vB vf va v vBa,
      eval_env G Ge ->
      eval_rel Ge f (dEl (vPiI vF vB)) vf ->
      eval_rel Ge a (dEl vF) va ->
      VappI (length Ge) vF vB vf va v ->
      Apply_val (length Ge) (va :: id_list (length Ge)) vB vBa ->
      eval_rel Ge (con "app_irr" [a; f; B; F; lF; rF; G]) (dEl vBa) v

  with eval_sub : senv -> senv -> term -> ssub -> Type :=
  | ev_id   : forall G Ge,
      eval_env G Ge -> eval_sub Ge Ge (con "id" [G]) (id_list (length Ge))
  | ev_wkn  : forall A i G Ge S,
      eval_env G Ge -> eval_ty Ge A S ->
      eval_sub Ge (shift_ty 0 1 S :: map (shift_ty 0 1) Ge) (con "wkn" [A; i; G])
               (wkn_list (length Ge))
  | ev_forget : forall G Ge,
      eval_env G Ge -> eval_sub [] Ge (con "forget" [G]) []
  | ev_cmp  : forall g f G3 G2 G1 Ge1 Ge2 Ge3 sf sg sfg,
      eval_sub Ge2 Ge1 f sf -> eval_sub Ge3 Ge2 g sg ->
      Apply_list (length Ge1) sf sg sfg ->
      eval_sub Ge3 Ge1 (con "cmp" [g; f; G3; G2; G1]) sfg
  | ev_snoc : forall v g A i G' G GeD GeC sg vv S St,
      eval_sub GeD GeC g sg -> eval_ty GeD A S ->
      Apply_ty (length GeC) sg S St ->
      eval_rel GeC v St vv ->
      eval_sub (shift_ty 0 1 S :: map (shift_ty 0 1) GeD) GeC
               (con "snoc" [v; g; A; i; G'; G]) (vv :: sg).

End EvalRel.

(* Mutual induction principle for the four typed eval judgments (paired by
   hand; [Combined Scheme] supports only [Prop]). *)
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
         f_Emptyrec f_Pi f_PiI f_lam f_lamI f_app f_appI f_id f_wkn f_forget
         f_cmp f_snoc =>
  ( @eval_env_mind P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_Pi f_PiI f_lam f_lamI f_app f_appI f_id
      f_wkn f_forget f_cmp f_snoc
  , @eval_ty_mind  P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_Pi f_PiI f_lam f_lamI f_app f_appI f_id
      f_wkn f_forget f_cmp f_snoc
  , @eval_rel_mind P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_Pi f_PiI f_lam f_lamI f_app f_appI f_id
      f_wkn f_forget f_cmp f_snoc
  , @eval_sub_mind P0 P1 P2 P3 f_emp f_ext f_U f_El f_tysub f_hd f_expsub f_zero
      f_suc f_Nat f_Empty f_Emptyrec f_Pi f_PiI f_lam f_lamI f_app f_appI f_id
      f_wkn f_forget f_cmp f_snoc ).
