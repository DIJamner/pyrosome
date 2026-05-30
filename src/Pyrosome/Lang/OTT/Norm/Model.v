Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Gluing Require Import CutTModel.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel.
From Pyrosome.Lang.OTT Require Import Base Nat.
Import Core.Notations.

(* The normalization (gluing) model as a cut-free Type-valued model over the
   first-order cast-free OTT language, on the ENVIRONMENT-FREE evaluator.

   The model relation has TWO components (a product):
   - the Core judgmental equality [eq_term fo_lang [] t e1 e2] (resp. [eq_sort]).
     This is the *well-formedness* gate the user identified as the missing
     structure: the relation only accepts inputs that are well formed AT THE
     SORT [t] (eq_term .. t entails wf_term .. t), and it is what every law
     discharges via the corresponding Core lemma (this part is exactly the
     SyntacticModel CutTModel_ok).
   - the eval GLUE: the two terms evaluate to the SAME semantic value/type/
     substitution/environment.  Because evaluation is environment-free the glue
     does NOT depend on the sort's arguments (no ambient context to thread), so
     it dispatches purely on the sort head; the static info sorts
     (relevance/lvl/tlvl/tyinfo) are compared by [nf_info], and proof-irrelevant
     sorts (ltl) are [unit].

   The well-formedness component supplies, for the Tier-C eliminator/composition
   cases, the typing/scope facts the eval glue needs (canonical forms, lengths)
   which are FALSE for the ill-typed junk that an unguarded relation would admit. *)

Definition fo_lang : lang string := ott_nat ++ ott_base ++ subst_ott ++ ott_info.

Section Model.
  Notation term := (@term string).
  Notation sort := (@sort string).
  Notation ctx := (@ctx string).

  Definition sort_head (S : sort) : string := match S with scon n _ => n end.

  (* The eval glue: two terms glue iff they evaluate (in the semantic context
     denoted by the sort's context argument, at the semantic type denoted by the
     sort's type argument) to the SAME semantic value.  With the TYPED evaluator
     (EvalRel.v) the glue threads those indices out of the sort:
       - [exp A i G] : in [Ge = eval G], at [T = eval A], both reach value [v];
       - [ty i G]    : in [Ge], both reach svalty [T];
       - [sub G' G]  : from [eval G'] to [eval G], both reach [sg];
       - [env]       : both reach [Ge]. *)
  (* Inductive presentation, with one constructor per MEANINGFUL sort head.
     The degenerate [unit] catch-alls of the old [match] (wrong-arity inputs and
     unknown heads) are dropped: glue is always paired with [eq_term fo_lang [] t]
     in [norm_ceq_term], whose well-formedness gate rules those junk inputs out.
     The proof-irrelevant [ltl] sort keeps its own trivial constructor. *)
  Inductive glue_term : sort -> term -> term -> Type :=
  | glue_exp : forall (A i G e1 e2 : term) (Ge : senv) (T : svalty) (v : sval),
      eval_env G Ge -> eval_ty Ge A T ->
      eval_rel Ge e1 T v -> eval_rel Ge e2 T v ->
      glue_term (scon "exp" [A; i; G]) e1 e2
  | glue_ty : forall (i G e1 e2 : term) (Ge : senv) (T : svalty),
      eval_env G Ge -> eval_ty Ge e1 T -> eval_ty Ge e2 T ->
      glue_term (scon "ty" [i; G]) e1 e2
  | glue_sub : forall (Gd Gc e1 e2 : term) (GeD GeC : senv) (s : ssub),
      eval_env Gd GeD -> eval_env Gc GeC ->
      eval_sub GeD GeC e1 s -> eval_sub GeD GeC e2 s ->
      glue_term (scon "sub" [Gd; Gc]) e1 e2
  | glue_env : forall (e1 e2 : term) (Genv : senv),
      eval_env e1 Genv -> eval_env e2 Genv ->
      glue_term (scon "env" []) e1 e2
  (* static-info sorts: compared by [nf_info], one constructor each *)
  | glue_relevance : forall (e1 e2 : term),
      nf_info e1 = nf_info e2 -> glue_term (scon "relevance" []) e1 e2
  | glue_lvl : forall (e1 e2 : term),
      nf_info e1 = nf_info e2 -> glue_term (scon "lvl" []) e1 e2
  | glue_tlvl : forall (e1 e2 : term),
      nf_info e1 = nf_info e2 -> glue_term (scon "tlvl" []) e1 e2
  | glue_tyinfo : forall (e1 e2 : term),
      nf_info e1 = nf_info e2 -> glue_term (scon "tyinfo" []) e1 e2
  | glue_ltl : forall (a b e1 e2 : term),  (* ltl: proof-irrelevant *)
      glue_term (scon "ltl" [a; b]) e1 e2.

  (* norm_ceq_term relates only WELL-FORMED terms at the sort [t] (the eq_term
     component), additionally gluing them to a common semantic value. *)
  Definition norm_ceq_term (t : sort) (e1 e2 : term) : Type :=
    (eq_term fo_lang [] t e1 e2 * glue_term t e1 e2)%type.

  (* Glue for sorts, inductive presentation mirroring [glue_term]: one
     constructor per MEANINGFUL sort head, each requiring [glue_term] on the
     sort's subterms (at the sort each subterm inhabits).  A dependent subterm
     (the type [A] of an [exp]) is glued at the [ty] sort built from the LEFT
     sort's index/context args [i1; G1]; this is coherent with the right side's
     [i2; G2] because the index subterms themselves glue (and [glue_ty] only
     reads the context's evaluated env, which is shared across glued envs). *)
  Inductive glue_sort : sort -> sort -> Type :=
  | glue_sort_exp : forall (A1 A2 i1 i2 G1 G2 : term),
      glue_term (scon "ty" [i1; G1]) A1 A2 ->
      glue_term (scon "tyinfo" []) i1 i2 ->
      glue_term (scon "env" []) G1 G2 ->
      glue_sort (scon "exp" [A1; i1; G1]) (scon "exp" [A2; i2; G2])
  | glue_sort_ty : forall (i1 i2 G1 G2 : term),
      glue_term (scon "tyinfo" []) i1 i2 ->
      glue_term (scon "env" []) G1 G2 ->
      glue_sort (scon "ty" [i1; G1]) (scon "ty" [i2; G2])
  | glue_sort_sub : forall (Gd1 Gd2 Gc1 Gc2 : term),
      glue_term (scon "env" []) Gd1 Gd2 ->
      glue_term (scon "env" []) Gc1 Gc2 ->
      glue_sort (scon "sub" [Gd1; Gc1]) (scon "sub" [Gd2; Gc2])
  | glue_sort_env :
      glue_sort (scon "env" []) (scon "env" [])
  | glue_sort_relevance :
      glue_sort (scon "relevance" []) (scon "relevance" [])
  | glue_sort_lvl :
      glue_sort (scon "lvl" []) (scon "lvl" [])
  | glue_sort_tlvl :
      glue_sort (scon "tlvl" []) (scon "tlvl" [])
  | glue_sort_tyinfo :
      glue_sort (scon "tyinfo" []) (scon "tyinfo" [])
  | glue_sort_ltl : forall (a1 a2 b1 b2 : term),
      glue_term (scon "lvl" []) a1 a2 ->
      glue_term (scon "lvl" []) b1 b2 ->
      glue_sort (scon "ltl" [a1; b1]) (scon "ltl" [a2; b2]).

  Definition norm_ceq_sort (S1 S2 : sort) : Type :=
    (eq_sort fo_lang [] S1 S2 * glue_sort S1 S2)%type.

  Definition Norm : CutTModel :=
    {|
      ceq_sort := norm_ceq_sort;
      ceq_term := norm_ceq_term;
    |}.

End Model.
