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
  | glue_info : forall (n : string) (e1 e2 : term),
      n <> "exp" -> n <> "ty" -> n <> "sub" -> n <> "env" ->
      nf_info e1 = nf_info e2 ->            (* relevance/lvl/tlvl/tyinfo *)
      glue_term (scon n []) e1 e2
  | glue_ltl : forall (a b e1 e2 : term),  (* ltl: proof-irrelevant *)
      glue_term (scon "ltl" [a; b]) e1 e2.

  (* norm_ceq_term relates only WELL-FORMED terms at the sort [t] (the eq_term
     component), additionally gluing them to a common semantic value. *)
  Definition norm_ceq_term (t : sort) (e1 e2 : term) : Type :=
    (eq_term fo_lang [] t e1 e2 * glue_term t e1 e2)%type.

  (* Glue for sorts: same head and arity. *)
  Definition glue_sort (S1 S2 : sort) : Type :=
    match S1, S2 with
    | scon n1 a1, scon n2 a2 => ((eqb n1 n2 = true) * (length a1 = length a2))%type
    end.

  Definition norm_ceq_sort (S1 S2 : sort) : Type :=
    (eq_sort fo_lang [] S1 S2 * glue_sort S1 S2)%type.

  Definition Norm : CutTModel :=
    {|
      ceq_sort := norm_ceq_sort;
      ceq_term := norm_ceq_term;
    |}.

End Model.
