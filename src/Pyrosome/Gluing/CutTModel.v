Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

(* A *cut-free*, Type-valued model of a language [l], over the syntactic terms.

   Where TModel (Gluing/TModel.v) mirrors the full Model — including the
   substitution/cut law and monotonicity — a [CutTModel] mirrors instead the
   cut-free judgment of Theory/ConvElim.v: its operations are exactly the
   constructors of that system (and of TreeProofs.pf / TreeProofs.check_proof):
   congruence, axiom instances, variables, transitivity, symmetry, conversion —
   with NO primitive substitution rule (substitution is baked into rule
   instances).  Consequences:

   - a generic evaluation [pf -> ceq_term G] is a direct fold over [pf] (it is
     [TreeProofs.pf_checker_sound] generalized to an arbitrary target G);
   - to build a model (e.g. the gluing/normalization model) one only provides
     these finitely-many operations, never a substitution-stability law.

   Carriers are the syntactic [term]/[sort] (the operations mention [con]/[var]/
   [scon] and rule membership in [l]); the model's content lives in the Type-valued
   judgments [ceq_sort]/[ceq_term] (e.g. attaching a normal form). *)
Section WithVar.
  Context {V : Type}
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation scon := (@scon V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Section WithLang.
    Context (l : lang).
    (* The ambient context is CONSTANT across a model (mirroring TreeProofs, where
       [check_proof]'s context never changes during the cut-free fold), so we fix
       it here rather than threading it through every judgment.  [ceq_sort]/
       [ceq_term] drop their context argument; only [cterm_var] still refers to
       [c] (a variable is well-formed against the ambient context). *)
    Context (c : ctx).

    Class CutTModel :=
      {
        ceq_sort : sort -> sort -> Type;
        ceq_term : sort -> term -> term -> Type;
      }.

    Section WithCM.
      Context {CM : CutTModel}.

      (* Argument equality, built pointwise from [ceq_term] exactly as
         TreeProofs.check_args_proof checks an argument list (each argument at the
         rule-context type substituted by the preceding right-hand values).  The
         index is the rule's context [c']; the ambient [c] is the fixed one above. *)
      Inductive ceq_args : ctx -> list term -> list term -> Type :=
      | ceq_args_nil : ceq_args [] [] []
      | ceq_args_cons : forall c' es1 es2,
          ceq_args c' es1 es2 ->
          forall name t e1 e2,
            ceq_term t[/with_names_from c' es2/] e1 e2 ->
            ceq_args ((name,t)::c') (e1::es1) (e2::es2).

      (* The cut-free operations.  Each lines up with a [check_proof] /
         [check_sort_proof] case (TreeProofs.v:169-228). *)
      Class CutTModel_ok :=
        {
          (* pvar *)
          cterm_var : forall n t,
            In (n, t) c -> ceq_term t (var n) (var n);
          (* pcon, term_rule: congruence *)
          cterm_cong : forall c' name args t s1 s2,
            In (name, term_rule c' args t) l ->
            ceq_args c' s1 s2 ->
            ceq_term t[/with_names_from c' s2/] (con name s1) (con name s2);
          (* pcon, term_eq_rule: axiom instance *)
          cterm_by : forall c' name e1 e2 t s1 s2,
            In (name, term_eq_rule c' e1 e2 t) l ->
            ceq_args c' s1 s2 ->
            ceq_term t[/with_names_from c' s2/]
                     e1[/with_names_from c' s1/] e2[/with_names_from c' s2/];
          (* ptrans *)
          cterm_trans : forall t e1 e12 e2,
            ceq_term t e1 e12 -> ceq_term t e12 e2 -> ceq_term t e1 e2;
          (* psym *)
          cterm_sym : forall t e1 e2,
            ceq_term t e1 e2 -> ceq_term t e2 e1;
          (* pconv *)
          cterm_conv : forall t1 t2 e1 e2,
            ceq_sort t1 t2 -> ceq_term t1 e1 e2 -> ceq_term t2 e1 e2;

          (* sort versions (check_sort_proof) *)
          csort_cong : forall c' name args s1 s2,
            In (name, sort_rule c' args) l ->
            ceq_args c' s1 s2 ->
            ceq_sort (scon name s1) (scon name s2);
          csort_by : forall c' name t1 t2 s1 s2,
            In (name, sort_eq_rule c' t1 t2) l ->
            ceq_args c' s1 s2 ->
            ceq_sort t1[/with_names_from c' s1/] t2[/with_names_from c' s2/];
          csort_trans : forall t1 t12 t2,
            ceq_sort t1 t12 -> ceq_sort t12 t2 -> ceq_sort t1 t2;
          csort_sym : forall t1 t2,
            ceq_sort t1 t2 -> ceq_sort t2 t1;
        }.

    End WithCM.

  End WithLang.

End WithVar.
