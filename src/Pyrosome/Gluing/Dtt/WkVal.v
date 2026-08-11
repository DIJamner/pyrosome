Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.Wf
  Pyrosome.Gluing.Dtt.Eqns Pyrosome.Gluing.Dtt.NormalForms.
Import Core.Notations.

(* =====================================================================
   T3: FUNCTIONAL WEAKENING OF CODE VALUES -- THE REPRESENTATION EXPERIMENT.

   The question this file answers is design.md's: can the value layer's
   weakening be a FUNCTION on the ANNOTATED syntax, or do the annotations
   force the de Bruijn detour?

   ANSWER, in two halves.

   (+) FOR THE CANONICAL CODE GRAMMAR THE ANNOTATIONS LINE UP EXACTLY.
       [wkV] below is an ordinary [Fixpoint] on the code, with the
       weakening [w] as a varying (non-recursive) parameter; it is
       accepted, it computes the right thing, and [wkV_sound] --
       "[wkV] preserves [NfCode] and realizes [exp_subst w]" -- is proved
       here by the very induction NfWk.v's [Nf_wk_str] already runs, with
       [exists c'] replaced by the computed [wkV ... c].  The three
       equational lemmas it needs ([eq_El_wk], [eq_pi_rel_wk],
       [eq_pi_irr_wk], plus [Wk_liftC]) are the ones NfWk.v already
       proves, and they slot in WITHOUT ANY RESHAPING: [wkV]'s [F'] is
       literally [eq_pi_rel_wk]'s [F'], and [Wk_liftC] hands back the
       weakening at exactly [oExtC D rF lF F'], which is the context the
       recursive call is made in.  NOTHING about the annotations fights.

   (-) AT VARIABLES IT DOES NOT WORK, AND THE OBSTRUCTION IS PRECISELY THE
       TYPE ANNOTATION.  Under a LIFTED weakening the value of [x[w]] is
       not [exp_subst w x]: [hd] goes to [hd] and [exp_subst wkn y] to
       [exp_subst wkn (y[w'])].  So the variable case must recurse on the
       SHAPE OF [w].  The term that recursion builds carries a type
       annotation -- the type of the inner variable in the smaller
       context -- and that annotation is itself a weakened TYPE, so it has
       to be computed by [wkV].  A recursion on [w] calling a recursion on
       [c] calling a recursion on [w]: no single argument decreases, and
       the guard checker says so in as many words:

         Recursive call to wkVar has principal argument equal to
         "w" instead of a subterm of "c".

       The genuinely decreasing structure is the DERIVATION, which is what
       [Nf_wk_str] recurses on and what a [Prop]-valued value judgement
       cannot be eliminated into [term] over.

   So this file carries the NEUTRAL case as a HYPOTHESIS [wkne] +
   [wkne_sound] (a section [Context], not an axiom) and proves everything
   else.  Two remarks on that hypothesis, so it is not mistaken for a
   fudge:

     * on the VARIABLE half of [NeCode] it is exactly the [exists c']
       statement NfWk.v's [Nf_wk_str] discharges at [nfcode_var]
       (:1551-1558, via the 340-line [vart_hd_wk_gen]/[vart_wkn_wk_gen]),
       so a witness demonstrably exists -- what is missing is a Gallina
       FUNCTION realizing it, which is the whole of the open question;

     * on the STUCK-[Id] half ([necode_id_l/r], [necode_id_nat_l/r]) it is
       genuinely new: those clauses did not exist when NfWk.v was written,
       and weakening them needs the "Id subst" rule plus ELEMENT-level
       weakening (an [Id]'s endpoints are terms), i.e. the mutual
       recursion between code and element normalization that design.md
       section 14d calls the real structural cost of [Id].
   ===================================================================== *)

Local Notation wft := (wf_term ott_dtt []).
Local Notation eqt := (eq_term ott_dtt []).

(* The lifted weakening, verbatim from NfWk.v:141. *)
Definition oLiftW (D G w i A A' : term) : term :=
  oSnoc (oExt D i A') G i A (oCmp (oExt D i A') D G (oWkn D i A') w)
    (oHd D i A').

Section WithNeutrals.

  (* The one hole.  [wkne D G w r l c] is meant to be the value of [c[w]]
     for [c] a NEUTRAL code -- a variable, or a stuck [Id] ([NeCode_shape]).
     See the header for why it cannot be defined by
     structural recursion on the annotated syntax. *)
  Context (wkne : term -> term -> term -> term -> term -> term -> term).

  Context
    (wkne_sound :
       forall G r l c, NeCode G r l c ->
       forall D w, Wk D G w -> EnvOk D ->
         NfCode D r l (wkne D G w r l c)
         /\ eqt (sCode D r l)
              (oExpSubst D G w (iCode l) (oU G r l) c) (wkne D G w r l c)).

  (* The three weakening equations of NfWk.v, taken as hypotheses because
     NfWk.v itself does not currently compile (the Id fragment changed the
     arity of [Nf_mutind] and added the [NeCode] judgement, so everything
     from [Nf_wk_str] on is being rewritten).  Each statement below is
     COPIED VERBATIM from the corresponding [Lemma] in NfWk.v, which proves
     it: [eq_El_wk] at :896, [Wk_liftC] at :909, [eq_pi_rel_wk] at :995,
     [eq_pi_irr_wk] at :1023, [eq_Nat_subst'] at :590 (specialized), and
     [eq_Empty_subst] from Eqns.v (specialized). *)
  Context
    (eq_nat_wk :
       forall D G w, Wk D G w -> EnvOk D -> EnvOk G ->
         eqt (sCode D oRel oL0)
           (oExpSubst D G w (iCode oL0) (oU G oRel oL0) (oNat G)) (oNat D))
    (eq_empty_wk :
       forall D G w, Wk D G w -> EnvOk D -> EnvOk G ->
         eqt (sCode D oIrr oL0)
           (oExpSubst D G w (iCode oL0) (oU G oIrr oL0) (oEmpty G))
           (oEmpty D))
    (Wk_liftC :
       forall D G w rF lF F F',
         Wk D G w -> EnvOk D -> NfCode G rF lF F -> NfCode D rF lF F' ->
         eqt (sCode D rF lF) (oCodeSubst D G w rF lF F) F' ->
         Wk (oExtC D rF lF F') (oExtC G rF lF F)
           (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
         /\ EnvOk (oExtC D rF lF F')
         /\ eqt (sTy D (iEl rF lF))
              (oTySubst D G w (iEl rF lF) (oEl G rF lF F))
              (oEl D rF lF F'))
    (eq_pi_rel_wk :
       forall D G w rF lF lG F B F' B',
         Wk D G w -> EnvOk D ->
         NfCode G rF lF F -> NfCode (oExtC G rF lF F) oRel lG B ->
         NfCode D rF lF F' -> NfCode (oExtC D rF lF F') oRel lG B' ->
         eqt (sCode D rF lF)
           (oExpSubst D G w (iCode lF) (oU G rF lF) F) F' ->
         eqt (sCode (oExtC D rF lF F') oRel lG)
           (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
              (iCode lG) (oU (oExtC G rF lF F) oRel lG) B) B' ->
         eqt (sCode D oRel lG)
           (oExpSubst D G w (iCode lG) (oU G oRel lG) (oPiRel G rF lF lG F B))
           (oPiRel D rF lF lG F' B'))
    (eq_pi_irr_wk :
       forall D G w rF lF F B F' B',
         Wk D G w -> EnvOk D ->
         NfCode G rF lF F -> NfCode (oExtC G rF lF F) oIrr oL0 B ->
         NfCode D rF lF F' -> NfCode (oExtC D rF lF F') oIrr oL0 B' ->
         eqt (sCode D rF lF)
           (oExpSubst D G w (iCode lF) (oU G rF lF) F) F' ->
         eqt (sCode (oExtC D rF lF F') oIrr oL0)
           (oExpSubst (oExtC D rF lF F') (oExtC G rF lF F)
              (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
              (iCode oL0) (oU (oExtC G rF lF F) oIrr oL0) B) B' ->
         eqt (sCode D oIrr oL0)
           (oExpSubst D G w (iCode oL0) (oU G oIrr oL0) (oPiIrr G rF lF F B))
           (oPiIrr D rF lF F' B')).

(* ------------------------------------------------------------------ *)
(* The function                                                         *)
(* ------------------------------------------------------------------ *)

(* Matched on the ARGUMENT-LIST SHAPE first and only then on the head
   symbol (via [eqb], not a literal string pattern), the idiom of
   Syntax.v's [ntlvl]: it keeps the case analyses below to a fixed, small
   number of [destruct]s.  Note [oPiRel] has six arguments and so does
   [oExpSubst] and [oIdEq]; the [eqb] guard is what separates them, and
   everything it does not claim goes to [wkne].

   STRUCTURAL ON THE CODE, with [D]/[G]/[w] varying: at a binder the
   recursive call is made in the EXTENDED context with the LIFTED
   weakening, which is bigger than [w] -- fine, since only [c] is the
   recursive argument. *)
Fixpoint wkV (D G w r l c : term) {struct c} : term :=
  match c with
  | con nm [_] =>
      if eqb nm "Nat" then oNat D
      else if eqb nm "Empty" then oEmpty D
      else wkne D G w r l c
  | con nm [B; F; lG; lF; rF; _] =>
      if eqb nm "Pi_rel"
      then let F' := wkV D G w rF lF F in
           oPiRel D rF lF lG F'
             (wkV (oExtC D rF lF F') (oExtC G rF lF F)
                  (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                  oRel lG B)
      else wkne D G w r l c
  | con nm [B; F; lF; rF; _] =>
      if eqb nm "Pi_irr"
      then let F' := wkV D G w rF lF F in
           oPiIrr D rF lF F'
             (wkV (oExtC D rF lF F') (oExtC G rF lF F)
                  (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
                  oIrr oL0 B)
      else wkne D G w r l c
  | _ => wkne D G w r l c
  end.

(* The four computation rules, as equations.  Each is [reflexivity]: the
   [eqb] guards reduce, and the annotations the recursive calls are made
   at are exactly the ones the judgements demand. *)

Lemma wkV_nat D G w r l : wkV D G w r l (oNat G) = oNat D.
Proof. reflexivity. Qed.

Lemma wkV_empty D G w r l : wkV D G w r l (oEmpty G) = oEmpty D.
Proof. reflexivity. Qed.

Lemma wkV_pi_rel D G w r l rF lF lG F B
  : wkV D G w r l (oPiRel G rF lF lG F B)
    = let F' := wkV D G w rF lF F in
      oPiRel D rF lF lG F'
        (wkV (oExtC D rF lF F') (oExtC G rF lF F)
             (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
             oRel lG B).
Proof. reflexivity. Qed.

Lemma wkV_pi_irr D G w r l rF lF F B
  : wkV D G w r l (oPiIrr G rF lF F B)
    = let F' := wkV D G w rF lF F in
      oPiIrr D rF lF F'
        (wkV (oExtC D rF lF F') (oExtC G rF lF F)
             (oLiftW D G w (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F'))
             oIrr oL0 B).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Soundness                                                            *)
(* ------------------------------------------------------------------ *)

(* THE T3 THEOREM.  Compare NfWk.v's [Nf_wk_str], [NfCode] conjunct:

     forall G r l c, NfCode G r l c -> forall D w, Wk D G w ->
       exists c', NfCode D r l c'
               /\ eqt (sCode D r l) (exp_subst w c) c'

   The only change is that [c'] is [wkV D G w r l c], and the proof is the
   same four cases with [destruct (IH ...) as [c' [Hc' Heq]]] replaced by
   the IH read at the computed value.  In particular [Wk_liftC] is applied
   at [F' := wkV D G w rF lF F] and hands back a weakening whose codomain
   is [oExtC D rF lF F'] -- the exact context the second recursive call is
   typed in.  That is the alignment the experiment was about. *)
Theorem wkV_sound
  : forall G r l c, NfCode G r l c ->
    forall D w, Wk D G w -> EnvOk D ->
      NfCode D r l (wkV D G w r l c)
      /\ eqt (sCode D r l)
           (oExpSubst D G w (iCode l) (oU G r l) c) (wkV D G w r l c).
Proof.
  induction 1 as [ G HG | G HG
                 | G rF lF lG F B HrF HlF HlG HF IHF HB IHB
                 | G rF lF F B HrF HlF HF IHF HB IHB
                 | G r l c Hne ];
    intros D w HW HD.
  (* ---- Nat ---- *)
  - rewrite wkV_nat; split;
      [ apply nfcode_nat; exact HD | apply eq_nat_wk; assumption ].
  (* ---- Empty ---- *)
  - rewrite wkV_empty; split;
      [ apply nfcode_empty; exact HD | apply eq_empty_wk; assumption ].
  (* ---- Pi_rel ---- *)
  - rewrite wkV_pi_rel; cbn zeta.
    destruct (IHF D w HW HD) as [HF' HeqF].
    destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 _]].
    destruct (IHB _ _ HW2 HD2) as [HB' HeqB].
    split;
      [ apply nfcode_pi_rel; assumption
      | apply eq_pi_rel_wk; assumption ].
  (* ---- Pi_irr ---- *)
  - rewrite wkV_pi_irr; cbn zeta.
    destruct (IHF D w HW HD) as [HF' HeqF].
    destruct (Wk_liftC HW HD HF HF' HeqF) as [HW2 [HD2 _]].
    destruct (IHB _ _ HW2 HD2) as [HB' HeqB].
    split;
      [ apply nfcode_pi_irr; assumption
      | apply eq_pi_irr_wk; assumption ].
  (* ---- neutral: THE HOLE ---- *)
  - destruct (NeCode_shape Hne) as [ Hv | [l0 [A [B [t [u ->]]]]] ].
    + (* a code variable.  [wkV] falls through to [wkne] on [oHd] (three
         arguments) and on [oExpSubst] (six, with head [exp_subst]), so
         the goal is literally [wkne_sound]. *)
      destruct (VarT_shape Hv) as [ [G0 [i0 [A0 ->]]]
                                  | [G0 [j [B [i0 [A0 [y ->]]]]]] ];
        cbn [wkV]; apply wkne_sound; assumption.
    + (* a stuck [Id]: six arguments, head [Id], so again [wkne]. *)
      cbn [wkV]; apply wkne_sound; assumption.
Qed.

End WithNeutrals.

(* =====================================================================
   WHAT THIS SETTLES, AND WHAT IT DOES NOT.

   SETTLED (the positive half).  On the canonical code grammar the
   annotated representation is fine.  [wkV] is a plain [Fixpoint]; its
   soundness is NfWk.v's induction with the existential replaced by the
   computed value; the [F']/[B'] slots of [eq_pi_rel_wk] / [eq_pi_irr_wk]
   and the context [oExtC D rF lF F'] handed back by [Wk_liftC] line up
   with the recursive calls with no reshaping at all.  No annotation had
   to be massaged, and no lemma had to be restated.

   OPEN (the negative half).  [wkne] cannot be defined.  See the header:
   the recursion on the weakening and the recursion on the code call each
   other, and Rocq's guard checker rejects the pair.  Three exits, in
   increasing order of cost:

     (a) MAKE WEAKENING A DETERMINISTIC RELATION, mutually with the value
         judgements, and prove functionality (design.md section 13b's
         property (D)) instead of getting it definitionally.  Costs a
         determinism proof by the same mutual induction; keeps every line
         of Values.v and this file.  Note the design's own [Nrm] is
         already of this shape -- "a deterministic big-step [Nrm e n]"
         with (D) as a THEOREM -- so this is not a new concession.

     (b) DE BRUIJN VALUES + ONE READBACK, the fallback design.md names.
         Weakening becomes a shift and the annotation problem evaporates
         because de Bruijn values carry no annotations.  Rigid.v's
         [rcode]/[rty]/[renv] (with [cren]/[csub]/[rshift] and their
         sigma laws, all proved) is a working template for the domain.
         Costs a readback and its soundness.

     (c) INDEX VARIABLE VALUES BY A DE BRUIJN DEPTH inside the annotated
         syntax, so the annotation is derivable from the depth and the
         context.  A hybrid; not obviously cheaper than (a).

   The choice is upstream of everything else in the value layer.
   ===================================================================== *)
