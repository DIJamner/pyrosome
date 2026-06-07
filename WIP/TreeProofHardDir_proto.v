(* ====================================================================== *)
(* z28 PROTOTYPE: hard direction driven off TreeProofs (Dustin's D2/route).*)
(*                                                                        *)
(* GOAL of this proto: validate the ARCHITECTURE before sinking the real  *)
(* proof.  Two questions:                                                 *)
(*   (Q-recursor) Does TreeProofs.pf_rect carry an ENV-KEYED Type motive   *)
(*                of the hard-direction shape                              *)
(*                  forall D g, OSUB G D g -> RED (e[g])                   *)
(*                (RED is Type-valued, e.g. RedTy)?  i.e. can we eliminate *)
(*                a tree proof INTO Type with a substitution-generalized   *)
(*                motive, closing the structural cases?                    *)
(*   (Q-complete) The make-or-break: where does the tree proof COME FROM   *)
(*                for a well-typed term?  Is `wf_term [] e S -> pf`        *)
(*                computational, or does it reintroduce Prop->Type/choice? *)
(*                                                                        *)
(* This file is NOT in _CoqProject.  It abstracts the OTT specifics        *)
(* (RedTy/osub) behind opaque Type-valued placeholders so the recursor     *)
(* mechanics are checked in isolation; admits mark the genuinely-hard      *)
(* leaves (axioms instances, the Pi case) — those are NOT the architecture *)
(* question, the recursor + completeness are.                             *)
(* ====================================================================== *)
Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Proof Require Import TreeProofs.
Import Core.Notations.

Section Proto.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation lang := (@lang V).
  Notation pf := (@pf V).

  Context (l : lang) (wfl : wf_lang l).

  (* --- Opaque stand-ins for the OTT LR layer (all Type-valued). --------- *)
  (* RedTy D A B : the Type-valued reducibility witness (LogicalRelation).  *)
  Context (RED : term -> term -> term -> Type).
  (* osub G D g : the object substitution (Prop in the real dev; here Prop  *)
  (*   too, to faithfully reproduce the elimination situation).            *)
  Context (OSUB : term -> term -> term -> Prop).
  (* g applied to a term (the real dev uses e[/g/] with an object subst).   *)
  Context (act : term -> term -> term).  (* act g e  ~  e[g] *)

  (* ===================================================================== *)
  (* Q-recursor: the env-keyed Type motive over a tree proof.              *)
  (*                                                                        *)
  (* The hard direction must produce, for a proof `p` checking to           *)
  (* (e,e,S) at context [] (a well-typedness proof), a RED witness under    *)
  (* every object substitution.  Substitution-generalized + env-keyed:      *)
  (* ===================================================================== *)
  (* The Pyrosome ctx is [] (LR convention: osub G D g := wf_term l [] g ...);*)
  (* the object env G : term is a separate argument carried in the motive.    *)
  Definition HardMot (G : term) (p : pf) : Type :=
    forall (e1 e2 : term) (S : sort),
      check_proof l [] p = Some (e1, e2, S) ->
      forall D g, OSUB G D g -> RED D (act g e1) (act g e2).

  (* Can pf_rect (Type motive!) be applied at THIS motive?  Yes: pf is      *)
  (* Type (TreeProofs.v:73), pf_rect's motive is `pf -> Type`              *)
  (* (TreeProofs.v:113), HardMot G p : Type.  We FIX G across the fold      *)
  (* (the cut-free fold never changes context — same as Eval.v).           *)
  Theorem hard_dir_skeleton (G : term) (p : pf) : HardMot G p.
  Proof.
    (* Apply the Type recursor with the env-keyed Type motive.  This is     *)
    (* the load-bearing architectural check: the elimination is Prop-free   *)
    (* (we induct a Type tree, not the Prop wf_term).                       *)
    revert p.
    refine (pf_rect (fun p => HardMot G p) _ _ _ _ _).
    - (* pvar n : variable.  check_proof on pvar gives (var n, var n, t)     *)
      (*   with t the ctx lookup.  RED at a var under g = bound-var          *)
      (*   reducibility from the env (osub) — the z19 bound_var_redtm.       *)
      (* At Pyrosome ctx [] the var lookup is None, so check_proof on pvar     *)
      (*   is vacuously None=Some -> the case closes by discriminate.  (Object  *)
      (*   openness lives in G/OSUB, not the Pyrosome ctx; a genuine object var *)
      (*   appears as a `con "hd"/"var"` term, handled in the pcon case.)       *)
      intros n. unfold HardMot. intros e1 e2 S Hchk D g Hos.
      cbn in Hchk. discriminate.
    - (* pcon n args : congruence (term_rule) or axiom (term_eq_rule).       *)
      intros n args IHargs. unfold HardMot. intros e1 e2 S Hchk D g Hos.
      (* The IHargs : fold_right (fun p => prod (HardMot G p)) unit args     *)
      (*   gives, positionally, the hard-direction witness for each sub-     *)
      (*   proof — i.e. RED for each argument under g.  The con case then    *)
      (*   assembles RED for (con n s) via the LR's congruence smart ctor    *)
      (*   (RedTy_nat/empty for base types, RedTy_pi for Pi, etc.).          *)
      admit. (* structural: dispatch on the rule; base types close, Pi hard.*)
    - (* ptrans : the two IHs (IH1/IH2 : HardMot G p_i) give RED D (act g a)   *)
      (*   (act g b) on each side; check_proof's `eqb b a'` glue bridges them;  *)
      (*   compose via RED member-PER transitivity.  (Plumbing of the nested    *)
      (*   check_proof matches deferred — architecture already validated.)      *)
      intros p1 IH1 p2 IH2. unfold HardMot. intros e1 e2 S Hchk D g Hos.
      admit. (* RED trans (member PER transitivity).                        *)
    - (* psym : RED member-PER symmetry over the single IH.                    *)
      intros p0 IH0. unfold HardMot. intros e1 e2 S Hchk D g Hos.
      admit. (* RED sym (member PER symmetry).                              *)
    - (* pconv : transport along the sort-equality SUB-PROOF p0 (a tree node,  *)
      (*   NOT a wf_term sub-derivation — this is the explicit conversion       *)
      (*   constructor that dodges the Prop->Type wall).  IH1 gives RED at the  *)
      (*   source sort; transport along p0's eq_sort to the target sort.        *)
      intros p0 IH0 p1 IH1. unfold HardMot. intros e1 e2 S Hchk D g Hos.
      admit. (* RED conv: transport RED along the sort-eq tree p0.          *)
  Admitted.

  (* ===================================================================== *)
  (* Q-complete (THE MAKE-OR-BREAK): to USE hard_dir_skeleton on a          *)
  (* well-typed term we need a tree `p` with check_proof l [] p =           *)
  (* Some (e,e,S).  Where does it come from?                                *)
  (*                                                                        *)
  (* The ONLY bridge that exists in src/ is SOUNDNESS:                      *)
  (*   pf_checker_sound : check_proof l c p = Some (e1,e2,t) -> eq_term ... *)
  (* (TreeProofs.v:370; Gluing/ProofModel.v:52 lifts it).  There is NO      *)
  (* completeness lemma `wf_term/eq_term -> { p & check_proof ... }`        *)
  (* anywhere (grep over src/Pyrosome/Proof, src/Pyrosome/Gluing).          *)
  (*                                                                        *)
  (* ProofModel.v:80 DEFINES `reflect_tm : term -> pf` structurally, but    *)
  (* its CORRECTNESS (check_proof (reflect_tm e) = Some (e,e,S) for a       *)
  (* well-typed e) is explicitly DEFERRED to "a later module (M6)" that     *)
  (* DOES NOT EXIST (grep: only the comment + the def).                     *)
  (*                                                                        *)
  (* The statement of that missing bridge is exactly:                      *)
  (* NB: this statement cannot even live in Prop — `{p & ...}` is a Type     *)
  (* sigT, so `wf_term -> {p & ...}` is forced into Type (universe-checked).  *)
  (* That is the wall in miniature: producing the tree IS a Type output, and  *)
  (* the only honest input is the Prop wf_term.                               *)
  Definition COMPLETENESS_BRIDGE : Type :=
    forall (G : ctx) (e : term) (S : sort),
      wf_term l G e S ->
      { p : pf & check_proof l G p = Some (e, e, S) }.
  (* This is `wf_term (Prop) -> {p & ...} (Type/sigT)`.  Proving it by      *)
  (* INDUCTION ON wf_term is Prop->Type large elimination — the SAME WALL   *)
  (* (z24).  The structural `reflect_tm` sidesteps INDUCTION but its        *)
  (* correctness proof (check_proof (reflect_tm e) = Some (e,e,S)) STILL    *)
  (* requires inverting wf_term to know e's rule/args are well-formed —     *)
  (* and that inversion, to feed a Type/sigT goal, is the wall again,       *)
  (* UNLESS reflect_tm's correctness is provable WITHOUT eliminating        *)
  (* wf_term into Type (e.g. via a decidable computational CHECKER on       *)
  (* CLOSED terms whose Some-ness is a decidable Prop one can case on).     *)
  (*                                                                        *)
  (* CRUCIAL FINDING (memory ott-open-term-wf-no-checker): the project's    *)
  (* computational wf checker (compute_wf_term') only works on CLOSED       *)
  (* terms and CANNOT evaluate a free Coq variable.  The hard-direction     *)
  (* subjects are OPEN (object env G : tm is a free var), so even a         *)
  (* checker-produces-tree route does not obviously apply at the leaves     *)
  (* under an object substitution.                                          *)

End Proto.
