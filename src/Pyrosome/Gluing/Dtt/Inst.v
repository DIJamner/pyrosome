Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Require Import Pyrosome.Gluing.Dtt.Syntax.
(* [Require EXPORT]: everything downstream of the instantiation layer wants the
   value judgements and (through Values.v) the weakening block as well. *)
Require Export Pyrosome.Gluing.Dtt.Values.
Import Core.Notations.

(* =====================================================================
   INSTANTIATION OF VALUES -- THE SUBSTITUTION HALF OF [Nrm].

   WHY THIS IS NOT A SECOND COPY OF WkRel.v.  Weakening never creates a
   redex; it only shifts, which is why WkRel.v is purely structural and
   why it was cheap (design.md section 14f).  Instantiation substitutes a
   VALUE for a variable, and a value in a neutral's head position turns
   that neutral into a redex.  So this relation must EVALUATE: it is not
   a sibling of the weakening block but a fragment of the normalizer
   (design.md section 14k).

   WHERE, EXACTLY, IT EVALUATES.  Only two places, and both are visible
   as a non-structural premise below:

     - [insttm_app_rel] hands its instantiated head to [AppV].  When the
       head was the variable being substituted and the substituted value
       is a [lam_rel], [AppV] fires beta; otherwise the application stays
       neutral.
     - [insttm_id] hands its four instantiated arguments to [IdV].  An
       [Id] value is a STUCK [Id] (Values.v's [necode_id_*]), and
       instantiation can unstick it: when the stuck endpoint is the
       de Bruijn-0 variable at [El _ rel L0 (Nat _)], substituting [zero]
       or [suc n] fires "Id-Nat-00"/"-0S"/"-S0"/"-SS".

   Everything else -- [Nat], [Empty], [Pi_rel], [Pi_irr], [zero], [suc],
   [*], [lam_rel], [Emptyrec], and code VARIABLES -- is structural.  A
   code variable's type is a universe, and the de Bruijn-0 variable of
   [oExtC G rF lF F] has type [El _ rF lF F[wkn]], an [El]; so a code
   variable is NEVER the one being substituted and always merely strips.
   For the same reason an [Id] stuck on a neutral CODE stays stuck.

   THE FIVE JUDGEMENTS (design.md section 14k's own count):

     InstTy  D G g i A A'      types
     InstTm  D G g e e'        codes AND elements, in ONE judgement
     InstVar D G g x x'        variables
     AppV    G rF lF lG F B f a r      the value of an application (beta)
     IdV     G l A B t u c             the section-12b Id computation table

   The first three mirror WkRel.v exactly, including the reason codes and
   elements share a judgement (their head symbols are pairwise disjoint,
   which turns determinism into a discrimination argument) and the reason
   [InstTm] carries no type index (every annotation a value carries is
   already stored in the subject).

   ONE DIFFERENCE FROM WkRel.v WORTH NOTING: [InstVar] needs no type index
   at all, so there is no analogue of WkRel.v's fourth judgement [VarTy].
   [VarTy] was forced there because [wkvar_wkn] EMITS
   [exp_subst wkn i A x], whose annotation [A] the relation would
   otherwise never pin.  No clause here emits a new annotation:
   [instvar_snoc_hd] returns the substituted value, [instvar_snoc_wkn]
   returns a recursive result, and [instvar_cmp] returns a WEAKENING of
   one, computed by the already-closed [WkTm].

   THE DEPENDENCY ON WkRel IS REAL AND ONE-WAY.  [instvar_cmp] is the
   single place it appears, and it is not removable.  Trace the
   de Bruijn-1 variable through one lift: the lifted substitution is
   [oLiftW D G g i A A'], i.e. [<cmp (wkn) g, hd>], so a shifted variable
   [y] goes to [y[cmp (wkn) g]] = [(y[g])[wkn]] -- and [y[g]] is in
   general the SUBSTITUTED VALUE, not a variable, so weakening it is a
   [WkTm] call and not something the emitted syntax already contains.
   (An earlier note expected the [oCmp _ (oWkn _) g] inside [oLiftW] to
   make this unnecessary.  It does not: that spelling supplies the
   weakening SUBSTITUTION, but the thing being weakened is a value, and
   only [WkTm] computes the value of a weakened value.)  Nothing runs the
   other way: no clause of WkRel.v mentions instantiation, exactly because
   weakening creates no redex.
   ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* Vocabulary                                                           *)
(* ------------------------------------------------------------------ *)

(* The weakening out of, and the de Bruijn-0 variable of, a context
   extended by the type named by a code -- the [oExtC] of Syntax.v. *)
Definition oWknC (G rF lF F : term) : term :=
  oWkn G (iEl rF lF) (oEl G rF lF F).
Definition oHdC (G rF lF F : term) : term :=
  oHd G (iEl rF lF) (oEl G rF lF F).

(* The lift of [g : sub D G] under a binder whose code is [F] over [G] and
   [F'] over [D].  It is WkRel.v's [oLiftW] at the [El] info, and that is
   not a coincidence: the shape is fixed by the compiled substitution
   commutations (Syntax.v's [oLift]), so weakening and instantiation lift
   the same way.  Note it is a [snoc] whose tail is a [cmp] with a [wkn] --
   which is exactly the two shapes [InstVar] dispatches on. *)
Definition oLiftC (D G g rF lF F F' : term) : term :=
  oLiftW D G g (iEl rF lF) (oEl G rF lF F) (oEl D rF lF F').

Section WithInstC.

  (* Values.v's last parameter, threaded through.  [instC G rF lF F a lG B]
     is the value of [B[<id,a>]], used only as the type index of an
     [app_rel] neutral.  It is exactly what [InstTm] below computes, so the
     two are destined to be identified -- but not here: Values.v is
     upstream of this file (its judgements are premises of [IdV]), so the
     identification is a job for whatever file replaces the [instC]
     parameter by an [InstTm] premise, in the same way [wkTy] was replaced
     by a [WkTy] premise. *)
  Context (instC : term -> term -> term -> term -> term -> term -> term -> term).

(* ------------------------------------------------------------------ *)
(* Three refutations, from Values.v's shape lemmas                      *)
(*                                                                      *)
(* These are the disjointness half of the tables below.  [NeCode_not_nat] *)
(* and [NeCode_not_pi_rel] (Values.v) separate a STUCK [Id] from a        *)
(* computing one at the CODE level; these three do the same at the        *)
(* ELEMENT level -- they are what stops a neutral endpoint from also      *)
(* matching [zero]/[suc], and a neutral function from also matching a     *)
(* [lam_rel].                                                            *)
(* ------------------------------------------------------------------ *)

Ltac ne_shape_discriminate H :=
  apply ValNe_shape in H;
  repeat match goal with
         | Hd : _ \/ _ |- _ => destruct Hd
         | Hd : exists _, _ |- _ => destruct Hd
         end;
  discriminate.

Lemma ValNe_not_zero G i A G0
  : ValNe instC G i A (oZero G0) -> False.
Proof. intro H; ne_shape_discriminate H. Qed.

Lemma ValNe_not_suc G i A G0 n
  : ValNe instC G i A (oSuc G0 n) -> False.
Proof. intro H; ne_shape_discriminate H. Qed.

Lemma ValNe_not_lam_rel G i A G0 rF lF lG F B t
  : ValNe instC G i A (oLamRel G0 rF lF lG F B t) -> False.
Proof. intro H; ne_shape_discriminate H. Qed.

(* ================================================================== *)
(* The block                                                           *)
(* ================================================================== *)

Inductive InstTy : term -> term -> term -> term -> term -> term -> Prop :=
| instty_U : forall D G g r l,
    InstTy D G g (iCode l) (oU G r l) (oU D r l)
| instty_El : forall D G g r l c c',
    InstTm D G g c c' ->
    InstTy D G g (iEl r l) (oEl G r l c) (oEl D r l c')

(* [InstTm D G g e e'] : [e], a value over [G], has value [e'] over [D]
   after the substitution [g : sub D G].  Head-directed on [e] except at
   the two variable clauses, which are head-directed too -- see the note
   on [wktm_var_hd]/[wktm_var_wkn] in WkRel.v for why the single-clause
   version is unsound for [inversion]. *)
with InstTm : term -> term -> term -> term -> term -> Prop :=
(* ---- codes: structural ---- *)
| insttm_nat : forall D G g, InstTm D G g (oNat G) (oNat D)
| insttm_empty : forall D G g, InstTm D G g (oEmpty G) (oEmpty D)
| insttm_pi_rel : forall D G g rF lF lG F B F' B',
    InstTm D G g F F' ->
    InstTm (oExtC D rF lF F') (oExtC G rF lF F) (oLiftC D G g rF lF F F') B B' ->
    InstTm D G g (oPiRel G rF lF lG F B) (oPiRel D rF lF lG F' B')
| insttm_pi_irr : forall D G g rF lF F B F' B',
    InstTm D G g F F' ->
    InstTm (oExtC D rF lF F') (oExtC G rF lF F) (oLiftC D G g rF lF F F') B B' ->
    InstTm D G g (oPiIrr G rF lF F B) (oPiIrr D rF lF F' B')
(* THE ONE CODE CLAUSE THAT EVALUATES.  A value [Id] is a stuck one, and
   instantiating its arguments can unstick it; [IdV] is the whole of
   design.md section 12b's computation table. *)
| insttm_id : forall D G g l A B t u A' B' t' u' c,
    InstTm D G g A A' -> InstTm D G g B B' ->
    InstTm D G g t t' -> InstTm D G g u u' ->
    IdV D l A' B' t' u' c ->
    InstTm D G g (oIdEq G l A B t u) c
(* ---- elements ---- *)
| insttm_zero : forall D G g, InstTm D G g (oZero G) (oZero D)
| insttm_suc : forall D G g n n',
    InstTm D G g n n' -> InstTm D G g (oSuc G n) (oSuc D n')
(* The entire irrelevant fragment, in one clause: [*] instantiates to
   [*].  This is what makes every irrelevant clause of the block free. *)
| insttm_star : forall D G g, InstTm D G g oStar oStar
| insttm_lam_rel : forall D G g rF lF lG F B t F' B' t',
    InstTm D G g F F' ->
    InstTm (oExtC D rF lF F') (oExtC G rF lF F) (oLiftC D G g rF lF F F') B B' ->
    InstTm (oExtC D rF lF F') (oExtC G rF lF F) (oLiftC D G g rF lF F F') t t' ->
    InstTm D G g (oLamRel G rF lF lG F B t) (oLamRel D rF lF lG F' B' t')
(* THE OTHER CLAUSE THAT EVALUATES: the head may become a [lam_rel]. *)
| insttm_app_rel : forall D G g rF lF lG F B f a F' B' f' a' r,
    InstTm D G g F F' ->
    InstTm (oExtC D rF lF F') (oExtC G rF lF F) (oLiftC D G g rF lF F F') B B' ->
    InstTm D G g f f' -> InstTm D G g a a' ->
    AppV D rF lF lG F' B' f' a' r ->
    InstTm D G g (oAppRel G rF lF lG F B f a) r
(* [Emptyrec] has no computation rule -- [Empty] has no constructors -- so
   it is structural even though it is an eliminator.  Its argument is the
   literal [oStar] of [valne_emptyrec]. *)
| insttm_emptyrec : forall D G g rA lA A A',
    InstTm D G g A A' ->
    InstTm D G g (oEmptyrec G rA lA A oStar) (oEmptyrec D rA lA A' oStar)
(* ---- variables ---- *)
| insttm_var_hd : forall D G g G0 i0 A0 x',
    InstVar D G g (oHd G0 i0 A0) x' ->
    InstTm D G g (oHd G0 i0 A0) x'
| insttm_var_wkn : forall D G g G0 j B i0 A0 y x',
    InstVar D G g (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y) x' ->
    InstTm D G g (oExpSubst (oExt G0 j B) G0 (oWkn G0 j B) i0 A0 y) x'

(* [InstVar D G g x x'] : the variable [x] of [G] has value [x'] over [D]
   after [g].  DISPATCH IS ON [g] FIRST, then on [x] -- the mirror image of
   [WkVar], and the reason [instvar_id]'s unconstrained subject is harmless
   (the clause is pinned by [g = oId G], which no other clause's [g]
   matches).

   No type index: see the header.  The three substitution shapes are
   exactly those reachable from [oInst] by lifting -- [oId] at the bottom,
   [oSnoc] for the substitution itself and for every lift of it, and
   [oCmp _ (oWkn _) _] for the tail a lift introduces. *)
with InstVar : term -> term -> term -> term -> term -> Prop :=
| instvar_id : forall G i A x,
    VarTy G i A x -> InstVar G G (oId G) x x
| instvar_snoc_hd : forall D G i A g0 v,
    InstVar D (oExt G i A) (oSnoc D G i A g0 v) (oHd G i A) v
| instvar_snoc_wkn : forall D G i A g0 v i0 A0 y y',
    InstVar D G g0 y y' ->
    InstVar D (oExt G i A) (oSnoc D G i A g0 v)
            (oExpSubst (oExt G i A) G (oWkn G i A) i0 A0 y) y'
(* THE [WkTm] CALL, and the only one in the block.  [x[cmp w g0]] is
   [(x[g0])[w]], and [x[g0]] is in general a substituted VALUE. *)
| instvar_cmp : forall D D0 G w g0 x x0 x',
    InstVar D0 G g0 x x0 ->
    WkTm D D0 w x0 x' ->
    InstVar D G (oCmp D D0 G w g0) x x'

(* [AppV G rF lF lG F B f a r] : applying the value [f] (at
   [El G rel lG (Pi_rel G rF lF lG F B)]) to the value [a] gives [r].

   TWO CLAUSES, and the asymmetry between them is worth stating.  At a
   [Pi_rel] type eta leaves no neutral VALUE ([Val_pi_rel_shape]), so
   [appv_beta] is the only case that can arise when [f] came from
   normalizing a term at that type.  But [valne_app_rel]'s own head
   premise is a [ValNe], not a [Val] -- a variable of [Pi] type is neutral
   without being a value there -- so an application whose head survives
   instantiation as a neutral is real, and [appv_ne] is what keeps
   [insttm_app_rel] from getting stuck on it. *)
with AppV : term -> term -> term -> term -> term -> term -> term -> term
            -> term -> Prop :=
| appv_beta : forall G rF lF lG F B t a r,
    InstTm G (oExtC G rF lF F) (oInst G rF lF F a) t r ->
    AppV G rF lF lG F B (oLamRel G rF lF lG F B t) a r
| appv_ne : forall G rF lF lG F B f a,
    ValNe instC G (iEl oRel lG) (oEl G oRel lG (oPiRel G rF lF lG F B)) f ->
    AppV G rF lF lG F B f a (oAppRel G rF lF lG F B f a)

(* ================================================================== *)
(* [IdV] -- THE Id COMPUTATION TABLE (design.md section 12b)           *)
(* ================================================================== *)

(* [IdV G l A B t u c] : the value of [Id G l A B t u], for value codes
   [A],[B] at [U G rel l] and values [t],[u] at [El A],[El B], is the
   value code [c] at [U G irr L0].

   THE ANALYSIS IS 3 x 3 IN THE CODES and, at [Nat]/[Nat], 3 x 3 IN THE
   ENDPOINTS.  That is exactly what Values.v's [ValCode_rel_shape] and
   [Val_nat_shape] say, and the table below is written against them:

     A, B           | value
     ---------------+-------------------------------------------------
     neutral, _     | STUCK          idv_ne_l
     _, neutral     | STUCK          idv_ne_r
     Nat, Pi_rel    | Empty          idv_nat_pi
     Pi_rel, Nat    | Empty          idv_pi_nat
     Pi_rel, Pi_rel | (rF1,lF1) <> (rF2,lF2): Empty, four clause
                    | (rF1,lF1)  = (rF2,lF2): FUNEXT, two clauses (rel/irr)
     Nat, Nat       | t, u          | value
                    | zero, zero    | Unit           idv_nat_00
                    | zero, suc     | Empty          idv_nat_0S
                    | suc,  zero    | Empty          idv_nat_S0
                    | suc,  suc     | recurse        idv_nat_SS
                    | neutral, _    | STUCK          idv_nat_ne_l
                    | _, neutral    | STUCK          idv_nat_ne_r

   ALL FOUR STUCK CLAUSES EMIT THE SAME TERM, [oIdEq G l A B t u], so the
   overlaps among them are free: two stuck derivations agree without any
   argument.  What determinism needs is that a stuck clause never overlaps
   a COMPUTING one, and that is precisely what Values.v's [NeCode_not_nat]
   / [NeCode_not_pi_rel] and this file's [ValNe_not_zero] /
   [ValNe_not_suc] supply.

   THE FOUR CLASH CLAUSES ARE A PARTITION AS THE LANGUAGE HAS THEM.
   IdComp.v's own comment says the four "overlap, which is harmless"; read
   off the compiled rules they do not.  "Id-Pi-Pi-rel-irr" and
   "-irr-rel" pin the two relevances to the DISTINCT literals [rel]/[irr],
   while "-L0-L1" and "-L1-L0" SHARE one relevance metavariable [rF] and
   pin the two levels to distinct literals.  So relevance-mismatch and
   level-mismatch are mutually exclusive, and the four transcribe directly
   as a partition of "(rF1,lF1) differs from (rF2,lF2)" -- no
   restructuring was needed. *)
with IdV : term -> term -> term -> term -> term -> term -> term -> Prop :=
(* ---- stuck on a neutral CODE ---- *)
| idv_ne_l : forall G l A B t u,
    NeCode instC G oRel l A ->
    IdV G l A B t u (oIdEq G l A B t u)
| idv_ne_r : forall G l A B t u,
    NeCode instC G oRel l B ->
    IdV G l A B t u (oIdEq G l A B t u)
(* ---- Nat against Nat: dispatch on the ENDPOINTS ---- *)
| idv_nat_00 : forall G,
    IdV G oL0 (oNat G) (oNat G) (oZero G) (oZero G) (oUnit G)
| idv_nat_0S : forall G n,
    IdV G oL0 (oNat G) (oNat G) (oZero G) (oSuc G n) (oEmpty G)
| idv_nat_S0 : forall G m,
    IdV G oL0 (oNat G) (oNat G) (oSuc G m) (oZero G) (oEmpty G)
| idv_nat_SS : forall G m n c,
    IdV G oL0 (oNat G) (oNat G) m n c ->
    IdV G oL0 (oNat G) (oNat G) (oSuc G m) (oSuc G n) c
| idv_nat_ne_l : forall G t u,
    ValNe instC G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) t ->
    IdV G oL0 (oNat G) (oNat G) t u (oIdEq G oL0 (oNat G) (oNat G) t u)
| idv_nat_ne_r : forall G t u,
    ValNe instC G (iEl oRel oL0) (oEl G oRel oL0 (oNat G)) u ->
    IdV G oL0 (oNat G) (oNat G) t u (oIdEq G oL0 (oNat G) (oNat G) t u)
(* ---- the heads differ: TYPE-DIRECTED, endpoints arbitrary ----
   Both rules are stated at [l = L0], and that is forced rather than a
   restriction: [Nat] is a code at [L0] only, and an [Id]'s two codes
   share a level, so the [Pi_rel]'s own [lG] is [L0] too. *)
| idv_nat_pi : forall G rF lF F B t u,
    IdV G oL0 (oNat G) (oPiRel G rF lF oL0 F B) t u (oEmpty G)
| idv_pi_nat : forall G rF lF F B t u,
    IdV G oL0 (oPiRel G rF lF oL0 F B) (oNat G) t u (oEmpty G)
(* ---- two Pi_rels with MISMATCHED domain indices ---- *)
| idv_pi_pi_rel_irr : forall G l lF1 lF2 F1 B1 F2 B2 t u,
    IdV G l (oPiRel G oRel lF1 l F1 B1) (oPiRel G oIrr lF2 l F2 B2) t u
        (oEmpty G)
| idv_pi_pi_irr_rel : forall G l lF1 lF2 F1 B1 F2 B2 t u,
    IdV G l (oPiRel G oIrr lF1 l F1 B1) (oPiRel G oRel lF2 l F2 B2) t u
        (oEmpty G)
| idv_pi_pi_L0_L1 : forall G l rF F1 B1 F2 B2 t u,
    IdV G l (oPiRel G rF oL0 l F1 B1) (oPiRel G rF oL1 l F2 B2) t u
        (oEmpty G)
| idv_pi_pi_L1_L0 : forall G l rF F1 B1 F2 B2 t u,
    IdV G l (oPiRel G rF oL1 l F1 B1) (oPiRel G rF oL0 l F2 B2) t u
        (oEmpty G)

(* ---- two Pi_rels with MATCHING domain indices: FUNCTION EXTENSIONALITY.

   THE ENDPOINTS ARE LAMBDAS, NOT NEUTRALS.  [Val_pi_rel_shape] is what
   licenses writing them as [oLamRel]s: at a [Pi_rel] type eta leaves no
   neutral alternative, and that asymmetry against [Nat] -- where the
   neutral case is real and gets its own two clauses above -- is the whole
   reason this clause can be written at all.

   RELEVANT DOMAIN, three binders (IdFunextDefs.v's [id_pi_pi_rel_rule]):

     Id (Pi rel lF l F1 B1) (Pi rel lF l F2 B2) f g
       = Pi_irr rel lF F1 (Pi_irr rel lF F2[w1]
           (Pi_irr irr L0 (Id F1[w21] F2[w21] a1[w2] a2)
             (Id B1[<w3G,a1z>] B2[<w3G,a2z>] (f[w3G]. a1z) (g[w3G]. a2z))))

   with contexts X1 = G.F1, Y = X1.F2[w1], Z = Y.(that middle Id).  Every
   piece of the right-hand side is named by a premise below rather than
   written out, because the VALUE of a weakened code is not its explicit
   substitution: [WkTm] computes [Nat G] |-> [Nat X1], not
   [Nat G [w1]].  Only the [Pi_irr] skeleton is literal.

   The middle binder's domain is a RECURSIVE [IdV] (premise [HP]); the
   body is another ([Hbody]); and the two applications go through [AppV],
   which fires beta because the weakened endpoints are still lambdas.  The
   codomain instances [cod1]/[cod2] are the rule's [B1[<w3G,a1z>]]
   factored as weaken-then-instantiate: [B1z] is [B1] weakened under its
   own binder along [w3G], and [InstTm] then substitutes [a1z] for the
   de Bruijn-0 variable.  That factoring is what keeps [InstTm]'s
   substitution argument in the shape its own clauses dispatch on. *)
| idv_funext_rel :
  forall G l lF F1 B1 F2 B2 tf tg
         F2w F1s F2s a1w P F1z F2z a1z a2z B1z B2z fz gz r1 r2 cod1 cod2 bodyv,
    (* --- binder 1 : a1 : El F1, in X1 = oExtC G rel lF F1 --- *)
    WkTm (oExtC G oRel lF F1) G (oWknC G oRel lF F1) F2 F2w ->
    (* --- binder 2 : a2 : El F2w, in Y = oExtC X1 rel lF F2w --- *)
    WkTm (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
         (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
               (oExtC G oRel lF F1) G
               (oWknC (oExtC G oRel lF F1) oRel lF F2w)
               (oWknC G oRel lF F1))
         F1 F1s ->
    WkTm (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
         (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
               (oExtC G oRel lF F1) G
               (oWknC (oExtC G oRel lF F1) oRel lF F2w)
               (oWknC G oRel lF F1))
         F2 F2s ->
    WkTm (oExtC (oExtC G oRel lF F1) oRel lF F2w) (oExtC G oRel lF F1)
         (oWknC (oExtC G oRel lF F1) oRel lF F2w)
         (oHdC G oRel lF F1) a1w ->
    (* --- binder 3 : p : Id F1s F2s a1w a2, in Z = oExtC Y irr L0 P --- *)
    IdV (oExtC (oExtC G oRel lF F1) oRel lF F2w) lF F1s F2s a1w
        (oHdC (oExtC G oRel lF F1) oRel lF F2w) P ->
    (* --- everything transported from G / Y to Z --- *)
    WkTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P) G
         (oCmp (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
               (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                     (oExtC G oRel lF F1) G
                     (oWknC (oExtC G oRel lF F1) oRel lF F2w)
                     (oWknC G oRel lF F1)))
         F1 F1z ->
    WkTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P) G
         (oCmp (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
               (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                     (oExtC G oRel lF F1) G
                     (oWknC (oExtC G oRel lF F1) oRel lF F2w)
                     (oWknC G oRel lF F1)))
         F2 F2z ->
    WkTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
         (oExtC (oExtC G oRel lF F1) oRel lF F2w)
         (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
         a1w a1z ->
    WkTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
         (oExtC (oExtC G oRel lF F1) oRel lF F2w)
         (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
         (oHdC (oExtC G oRel lF F1) oRel lF F2w) a2z ->
    (* --- the two codomain codes, weakened UNDER their own binder --- *)
    WkTm (oExtC (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                oRel lF F1z)
         (oExtC G oRel lF F1)
         (oLiftC (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P) G
            (oCmp (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
                  (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                        (oExtC G oRel lF F1) G
                        (oWknC (oExtC G oRel lF F1) oRel lF F2w)
                        (oWknC G oRel lF F1)))
            oRel lF F1 F1z)
         B1 B1z ->
    WkTm (oExtC (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                oRel lF F2z)
         (oExtC G oRel lF F2)
         (oLiftC (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P) G
            (oCmp (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
                  (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                        (oExtC G oRel lF F1) G
                        (oWknC (oExtC G oRel lF F1) oRel lF F2w)
                        (oWknC G oRel lF F1)))
            oRel lF F2 F2z)
         B2 B2z ->
    (* --- the two endpoints, weakened to Z (still lambdas) --- *)
    WkTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P) G
         (oCmp (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
               (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                     (oExtC G oRel lF F1) G
                     (oWknC (oExtC G oRel lF F1) oRel lF F2w)
                     (oWknC G oRel lF F1)))
         (oLamRel G oRel lF l F1 B1 tf) fz ->
    WkTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P) G
         (oCmp (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oExtC (oExtC G oRel lF F1) oRel lF F2w) G
               (oWknC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
               (oCmp (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                     (oExtC G oRel lF F1) G
                     (oWknC (oExtC G oRel lF F1) oRel lF F2w)
                     (oWknC G oRel lF F1)))
         (oLamRel G oRel lF l F2 B2 tg) gz ->
    (* --- the two applications (beta) --- *)
    AppV (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
         oRel lF l F1z B1z fz a1z r1 ->
    AppV (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
         oRel lF l F2z B2z gz a2z r2 ->
    (* --- the two codomain instances --- *)
    InstTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
           (oExtC (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  oRel lF F1z)
           (oInst (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  oRel lF F1z a1z)
           B1z cod1 ->
    InstTm (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
           (oExtC (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  oRel lF F2z)
           (oInst (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
                  oRel lF F2z a2z)
           B2z cod2 ->
    (* --- and the body --- *)
    IdV (oExtC (oExtC (oExtC G oRel lF F1) oRel lF F2w) oIrr oL0 P)
        l cod1 cod2 r1 r2 bodyv ->
    IdV G l (oPiRel G oRel lF l F1 B1) (oPiRel G oRel lF l F2 B2)
        (oLamRel G oRel lF l F1 B1 tf) (oLamRel G oRel lF l F2 B2 tg)
        (oPiIrr G oRel lF F1
           (oPiIrr (oExtC G oRel lF F1) oRel lF F2w
              (oPiIrr (oExtC (oExtC G oRel lF F1) oRel lF F2w)
                      oIrr oL0 P bodyv)))

(* ---- IRRELEVANT DOMAIN, two binders (IdFunextDefs.v's
   [id_pi_pi_irr_rule]).  There is no domain-equality premise: a relevant
   result cannot depend on an irrelevant argument except through
   [Emptyrec], so the pair of arguments needs no proof relating them.

   AND THE TWO BOUND VARIABLES ARE [*].  This is the one place the value
   layer visibly departs from the rule as written.  The rule's [a1w] and
   [a2] are variables at an IRRELEVANT [El], where the only value is
   [oStar] (Values.v's [Val_irr_star]); so the arguments of the two
   applications, and the two codomain instantiations, take [oStar].  The
   choice is not merely licensed but immaterial: a value over
   [oExtC G irr lF F1] cannot mention that context's de Bruijn-0 variable
   at all, since every position it could occupy is itself irrelevant and
   therefore already [*].  (Contrast the relevant clause above, where
   [a1w]/[a1z]/[a2z] are genuine variables and only the middle binder's
   [p] -- which is never used -- collapses.) *)
| idv_funext_irr :
  forall G l lF F1 B1 F2 B2 tf tg
         F2w F1s F2s B1y B2y fy gy r1 r2 cod1 cod2 bodyv,
    WkTm (oExtC G oIrr lF F1) G (oWknC G oIrr lF F1) F2 F2w ->
    WkTm (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) G
         (oCmp (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oExtC G oIrr lF F1) G
               (oWknC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oWknC G oIrr lF F1))
         F1 F1s ->
    WkTm (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) G
         (oCmp (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oExtC G oIrr lF F1) G
               (oWknC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oWknC G oIrr lF F1))
         F2 F2s ->
    WkTm (oExtC (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF F1s)
         (oExtC G oIrr lF F1)
         (oLiftC (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) G
            (oCmp (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
                  (oExtC G oIrr lF F1) G
                  (oWknC (oExtC G oIrr lF F1) oIrr lF F2w)
                  (oWknC G oIrr lF F1))
            oIrr lF F1 F1s)
         B1 B1y ->
    WkTm (oExtC (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF F2s)
         (oExtC G oIrr lF F2)
         (oLiftC (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) G
            (oCmp (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
                  (oExtC G oIrr lF F1) G
                  (oWknC (oExtC G oIrr lF F1) oIrr lF F2w)
                  (oWknC G oIrr lF F1))
            oIrr lF F2 F2s)
         B2 B2y ->
    WkTm (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) G
         (oCmp (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oExtC G oIrr lF F1) G
               (oWknC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oWknC G oIrr lF F1))
         (oLamRel G oIrr lF l F1 B1 tf) fy ->
    WkTm (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) G
         (oCmp (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oExtC G oIrr lF F1) G
               (oWknC (oExtC G oIrr lF F1) oIrr lF F2w)
               (oWknC G oIrr lF F1))
         (oLamRel G oIrr lF l F2 B2 tg) gy ->
    AppV (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF l F1s B1y fy oStar r1 ->
    AppV (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF l F2s B2y gy oStar r2 ->
    InstTm (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
           (oExtC (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF F1s)
           (oInst (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF F1s oStar)
           B1y cod1 ->
    InstTm (oExtC (oExtC G oIrr lF F1) oIrr lF F2w)
           (oExtC (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF F2s)
           (oInst (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) oIrr lF F2s oStar)
           B2y cod2 ->
    IdV (oExtC (oExtC G oIrr lF F1) oIrr lF F2w) l cod1 cod2 r1 r2 bodyv ->
    IdV G l (oPiRel G oIrr lF l F1 B1) (oPiRel G oIrr lF l F2 B2)
        (oLamRel G oIrr lF l F1 B1 tf) (oLamRel G oIrr lF l F2 B2 tg)
        (oPiIrr G oIrr lF F1
           (oPiIrr (oExtC G oIrr lF F1) oIrr lF F2w bodyv)).

Scheme InstTy_min := Minimality for InstTy Sort Prop
  with InstTm_min := Minimality for InstTm Sort Prop
  with InstVar_min := Minimality for InstVar Sort Prop
  with AppV_min := Minimality for AppV Sort Prop
  with IdV_min := Minimality for IdV Sort Prop.

Combined Scheme Inst_mutind from
  InstTy_min, InstTm_min, InstVar_min, AppV_min, IdV_min.

(* ================================================================== *)
(* DETERMINISM -- design.md section 13b's property (D)                 *)
(* ================================================================== *)

(* The argument is the one WkRel.v's [Wk_det] runs, with two additions.
   (1) The [WkTm] premises carry no induction hypothesis -- WkRel is a
   CLOSED block below this one -- so they are discharged by [WkTm_det]
   explicitly rather than by an IH.  (2) The tables have clauses that
   agree on their subject's head and are separated only by a neutrality
   premise; those are killed by the five refutation lemmas
   ([NeCode_not_nat], [NeCode_not_pi_rel], [ValNe_not_zero],
   [ValNe_not_suc], [ValNe_not_lam_rel]).

   TOTALITY IS NOT ATTEMPTED and does not belong here: it is design.md
   section 13b's property (T), it is what the model proves, and it is
   where the lexicographic measure that this relational presentation
   avoids comes back (section 14k). *)

Theorem Inst_det :
  (forall D G g i A A', InstTy D G g i A A' ->
     forall A2, InstTy D G g i A A2 -> A' = A2)
  /\ (forall D G g e e', InstTm D G g e e' ->
     forall e2, InstTm D G g e e2 -> e' = e2)
  /\ (forall D G g x x', InstVar D G g x x' ->
     forall x2, InstVar D G g x x2 -> x' = x2)
  /\ (forall G rF lF lG F B f a r, AppV G rF lF lG F B f a r ->
     forall r2, AppV G rF lF lG F B f a r2 -> r = r2)
  /\ (forall G l A B t u c, IdV G l A B t u c ->
     forall c2, IdV G l A B t u c2 -> c = c2).
Proof.
  apply Inst_mutind; intros;
    (* (1) Drop the clause's OWN premises, so that the second derivation's
       premises are the only ones an induction hypothesis can consume. *)
    repeat match goal with
    | Hp : InstTy ?D ?G ?g ?i ?A ?X,
      _ : forall z, InstTy ?D ?G ?g ?i ?A z -> ?X = z |- _ => clear Hp
    | Hp : InstTm ?D ?G ?g ?e ?X,
      _ : forall z, InstTm ?D ?G ?g ?e z -> ?X = z |- _ => clear Hp
    | Hp : InstVar ?D ?G ?g ?x ?X,
      _ : forall z, InstVar ?D ?G ?g ?x z -> ?X = z |- _ => clear Hp
    | Hp : AppV ?G ?rF ?lF ?lG ?F ?B ?f ?a ?X,
      _ : forall z, AppV ?G ?rF ?lF ?lG ?F ?B ?f ?a z -> ?X = z |- _ => clear Hp
    | Hp : IdV ?G ?l ?A ?B ?t ?u ?X,
      _ : forall z, IdV ?G ?l ?A ?B ?t ?u z -> ?X = z |- _ => clear Hp
    end;
    (* (2) Invert the second derivation.  Every judgement is head-directed
       -- in the subject for [InstTy]/[InstTm], in the substitution and
       then the subject for [InstVar], in the function for [AppV], and in
       the two codes and then the endpoints for [IdV]. *)
    match goal with
    | H : InstTy _ _ _ _ _ ?X |- _ = ?X => inversion H; subst
    | H : InstTm _ _ _ _ ?X |- _ = ?X => inversion H; subst
    | H : InstVar _ _ _ _ ?X |- _ = ?X => inversion H; subst
    | H : AppV _ _ _ _ _ _ _ _ ?X |- _ = ?X => inversion H; subst
    | H : IdV _ _ _ _ _ _ ?X |- _ = ?X => inversion H; subst
    end;
    (* (3) Kill the clause pairs that agree on the head and are separated
       only by neutrality. *)
    try match goal with
    | H : NeCode _ _ _ _ (oNat _) |- _ => destruct (NeCode_not_nat H)
    | H : NeCode _ _ _ _ (oPiRel _ _ _ _ _ _) |- _ =>
        destruct (NeCode_not_pi_rel H)
    | H : ValNe _ _ _ _ (oZero _) |- _ => destruct (ValNe_not_zero H)
    | H : ValNe _ _ _ _ (oSuc _ _) |- _ => destruct (ValNe_not_suc H)
    | H : ValNe _ _ _ _ (oLamRel _ _ _ _ _ _ _) |- _ =>
        destruct (ValNe_not_lam_rel H)
    end;
    (* (4) Feed the surviving premises to the induction hypotheses, and the
       [WkTm] ones to [WkTm_det]. *)
    repeat first
    [ match goal with
      | IH : forall z, InstTy ?D ?G ?g ?i ?A z -> _,
        H : InstTy ?D ?G ?g ?i ?A _ |- _ => specialize (IH _ H); subst
      | IH : forall z, InstTm ?D ?G ?g ?e z -> _,
        H : InstTm ?D ?G ?g ?e _ |- _ => specialize (IH _ H); subst
      | IH : forall z, InstVar ?D ?G ?g ?x z -> _,
        H : InstVar ?D ?G ?g ?x _ |- _ => specialize (IH _ H); subst
      | IH : forall z, AppV ?G ?rF ?lF ?lG ?F ?B ?f ?a z -> _,
        H : AppV ?G ?rF ?lF ?lG ?F ?B ?f ?a _ |- _ => specialize (IH _ H); subst
      | IH : forall z, IdV ?G ?l ?A ?B ?t ?u z -> _,
        H : IdV ?G ?l ?A ?B ?t ?u _ |- _ => specialize (IH _ H); subst
      end
    | match goal with
      | H1 : WkTm ?D ?G ?w ?e ?X, H2 : WkTm ?D ?G ?w ?e ?Y |- _ =>
          assert_fails (constr_eq X Y);
          let Heq := fresh "Hwk" in
          pose proof (WkTm_det H1 H2) as Heq; subst
      end ];
    auto.
Qed.

(* ================================================================== *)
(* THE TABLE IS COMPLETE -- the shape analysis its clauses cover       *)
(* ================================================================== *)

(* Determinism does NOT witness completeness: a table with a case missing
   is still deterministic, and the omission would surface only much later,
   as an unprovable totality obligation.  These two lemmas close that gap
   at the only place it is open, by exhibiting the case analysis the
   clauses were written against and showing it is exhaustive.  The third
   axis -- the endpoints at [Nat]/[Nat] -- needs nothing new: it is
   Values.v's [Val_nat_shape] verbatim, three-way into [zero] / [suc] /
   neutral, matched by [idv_nat_00] / [idv_nat_0S] / [idv_nat_S0] /
   [idv_nat_SS] / [idv_nat_ne_l] / [idv_nat_ne_r]. *)

Local Ltac pick := split; [ reflexivity | ].

(* AXIS 1: the two codes, six ways.  This is [ValCode_rel_shape] squared,
   and the six disjuncts are, in order, [idv_ne_l], [idv_ne_r], the
   [Nat]/[Nat] block, [idv_nat_pi], [idv_pi_nat], and the [Pi_rel] block.
   Note the [l = oL0] that comes free with every [Nat]: it is why
   [idv_nat_pi] and [idv_pi_nat] can pin the [Pi_rel]'s own [lG] to [L0]
   without loss, matching "Id-Nat-Pi"/"Id-Pi-Nat" as compiled. *)
Lemma IdV_code_cases G l A B
  : ValCode instC G oRel l A -> ValCode instC G oRel l B ->
    NeCode instC G oRel l A
    \/ NeCode instC G oRel l B
    \/ (l = oL0 /\ A = oNat G /\ B = oNat G)
    \/ (l = oL0 /\ A = oNat G
        /\ exists rF lF F0 B0, B = oPiRel G rF lF oL0 F0 B0)
    \/ (l = oL0 /\ B = oNat G
        /\ exists rF lF F0 B0, A = oPiRel G rF lF oL0 F0 B0)
    \/ (exists rF1 lF1 F1 B1' rF2 lF2 F2 B2',
           A = oPiRel G rF1 lF1 l F1 B1'
           /\ B = oPiRel G rF2 lF2 l F2 B2').
Proof.
  intros HA HB.
  destruct (ValCode_rel_shape HA)
    as [[HlA HA']|[[rF1 [lF1 [F1 [B1' HA']]]]|HneA]]; [ | | now left ].
  - subst.
    destruct (ValCode_rel_shape HB)
      as [[HlB HB']|[[rF2 [lF2 [F2 [B2' HB']]]]|HneB]]; [ | | now right; left ].
    + subst. do 2 right; left; pick; pick; reflexivity.
    + subst. do 3 right; left; pick; pick.
      exists rF2, lF2, F2, B2'; reflexivity.
  - destruct (ValCode_rel_shape HB)
      as [[HlB HB']|[[rF2 [lF2 [F2 [B2' HB']]]]|HneB]]; [ | | now right; left ].
    + subst. do 4 right; left; pick; pick.
      exists rF1, lF1, F1, B1'; reflexivity.
    + subst. do 5 right.
      exists rF1, lF1, F1, B1', rF2, lF2, F2, B2'; pick; reflexivity.
Qed.

(* AXIS 2: two [Pi_rel]s, five ways in their DOMAIN INDICES.  The four
   clash clauses plus funext, and the reason no restructuring of the
   language's rules was needed: they already partition.  [RelNf]/[LvlNf]
   are what make the enumeration finite -- [relevance] and [lvl] are rigid
   two-constructor sorts (Syntax.v). *)
Lemma IdV_pi_index_cases rF1 lF1 rF2 lF2
  : RelNf rF1 -> LvlNf lF1 -> RelNf rF2 -> LvlNf lF2 ->
    (rF1 = oRel /\ rF2 = oIrr)                     (* idv_pi_pi_rel_irr *)
    \/ (rF1 = oIrr /\ rF2 = oRel)                  (* idv_pi_pi_irr_rel *)
    \/ (rF1 = rF2 /\ lF1 = oL0 /\ lF2 = oL1)       (* idv_pi_pi_L0_L1   *)
    \/ (rF1 = rF2 /\ lF1 = oL1 /\ lF2 = oL0)       (* idv_pi_pi_L1_L0   *)
    \/ (rF1 = rF2 /\ lF1 = lF2).                   (* the two funexts   *)
Proof.
  intros [] [] [] [];
    first [ solve [ left; repeat split; reflexivity ]
          | solve [ right; left; repeat split; reflexivity ]
          | solve [ do 2 right; left; repeat split; reflexivity ]
          | solve [ do 3 right; left; repeat split; reflexivity ]
          | solve [ do 4 right; repeat split; reflexivity ] ].
Qed.

Definition InstTy_det := proj1 Inst_det.
Definition InstTm_det := proj1 (proj2 Inst_det).
Definition InstVar_det := proj1 (proj2 (proj2 Inst_det)).
Definition AppV_det := proj1 (proj2 (proj2 (proj2 Inst_det))).
Definition IdV_det := proj2 (proj2 (proj2 (proj2 Inst_det))).

End WithInstC.
