(* Prototype 3 (staged reference -> concrete development): the OTT-CONCRETE
   Kripke RedTy for src/.../Pi/LogicalRelation.v.

   DESIGN (decided 2026-06-07u): the generic act/cod/mapp : term->term->term
   interface in the committed LogicalRelation.v RedTyDef is TOO THIN -- OTT
   explicit substitutions carry full type annotations (exp_subst needs the code's
   U-type and info, the source/target envs, and the relevance/level), all of
   which live only inside the Pi telescope.  So we go OTT-CONCRETE (option b):
   inline the builders, carry rF/lF/lG/F/C/F'/C' in rtt_pi.

   CON-ARG ORDERS verified empirically against the built Base/Pi/Nat .vo
   (2026-06-07; WIP/ProbeSubst.v).  KEY CORRECTION vs the prior staged file and
   memory ott-con-arg-orders: snoc = [v; g; A; i; G'; G] (the underlying subst g
   is at index 1, NOT index 3).  cmp = [g; f; G3; G2; G1].

   Correctness of the codomain `under'` lift (direction + annotations) is only
   checkable once the OTT subst lemmas + wf_lang are in scope -- DEFERRED to
   file 4 (FundamentalLemma).  This file lands the DEFINITION green + axiom-free. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral LogicalRelation.
Import Core.Notations.
Open Scope string.

Notation tm := (@Term.term string).
Notation sort := (@Term.sort string).

(* OTT principal-argument selector (verified indices). *)
Definition ott_pa (n : string) : option nat :=
  if eqb n "app_rel" then Some 1
  else if eqb n "app_irr" then Some 1
  else if eqb n "Emptyrec" then Some 0
  else if eqb n "exp_subst" then Some 0
  else if eqb n "ty_subst" then Some 0
  else None.

(* ====================================================================== *)
(* OTT term builders (verified con-arg orders).                            *)
(* ====================================================================== *)

(* ---- info / universe / decode ---- *)
Definition orel : tm := con "rel" [].
Definition oirr : tm := con "irr" [].
Definition oL0  : tm := con "L0" [].
Definition onext (l : tm) : tm := con "next" [l].
Definition oiota (l : tm) : tm := con "iota" [l].
(* info args = [l; r]  (e.g. #"info" #"rel" (#"next" lF) = con "info" [next lF; rel]) *)
Definition oinfo (r l : tm) : tm := con "info" [l; r].
(* U args = [l; r; G]   El args = [e; l; r; G] *)
Definition oU (r l G : tm) : tm := con "U" [l; r; G].
Definition oEl (r l G e : tm) : tm := con "El" [e; l; r; G].

(* a CODE F : exp G (info rel (next l)) (U r l) has info [rel,next l]. *)
Definition code_info (l : tm) : tm := oinfo orel (onext l).
(* a TERM a : El F  (F a code in U r l) has info [r, iota l]. *)
Definition term_info (r l : tm) : tm := oinfo r (oiota l).

(* ---- substitution calculus (parameterized over tyinfo i) ---- *)
Definition oid (G : tm) : tm := con "id" [G].
Definition oext (A i G : tm) : tm := con "ext" [A; i; G].
Definition owkn (A i G : tm) : tm := con "wkn" [A; i; G].
Definition ohd  (A i G : tm) : tm := con "hd"  [A; i; G].
(* cmp X Y : sub G1 G3   with X(=g) : sub G2 G3, Y(=f) : sub G1 G2. *)
Definition ocmp (g f G3 G2 G1 : tm) : tm := con "cmp" [g; f; G3; G2; G1].
(* exp_subst v A i g G' G : v : exp G' i A, g : sub G G' -> exp G i A[g].
   So G' is the SOURCE env (where v lives), G is the TARGET env. *)
Definition oexp_subst (v A i g G' G : tm) : tm :=
  con "exp_subst" [v; A; i; g; G'; G].
(* snoc v g A i G' G : extends g : sub G G' by v : exp G i A[g]
   to snoc : sub G (ext G' i A).  CORRECTED order [v; g; A; i; G'; G]. *)
Definition osnoc (v g A i G' G : tm) : tm := con "snoc" [v; g; A; i; G'; G].

(* ---- type/term formers ---- *)
Definition oNat (G : tm) : tm := con "Nat" [G].
Definition oEmpty (G : tm) : tm := con "Empty" [G].
Definition ozero (G : tm) : tm := con "zero" [G].
Definition osuc (G n : tm) : tm := con "suc" [n; G].
Definition oPi_rel (rF lF lG F C G : tm) : tm := con "Pi_rel" [C; F; lG; lF; rF; G].
Definition oapp_rel (rF lF lG F C f a G : tm) : tm :=
  con "app_rel" [a; f; C; F; lG; lF; rF; G].

(* ====================================================================== *)
(* The Kripke operations, OTT-concrete.  All take the Pi telescope         *)
(* (rF lF lG) plus the home/future envs (G/D), the object subst g, and the  *)
(* domain/codomain codes (F/C) as explicit arguments.                       *)
(* ====================================================================== *)

(* push the domain code F : exp G (code_info lF)(U rF lF) along g : sub D G,
   landing in env D. *)
Definition act_code (rF lF g G D F : tm) : tm :=
  oexp_subst F (oU rF lF G) (code_info lF) g G D.

(* the domain binder info (info of an element of El F). *)
Definition dom_info (rF lF : tm) : tm := term_info rF lF.

(* extend env D by the (decoded) pushed domain code. *)
Definition extc (rF lF g G D F : tm) : tm :=
  oext (oEl rF lF D (act_code rF lF g G D F)) (dom_info rF lF) D.

(* push the function member f : exp G (info rel (iota lG)) (El (Pi_rel ..))
   along g : sub D G. *)
Definition act_member (rF lF lG g G D F C f : tm) : tm :=
  oexp_subst f
    (oEl orel lG G (oPi_rel rF lF lG F C G))
    (term_info orel lG)
    g G D.

(* under' g : lift g : sub D G over the domain binder, landing
   : sub (extc .. D ..) (ext G (info) (El F)). *)
Definition ounder (rF lF g G D F : tm) : tm :=
  let iF    := dom_info rF lF in
  let actF  := act_code rF lF g G D F in
  let ElaF  := oEl rF lF D actF in
  let extD  := oext ElaF iF D in
  let wknD  := owkn ElaF iF D in
  let g0    := ocmp g wknD G D extD in   (* sub extD G *)
  let hdD   := ohd ElaF iF D in
  osnoc hdD g0 (oEl rF lF G F) iF G extD. (* sub extD (ext G iF (El F)) *)

(* push the codomain code C : exp (ext G (El F)) (code_info lG)(U rel lG)
   along under' g, landing in env (extc .. D ..). *)
Definition act_cod (rF lF lG g G D F C : tm) : tm :=
  let iF   := dom_info rF lF in
  let extG := oext (oEl rF lF G F) iF G in
  let extD := extc rF lF g G D F in
  oexp_subst C (oU orel lG extG) (code_info lG) (ounder rF lF g G D F) extG extD.

(* the pushed codomain code instantiated at argument a : exp D .. (El (act F)). *)
Definition cod_at (rF lF lG g G D F C a : tm) : tm :=
  let iF      := dom_info rF lF in
  let actF    := act_code rF lF g G D F in
  let ElaF    := oEl rF lF D actF in
  let extD    := extc rF lF g G D F in
  let snoc_a  := osnoc a (oid D) ElaF iF D D in   (* sub D extD *)
  oexp_subst (act_cod rF lF lG g G D F C) (oU orel lG extD) (code_info lG)
    snoc_a extD D.

(* member application at env D : (act_member f) applied to a. *)
Definition mapp (rF lF lG g G D F C f a : tm) : tm :=
  oapp_rel rF lF lG
    (act_code rF lF g G D F)
    (act_cod rF lF lG g G D F C)
    (act_member rF lF lG g G D F C f)
    a D.

(* ====================================================================== *)
(* Recognizers + base member relations, over an abstract wf lang `l`.       *)
(* ====================================================================== *)
Section Concrete.
  Context (l : Rule.lang string) (wfl : wf_lang l).

  Notation reds   := (reds string l ott_pa).
  Notation neutral := (neutral ott_pa).
  Notation ne_eq  := (ne_eq string l ott_pa).

  (* A reduces to the Nat code in env G. *)
  Definition RNat (G A : tm) : Prop := reds A (oNat G).
  (* object substitution g : sub D G  (home G, future D). *)
  Definition osub (G D g : tm) : Prop := wf_term l [] g (scon "sub" [G; D]).

  (* the sort of Nat-typed elements in env G. *)
  Definition nat_sort (G : tm) : sort :=
    scon "exp" [oEl orel oL0 G (oNat G); term_info orel oL0; G].

  (* ---- base member relations ---- *)

  (* Neutral-code members: compared by ne_eq at the carried sort. *)
  Inductive RedNe (t : sort) (a b : tm) : Type :=
  | red_ne : ne_eq t a b -> RedNe t a b.

  (* Nat members: zero/suc congruence + stuck neutrals. *)
  Inductive RedNatMem (G : tm) : tm -> tm -> Type :=
  | rnm_zero : forall a b,
      reds a (ozero G) -> reds b (ozero G) -> RedNatMem G a b
  | rnm_suc  : forall a b a' b',
      reds a (osuc G a') -> reds b (osuc G b') ->
      RedNatMem G a' b' -> RedNatMem G a b
  | rnm_ne   : forall a b na nb,
      reds a na -> reds b nb -> ne_eq (nat_sort G) na nb -> RedNatMem G a b.

  (* Kripke Pi member relation: t,u related at home G iff under every object
     subst g : sub D G and every domain-related (a,a') the applications are
     codomain-related. *)
  Inductive RedAtPi
    (rF lF lG G F C F' C' : tm)
    (RDom : forall D g, osub G D g -> tm -> tm -> Type)
    (RCod : forall D g (os : osub G D g) a a',
        RDom D g os a a' -> tm -> tm -> Type)
    (t u : tm) : Type :=
  | at_pi_app :
      (forall D g (os : osub G D g) a a' (raa' : RDom D g os a a'),
          RCod D g os a a' raa'
            (mapp rF lF lG g G D F C t a)
            (mapp rF lF lG g G D F' C' u a'))
      -> RedAtPi rF lF lG G F C F' C' RDom RCod t u.

  (* ---- the type-code logical relation ---- *)
  Inductive RedTy_tot
    : tm -> tm -> tm -> (tm -> tm -> Type) -> Type :=
  | rtt_nat : forall G A B,
      RNat G A -> RNat G B -> RedTy_tot G A B (RedNatMem G)
  | rtt_ne : forall G A B na nb (t : sort),
      reds A na -> reds B nb -> ne_eq t na nb ->
      RedTy_tot G A B (RedNe t)
  | rtt_pi : forall G A B rF lF lG F C F' C',
      reds A (oPi_rel rF lF lG F C G) ->
      reds B (oPi_rel rF lF lG F' C' G) ->
      forall (RDom : forall D g, osub G D g -> tm -> tm -> Type)
             (DomRed : forall D g (os : osub G D g),
                 RedTy_tot D (act_code rF lF g G D F)
                             (act_code rF lF g G D F')
                             (RDom D g os))
             (RCod : forall D g (os : osub G D g) a a',
                 RDom D g os a a' -> tm -> tm -> Type)
             (CodRed : forall D g (os : osub G D g) a a'
                              (raa' : RDom D g os a a'),
                 RedTy_tot (extc rF lF g G D F)
                   (cod_at rF lF lG g G D F C a)
                   (cod_at rF lF lG g G D F' C' a')
                   (RCod D g os a a' raa')),
      RedTy_tot G A B (RedAtPi rF lF lG G F C F' C' RDom RCod).

  (* Sig packaging: the member relation is the first projection. *)
  Definition RedTy (G A B : tm) : Type :=
    { R : tm -> tm -> Type & RedTy_tot G A B R }.
  Definition RedTy_R {G A B} (r : RedTy G A B) : tm -> tm -> Type := projT1 r.
  Definition RedTm {G A B} (r : RedTy G A B) (t u : tm) : Type := RedTy_R r t u.

  (* Smart constructors. *)
  Definition RedTy_nat {G A B} (ra : RNat G A) (rb : RNat G B) : RedTy G A B :=
    existT _ _ (rtt_nat G A B ra rb).

  Definition RedTy_ne {G A B} na nb t
    (ra : reds A na) (rb : reds B nb) (h : ne_eq t na nb) : RedTy G A B :=
    existT _ _ (rtt_ne G A B na nb t ra rb h).

  Definition RedTy_pi {G A B rF lF lG F C F' C'}
    (hA : reds A (oPi_rel rF lF lG F C G))
    (hB : reds B (oPi_rel rF lF lG F' C' G))
    (DomRed : forall D g (os : osub G D g),
        RedTy D (act_code rF lF g G D F) (act_code rF lF g G D F'))
    (CodRed : forall D g (os : osub G D g) a a',
        RedTm (DomRed D g os) a a' ->
        RedTy (extc rF lF g G D F)
          (cod_at rF lF lG g G D F C a)
          (cod_at rF lF lG g G D F' C' a'))
    : RedTy G A B.
  Proof.
    unshelve eexists.
    - exact (RedAtPi rF lF lG G F C F' C'
               (fun D g os => RedTy_R (DomRed D g os))
               (fun D g os a a' raa' => RedTy_R (CodRed D g os a a' raa'))).
    - eapply rtt_pi; try eassumption.
      + intros D g os. exact (projT2 (DomRed D g os)).
      + intros D g os a a' raa'. exact (projT2 (CodRed D g os a a' raa')).
  Defined.

  (* Custom eliminator threading the Kripke domain + codomain IHs. *)
  Theorem RedTy_rect
    (P : forall G A B, RedTy G A B -> Type)
    (Hnat : forall G A B (ra : RNat G A) (rb : RNat G B),
        P G A B (RedTy_nat ra rb))
    (Hne : forall G A B na nb t (ra : reds A na) (rb : reds B nb)
                  (h : ne_eq t na nb),
        P G A B (RedTy_ne na nb t ra rb h))
    (Hpi : forall G A B rF lF lG F C F' C'
             (hA : reds A (oPi_rel rF lF lG F C G))
             (hB : reds B (oPi_rel rF lF lG F' C' G))
             (DomRed : forall D g (os : osub G D g),
                 RedTy D (act_code rF lF g G D F) (act_code rF lF g G D F'))
             (CodRed : forall D g (os : osub G D g) a a',
                 RedTm (DomRed D g os) a a' ->
                 RedTy (extc rF lF g G D F)
                   (cod_at rF lF lG g G D F C a)
                   (cod_at rF lF lG g G D F' C' a')),
          (forall D g (os : osub G D g), P D _ _ (DomRed D g os)) ->
          (forall D g (os : osub G D g) a a'
                  (raa' : RedTm (DomRed D g os) a a'),
              P _ _ _ (CodRed D g os a a' raa')) ->
          P G A B (RedTy_pi hA hB DomRed CodRed))
    : forall G A B (r : RedTy G A B), P G A B r.
  Proof.
    intros G A B [R r].
    induction r as [ G A B ra rb
                   | G A B na nb t ra rb h
                   | G A B rF lF lG F C F' C' hA hB
                     RDom DomRed IHDom RCod CodRed IHCod ].
    - apply Hnat.
    - apply Hne.
    - apply (Hpi G A B rF lF lG F C F' C' hA hB
               (fun D g os => existT _ (RDom D g os) (DomRed D g os))
               (fun D g os a a' raa' =>
                  existT _ (RCod D g os a a' raa') (CodRed D g os a a' raa'))).
      + intros D g os. exact (IHDom D g os).
      + intros D g os a a' raa'. exact (IHCod D g os a a' raa').
  Defined.

End Concrete.
