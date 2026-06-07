(* ====================================================================== *)
(* OTT pivot, file 3/5 (see WIP/NEXT_SESSION.md UPDATE-n .. -r).            *)
(*                                                                        *)
(* The reduction-on-syntax LOGICAL RELATION over CLOSED Pyrosome terms      *)
(* (Pyrosome ctx = []; object open-ness lives in the `env` carried by the   *)
(* sort).  This file builds the FOUNDATION shared by every variant of the   *)
(* relation, then the reducibility relation itself.                        *)
(*                                                                        *)
(* FOUNDATION (this file, lower half) — generic over `wf_lang l` and a      *)
(* principal-argument selector `pa`:                                       *)
(*   - `reds a b`     : `a` weak-head reduces (via `star whstep`) to the    *)
(*                      whnf `b`.  This is the Pyrosome-native analog of     *)
(*                      metamltt's `WfRedTy`/`WfRedTm` records, EXCEPT we    *)
(*                      do not bake in a deterministic normalizer: the whnf  *)
(*                      reached is carried existentially and SOUNDNESS comes *)
(*                      for free from `star_whstep_sound` (reduction ⊆       *)
(*                      eq_term).  Where metamltt needs `whnf_det`, we will  *)
(*                      instead use Pyrosome constructor INJECTIVITY on the  *)
(*                      common reduct (the two whnfs of one term are         *)
(*                      eq_term-equal, hence same head by sort/term          *)
(*                      injectivity), so confluence of `whstep` is never     *)
(*                      required.                                           *)
(*   - `ne_eq t a b` : `a` and `b` are NEUTRAL and `eq_term`-equal at sort   *)
(*                      `t`.  This resolves UPDATE-n's open design Q2: the   *)
(*                      pivot makes `eq_term` THE declarative equality, so   *)
(*                      neutral members are compared by `eq_term` + a        *)
(*                      "both stuck" gate, NOT by a separate `~ne`           *)
(*                      inductive (metamltt needs `~ne` only because its     *)
(*                      `≡` is declarative-only; here `eq_term` already IS    *)
(*                      declarative).                                       *)
(*                                                                        *)
(* DESIGN NOTE for the reducibility relation (built on top): OTT's Tarski    *)
(* universe has NO universe CODE (`U` is a `ty`, never an `exp`), so type    *)
(* codes are only `Nat`/`Empty`/`Pi_*`/neutrals — the impredicative         *)
(* recursion that forces metamltt's Small/Large tower is ABSENT, and the     *)
(* type-LR is a single plain inductive.  "Under a Pi binder" extends the     *)
(* object env `G` (a term-level op), so the Kripke quantification is over    *)
(* object substitutions, not Pyrosome renamings.                           *)
(* ====================================================================== *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral.
Import Core.Notations.

(* Transitivity of the reflexive-transitive closure (OperationalBridge's `star`
   is right-recursive, so this is by induction on the SECOND reduction). *)
Lemma star_trans {A} (R : A -> A -> Prop) a b c
  : star R a b -> star R b c -> star R a c.
Proof.
  induction 2; eauto using star_step.
Qed.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Section WithLang.
    Context (l : lang) (wfl : wf_lang l).
    Context (pa : V -> option nat).
    (* head of the CwF bound-variable projection; instantiated with "hd". *)
    Context (hd_name : V).

    Notation whstep := (whstep V l pa).
    Notation whnf := (whnf pa hd_name).
    Notation neutral := (neutral pa hd_name).

    (* ------------------------------------------------------------------ *)
    (* Reduction to weak-head normal form.                                 *)
    (* `reds a b` := `a` weak-head reduces to the whnf `b`.  Sort-erased    *)
    (* (so it can be reused at every sort head); the sort at which the      *)
    (* equation `a = b` holds is supplied separately to `reds_sound`.      *)
    (* ------------------------------------------------------------------ *)
    Definition reds (a b : term) : Prop :=
      star whstep a b /\ whnf b.

    Lemma reds_star a b : reds a b -> star whstep a b.
    Proof. intros [H _]; exact H. Qed.

    Lemma reds_whnf a b : reds a b -> whnf b.
    Proof. intros [_ H]; exact H. Qed.

    (* A whnf reduces (in zero steps) to itself. *)
    Lemma reds_refl a : whnf a -> reds a a.
    Proof. intro H; split; [ constructor | exact H ]. Qed.

    (* Soundness: a reduction-to-whnf is an `eq_term` at any sort at which
       the source is well typed (reduction ⊆ eq_term, for free). *)
    Lemma reds_sound a b t
      : wf_term l [] a t -> reds a b -> eq_term l [] t a b.
    Proof.
      intros Hwf [Hstar _].
      eapply star_whstep_sound; eauto.
    Qed.

    (* Subject reduction for reduction-to-whnf. *)
    Lemma reds_wf a b t
      : wf_term l [] a t -> reds a b -> wf_term l [] b t.
    Proof.
      intros Hwf [Hstar _].
      eapply star_whstep_wf; eauto.
    Qed.

    (* Determinism UP TO CONVERSION: the two whnfs reached from one well-typed
       term are `eq_term`-equal.  This is the Pyrosome-native replacement for
       metamltt's syntactic `whnf_det` — it needs only soundness (reduction ⊆
       eq_term), never confluence of `whstep`.  The LR inversions that metamltt
       does by `whnf_det` we do by combining this with sort/term constructor
       INJECTIVITY on `b1 = b2` (up to eq_term). *)
    Lemma reds_eq a b1 b2 t
      : wf_term l [] a t -> reds a b1 -> reds a b2 -> eq_term l [] t b1 b2.
    Proof.
      intros Hwf Hr1 Hr2.
      eapply eq_term_trans.
      - eapply eq_term_sym; eapply reds_sound; eauto.
      - eapply reds_sound; eauto.
    Qed.

    (* ------------------------------------------------------------------ *)
    (* Neutral equality.  Two terms are "neutral-equal" at sort `t` when    *)
    (* both are stuck (neutral) and they are `eq_term`-equal.  This is the   *)
    (* base PER carried by the Ne case of the LR (cf. metamltt `~ne`, but    *)
    (* delegated to the project's existing declarative equality).           *)
    (* ------------------------------------------------------------------ *)
    Definition ne_eq (t : sort) (a b : term) : Prop :=
      neutral a /\ neutral b /\ eq_term l [] t a b.

    Lemma ne_eq_l t a b : ne_eq t a b -> neutral a.
    Proof. intros (H & _ & _); exact H. Qed.

    Lemma ne_eq_r t a b : ne_eq t a b -> neutral b.
    Proof. intros (_ & H & _); exact H. Qed.

    Lemma ne_eq_conv t a b : ne_eq t a b -> eq_term l [] t a b.
    Proof. intros (_ & _ & H); exact H. Qed.

    (* `ne_eq` is symmetric and transitive (a PER), inheriting both from
       `eq_term`; reflexivity holds for any well-typed neutral. *)
    Lemma ne_eq_sym t a b : ne_eq t a b -> ne_eq t b a.
    Proof.
      intros (Ha & Hb & Hc); repeat split; eauto using eq_term_sym with lang_core.
    Qed.

    Lemma ne_eq_trans t a b c : ne_eq t a b -> ne_eq t b c -> ne_eq t a c.
    Proof.
      intros (Ha & Hb & Hab) (Hb' & Hc & Hbc); repeat split;
        eauto using eq_term_trans with lang_core.
    Qed.

    Lemma ne_eq_refl t a : neutral a -> wf_term l [] a t -> ne_eq t a a.
    Proof.
      intros Hn Hwf; repeat split; eauto using eq_term_refl with lang_core.
    Qed.

    (* Backward (anti-) reduction at the level of `reds`: prepending a
       weak-head reduction prefix `a ↝* b` to a reduction-to-whnf `b ↝* c`
       (with `c` a whnf) yields a reduction-to-whnf `a ↝* c`.  This is the
       reduction-side ingredient of the LR's anti-reduction closure. *)
    Lemma reds_back a b c : star whstep a b -> reds b c -> reds a c.
    Proof.
      intros Hab [Hbc Hc]; split; [ eapply star_trans; eassumption | exact Hc ].
    Qed.

  End WithLang.

End WithVar.

(* ====================================================================== *)
(* The reducibility logical relation over TYPE CODES, OTT-CONCRETE.        *)
(*                                                                        *)
(* A SINGLE plain inductive `RedTy_tot` carrying the member relation as an  *)
(* OUTPUT index (the Sig trick), so no Small/Large universe tower and no    *)
(* LogRel2-style PolyRedPack + adequacy split is needed.  The Pi case is    *)
(* KRIPKE from the start: domain/codomain reducibility is quantified over   *)
(* every object substitution `g : osub G D` into a future env `D`.         *)
(*                                                                        *)
(* DESIGN (NEXT_SESSION UPDATE-u): the abstract `act/cod/mapp` interface    *)
(* (term->term->term) is TOO THIN -- OTT explicit substitutions carry full  *)
(* type annotations (exp_subst needs the code's U-type and info, the        *)
(* source/target envs and the relevance/level), all of which live only in   *)
(* the Pi telescope.  So this is OTT-CONCRETE: the builders are inlined and  *)
(* rF/lF/lG/F/C/F'/C' are carried in `rtt_pi`.  Everything is at Pyrosome   *)
(* ctx = []; the object env `G : tm` (sort `env`) carries object openness.  *)
(*                                                                        *)
(* CON-ARG ORDERS verified against the built Base/Pi/Nat .vo               *)
(* (WIP/ProbeSubst.v).  KEY: snoc = [v; g; A; i; G'; G] (subst g at idx 1); *)
(* cmp = [g; f; G3; G2; G1]; exp_subst = [v; A; i; g; G'(src); G(tgt)].     *)
(*                                                                        *)
(* CORRECTNESS of the codomain `under'` lift (direction + annotations) is   *)
(* only checkable once the OTT subst lemmas + wf_lang are in scope --       *)
(* DEFERRED to file 4 (FundamentalLemma).  This lands the DEFINITION.       *)
(* ====================================================================== *)
Notation tm := (@Term.term string).
Notation osort := (@Term.sort string).

Open Scope string.

(* OTT principal-argument selector (verified indices). *)
Definition ott_pa (n : string) : option nat :=
  if eqb n "app_rel" then Some 1
  else if eqb n "app_irr" then Some 1
  else if eqb n "Emptyrec" then Some 0
  else if eqb n "exp_subst" then Some 0
  else if eqb n "ty_subst" then Some 0
  else None.

(* ---- OTT term builders (verified con-arg orders) ---- *)
(* info / universe / decode *)
Definition orel : tm := con "rel" [].
Definition oirr : tm := con "irr" [].
Definition oL0  : tm := con "L0" [].
Definition onext (l : tm) : tm := con "next" [l].
Definition oiota (l : tm) : tm := con "iota" [l].
Definition oinfo (r l : tm) : tm := con "info" [l; r].
Definition oU (r l G : tm) : tm := con "U" [l; r; G].
Definition oEl (r l G e : tm) : tm := con "El" [e; l; r; G].
(* a CODE F : exp G (info rel (next l)) (U r l) has info [rel, next l]. *)
Definition code_info (l : tm) : tm := oinfo orel (onext l).
(* a TERM a : El F (F a code in U r l) has info [r, iota l]. *)
Definition term_info (r l : tm) : tm := oinfo r (oiota l).

(* substitution calculus (parameterized over tyinfo i) *)
Definition oid (G : tm) : tm := con "id" [G].
Definition oext (A i G : tm) : tm := con "ext" [A; i; G].
Definition owkn (A i G : tm) : tm := con "wkn" [A; i; G].
Definition ohd  (A i G : tm) : tm := con "hd"  [A; i; G].
(* cmp X Y : sub G1 G3  with X(=g):sub G2 G3, Y(=f):sub G1 G2. *)
Definition ocmp (g f G3 G2 G1 : tm) : tm := con "cmp" [g; f; G3; G2; G1].
(* exp_subst v A i g G' G : v : exp G' i A, g : sub G G' -> exp G i A[g]
   (G' SOURCE env, G TARGET env). *)
Definition oexp_subst (v A i g G' G : tm) : tm :=
  con "exp_subst" [v; A; i; g; G'; G].
(* snoc v g A i G' G : extends g : sub G G' by v -> sub G (ext G' i A). *)
Definition osnoc (v g A i G' G : tm) : tm := con "snoc" [v; g; A; i; G'; G].

(* type/term formers *)
Definition oNat (G : tm) : tm := con "Nat" [G].
Definition oEmpty (G : tm) : tm := con "Empty" [G].
Definition ozero (G : tm) : tm := con "zero" [G].
Definition osuc (G n : tm) : tm := con "suc" [n; G].
Definition oPi_rel (rF lF lG F C G : tm) : tm := con "Pi_rel" [C; F; lG; lF; rF; G].
Definition oapp_rel (rF lF lG F C f a G : tm) : tm :=
  con "app_rel" [a; f; C; F; lG; lF; rF; G].

(* ---- Kripke operations, OTT-concrete ---- *)
(* push the domain code F along g : sub D G, landing in env D. *)
Definition act_code (rF lF g G D F : tm) : tm :=
  oexp_subst F (oU rF lF G) (code_info lF) g G D.
(* the domain binder info (info of an element of El F). *)
Definition dom_info (rF lF : tm) : tm := term_info rF lF.
(* extend env D by the (decoded) pushed domain code. *)
Definition extc (rF lF g G D F : tm) : tm :=
  oext (oEl rF lF D (act_code rF lF g G D F)) (dom_info rF lF) D.
(* push the function member f along g : sub D G. *)
Definition act_member (rF lF lG g G D F C f : tm) : tm :=
  oexp_subst f (oEl orel lG G (oPi_rel rF lF lG F C G)) (term_info orel lG) g G D.
(* under' g : lift g over the domain binder
   : sub (extc ..) (ext G (info) (El F)). *)
Definition ounder (rF lF g G D F : tm) : tm :=
  let iF    := dom_info rF lF in
  let actF  := act_code rF lF g G D F in
  let ElaF  := oEl rF lF D actF in
  let extD  := oext ElaF iF D in
  let wknD  := owkn ElaF iF D in
  let g0    := ocmp g wknD G D extD in   (* sub extD G *)
  let hdD   := ohd ElaF iF D in
  osnoc hdD g0 (oEl rF lF G F) iF G extD.
(* push the codomain code C along under' g, landing in env (extc ..). *)
Definition act_cod (rF lF lG g G D F C : tm) : tm :=
  let iF   := dom_info rF lF in
  let extG := oext (oEl rF lF G F) iF G in
  let extD := extc rF lF g G D F in
  oexp_subst C (oU orel lG extG) (code_info lG) (ounder rF lF g G D F) extG extD.
(* the pushed codomain code instantiated at argument a. *)
Definition cod_at (rF lF lG g G D F C a : tm) : tm :=
  let iF     := dom_info rF lF in
  let actF   := act_code rF lF g G D F in
  let ElaF   := oEl rF lF D actF in
  let extD   := extc rF lF g G D F in
  let snoc_a := osnoc a (oid D) ElaF iF D D in   (* sub D extD *)
  oexp_subst (act_cod rF lF lG g G D F C) (oU orel lG extD) (code_info lG)
    snoc_a extD D.
(* member application at env D : (act_member f) applied to a. *)
Definition mapp (rF lF lG g G D F C f a : tm) : tm :=
  oapp_rel rF lF lG (act_code rF lF g G D F) (act_cod rF lF lG g G D F C)
    (act_member rF lF lG g G D F C f) a D.

(* ---- neutral preservation along the Kripke operations ---- *)
(* Pushing a member `f` along `g` (`exp_subst`, principal arg 0) preserves
   neutrality; so does applying it (`app_rel`, principal arg 1).  These feed the
   reflect-at-Pi case: a neutral function applied to any argument is neutral, so
   it lands back in the neutral fiber of the codomain. *)
Lemma act_member_neutral rF lF lG g G D F C f
  : neutral ott_pa "hd" f -> neutral ott_pa "hd" (act_member rF lF lG g G D F C f).
Proof.
  intro Hf; unfold act_member, oexp_subst.
  eapply neutral_elim with (i:=0); [ reflexivity | reflexivity | exact Hf ].
Qed.

Lemma mapp_neutral rF lF lG g G D F C f a
  : neutral ott_pa "hd" f -> neutral ott_pa "hd" (mapp rF lF lG g G D F C f a).
Proof.
  intro Hf; unfold mapp, oapp_rel.
  eapply neutral_elim with (i:=1); [ reflexivity | reflexivity | ].
  apply act_member_neutral; exact Hf.
Qed.

Section RedTyConcrete.
  Context (l : Rule.lang string) (wfl : wf_lang l).

  Notation reds    := (reds string l ott_pa "hd").
  Notation ne_eq   := (ne_eq string l ott_pa "hd").

  (* A reduces to the Nat code in env G. *)
  Definition RNat (G A : tm) : Prop := reds A (oNat G).
  (* A reduces to the Empty code in env G (Empty is at relevance irr, level L0). *)
  Definition REmpty (G A : tm) : Prop := reds A (oEmpty G).
  (* object substitution g : sub D G (home G, future D). *)
  Definition osub (G D g : tm) : Prop := wf_term l [] g (scon "sub" [G; D]).
  (* the sort of Nat-typed elements in env G. *)
  Definition nat_sort (G : tm) : osort :=
    scon "exp" [oEl orel oL0 G (oNat G); term_info orel oL0; G].
  (* the sort of Empty-typed elements in env G. *)
  Definition empty_sort (G : tm) : osort :=
    scon "exp" [oEl oirr oL0 G (oEmpty G); term_info oirr oL0; G].
  (* the sort of a type CODE A : U r l in env G (a code lives at `code_info`). *)
  Definition code_sort (r l G : tm) : osort :=
    scon "exp" [oU r l G; code_info l; G].
  (* the sort of the ELEMENTS of a type code A : U r l in env G (`El A`). *)
  Definition el_sort (r l G A : tm) : osort :=
    scon "exp" [oEl r l G A; term_info r l; G].

  (* ---- base member relations ---- *)
  (* Neutral-code members: each side weak-head reduces to a neutral, and the
     two neutral reducts are ne_eq at the carried sort.  Carrying the `reds`
     witnesses (rather than demanding `a`/`b` themselves neutral) is what makes
     the neutral fiber BACKWARD-CLOSED — a well-typed term of neutral type may
     reduce before becoming neutral.  Mirrors `RedNatMem`'s `rnm_ne`. *)
  Inductive RedNe (t : osort) (a b : tm) : Type :=
  | red_ne : forall na nb, reds a na -> reds b nb -> ne_eq t na nb -> RedNe t a b.

  (* Nat members: zero/suc congruence + stuck neutrals. *)
  Inductive RedNatMem (G : tm) : tm -> tm -> Type :=
  | rnm_zero : forall a b,
      reds a (ozero G) -> reds b (ozero G) -> RedNatMem G a b
  | rnm_suc  : forall a b a' b',
      reds a (osuc G a') -> reds b (osuc G b') ->
      RedNatMem G a' b' -> RedNatMem G a b
  | rnm_ne   : forall a b na nb,
      reds a na -> reds b nb -> ne_eq (nat_sort G) na nb -> RedNatMem G a b.

  (* Kripke Pi member relation. *)
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
  Inductive RedTy_tot : tm -> tm -> tm -> (tm -> tm -> Type) -> Type :=
  | rtt_nat : forall G A B,
      RNat G A -> RNat G B -> RedTy_tot G A B (RedNatMem G)
  | rtt_empty : forall G A B,
      REmpty G A -> REmpty G B -> RedTy_tot G A B (RedNe (empty_sort G))
  (* Neutral type code: A,B reduce to neutral CODES na,nb that are `ne_eq` at
     the U code-sort `code_sort rN lN G`; the MEMBERS of this neutral type live
     at the element sort `el_sort rN lN G na` (= `El na`, the whnf reduct, so
     the member sort is stable under backward closure / `anti_*`). *)
  | rtt_ne : forall G A B na nb (rN lN : tm),
      reds A na -> reds B nb -> ne_eq (code_sort rN lN G) na nb ->
      RedTy_tot G A B (RedNe (el_sort rN lN G na))
  | rtt_pi : forall G A B rF lF lG F C F' C',
      reds A (oPi_rel rF lF lG F C G) ->
      reds B (oPi_rel rF lF lG F' C' G) ->
      forall (RDom : forall D g, osub G D g -> tm -> tm -> Type)
             (DomRed : forall D g (os : osub G D g),
                 RedTy_tot D (act_code rF lF g G D F)
                             (act_code rF lF g G D F') (RDom D g os))
             (RCod : forall D g (os : osub G D g) a a',
                 RDom D g os a a' -> tm -> tm -> Type)
             (CodRed : forall D g (os : osub G D g) a a'
                              (raa' : RDom D g os a a'),
                 RedTy_tot D
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

  Definition RedTy_empty {G A B} (ra : REmpty G A) (rb : REmpty G B) : RedTy G A B :=
    existT _ _ (rtt_empty G A B ra rb).

  Definition RedTy_ne {G A B} na nb rN lN
    (ra : reds A na) (rb : reds B nb) (h : ne_eq (code_sort rN lN G) na nb)
    : RedTy G A B :=
    existT _ _ (rtt_ne G A B na nb rN lN ra rb h).

  Definition RedTy_pi {G A B rF lF lG F C F' C'}
    (hA : reds A (oPi_rel rF lF lG F C G))
    (hB : reds B (oPi_rel rF lF lG F' C' G))
    (DomRed : forall D g (os : osub G D g),
        RedTy D (act_code rF lF g G D F) (act_code rF lF g G D F'))
    (CodRed : forall D g (os : osub G D g) a a',
        RedTm (DomRed D g os) a a' ->
        RedTy D
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
    (Hempty : forall G A B (ra : REmpty G A) (rb : REmpty G B),
        P G A B (RedTy_empty ra rb))
    (Hne : forall G A B na nb rN lN (ra : reds A na) (rb : reds B nb)
                  (h : ne_eq (code_sort rN lN G) na nb),
        P G A B (RedTy_ne na nb rN lN ra rb h))
    (Hpi : forall G A B rF lF lG F C F' C'
             (hA : reds A (oPi_rel rF lF lG F C G))
             (hB : reds B (oPi_rel rF lF lG F' C' G))
             (DomRed : forall D g (os : osub G D g),
                 RedTy D (act_code rF lF g G D F) (act_code rF lF g G D F'))
             (CodRed : forall D g (os : osub G D g) a a',
                 RedTm (DomRed D g os) a a' ->
                 RedTy D
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
                   | G A B ra rb
                   | G A B na nb rN lN ra rb h
                   | G A B rF lF lG F C F' C' hA hB
                     RDom DomRed IHDom RCod CodRed IHCod ].
    - apply Hnat.
    - apply Hempty.
    - apply Hne.
    - apply (Hpi G A B rF lF lG F C F' C' hA hB
               (fun D g os => existT _ (RDom D g os) (DomRed D g os))
               (fun D g os a a' raa' =>
                  existT _ (RCod D g os a a' raa') (CodRed D g os a a' raa'))).
      + intros D g os. exact (IHDom D g os).
      + intros D g os a a' raa'. exact (IHCod D g os a a' raa').
  Defined.

  (* ---- anti-reduction (backward) closure of the type LR ---- *)
  (* The member relation `R` is determined by the env/Pi data, not by the
     codes `A`/`B`, so weak-head-reducing either code leaves `R` unchanged.
     These lemmas let the fundamental lemma's conversion/β cases replace a
     code by any term that weak-head reduces to it. *)
  Notation whstep := (whstep string l ott_pa).

  Lemma RedTy_tot_anti_l G A A' B R
    : star whstep A A' -> RedTy_tot G A' B R -> RedTy_tot G A B R.
  Proof.
    intros Hred Hr; destruct Hr.
    - apply rtt_nat; [ eapply reds_back; eassumption | assumption ].
    - apply rtt_empty; [ eapply reds_back; eassumption | assumption ].
    - eapply rtt_ne; [ eapply reds_back; eassumption | eassumption | eassumption ].
    - eapply rtt_pi; [ eapply reds_back; eassumption | eassumption
                     | eassumption | eassumption ].
  Qed.

  Lemma RedTy_tot_anti_r G A B B' R
    : star whstep B B' -> RedTy_tot G A B' R -> RedTy_tot G A B R.
  Proof.
    intros Hred Hr; destruct Hr.
    - apply rtt_nat; [ assumption | eapply reds_back; eassumption ].
    - apply rtt_empty; [ assumption | eapply reds_back; eassumption ].
    - eapply rtt_ne; [ eassumption | eapply reds_back; eassumption | eassumption ].
    - eapply rtt_pi; [ eassumption | eapply reds_back; eassumption
                     | eassumption | eassumption ].
  Qed.

  Lemma RedTy_anti_l G A A' B
    : star whstep A A' -> RedTy G A' B -> RedTy G A B.
  Proof. intros H [R r]; exists R; eapply RedTy_tot_anti_l; eassumption. Qed.

  Lemma RedTy_anti_r G A B B'
    : star whstep B B' -> RedTy G A B' -> RedTy G A B.
  Proof. intros H [R r]; exists R; eapply RedTy_tot_anti_r; eassumption. Qed.

  (* ---- whnf of the canonical (non-eliminator) formers ---- *)
  (* A `con` whose head is not an eliminator (`ott_pa _ = None`) is a whnf;
     the canonical type/term formers below all qualify. *)
  Lemma whnf_Nat G : whnf ott_pa "hd" (oNat G).
  Proof. right; exists "Nat", [G]; split; reflexivity. Qed.

  Lemma whnf_Empty G : whnf ott_pa "hd" (oEmpty G).
  Proof. right; exists "Empty", [G]; split; reflexivity. Qed.

  Lemma whnf_Pi_rel rF lF lG F C G : whnf ott_pa "hd" (oPi_rel rF lF lG F C G).
  Proof. right; eexists "Pi_rel", _; split; reflexivity. Qed.

  (* ---- leaf reducibility: the closed base type Nat is reducible ---- *)
  Lemma RNat_Nat G : RNat G (oNat G).
  Proof. unfold RNat; apply reds_refl, whnf_Nat. Qed.

  Definition RedTy_Nat G : RedTy G (oNat G) (oNat G) :=
    RedTy_nat (RNat_Nat G) (RNat_Nat G).

  Lemma REmpty_Empty G : REmpty G (oEmpty G).
  Proof. unfold REmpty; apply reds_refl, whnf_Empty. Qed.

  Definition RedTy_Empty G : RedTy G (oEmpty G) (oEmpty G) :=
    RedTy_empty (REmpty_Empty G) (REmpty_Empty G).

  (* ---- the Nat fiber is a (backward-closed) PER ---- *)
  (* Nat members never recurse into `RedTy`, so symmetry and backward closure
     are self-contained inductions on `RedNatMem` (no irrelevance / typing
     needed); they feed the fundamental lemma's Nat term cases directly. *)
  Lemma RedNatMem_sym G a b : RedNatMem G a b -> RedNatMem G b a.
  Proof.
    induction 1.
    - eapply rnm_zero; eassumption.
    - eapply rnm_suc; eassumption.
    - eapply rnm_ne; [ eassumption | eassumption | apply ne_eq_sym; eassumption ].
  Qed.

  Lemma RedNatMem_back_l G a a' b
    : star whstep a a' -> RedNatMem G a' b -> RedNatMem G a b.
  Proof.
    intros H Hm; destruct Hm.
    - eapply rnm_zero; [ eapply reds_back; eassumption | eassumption ].
    - eapply rnm_suc; [ eapply reds_back; eassumption | eassumption | eassumption ].
    - eapply rnm_ne; [ eapply reds_back; eassumption | eassumption | eassumption ].
  Qed.

  Lemma RedNatMem_back_r G a b b'
    : star whstep b b' -> RedNatMem G a b' -> RedNatMem G a b.
  Proof.
    intros H Hm.
    apply RedNatMem_sym; eapply RedNatMem_back_l;
      [ eassumption | apply RedNatMem_sym; eassumption ].
  Qed.

  (* ---- the neutral fiber is likewise a backward-closed PER ---- *)
  Lemma RedNe_sym t a b : RedNe t a b -> RedNe t b a.
  Proof.
    intros [na nb ra rb h]; eapply red_ne;
      [ exact rb | exact ra | apply ne_eq_sym; exact h ].
  Qed.

  Lemma RedNe_back_l t a a' b
    : star whstep a a' -> RedNe t a' b -> RedNe t a b.
  Proof.
    intros H [na nb ra rb h]; eapply red_ne;
      [ eapply reds_back; eassumption | exact rb | exact h ].
  Qed.

  Lemma RedNe_back_r t a b b'
    : star whstep b b' -> RedNe t a b' -> RedNe t a b.
  Proof.
    intros H [na nb ra rb h]; eapply red_ne;
      [ exact ra | eapply reds_back; eassumption | exact h ].
  Qed.

  (* ---- ESCAPE (soundness) for the neutral fiber ---- *)
  (* Reducibility of a neutral pair, together with WELL-TYPEDNESS of the two
     members, escapes to declarative `eq_term`.  Members are raw terms (the LR
     does NOT bundle typing), so `reds_sound` needs the wf hypotheses supplied
     externally — exactly what the fundamental lemma threads.  The neutral fiber
     is non-recursive, so this is abstract over `l`.

     NB the *Nat* fiber escape (`RedNatMem` ⇒ `eq_term`) and the *type-level*
     escape (`RedTy` ⇒ `eq_term`) are NOT here: their `rnm_suc` / `rtt_pi`
     cases recurse and must re-derive a sub-member's typing by subject reduction
     + constructor inversion, which needs the CONCRETE `suc` / `Pi_rel` rule
     shapes.  They land in file 4 (`FundamentalLemma`) where `l := ott`. *)
  Lemma RedNe_sound t a b
    : RedNe t a b -> wf_term l [] a t -> wf_term l [] b t -> eq_term l [] t a b.
  Proof.
    intros [na nb ra rb h] Hwfa Hwfb.
    pose proof (@reds_sound string _ _ l wfl ott_pa "hd" a na t Hwfa ra) as H1.
    pose proof (@reds_sound string _ _ l wfl ott_pa "hd" b nb t Hwfb rb) as H2.
    eapply eq_term_trans; [ exact H1 | ].
    eapply eq_term_trans; [ | eapply eq_term_sym; exact H2 ].
    exact (proj2 (proj2 h)).
  Qed.

  (* ---- REFLECT leaves: a well-typed neutral is reducible ---- *)
  (* The easy direction of the fundamental lemma's neutral/variable cases: a
     well-typed stuck term is a reducible member of its (neutral or Nat) fiber,
     and a well-typed neutral type code is reducible.  All are constructors
     (`reds_refl` on the whnf neutral + `ne_eq_refl`), hence abstract over `l`.
     Reflect AT Π (a neutral function is a reducible Π-member) is the eta crux
     and is NOT a leaf — it lands with the Pi case of the fundamental lemma. *)
  Lemma RedNe_refl t a : neutral ott_pa "hd" a -> wf_term l [] a t -> RedNe t a a.
  Proof.
    intros Hn Hwf.
    eapply red_ne; [ apply reds_refl; apply neutral_whnf; exact Hn
                   | apply reds_refl; apply neutral_whnf; exact Hn
                   | apply ne_eq_refl; assumption ].
  Qed.

  Lemma RedNatMem_refl_ne G a
    : neutral ott_pa "hd" a -> wf_term l [] a (nat_sort G) -> RedNatMem G a a.
  Proof.
    intros Hn Hwf.
    eapply rnm_ne; [ apply reds_refl; apply neutral_whnf; exact Hn
                   | apply reds_refl; apply neutral_whnf; exact Hn
                   | apply ne_eq_refl; assumption ].
  Qed.

  Lemma RedTy_ne_refl G A rN lN
    : neutral ott_pa "hd" A -> wf_term l [] A (code_sort rN lN G) -> RedTy G A A.
  Proof.
    intros Hn Hwf.
    eapply (RedTy_ne A A rN lN);
      [ apply reds_refl; apply neutral_whnf; exact Hn
      | apply reds_refl; apply neutral_whnf; exact Hn
      | apply ne_eq_refl; assumption ].
  Qed.

  (* ---- TWO-SIDED reflect leaves (the PER form) ---- *)
  (* The fundamental lemma's neutral/variable cases compare two DISTINCT terms
     `a`,`b` that are `ne_eq` (both stuck + declaratively equal), not a term with
     itself.  Each such pair is directly a reducible member of its fiber: both
     sides are already whnf (a neutral is whnf), so `reds_refl` discharges the
     reduction witnesses and the `ne_eq` is carried verbatim.  The reflexive
     leaves above are the `a = b` instances of these (via `ne_eq_refl`). *)
  Lemma RedNe_reflect t a b : ne_eq t a b -> RedNe t a b.
  Proof.
    intros (Ha & Hb & Hab); eapply red_ne;
      [ apply reds_refl; apply neutral_whnf; exact Ha
      | apply reds_refl; apply neutral_whnf; exact Hb
      | exact (conj Ha (conj Hb Hab)) ].
  Qed.

  Lemma RedNatMem_reflect G a b : ne_eq (nat_sort G) a b -> RedNatMem G a b.
  Proof.
    intros (Ha & Hb & Hab); eapply rnm_ne;
      [ apply reds_refl; apply neutral_whnf; exact Ha
      | apply reds_refl; apply neutral_whnf; exact Hb
      | exact (conj Ha (conj Hb Hab)) ].
  Qed.

  Lemma RedTy_ne_reflect G A B rN lN
    : ne_eq (code_sort rN lN G) A B -> RedTy G A B.
  Proof.
    intros (Ha & Hb & Hab); eapply (RedTy_ne A B rN lN);
      [ apply reds_refl; apply neutral_whnf; exact Ha
      | apply reds_refl; apply neutral_whnf; exact Hb
      | exact (conj Ha (conj Hb Hab)) ].
  Qed.

End RedTyConcrete.
