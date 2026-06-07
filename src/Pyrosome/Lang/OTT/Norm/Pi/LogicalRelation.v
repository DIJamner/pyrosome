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
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Compilers Require Import OperationalBridge.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral.
Import Core.Notations.

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

    Notation whstep := (whstep V l pa).
    Notation whnf := (whnf pa).
    Notation neutral := (neutral pa).

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

    (* ================================================================== *)
    (* The reducibility logical relation over TYPE CODES.                  *)
    (*                                                                    *)
    (* This is the concrete-for-OTT analog of the validated Kripke         *)
    (* encoding (WIP/LRProto2.v): a SINGLE plain inductive `RedTy_tot`      *)
    (* carrying the member relation as an OUTPUT index (the Sig trick), so  *)
    (* no Small/Large universe tower and no LogRel2-style PolyRedPack +     *)
    (* adequacy split is needed.  The Pi case is KRIPKE from the start      *)
    (* (UPDATE-s item 3): domain/codomain reducibility is quantified over   *)
    (* every object substitution `g : osub G D` into a future env `D`.     *)
    (*                                                                    *)
    (* GENERIC over the OTT type-former interface below; the concrete OTT   *)
    (* instantiation (the verified `ott_pa` selector + the `Pi_rel`/`Nat`/  *)
    (* `exp_subst`/... con builders, memory ott-con-arg-orders) plugs these *)
    (* in downstream.  Everything is at Pyrosome ctx = []; the object env   *)
    (* `G : term` (sort `env`) carries object open-ness.                    *)
    (* ================================================================== *)
    Section RedTyDef.

      (* `RNat G A`     : A weak-head reduces to the `Nat` code in env G.    *)
      (* `RPi G A F C`  : A reduces to a `Pi_rel` code with domain code F     *)
      (*                  and codomain code C, in env G.                      *)
      Context (RNat : term -> term -> Prop)
              (RPi  : term -> term -> term -> term -> Prop).
      (* members of `Nat` in env G (zero/suc/neutral); abstract for now.     *)
      Context (RNatMem : term -> term -> term -> Type).
      (* `osub G D g` : g is an object substitution from home env G to a      *)
      (* future env D (g : sub G D).                                          *)
      Context (osub : term -> term -> term -> Prop).
      (* `act g F`   : push a code F along object subst g.                    *)
      (* `extc D F'` : extend env D by the (decoded) domain code F'.          *)
      (* `cod g a C` : codomain code C pushed under g and instantiated at a.  *)
      (* `mapp f a`  : member application (f applied to a).                   *)
      Context (act  : term -> term -> term)
              (extc : term -> term -> term)
              (cod  : term -> term -> term -> term)
              (mapp : term -> term -> term).

      (* Neutral-code member relation (Type-valued wrapper over `ne_eq`). *)
      Inductive RedNe (t : sort) (a b : term) : Type :=
      | red_ne : ne_eq t a b -> RedNe t a b.

      (* Kripke Pi member relation: functions t,u are related at the home env
         G iff, under every object subst g into a future env D and every
         domain-related (a,a'), the applications are codomain-related. *)
      Inductive RedAtPi
        (G F C F' C' : term)
        (RDom : forall D g, osub G D g -> term -> term -> Type)
        (RCod : forall D g (os : osub G D g) a a',
            RDom D g os a a' -> term -> term -> Type)
        (t u : term) : Type :=
      | at_pi_app :
          (forall D g (os : osub G D g) a a' (raa' : RDom D g os a a'),
              RCod D g os a a' raa' (mapp (act g t) a) (mapp (act g u) a'))
          -> RedAtPi G F C F' C' RDom RCod t u.

      Inductive RedTy_tot
        : term -> term -> term -> (term -> term -> Type) -> Type :=
      | rtt_nat : forall G A B,
          RNat G A -> RNat G B ->
          RedTy_tot G A B (RNatMem G)
      | rtt_ne : forall G A B na nb (t : sort),
          reds A na -> reds B nb -> ne_eq t na nb ->
          RedTy_tot G A B (RedNe t)
      | rtt_pi : forall G A B F C F' C',
          RPi G A F C -> RPi G B F' C' ->
          forall (RDom : forall D g, osub G D g -> term -> term -> Type)
                 (DomRed : forall D g (os : osub G D g),
                     RedTy_tot D (act g F) (act g F') (RDom D g os))
                 (RCod : forall D g (os : osub G D g) a a',
                     RDom D g os a a' -> term -> term -> Type)
                 (CodRed : forall D g (os : osub G D g) a a'
                                  (raa' : RDom D g os a a'),
                     RedTy_tot (extc D (act g F)) (cod g a C) (cod g a' C')
                       (RCod D g os a a' raa')),
          RedTy_tot G A B (RedAtPi G F C F' C' RDom RCod).

      (* Sig packaging: the member relation is the first projection. *)
      Definition RedTy (G A B : term) : Type :=
        { R : term -> term -> Type & RedTy_tot G A B R }.
      Definition RedTy_R {G A B} (r : RedTy G A B) : term -> term -> Type :=
        projT1 r.
      Definition RedTm {G A B} (r : RedTy G A B) (t u : term) : Type :=
        RedTy_R r t u.

      (* Smart constructors. *)
      Definition RedTy_nat {G A B} (ra : RNat G A) (rb : RNat G B) : RedTy G A B :=
        existT _ _ (rtt_nat G A B ra rb).

      Definition RedTy_ne {G A B} na nb t
        (ra : reds A na) (rb : reds B nb) (h : ne_eq t na nb) : RedTy G A B :=
        existT _ _ (rtt_ne G A B na nb t ra rb h).

      Definition RedTy_pi {G A B F C F' C'}
        (hA : RPi G A F C) (hB : RPi G B F' C')
        (DomRed : forall D g (os : osub G D g), RedTy D (act g F) (act g F'))
        (CodRed : forall D g (os : osub G D g) a a',
            RedTm (DomRed D g os) a a' ->
            RedTy (extc D (act g F)) (cod g a C) (cod g a' C'))
        : RedTy G A B.
      Proof.
        unshelve eexists.
        - exact (RedAtPi G F C F' C'
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
        (Hpi : forall G A B F C F' C'
                 (hA : RPi G A F C) (hB : RPi G B F' C')
                 (DomRed : forall D g (os : osub G D g), RedTy D (act g F) (act g F'))
                 (CodRed : forall D g (os : osub G D g) a a',
                     RedTm (DomRed D g os) a a' ->
                     RedTy (extc D (act g F)) (cod g a C) (cod g a' C')),
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
                       | G A B F C F' C' hA hB RDom DomRed IHDom RCod CodRed IHCod ].
        - apply Hnat.
        - apply Hne.
        - apply (Hpi G A B F C F' C' hA hB
                   (fun D g os => existT _ (RDom D g os) (DomRed D g os))
                   (fun D g os a a' raa' =>
                      existT _ (RCod D g os a a' raa') (CodRed D g os a a' raa'))).
          + intros D g os. exact (IHDom D g os).
          + intros D g os a a' raa'. exact (IHCod D g os a a' raa').
      Defined.

    End RedTyDef.

  End WithLang.

End WithVar.
