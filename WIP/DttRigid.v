Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
Require Import WIP.DttSyntax WIP.DttNf WIP.DttErase.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 0.5b: THE RIGID MODEL, the semantic half of
   code rigidity.

   A second, much smaller [CutTModel] over [ott_dtt] with the empty
   meta-context.  It interprets ONLY the sigma-fragment (environments,
   substitutions, types and codes) and is trivial everywhere else.  Its
   whole point is design section 2:

     no eliminator of [ott_dtt] has a universe as its result type,

   so no equation of the theory can ever rewrite a CODE: beta and eta live
   at [El]-sorts and are discharged by [exact I].  The obligations that
   carry content are exactly the sigma ones.

   The semantic domain is the de Bruijn domain of WIP/DttErase.v
   ([rcode]/[rty]/[renv]) plus rigid substitutions

     rsub := nat -> rcode

   with the usual sigma operations.  A substitution [g : sub G G'] is read
   as a map from the slots of the CODOMAIN environment [G'] to codes over
   [G].  Slots whose type is not a universe carry no code; they are filled
   with the junk value [rc_nat] and are EXCLUDED from the model's notion of
   equality of substitutions ([subeq] below quantifies only over universe
   slots).  That exclusion is forced: [snoc_wkn_hd] identifies
   [<wkn, hd>] with [id], and at a non-universe slot the two sides carry
   different junk.

   Interpretation is by four mutually inductive relations over ARBITRARY
   syntax ([IEnv]/[ITy]/[ICode]/[ISub]); they cover the sigma formers
   ([ty_subst], [exp_subst], [id], [wkn], [cmp], [snoc], [forget], [emp],
   [ext], [hd]) as well as [U]/[El]/[Nat]/[Empty]/[Pi_rel]/[Pi_irr].

   Nothing here is stated in terms of [ErCode]/[ErTy]/[ErEnv]: injectivity
   is proved directly against the model's own relations (section 9), which
   is what makes the recursion in the variable case go through without the
   [WknInj] assumption.  [WknInj] is then DERIVED (section 10), so
   WIP/DttErase.v's injectivity theorems become available too.
   ===================================================================== *)

Local Notation eqt := (eq_term ott_dtt []).

(* =====================================================================
   1.  Rigid substitutions and their calculus.

   Substitutions are total functions [nat -> rcode].  Totality is what
   makes [csub rid c = c] and [csub s (csub t c) = csub (rcmp s t) c]
   unconditional; the scoping information that a finite representation
   would carry is recovered separately by [cwf] (section 3), which is
   needed only to compare two substitutions that agree on the universe
   slots.
   ===================================================================== *)

Definition rsub := nat -> rcode.

Definition upren (f : nat -> nat) : nat -> nat :=
  fun k => match k with 0 => 0 | S k' => S (f k') end.

Fixpoint cren (f : nat -> nat) (c : rcode) : rcode :=
  match c with
  | rc_var k => rc_var (f k)
  | rc_nat => rc_nat
  | rc_empty => rc_empty
  | rc_pi b br bl F B => rc_pi b br bl (cren f F) (cren (upren f) B)
  end.

Definition up (s : rsub) : rsub :=
  fun k => match k with 0 => rc_var 0 | S k' => cren S (s k') end.

Fixpoint csub (s : rsub) (c : rcode) : rcode :=
  match c with
  | rc_var k => s k
  | rc_nat => rc_nat
  | rc_empty => rc_empty
  | rc_pi b br bl F B => rc_pi b br bl (csub s F) (csub (up s) B)
  end.

Definition tsub (s : rsub) (T : rty) : rty :=
  match T with
  | rt_U br bl => rt_U br bl
  | rt_El br bl n => rt_El br bl (csub s n)
  end.

Definition rid : rsub := fun k => rc_var k.
Definition rshift : rsub := fun k => rc_var (S k).
Definition rcmp (s t : rsub) : rsub := fun k => csub s (t k).
Definition rsnoc (c : rcode) (s : rsub) : rsub :=
  fun k => match k with 0 => c | S k' => s k' end.
Definition rforget : rsub := fun _ => rc_nat.

(* ---- the sigma laws, all unconditional ---- *)

Lemma cren_ext c : forall f g, (forall k, f k = g k) -> cren f c = cren g c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros f g H; cbn;
    try reflexivity.
  - rewrite H; reflexivity.
  - f_equal; [ apply IHF; assumption | ].
    apply IHB; intros [|k]; cbn; [ reflexivity | rewrite H; reflexivity ].
Qed.

Lemma csub_ext c : forall s t, (forall k, s k = t k) -> csub s c = csub t c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros s t H; cbn;
    try reflexivity.
  - apply H.
  - f_equal; [ apply IHF; assumption | ].
    apply IHB; intros [|k]; cbn; [ reflexivity | rewrite H; reflexivity ].
Qed.

Lemma cren_cren c : forall f g, cren f (cren g c) = cren (fun k => f (g k)) c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros f g; cbn;
    try reflexivity.
  f_equal; [ apply IHF | ].
  rewrite IHB; apply cren_ext; intros [|k]; cbn; reflexivity.
Qed.

Lemma csub_cren c : forall s f, csub s (cren f c) = csub (fun k => s (f k)) c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros s f; cbn;
    try reflexivity.
  f_equal; [ apply IHF | ].
  rewrite IHB; apply csub_ext; intros [|k]; cbn; reflexivity.
Qed.

Lemma cren_csub c : forall f s, cren f (csub s c) = csub (fun k => cren f (s k)) c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros f s; cbn;
    try reflexivity.
  f_equal; [ apply IHF | ].
  rewrite IHB; apply csub_ext; intros [|k]; cbn; [ reflexivity | ].
  rewrite !cren_cren; apply cren_ext; intros j; cbn; reflexivity.
Qed.

Lemma csub_comp c : forall s t, csub s (csub t c) = csub (rcmp s t) c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros s t; cbn;
    try reflexivity.
  f_equal; [ apply IHF | ].
  rewrite IHB; apply csub_ext; intros [|k]; cbn; [ reflexivity | ].
  unfold rcmp; cbn.
  rewrite csub_cren, cren_csub; apply csub_ext; intros j; cbn; reflexivity.
Qed.

Lemma csub_id c : csub rid c = c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; cbn; try reflexivity.
  f_equal; [ assumption | ].
  rewrite <- IHB at 2.
  apply csub_ext; intros [|k]; cbn; reflexivity.
Qed.

Lemma cren_as_csub c : forall f, cren f c = csub (fun k => rc_var (f k)) c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ]; intros f; cbn;
    try reflexivity.
  f_equal; [ apply IHF | ].
  rewrite IHB; apply csub_ext; intros [|k]; cbn; reflexivity.
Qed.

Lemma csub_rshift c : csub rshift c = cren S c.
Proof. rewrite cren_as_csub; apply csub_ext; reflexivity. Qed.

Lemma tsub_id T : tsub rid T = T.
Proof. destruct T; cbn; [ reflexivity | rewrite csub_id; reflexivity ]. Qed.

Lemma tsub_comp s t T : tsub s (tsub t T) = tsub (rcmp s t) T.
Proof. destruct T; cbn; [ reflexivity | rewrite csub_comp; reflexivity ]. Qed.

(* [cren] with an injective renaming is injective; the only instance
   needed is [S], for the weakening/shift step of [WknInj]. *)
Lemma cren_inj c1 : forall c2 f,
    (forall k1 k2, f k1 = f k2 -> k1 = k2) -> cren f c1 = cren f c2 -> c1 = c2.
Proof.
  induction c1 as [ k | | | b br bl F IHF B IHB ];
    intros [ k2 | | | b2 br2 bl2 F2 B2 ] f Hf Heq; cbn in Heq;
    try discriminate; try reflexivity.
  - assert (f k = f k2) as Hk by (injection Heq; auto).
    apply Hf in Hk; subst; reflexivity.
  - assert (b = b2 /\ br = br2 /\ bl = bl2
            /\ cren f F = cren f F2
            /\ cren (upren f) B = cren (upren f) B2) as
      [-> [-> [-> [HF HB]]]]
        by (injection Heq; intros; repeat split; assumption).
    f_equal; [ eapply IHF; eassumption | ].
    eapply IHB; [ | exact HB ].
    intros [|k1] [|k3]; cbn; try discriminate; try reflexivity.
    intro Hq; assert (f k1 = f k3) as Hk by (injection Hq; auto).
    apply Hf in Hk; subst; reflexivity.
Qed.

Lemma tsub_shift_inj T1 T2 : tsub rshift T1 = tsub rshift T2 -> T1 = T2.
Proof.
  destruct T1 as [ br bl | br bl n1 ]; destruct T2 as [ br2 bl2 | br2 bl2 n2 ];
    cbn; intro H; try discriminate; try assumption.
  assert (br = br2 /\ bl = bl2 /\ csub rshift n1 = csub rshift n2) as
    [-> [-> Hn]] by (injection H; intros; repeat split; assumption).
  rewrite !csub_rshift in Hn.
  f_equal; eapply cren_inj; [ | exact Hn ].
  intros k1 k2 Hk; injection Hk; auto.
Qed.

(* =====================================================================
   2.  "Universe-like" types.

   With the empty meta-context, a type is built from [U], [El] and
   [ty_subst] alone, so U-ness is decided structurally.  That the two
   sides of a provable type equation agree on [USkel] is a corollary of
   the [ty] row of the model ([ITy_USkel], section 5).
   ===================================================================== *)

Fixpoint USkel (A : term) : bool :=
  match A with
  | con nm l =>
      if eqb nm "U" then true
      else if eqb nm "ty_subst"
           then match l with A0 :: _ => USkel A0 | _ => false end
           else false
  | _ => false
  end.

Lemma USkel_U G r l : USkel (oU G r l) = true.
Proof. reflexivity. Qed.

Lemma USkel_El G r l e : USkel (oEl G r l e) = false.
Proof. reflexivity. Qed.

Lemma USkel_subst G G' g i A : USkel (oTySubst G G' g i A) = USkel A.
Proof. reflexivity. Qed.

(* =====================================================================
   3.  Scoping: which de Bruijn slots a code may mention.

   A code over an environment [E] may only mention slots whose type is a
   UNIVERSE -- a variable of an [El]-type is not a code.  [cwf] records
   exactly that, and it is what lets two substitutions that agree on the
   universe slots ([subeq]) act identically on codes.
   ===================================================================== *)

Definition isU (T : rty) : bool :=
  match T with rt_U _ _ => true | rt_El _ _ _ => false end.

Definition isUat (E : renv) (k : nat) : bool :=
  match nth_error E k with Some T => isU T | None => false end.

Fixpoint cwf (E : renv) (c : rcode) : Prop :=
  match c with
  | rc_var k => isUat E k = true
  | rc_nat => True
  | rc_empty => True
  | rc_pi b br bl F B => cwf E F /\ cwf (rt_El br bl F :: E) B
  end.

Definition twf (E : renv) (T : rty) : Prop :=
  match T with rt_U _ _ => True | rt_El _ _ n => cwf E n end.

Definition swf (E E' : renv) (s : rsub) : Prop :=
  forall k, isUat E' k = true -> cwf E (s k).

Definition subeq (E' : renv) (s1 s2 : rsub) : Prop :=
  forall k, isUat E' k = true -> s1 k = s2 k.

Lemma isUat_cons_S T E k : isUat (T :: E) (S k) = isUat E k.
Proof. reflexivity. Qed.

Lemma isUat_El_0 br bl n E : isUat (rt_El br bl n :: E) 0 = false.
Proof. reflexivity. Qed.

(* [cwf] only ever looks at the U-ness of the slots, so replacing an
   [rt_El] entry by another [rt_El] entry is invisible to it. *)
Lemma cwf_isU_ext c : forall E1 E2,
    (forall k, isUat E1 k = isUat E2 k) -> cwf E1 c -> cwf E2 c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ];
    intros E1 E2 Hext H; cbn in *; try exact I.
  - rewrite <- Hext; exact H.
  - destruct H as [HF HB]; split.
    + eapply IHF; eassumption.
    + eapply IHB; [ | exact HB ].
      intros [|k]; cbn; [ reflexivity | apply Hext ].
Qed.

Lemma cwf_El_irrel c E br bl n1 n2 :
  cwf (rt_El br bl n1 :: E) c -> cwf (rt_El br bl n2 :: E) c.
Proof.
  apply cwf_isU_ext; intros [|k]; reflexivity.
Qed.

Lemma cren_cwf c : forall E1 E2 f,
    (forall k, isUat E1 k = true -> isUat E2 (f k) = true) ->
    cwf E1 c -> cwf E2 (cren f c).
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ];
    intros E1 E2 f Hf H; cbn in *; try exact I.
  - apply Hf; assumption.
  - destruct H as [HF HB]; split.
    + eapply IHF; eassumption.
    + eapply IHB; [ | exact HB ].
      intros [|k]; cbn; [ discriminate | apply Hf ].
Qed.

Lemma cwf_shift c T E : cwf E c -> cwf (T :: E) (cren S c).
Proof.
  intro H; eapply cren_cwf; [ | exact H ].
  intros k Hk; rewrite isUat_cons_S; exact Hk.
Qed.

Lemma swf_up E E' s br bl F :
  swf E E' s -> swf (rt_El br bl (csub s F) :: E) (rt_El br bl F :: E') (up s).
Proof.
  intros H [|k] Hk; cbn in Hk; [ discriminate | ].
  cbn; apply cwf_shift; apply H; exact Hk.
Qed.

Lemma cwf_csub c : forall E E' s, swf E E' s -> cwf E' c -> cwf E (csub s c).
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ];
    intros E E' s Hs H; cbn in *; try exact I.
  - apply Hs; assumption.
  - destruct H as [HF HB]; split.
    + eapply IHF; eassumption.
    + eapply IHB; [ apply swf_up; exact Hs | exact HB ].
Qed.

Lemma twf_tsub T E E' s : swf E E' s -> twf E' T -> twf E (tsub s T).
Proof.
  destruct T; cbn; intros; [ exact I | eapply cwf_csub; eassumption ].
Qed.

Lemma subeq_up E' s1 s2 br bl F :
  subeq E' s1 s2 -> subeq (rt_El br bl F :: E') (up s1) (up s2).
Proof.
  intros H [|k] Hk; cbn in Hk; [ discriminate | ].
  cbn; f_equal; apply H; exact Hk.
Qed.

Lemma csub_ext_wf c : forall E' s1 s2,
    cwf E' c -> subeq E' s1 s2 -> csub s1 c = csub s2 c.
Proof.
  induction c as [ k | | | b br bl F IHF B IHB ];
    intros E' s1 s2 Hwf Heq; cbn in *; try reflexivity.
  - apply Heq; assumption.
  - destruct Hwf as [HF HB]; f_equal.
    + eapply IHF; eassumption.
    + eapply IHB; [ exact HB | apply subeq_up; exact Heq ].
Qed.

Lemma tsub_ext_wf T E' s1 s2 :
  twf E' T -> subeq E' s1 s2 -> tsub s1 T = tsub s2 T.
Proof.
  destruct T; cbn; intros; [ reflexivity | ].
  f_equal; eapply csub_ext_wf; eassumption.
Qed.

(* =====================================================================
   4.  The interpretation relations.

   Defined over ARBITRARY syntax of the four relevant sorts (not only over
   normal forms): the model's congruence obligations conclude about the
   raw term formers, so the relations have to cover the sigma formers too.

   Every clause pins the [renv] index to the term's own syntactic
   environment through an [IEnv] premise.  That is what makes the indices
   FUNCTIONAL (section 5) -- and functionality of the indices is in turn
   what lets [rceq_term] at the [ty]/[exp]/[sub] sorts existentially
   quantify them.
   ===================================================================== *)

Inductive IEnv : term -> renv -> Prop :=
| ienv_emp : IEnv oEmp []
| ienv_ext : forall G i A E T,
    IEnv G E -> ITy E A T -> IEnv (oExt G i A) (T :: E)

with ITy : renv -> term -> rty -> Prop :=
| ity_U : forall E G r l br bl,
    IEnv G E -> ErRel r br -> ErLvl l bl ->
    ITy E (oU G r l) (rt_U br bl)
| ity_El : forall E G r l c br bl n,
    IEnv G E -> ErRel r br -> ErLvl l bl -> ICode E c n ->
    ITy E (oEl G r l c) (rt_El br bl n)
| ity_subst : forall E E' G G' g i A T s,
    IEnv G E -> IEnv G' E' -> ISub E E' g s -> ITy E' A T ->
    ITy E (oTySubst G G' g i A) (tsub s T)

with ICode : renv -> term -> rcode -> Prop :=
| icode_nat : forall E G, IEnv G E -> ICode E (oNat G) rc_nat
| icode_empty : forall E G, IEnv G E -> ICode E (oEmpty G) rc_empty
| icode_pi_rel : forall E G rF lF lG F B brF blF nF nB,
    IEnv G E -> ErRel rF brF -> ErLvl lF blF ->
    ICode E F nF ->
    ICode (rt_El brF blF nF :: E) B nB ->
    ICode E (oPiRel G rF lF lG F B) (rc_pi true brF blF nF nB)
| icode_pi_irr : forall E G rF lF F B brF blF nF nB,
    IEnv G E -> ErRel rF brF -> ErLvl lF blF ->
    ICode E F nF ->
    ICode (rt_El brF blF nF :: E) B nB ->
    ICode E (oPiIrr G rF lF F B) (rc_pi false brF blF nF nB)
| icode_hd : forall E G i A br bl,
    IEnv G E -> ITy E A (rt_U br bl) ->
    ICode (rt_U br bl :: E) (oHd G i A) (rc_var 0)
| icode_subst : forall E E' G G' g i A v s n,
    IEnv G E -> IEnv G' E' -> ISub E E' g s -> ICode E' v n ->
    ICode E (oExpSubst G G' g i A v) (csub s n)

with ISub : renv -> renv -> term -> rsub -> Prop :=
| isub_id : forall E G, IEnv G E -> ISub E E (oId G) rid
| isub_forget : forall E G, IEnv G E -> ISub E [] (oForget G) rforget
| isub_wkn : forall E G i A T,
    IEnv G E -> ITy E A T -> ISub (T :: E) E (oWkn G i A) rshift
| isub_cmp : forall E1 E2 E3 G1 G2 G3 f g sf sg,
    IEnv G1 E1 -> IEnv G2 E2 -> IEnv G3 E3 ->
    ISub E1 E2 f sf -> ISub E2 E3 g sg ->
    ISub E1 E3 (oCmp G1 G2 G3 f g) (rcmp sf sg)
| isub_snoc_U : forall E E' G G' i A g v s br bl n,
    IEnv G E -> IEnv G' E' -> ISub E E' g s ->
    ITy E' A (rt_U br bl) -> ICode E v n ->
    ISub E (rt_U br bl :: E') (oSnoc G G' i A g v) (rsnoc n s)
| isub_snoc_El : forall E E' G G' i A g v s br bl n,
    IEnv G E -> IEnv G' E' -> ISub E E' g s ->
    ITy E' A (rt_El br bl n) ->
    ISub E (rt_El br bl n :: E') (oSnoc G G' i A g v) (rsnoc rc_nat s).

Scheme IEnv_min := Minimality for IEnv Sort Prop
  with ITy_min := Minimality for ITy Sort Prop
  with ICode_min := Minimality for ICode Sort Prop
  with ISub_min := Minimality for ISub Sort Prop.

Combined Scheme I_mutind from IEnv_min, ITy_min, ICode_min, ISub_min.

(* The environment extension a binder makes. *)
Lemma IEnv_extC E G rF lF F brF blF nF :
  IEnv G E -> ErRel rF brF -> ErLvl lF blF -> ICode E F nF ->
  IEnv (oExtC G rF lF F) (rt_El brF blF nF :: E).
Proof.
  intros; unfold oExtC; econstructor; [ eassumption | ].
  econstructor; eassumption.
Qed.

(* =====================================================================
   5.  Functionality, scoping and the [USkel] invariant.
   ===================================================================== *)

Lemma I_fun :
  (forall G E1, IEnv G E1 -> forall E2, IEnv G E2 -> E1 = E2)
  /\ (forall E1 A T1, ITy E1 A T1 -> forall E2 T2, ITy E2 A T2 ->
        E1 = E2 /\ T1 = T2)
  /\ (forall E1 c n1, ICode E1 c n1 -> forall E2 n2, ICode E2 c n2 ->
        E1 = E2 /\ n1 = n2)
  /\ (forall E1 E1' g s1, ISub E1 E1' g s1 -> forall E2 E2' s2,
        ISub E2 E2' g s2 -> E1 = E2 /\ E1' = E2' /\ s1 = s2).
Proof.
  apply I_mutind.
  (* ienv_emp *)
  - intros E2 H; inversion H; reflexivity.
  (* ienv_ext *)
  - intros G i A E T HE IHE HT IHT E2 H; inversion H; subst.
    f_equal; [ eapply IHT; eassumption | apply IHE; assumption ].
  (* ity_U *)
  - intros E G r l br bl HE IHE Hr Hl E2 T2 H; inversion H; subst.
    split; [ apply IHE; assumption | ].
    f_equal; [ eapply ErRel_fun | eapply ErLvl_fun ]; eassumption.
  (* ity_El *)
  - intros E G r l c br bl n HE IHE Hr Hl Hc IHc E2 T2 H; inversion H; subst.
    destruct (IHc _ _ ltac:(eassumption)) as [? ?]; subst.
    split; [ reflexivity | ].
    f_equal; [ eapply ErRel_fun | eapply ErLvl_fun ]; eassumption.
  (* ity_subst *)
  - intros E E' G G' g i A T s HE IHE HE' IHE' Hs IHs HT IHT E2 T2 H;
      inversion H; subst.
    destruct (IHs _ _ _ ltac:(eassumption)) as [? [? ?]]; subst.
    destruct (IHT _ _ ltac:(eassumption)) as [? ?]; subst.
    split; reflexivity.
  (* icode_nat *)
  - intros E G HE IHE E2 n2 H; inversion H; subst.
    split; [ apply IHE; assumption | reflexivity ].
  (* icode_empty *)
  - intros E G HE IHE E2 n2 H; inversion H; subst.
    split; [ apply IHE; assumption | reflexivity ].
  (* icode_pi_rel *)
  - intros E G rF lF lG F B brF blF nF nB HE IHE Hr Hl HF IHF HB IHB E2 n2 H;
      inversion H; subst.
    destruct (IHF _ _ ltac:(eassumption)) as [? ?]; subst.
    pose proof (ErRel_fun Hr ltac:(eassumption)) as ?; subst.
    pose proof (ErLvl_fun Hl ltac:(eassumption)) as ?; subst.
    destruct (IHB _ _ ltac:(eassumption)) as [? ?]; subst.
    split; reflexivity.
  (* icode_pi_irr *)
  - intros E G rF lF F B brF blF nF nB HE IHE Hr Hl HF IHF HB IHB E2 n2 H;
      inversion H; subst.
    destruct (IHF _ _ ltac:(eassumption)) as [? ?]; subst.
    pose proof (ErRel_fun Hr ltac:(eassumption)) as ?; subst.
    pose proof (ErLvl_fun Hl ltac:(eassumption)) as ?; subst.
    destruct (IHB _ _ ltac:(eassumption)) as [? ?]; subst.
    split; reflexivity.
  (* icode_hd *)
  - intros E G i A br bl HE IHE HT IHT E2 n2 H; inversion H; subst.
    destruct (IHT _ _ ltac:(eassumption)) as [? Heq]; subst.
    injection Heq as ? ?; subst.
    split; reflexivity.
  (* icode_subst *)
  - intros E E' G G' g i A v s n HE IHE HE' IHE' Hs IHs Hv IHv E2 n2 H;
      inversion H; subst.
    destruct (IHs _ _ _ ltac:(eassumption)) as [? [? ?]]; subst.
    destruct (IHv _ _ ltac:(eassumption)) as [? ?]; subst.
    split; reflexivity.
  (* isub_id *)
  - intros E G HE IHE E2 E2' s2 H; inversion H; subst.
    pose proof (IHE _ ltac:(eassumption)) as ?; subst.
    repeat split.
  (* isub_forget *)
  - intros E G HE IHE E2 E2' s2 H; inversion H; subst.
    pose proof (IHE _ ltac:(eassumption)) as ?; subst.
    repeat split.
  (* isub_wkn *)
  - intros E G i A T HE IHE HT IHT E2 E2' s2 H; inversion H; subst.
    destruct (IHT _ _ ltac:(eassumption)) as [? ?]; subst.
    repeat split.
  (* isub_cmp *)
  - intros E1 E2 E3 G1 G2 G3 f g sf sg H1 IH1 H2 IH2 H3 IH3 Hf IHf Hg IHg
      Ea Eb s2 H; inversion H; subst.
    destruct (IHf _ _ _ ltac:(eassumption)) as [? [? ?]]; subst.
    destruct (IHg _ _ _ ltac:(eassumption)) as [? [? ?]]; subst.
    repeat split.
  (* isub_snoc_U *)
  - intros E E' G G' i A g v s br bl n HE IHE HE' IHE' Hs IHs HT IHT Hv IHv
      Ea Eb s2 H; inversion H; subst.
    + destruct (IHs _ _ _ ltac:(eassumption)) as [? [? ?]]; subst.
      destruct (IHT _ _ ltac:(eassumption)) as [? Heq]; subst.
      destruct (IHv _ _ ltac:(eassumption)) as [? ?]; subst.
      injection Heq as ? ?; subst.
      repeat split.
    + destruct (IHT _ _ ltac:(eassumption)) as [? Heq]; discriminate Heq.
  (* isub_snoc_El *)
  - intros E E' G G' i A g v s br bl n HE IHE HE' IHE' Hs IHs HT IHT
      Ea Eb s2 H; inversion H; subst.
    + destruct (IHT _ _ ltac:(eassumption)) as [? Heq]; discriminate Heq.
    + destruct (IHs _ _ _ ltac:(eassumption)) as [? [? ?]]; subst.
      destruct (IHT _ _ ltac:(eassumption)) as [? Heq]; subst.
      injection Heq as ? ? ?; subst.
      repeat split.
Qed.

Definition IEnv_fun := proj1 I_fun.
Definition ITy_fun := proj1 (proj2 I_fun).
Definition ICode_fun := proj1 (proj2 (proj2 I_fun)).
Definition ISub_fun := proj2 (proj2 (proj2 I_fun)).

Lemma isU_tsub s T : isU (tsub s T) = isU T.
Proof. destruct T; reflexivity. Qed.

Lemma I_wf :
  (forall G E, IEnv G E -> True)
  /\ (forall E A T, ITy E A T -> twf E T)
  /\ (forall E c n, ICode E c n -> cwf E n)
  /\ (forall E E' g s, ISub E E' g s -> swf E E' s).
Proof.
  apply I_mutind; try (intros; exact I).
  (* ity_El *)
  - intros; cbn; assumption.
  (* ity_subst *)
  - intros E E' G G' g i A T s HE _ HE' _ Hs IHs HT IHT.
    eapply twf_tsub; eassumption.
  (* icode_pi_rel *)
  - intros E G rF lF lG F B brF blF nF nB HE _ Hr Hl HF IHF HB IHB.
    cbn; split; assumption.
  (* icode_pi_irr *)
  - intros E G rF lF F B brF blF nF nB HE _ Hr Hl HF IHF HB IHB.
    cbn; split; assumption.
  (* icode_hd *)
  - intros; cbn; reflexivity.
  (* icode_subst *)
  - intros E E' G G' g i A v s n HE _ HE' _ Hs IHs Hv IHv.
    eapply cwf_csub; eassumption.
  (* isub_id *)
  - intros E G HE _ k Hk; cbn; exact Hk.
  (* isub_forget *)
  - intros E G HE _ k Hk; unfold isUat in Hk; destruct k; discriminate.
  (* isub_wkn *)
  - intros E G i A T HE _ HT _ k Hk; cbn; rewrite isUat_cons_S; exact Hk.
  (* isub_cmp *)
  - intros E1 E2 E3 G1 G2 G3 f g sf sg H1 _ H2 _ H3 _ Hf IHf Hg IHg k Hk.
    unfold rcmp; eapply cwf_csub; [ exact IHf | apply IHg; exact Hk ].
  (* isub_snoc_U *)
  - intros E E' G G' i A g v s br bl n HE _ HE' _ Hs IHs HT _ Hv IHv [|k] Hk.
    + exact IHv.
    + apply IHs; exact Hk.
  (* isub_snoc_El *)
  - intros E E' G G' i A g v s br bl n HE _ HE' _ Hs IHs HT _ [|k] Hk.
    + cbn in Hk; discriminate.
    + apply IHs; exact Hk.
Qed.

Definition ITy_twf := proj1 (proj2 I_wf).
Definition ICode_cwf := proj1 (proj2 (proj2 I_wf)).
Definition ISub_swf := proj2 (proj2 (proj2 I_wf)).

(* U-ness of a type is read off its interpretation, so it is stable under
   provable equality: that is what makes the [exp] row of [rceq_term]
   well defined. *)
Lemma ITy_USkel E A T : ITy E A T -> USkel A = isU T.
Proof.
  induction 1; cbn; try reflexivity.
  rewrite isU_tsub; exact IHITy.
Qed.

(* =====================================================================
   6.  The model.
   ===================================================================== *)

Definition Req_env (G1 G2 : term) : Prop := exists E, IEnv G1 E /\ IEnv G2 E.

Definition Req_ty (G A1 A2 : term) : Prop :=
  exists E T, IEnv G E /\ ITy E A1 T /\ ITy E A2 T.

Definition Req_code (G e1 e2 : term) : Prop :=
  exists E n, IEnv G E /\ ICode E e1 n /\ ICode E e2 n.

Definition Req_sub (G G' g1 g2 : term) : Prop :=
  exists E E' s1 s2,
    IEnv G E /\ IEnv G' E'
    /\ ISub E E' g1 s1 /\ ISub E E' g2 s2 /\ subeq E' s1 s2.

Definition rceq_term (t : sort) (e1 e2 : term) : Prop :=
  match t with
  | scon nm [] =>
      if eqb nm "relevance" then exists b, ErRel e1 b /\ ErRel e2 b
      else if eqb nm "lvl" then exists b, ErLvl e1 b /\ ErLvl e2 b
      else if eqb nm "tlvl" then ntlvl e1 = ntlvl e2
      else if eqb nm "tyinfo" then ninfo e1 = ninfo e2
      else if eqb nm "env" then Req_env e1 e2
      else True
  | scon nm [x; y] =>
      if eqb nm "sub" then Req_sub y x e1 e2
      else if eqb nm "ty" then Req_ty y e1 e2
      else True
  | scon nm [A; i; G] =>
      if eqb nm "exp" then (if USkel A then Req_code G e1 e2 else True)
      else True
  | _ => True
  end.

Definition rceq_sort (t1 t2 : sort) : Prop :=
  forall e1 e2, rceq_term t1 e1 e2 <-> rceq_term t2 e1 e2.

Definition RigCM : CutTModel := {| ceq_sort := rceq_sort; ceq_term := rceq_term |}.

(* ---- clause readings (all by conversion) ---- *)

Lemma rceq_rel_eq r1 r2
  : rceq_term sRelevance r1 r2 = exists b, ErRel r1 b /\ ErRel r2 b.
Proof. reflexivity. Qed.

Lemma rceq_lvl_eq l1 l2
  : rceq_term sLvl l1 l2 = exists b, ErLvl l1 b /\ ErLvl l2 b.
Proof. reflexivity. Qed.

Lemma rceq_tlvl_eq n1 n2 : rceq_term sTlvl n1 n2 = (ntlvl n1 = ntlvl n2).
Proof. reflexivity. Qed.

Lemma rceq_info_eq i1 i2 : rceq_term sInfo i1 i2 = (ninfo i1 = ninfo i2).
Proof. reflexivity. Qed.

Lemma rceq_ltl_eq a b p1 p2 : rceq_term (sLtl a b) p1 p2 = True.
Proof. reflexivity. Qed.

Lemma rceq_env_eq G1 G2 : rceq_term sEnv G1 G2 = Req_env G1 G2.
Proof. reflexivity. Qed.

Lemma rceq_sub_eq G G' g1 g2 : rceq_term (sSub G G') g1 g2 = Req_sub G G' g1 g2.
Proof. reflexivity. Qed.

Lemma rceq_ty_eq G i A1 A2 : rceq_term (sTy G i) A1 A2 = Req_ty G A1 A2.
Proof. reflexivity. Qed.

Lemma rceq_exp_eq G i A e1 e2
  : rceq_term (sExp G i A) e1 e2
    = (if USkel A then Req_code G e1 e2 else True).
Proof. reflexivity. Qed.

(* =====================================================================
   7.  The structural obligations of [CutTModel_ok].

   [cterm_conv], [csort_trans], [csort_sym] are immediate because
   [rceq_sort] IS the bidirectional transfer of [rceq_term]; [csort_by] is
   vacuous ([ott_dtt] has no sort equations); [cterm_var] is vacuous (the
   meta-context is empty, openness being object-level).
   ===================================================================== *)

Lemma Req_env_sym G1 G2 : Req_env G1 G2 -> Req_env G2 G1.
Proof. intros [E [H1 H2]]; exists E; split; assumption. Qed.

Lemma Req_env_trans G1 G12 G2
  : Req_env G1 G12 -> Req_env G12 G2 -> Req_env G1 G2.
Proof.
  intros [E [H1 H2]] [E' [H3 H4]].
  pose proof (IEnv_fun H2 H3) as Heq; subst.
  eexists; split; eassumption.
Qed.

Lemma Req_ty_sym G A1 A2 : Req_ty G A1 A2 -> Req_ty G A2 A1.
Proof. intros [E [T [H1 [H2 H3]]]]; exists E, T; repeat split; assumption. Qed.

Lemma Req_ty_trans G A1 A12 A2
  : Req_ty G A1 A12 -> Req_ty G A12 A2 -> Req_ty G A1 A2.
Proof.
  intros [E [T [H1 [H2 H3]]]] [E' [T' [H4 [H5 H6]]]].
  destruct (ITy_fun H3 H5) as [? ?]; subst.
  exists E', T'; repeat split; assumption.
Qed.

Lemma Req_code_sym G e1 e2 : Req_code G e1 e2 -> Req_code G e2 e1.
Proof. intros [E [n [H1 [H2 H3]]]]; exists E, n; repeat split; assumption. Qed.

Lemma Req_code_trans G e1 e12 e2
  : Req_code G e1 e12 -> Req_code G e12 e2 -> Req_code G e1 e2.
Proof.
  intros [E [n [H1 [H2 H3]]]] [E' [n' [H4 [H5 H6]]]].
  destruct (ICode_fun H3 H5) as [? ?]; subst.
  exists E', n'; repeat split; assumption.
Qed.

Lemma Req_sub_sym G G' g1 g2 : Req_sub G G' g1 g2 -> Req_sub G G' g2 g1.
Proof.
  intros [E [E' [s1 [s2 [H1 [H2 [H3 [H4 H5]]]]]]]].
  exists E, E', s2, s1; repeat split; try assumption.
  intros k Hk; symmetry; apply H5; assumption.
Qed.

Lemma Req_sub_trans G G' g1 g12 g2
  : Req_sub G G' g1 g12 -> Req_sub G G' g12 g2 -> Req_sub G G' g1 g2.
Proof.
  intros [E [E' [s1 [s12 [H1 [H2 [H3 [H4 H5]]]]]]]].
  intros [Ea [Eb [s12' [s2 [K1 [K2 [K3 [K4 K5]]]]]]]].
  destruct (ISub_fun H4 K3) as [? [? ?]]; subst.
  exists Ea, Eb, s1, s2; repeat split; try assumption.
  intros k Hk; rewrite H5 by assumption; apply K5; assumption.
Qed.

(* The case analysis every sort-generic obligation needs: the four
   argument-list shapes [rceq_term] distinguishes, and then the name
   tests. *)
Ltac rcases t :=
  let nm := fresh "nm" in
  let l := fresh "l" in
  destruct t as [nm l];
  destruct l as [ | ?x [ | ?y [ | ?z [ | ?w ?l ] ] ] ];
  cbn [rceq_term];
  repeat match goal with
    | [ |- context [ if eqb nm ?s then _ else _ ] ] => destruct (eqb nm s)
    end.

Lemma term_sym_obligation t e1 e2 : rceq_term t e1 e2 -> rceq_term t e2 e1.
Proof.
  rcases t; intro H;
    try exact I;
    try (destruct H as [b [H1 H2]]; exists b; split; assumption);
    try (symmetry; exact H);
    try (apply Req_env_sym; exact H);
    try (apply Req_sub_sym; exact H);
    try (apply Req_ty_sym; exact H).
  (* exp *)
  all: try (destruct (USkel x); [ apply Req_code_sym; exact H | exact I ]).
Qed.

Lemma term_trans_obligation t e1 e12 e2
  : rceq_term t e1 e12 -> rceq_term t e12 e2 -> rceq_term t e1 e2.
Proof.
  rcases t; intros H K;
    try exact I;
    try (destruct H as [b [H1 H2]]; destruct K as [b' [K1 K2]];
         pose proof (ErRel_fun H2 K1) as ?; subst; exists b';
         split; assumption);
    try (destruct H as [b [H1 H2]]; destruct K as [b' [K1 K2]];
         pose proof (ErLvl_fun H2 K1) as ?; subst; exists b';
         split; assumption);
    try (etransitivity; eassumption);
    try (eapply Req_env_trans; eassumption);
    try (eapply Req_sub_trans; eassumption);
    try (eapply Req_ty_trans; eassumption).
  all: try (destruct (USkel x); [ eapply Req_code_trans; eassumption | exact I ]).
Qed.

Lemma term_conv_obligation t1 t2 e1 e2
  : rceq_sort t1 t2 -> rceq_term t1 e1 e2 -> rceq_term t2 e1 e2.
Proof. intros Ht H; apply Ht; exact H. Qed.

Lemma sort_trans_obligation t1 t12 t2
  : rceq_sort t1 t12 -> rceq_sort t12 t2 -> rceq_sort t1 t2.
Proof.
  intros H K e1 e2; split; intro X.
  - apply K; apply H; exact X.
  - apply H; apply K; exact X.
Qed.

Lemma sort_sym_obligation t1 t2 : rceq_sort t1 t2 -> rceq_sort t2 t1.
Proof. intros H e1 e2; split; intro X; apply H; exact X. Qed.

Lemma var_obligation
  : forall n t, In (n, t) (@nil (string * sort)) -> rceq_term t (var n) (var n).
Proof. intros n t H; destruct H. Qed.

(* =====================================================================
   8.  The rule obligations.

   [ott_dtt] is a closed 69-element list, so [In] is a concrete
   disjunction; [vm_compute] pins it before destructing, exactly as
   Gluing/Stlc/ModelCong.v does (left unreduced each rule instance is
   prohibitively slow).
   ===================================================================== *)

Ltac nrm :=
  repeat match goal with
    | [ H : rceq_term ?t ?a ?b |- _ ] =>
        let t' := eval vm_compute in t in
        let a' := eval vm_compute in a in
        let b' := eval vm_compute in b in
        tryif (constr_eq t t'; constr_eq a a'; constr_eq b b')
        then fail
        else change_no_check (rceq_term t' a' b') in H
    | [ |- rceq_term ?t ?a ?b ] =>
        let t' := eval vm_compute in t in
        let a' := eval vm_compute in a in
        let b' := eval vm_compute in b in
        tryif (constr_eq t t'; constr_eq a a'; constr_eq b b')
        then fail
        else change_no_check (rceq_term t' a' b')
    end.

Ltac decomp :=
  match goal with
  | [ Hin : In _ ott_dtt |- _ ] =>
      vm_compute in Hin;
      repeat (destruct Hin as [Hin|Hin]); try discriminate;
      inversion Hin; subst; clear Hin
  end;
  repeat match goal with
    | [ H : ceq_args (_::_) _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ceq_args [] _ _ |- _ ] => inversion H; subst; clear H
    end;
  cbn [ceq_term ceq_sort RigCM] in *; nrm.

(* [csort_by] is vacuous: [ott_dtt] has no sort equations at all. *)
Lemma sort_by_obligation
  : forall c' name t1 t2 s1 s2,
    In (name, sort_eq_rule c' t1 t2) ott_dtt ->
    ceq_args (CM := RigCM) c' s1 s2 ->
    rceq_sort t1[/with_names_from c' s1/] t2[/with_names_from c' s2/].
Proof.
  intros c' name t1 t2 s1 s2 Hin Hargs.
  vm_compute in Hin; repeat (destruct Hin as [Hin|Hin]);
    first [ discriminate | destruct Hin ].
Qed.

(* ---- introduction / elimination for each clause (all by conversion) ---- *)

Lemma rceq_rel_i r1 r2 : (exists b, ErRel r1 b /\ ErRel r2 b) -> rceq_term sRelevance r1 r2.
Proof. exact (fun x => x). Qed.
Lemma rceq_rel_e r1 r2 : rceq_term sRelevance r1 r2 -> exists b, ErRel r1 b /\ ErRel r2 b.
Proof. exact (fun x => x). Qed.
Lemma rceq_lvl_i l1 l2 : (exists b, ErLvl l1 b /\ ErLvl l2 b) -> rceq_term sLvl l1 l2.
Proof. exact (fun x => x). Qed.
Lemma rceq_lvl_e l1 l2 : rceq_term sLvl l1 l2 -> exists b, ErLvl l1 b /\ ErLvl l2 b.
Proof. exact (fun x => x). Qed.
Lemma rceq_tlvl_i n1 n2 : ntlvl n1 = ntlvl n2 -> rceq_term sTlvl n1 n2.
Proof. exact (fun x => x). Qed.
Lemma rceq_tlvl_e n1 n2 : rceq_term sTlvl n1 n2 -> ntlvl n1 = ntlvl n2.
Proof. exact (fun x => x). Qed.
Lemma rceq_info_i i1 i2 : ninfo i1 = ninfo i2 -> rceq_term sInfo i1 i2.
Proof. exact (fun x => x). Qed.
Lemma rceq_info_e i1 i2 : rceq_term sInfo i1 i2 -> ninfo i1 = ninfo i2.
Proof. exact (fun x => x). Qed.
Lemma rceq_env_i G1 G2 : Req_env G1 G2 -> rceq_term sEnv G1 G2.
Proof. exact (fun x => x). Qed.
Lemma rceq_env_e G1 G2 : rceq_term sEnv G1 G2 -> Req_env G1 G2.
Proof. exact (fun x => x). Qed.
Lemma rceq_sub_i G G' g1 g2 : Req_sub G G' g1 g2 -> rceq_term (sSub G G') g1 g2.
Proof. exact (fun x => x). Qed.
Lemma rceq_sub_e G G' g1 g2 : rceq_term (sSub G G') g1 g2 -> Req_sub G G' g1 g2.
Proof. exact (fun x => x). Qed.
Lemma rceq_ty_i G i A1 A2 : Req_ty G A1 A2 -> rceq_term (sTy G i) A1 A2.
Proof. exact (fun x => x). Qed.
Lemma rceq_ty_e G i A1 A2 : rceq_term (sTy G i) A1 A2 -> Req_ty G A1 A2.
Proof. exact (fun x => x). Qed.

Lemma rceq_exp_i G i A e1 e2
  : (USkel A = true -> Req_code G e1 e2) -> rceq_term (sExp G i A) e1 e2.
Proof.
  intro H; change (if USkel A then Req_code G e1 e2 else True).
  destruct (USkel A) eqn:Hu; [ apply H; reflexivity | exact I ].
Qed.

Lemma rceq_exp_e G i A e1 e2
  : USkel A = true -> rceq_term (sExp G i A) e1 e2 -> Req_code G e1 e2.
Proof.
  intros Hu H; change (if USkel A then Req_code G e1 e2 else True) in H.
  rewrite Hu in H; exact H.
Qed.

Lemma rceq_code_i G r l e1 e2 : Req_code G e1 e2 -> rceq_term (sCode G r l) e1 e2.
Proof. exact (fun x => x). Qed.
Lemma rceq_code_e G r l e1 e2 : rceq_term (sCode G r l) e1 e2 -> Req_code G e1 e2.
Proof. exact (fun x => x). Qed.

(* ---- transfer along a provable equality of environments ---- *)

Lemma Req_env_transfer G1 G2 : Req_env G1 G2 -> forall E, IEnv G1 E -> IEnv G2 E.
Proof.
  intros [E0 [H1 H2]] E H; pose proof (IEnv_fun H H1) as ?; subst; assumption.
Qed.

Lemma Req_code_transfer G1 G2 e1 e2
  : Req_env G1 G2 -> Req_code G1 e1 e2 -> Req_code G2 e1 e2.
Proof.
  intros HG [E [n [H1 [H2 H3]]]]; exists E, n; repeat split; try assumption.
  eapply Req_env_transfer; eassumption.
Qed.

Lemma Req_ty_transfer G1 G2 A1 A2
  : Req_env G1 G2 -> Req_ty G1 A1 A2 -> Req_ty G2 A1 A2.
Proof.
  intros HG [E [T [H1 [H2 H3]]]]; exists E, T; repeat split; try assumption.
  eapply Req_env_transfer; eassumption.
Qed.

Lemma Req_sub_transfer G1 G2 G1' G2' g1 g2
  : Req_env G1 G2 -> Req_env G1' G2' -> Req_sub G1 G1' g1 g2 -> Req_sub G2 G2' g1 g2.
Proof.
  intros HG HG' [E [E' [s1 [s2 [H1 [H2 [H3 [H4 H5]]]]]]]].
  exists E, E', s1, s2; repeat split; try assumption;
    eapply Req_env_transfer; eassumption.
Qed.

(* ---- [csort_cong]: the 9 sort rules ---- *)

Lemma sort_cong_refl t : rceq_sort t t.
Proof. intros e1 e2; split; exact (fun x => x). Qed.

Lemma sort_cong_ltl a1 a2 b1 b2 : rceq_sort (sLtl a1 b1) (sLtl a2 b2).
Proof. intros e1 e2; split; intros _; exact I. Qed.

Lemma sort_cong_ty G1 G2 i1 i2
  : Req_env G1 G2 -> rceq_sort (sTy G1 i1) (sTy G2 i2).
Proof.
  intros HG u v; split; intro H; apply rceq_ty_i;
    eapply Req_ty_transfer; try (apply rceq_ty_e in H; exact H).
  - exact HG.
  - apply Req_env_sym; exact HG.
Qed.

Lemma sort_cong_sub G1 G2 G1' G2'
  : Req_env G1 G2 -> Req_env G1' G2' -> rceq_sort (sSub G1 G1') (sSub G2 G2').
Proof.
  intros HG HG' u v; split; intro H; apply rceq_sub_i;
    eapply Req_sub_transfer; try (apply rceq_sub_e in H; exact H).
  - exact HG.
  - exact HG'.
  - apply Req_env_sym; exact HG.
  - apply Req_env_sym; exact HG'.
Qed.

Lemma sort_cong_exp G1 G2 i1 i2 A1 A2
  : Req_env G1 G2 -> Req_ty G2 A1 A2 ->
    rceq_sort (sExp G1 i1 A1) (sExp G2 i2 A2).
Proof.
  intros HG HA u v.
  destruct HA as [E [T [HE [H1 H2]]]].
  pose proof (ITy_USkel H1) as Hu1; pose proof (ITy_USkel H2) as Hu2.
  split; intro H; apply rceq_exp_i; intro Hs.
  - eapply Req_code_transfer; [ exact HG | ].
    eapply rceq_exp_e; [ | exact H ]; rewrite Hu1, <- Hu2; exact Hs.
  - eapply Req_code_transfer; [ apply Req_env_sym; exact HG | ].
    eapply rceq_exp_e; [ | exact H ]; rewrite Hu2, <- Hu1; exact Hs.
Qed.

Lemma sort_cong_obligation
  : forall c' name args s1 s2,
    In (name, sort_rule c' args) ott_dtt ->
    ceq_args (CM := RigCM) c' s1 s2 ->
    rceq_sort (scon name s1) (scon name s2).
Proof.
  intros c' name args s1 s2 Hin Hargs.
  decomp.
  - (* exp *)
    apply sort_cong_exp;
      [ apply rceq_env_e; assumption | eapply rceq_ty_e; eassumption ].
  - (* ty *) apply sort_cong_ty; apply rceq_env_e; assumption.
  - (* sub *) apply sort_cong_sub; apply rceq_env_e; assumption.
  - (* env *) apply sort_cong_refl.
  - (* tyinfo *) apply sort_cong_refl.
  - (* tlvl *) apply sort_cong_refl.
  - (* ltl *) apply sort_cong_ltl.
  - (* lvl *) apply sort_cong_refl.
  - (* relevance *) apply sort_cong_refl.
Qed.

(* ---- smart constructors for the four [Req_*] relations ---- *)

Lemma Req_env_mk G1 G2 E : IEnv G1 E -> IEnv G2 E -> Req_env G1 G2.
Proof. intros; exists E; split; assumption. Qed.

Lemma Req_ty_mk G A1 A2 E T
  : IEnv G E -> ITy E A1 T -> ITy E A2 T -> Req_ty G A1 A2.
Proof. intros; exists E, T; repeat split; assumption. Qed.

Lemma Req_code_mk G e1 e2 E n
  : IEnv G E -> ICode E e1 n -> ICode E e2 n -> Req_code G e1 e2.
Proof. intros; exists E, n; repeat split; assumption. Qed.

Lemma Req_sub_mk G G' g1 g2 E E' s1 s2
  : IEnv G E -> IEnv G' E' -> ISub E E' g1 s1 -> ISub E E' g2 s2 ->
    subeq E' s1 s2 -> Req_sub G G' g1 g2.
Proof. intros; exists E, E', s1, s2; repeat split; assumption. Qed.

(* ---- [cterm_cong]: the 32 term rules ----

   Only the 24 whose conclusion sort is not an [El] carry content; the
   other 8 ([zero], [suc], [Emptyrec], [lam_rel], [lam_irr], [app_rel],
   [app_irr], [L0<L1]) are [exact I].  *)

Lemma cong_emp : Req_env oEmp oEmp.
Proof. eapply Req_env_mk with (E := @nil rty); constructor. Qed.

Lemma cong_ext G1 G2 i1 i2 A1 A2
  : Req_env G1 G2 -> Req_ty G2 A1 A2 -> Req_env (oExt G1 i1 A1) (oExt G2 i2 A2).
Proof.
  intros HG [E [T [HE [H1 H2]]]].
  eapply Req_env_mk with (E := T :: E); econstructor; try eassumption.
  eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact HE ].
Qed.

Lemma cong_id G1 G2 : Req_env G1 G2 -> Req_sub G2 G2 (oId G1) (oId G2).
Proof.
  intros [E [H1 H2]].
  eapply Req_sub_mk with (E := E) (E' := E) (s1 := rid) (s2 := rid).
  - exact H2.
  - exact H2.
  - constructor; exact H1.
  - constructor; exact H2.
  - intros k Hk; reflexivity.
Qed.

Lemma cong_forget G1 G2
  : Req_env G1 G2 -> Req_sub G2 oEmp (oForget G1) (oForget G2).
Proof.
  intros [E [H1 H2]].
  eapply Req_sub_mk with (E := E) (E' := @nil rty)
                         (s1 := rforget) (s2 := rforget).
  - exact H2.
  - constructor.
  - constructor; exact H1.
  - constructor; exact H2.
  - intros k Hk; reflexivity.
Qed.

Lemma cong_cmp X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_env X3 Y3 ->
    Req_sub Y1 Y2 f1 f2 -> Req_sub Y2 Y3 g1 g2 ->
    Req_sub Y1 Y3 (oCmp X1 X2 X3 f1 g1) (oCmp Y1 Y2 Y3 f2 g2).
Proof.
  intros H1 H2 H3
    [E1 [E2 [sf1 [sf2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [E2' [E3 [sg1 [sg2 [L1 [L2 [L3 [L4 L5]]]]]]]].
  pose proof (IEnv_fun L1 K2) as HE; subst E2'.
  eapply Req_sub_mk with (E := E1) (E' := E3)
                         (s1 := rcmp sf1 sg1) (s2 := rcmp sf2 sg2).
  - exact K1.
  - exact L2.
  - econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact H1 | exact K1 ]
      | eapply Req_env_transfer; [ apply Req_env_sym; exact H2 | exact K2 ]
      | eapply Req_env_transfer; [ apply Req_env_sym; exact H3 | exact L2 ]
      | exact K3 | exact L3 ].
  - econstructor; [ exact K1 | exact K2 | exact L2 | exact K4 | exact L4 ].
  - intros k Hk; unfold rcmp.
    rewrite (L5 k Hk).
    eapply csub_ext_wf; [ | exact K5 ].
    eapply (ISub_swf L4); exact Hk.
Qed.

Lemma cong_wkn G1 G2 i1 i2 A1 A2
  : Req_env G1 G2 -> Req_ty G2 A1 A2 ->
    Req_sub (oExt G2 i2 A2) G2 (oWkn G1 i1 A1) (oWkn G2 i2 A2).
Proof.
  intros HG [E [T [HE [H1 H2]]]].
  eapply Req_sub_mk with (E := T :: E) (E' := E) (s1 := rshift) (s2 := rshift).
  - econstructor; [ exact HE | exact H2 ].
  - exact HE.
  - econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact HE ]
      | exact H1 ].
  - econstructor; [ exact HE | exact H2 ].
  - intros k Hk; reflexivity.
Qed.

Lemma cong_snoc G1 G2 G1' G2' i1 i2 A1 A2 g1 g2 v1 v2
  : Req_env G1 G2 -> Req_env G1' G2' -> Req_ty G2' A1 A2 ->
    Req_sub G2 G2' g1 g2 ->
    (USkel A2 = true -> Req_code G2 v1 v2) ->
    Req_sub G2 (oExt G2' i2 A2)
      (oSnoc G1 G1' i1 A1 g1 v1) (oSnoc G2 G2' i2 A2 g2 v2).
Proof.
  intros HG HG' [E' [T [HE' [HA1 HA2]]]]
    [Ea [Eb [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]] Hv.
  pose proof (IEnv_fun K2 HE') as HEb; subst Eb.
  pose proof (Req_env_transfer (Req_env_sym HG) K1) as HG1.
  pose proof (Req_env_transfer (Req_env_sym HG') HE') as HG1'.
  destruct T as [ br bl | br bl nc ].
  - (* universe slot: the value is a code *)
    destruct (Hv (ITy_USkel HA2)) as [Ec [n [M1 [M2 M3]]]].
    pose proof (IEnv_fun M1 K1) as HEc; subst Ec.
    eapply Req_sub_mk with (E := Ea) (E' := rt_U br bl :: E')
                           (s1 := rsnoc n s1) (s2 := rsnoc n s2).
    + exact K1.
    + econstructor; [ exact HE' | exact HA2 ].
    + eapply isub_snoc_U;
        [ exact HG1 | exact HG1' | exact K3 | exact HA1 | exact M2 ].
    + eapply isub_snoc_U;
        [ exact K1 | exact HE' | exact K4 | exact HA2 | exact M3 ].
    + intros [|k] Hk; [ reflexivity | apply K5; exact Hk ].
  - (* non-universe slot: both sides carry the same junk *)
    eapply Req_sub_mk with (E := Ea) (E' := rt_El br bl nc :: E')
                           (s1 := rsnoc rc_nat s1) (s2 := rsnoc rc_nat s2).
    + exact K1.
    + econstructor; [ exact HE' | exact HA2 ].
    + eapply isub_snoc_El; [ exact HG1 | exact HG1' | exact K3 | exact HA1 ].
    + eapply isub_snoc_El; [ exact K1 | exact HE' | exact K4 | exact HA2 ].
    + intros [|k] Hk; [ reflexivity | apply K5; exact Hk ].
Qed.

Lemma cong_hd G1 G2 i1 i2 A1 A2
  : Req_env G1 G2 -> Req_ty G2 A1 A2 -> USkel A2 = true ->
    Req_code (oExt G2 i2 A2) (oHd G1 i1 A1) (oHd G2 i2 A2).
Proof.
  intros HG [E [T [HE [H1 H2]]]] Hu.
  rewrite (ITy_USkel H2) in Hu.
  destruct T as [ br bl | br bl nc ]; [ | discriminate ].
  eapply Req_code_mk with (E := rt_U br bl :: E) (n := rc_var 0).
  - econstructor; [ exact HE | exact H2 ].
  - econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact HE ]
      | exact H1 ].
  - econstructor; [ exact HE | exact H2 ].
Qed.

Lemma cong_ty_subst G1 G2 G1' G2' g1 g2 i1 i2 A1 A2
  : Req_env G1 G2 -> Req_env G1' G2' -> Req_sub G2 G2' g1 g2 ->
    Req_ty G2' A1 A2 ->
    Req_ty G2 (oTySubst G1 G1' g1 i1 A1) (oTySubst G2 G2' g2 i2 A2).
Proof.
  intros HG HG' [Ea [Eb [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [E' [T [HE' [H1 H2]]]].
  pose proof (IEnv_fun K2 HE') as HEb; subst Eb.
  assert (tsub s1 T = tsub s2 T) as Hts
      by (eapply tsub_ext_wf; [ eapply ITy_twf; exact H1 | exact K5 ]).
  eapply Req_ty_mk with (E := Ea) (T := tsub s2 T).
  - exact K1.
  - rewrite <- Hts.
    econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact K1 ]
      | eapply Req_env_transfer; [ apply Req_env_sym; exact HG' | exact HE' ]
      | exact K3 | exact H1 ].
  - econstructor; [ exact K1 | exact HE' | exact K4 | exact H2 ].
Qed.

Lemma cong_exp_subst G1 G2 G1' G2' g1 g2 i1 i2 A1 A2 v1 v2
  : Req_env G1 G2 -> Req_env G1' G2' -> Req_sub G2 G2' g1 g2 ->
    Req_code G2' v1 v2 ->
    Req_code G2 (oExpSubst G1 G1' g1 i1 A1 v1) (oExpSubst G2 G2' g2 i2 A2 v2).
Proof.
  intros HG HG' [Ea [Eb [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]] [Ec [n [M1 [M2 M3]]]].
  pose proof (IEnv_fun M1 K2) as HEc; subst Ec.
  assert (csub s1 n = csub s2 n) as Hcs
      by (eapply csub_ext_wf; [ eapply ICode_cwf; exact M2 | exact K5 ]).
  eapply Req_code_mk with (E := Ea) (n := csub s2 n).
  - exact K1.
  - rewrite <- Hcs.
    econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact K1 ]
      | eapply Req_env_transfer; [ apply Req_env_sym; exact HG' | exact K2 ]
      | exact K3 | exact M2 ].
  - econstructor; [ exact K1 | exact K2 | exact K4 | exact M3 ].
Qed.

Lemma cong_U G1 G2 r1 r2 l1 l2
  : Req_env G1 G2 -> (exists b, ErRel r1 b /\ ErRel r2 b) ->
    (exists b, ErLvl l1 b /\ ErLvl l2 b) ->
    Req_ty G2 (oU G1 r1 l1) (oU G2 r2 l2).
Proof.
  intros [E [HE1 HE2]] [br [Hr1 Hr2]] [bl [Hl1 Hl2]].
  eapply Req_ty_mk with (E := E) (T := rt_U br bl).
  - exact HE2.
  - econstructor; [ exact HE1 | exact Hr1 | exact Hl1 ].
  - econstructor; [ exact HE2 | exact Hr2 | exact Hl2 ].
Qed.

Lemma cong_El G1 G2 r1 r2 l1 l2 c1 c2
  : Req_env G1 G2 -> (exists b, ErRel r1 b /\ ErRel r2 b) ->
    (exists b, ErLvl l1 b /\ ErLvl l2 b) -> Req_code G2 c1 c2 ->
    Req_ty G2 (oEl G1 r1 l1 c1) (oEl G2 r2 l2 c2).
Proof.
  intros HG [br [Hr1 Hr2]] [bl [Hl1 Hl2]] [E [n [HE [Hc1 Hc2]]]].
  eapply Req_ty_mk with (E := E) (T := rt_El br bl n).
  - exact HE.
  - econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact HE ]
      | exact Hr1 | exact Hl1 | exact Hc1 ].
  - econstructor; [ exact HE | exact Hr2 | exact Hl2 | exact Hc2 ].
Qed.

Lemma cong_Nat G1 G2 : Req_env G1 G2 -> Req_code G2 (oNat G1) (oNat G2).
Proof.
  intros [E [H1 H2]]; eapply Req_code_mk with (E := E) (n := rc_nat);
    [ exact H2 | econstructor; exact H1 | econstructor; exact H2 ].
Qed.

Lemma cong_Empty G1 G2 : Req_env G1 G2 -> Req_code G2 (oEmpty G1) (oEmpty G2).
Proof.
  intros [E [H1 H2]]; eapply Req_code_mk with (E := E) (n := rc_empty);
    [ exact H2 | econstructor; exact H1 | econstructor; exact H2 ].
Qed.

Lemma cong_Pi_rel G1 G2 rF1 rF2 lF1 lF2 lG1 lG2 F1 F2 B1 B2
  : Req_env G1 G2 -> (exists b, ErRel rF1 b /\ ErRel rF2 b) ->
    (exists b, ErLvl lF1 b /\ ErLvl lF2 b) ->
    Req_code G2 F1 F2 -> Req_code (oExtC G2 rF2 lF2 F2) B1 B2 ->
    Req_code G2 (oPiRel G1 rF1 lF1 lG1 F1 B1) (oPiRel G2 rF2 lF2 lG2 F2 B2).
Proof.
  intros HG [br [Hr1 Hr2]] [bl [Hl1 Hl2]] [E [nF [HE [HF1 HF2]]]]
    [E2 [nB [HE2 [HB1 HB2]]]].
  assert (IEnv (oExtC G2 rF2 lF2 F2) (rt_El br bl nF :: E)) as HX
      by (eapply IEnv_extC; eassumption).
  pose proof (IEnv_fun HE2 HX) as HE2eq; subst E2.
  eapply Req_code_mk with (E := E) (n := rc_pi true br bl nF nB).
  - exact HE.
  - econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact HE ]
      | exact Hr1 | exact Hl1 | exact HF1 | exact HB1 ].
  - econstructor; [ exact HE | exact Hr2 | exact Hl2 | exact HF2 | exact HB2 ].
Qed.

Lemma cong_Pi_irr G1 G2 rF1 rF2 lF1 lF2 F1 F2 B1 B2
  : Req_env G1 G2 -> (exists b, ErRel rF1 b /\ ErRel rF2 b) ->
    (exists b, ErLvl lF1 b /\ ErLvl lF2 b) ->
    Req_code G2 F1 F2 -> Req_code (oExtC G2 rF2 lF2 F2) B1 B2 ->
    Req_code G2 (oPiIrr G1 rF1 lF1 F1 B1) (oPiIrr G2 rF2 lF2 F2 B2).
Proof.
  intros HG [br [Hr1 Hr2]] [bl [Hl1 Hl2]] [E [nF [HE [HF1 HF2]]]]
    [E2 [nB [HE2 [HB1 HB2]]]].
  assert (IEnv (oExtC G2 rF2 lF2 F2) (rt_El br bl nF :: E)) as HX
      by (eapply IEnv_extC; eassumption).
  pose proof (IEnv_fun HE2 HX) as HE2eq; subst E2.
  eapply Req_code_mk with (E := E) (n := rc_pi false br bl nF nB).
  - exact HE.
  - econstructor;
      [ eapply Req_env_transfer; [ apply Req_env_sym; exact HG | exact HE ]
      | exact Hr1 | exact Hl1 | exact HF1 | exact HB1 ].
  - econstructor; [ exact HE | exact Hr2 | exact Hl2 | exact HF2 | exact HB2 ].
Qed.

Lemma cong_info r1 r2 n1 n2
  : (exists b, ErRel r1 b /\ ErRel r2 b) -> ntlvl n1 = ntlvl n2 ->
    ninfo (oInfo r1 n1) = ninfo (oInfo r2 n2).
Proof.
  intros [b [H1 H2]] Hn.
  pose proof (ErRel_inj H1 H2) as Hrr; subst.
  rewrite !ninfo_oInfo, Hn; reflexivity.
Qed.

Lemma cong_next l1 l2
  : (exists b, ErLvl l1 b /\ ErLvl l2 b) -> ntlvl (oNext l1) = ntlvl (oNext l2).
Proof.
  intros [b [H1 H2]]; pose proof (ErLvl_inj H1 H2) as Hll; subst; reflexivity.
Qed.

Lemma cong_iota l1 l2
  : (exists b, ErLvl l1 b /\ ErLvl l2 b) -> ntlvl (oIota l1) = ntlvl (oIota l2).
Proof.
  intros [b [H1 H2]]; pose proof (ErLvl_inj H1 H2) as Hll; subst; reflexivity.
Qed.

Lemma rceq_exp_e' G i A e1 e2
  : rceq_term (sExp G i A) e1 e2 -> USkel A = true -> Req_code G e1 e2.
Proof.
  intros H Hu; change (if USkel A then Req_code G e1 e2 else True) in H.
  rewrite Hu in H; exact H.
Qed.

Lemma cong_obligation
  : forall c' name args t s1 s2,
    In (name, term_rule c' args t) ott_dtt ->
    ceq_args (CM := RigCM) c' s1 s2 ->
    rceq_term t[/with_names_from c' s2/] (con name s1) (con name s2).
Proof.
  intros c' name args t s1 s2 Hin Hargs.
  decomp; try exact I.
  - (* Pi_irr *)
    apply rceq_exp_i; intros _; apply cong_Pi_irr;
      solve [ apply rceq_env_e; eassumption
            | apply rceq_rel_e; eassumption
            | apply rceq_lvl_e; eassumption
            | eapply rceq_exp_e'; [ eassumption | reflexivity ] ].
  - (* Pi_rel *)
    apply rceq_exp_i; intros _; apply cong_Pi_rel;
      solve [ apply rceq_env_e; eassumption
            | apply rceq_rel_e; eassumption
            | apply rceq_lvl_e; eassumption
            | eapply rceq_exp_e'; [ eassumption | reflexivity ] ].
  - (* Empty *)
    apply rceq_exp_i; intros _; apply cong_Empty; apply rceq_env_e; eassumption.
  - (* Nat *)
    apply rceq_exp_i; intros _; apply cong_Nat; apply rceq_env_e; eassumption.
  - (* El *)
    apply rceq_ty_i; apply cong_El;
      solve [ apply rceq_env_e; eassumption
            | apply rceq_rel_e; eassumption
            | apply rceq_lvl_e; eassumption
            | eapply rceq_exp_e'; [ eassumption | reflexivity ] ].
  - (* U *)
    apply rceq_ty_i; apply cong_U;
      solve [ apply rceq_env_e; eassumption
            | apply rceq_rel_e; eassumption
            | apply rceq_lvl_e; eassumption ].
  - (* hd *)
    apply rceq_exp_i; intro Hu; apply cong_hd;
      solve [ apply rceq_env_e; eassumption
            | eapply rceq_ty_e; eassumption
            | exact Hu ].
  - (* wkn *)
    apply rceq_sub_i; apply cong_wkn;
      solve [ apply rceq_env_e; eassumption
            | eapply rceq_ty_e; eassumption ].
  - (* snoc *)
    apply rceq_sub_i; apply cong_snoc;
      solve [ apply rceq_env_e; eassumption
            | eapply rceq_ty_e; eassumption
            | apply rceq_sub_e; eassumption
            | (intro Hu; eapply rceq_exp_e'; [ eassumption | exact Hu ]) ].
  - (* ext *)
    apply rceq_env_i; apply cong_ext;
      solve [ apply rceq_env_e; eassumption | eapply rceq_ty_e; eassumption ].
  - (* forget *)
    apply rceq_sub_i; apply cong_forget; apply rceq_env_e; eassumption.
  - (* emp *) apply rceq_env_i; apply cong_emp.
  - (* exp_subst *)
    apply rceq_exp_i; intro Hu; apply cong_exp_subst;
      solve [ apply rceq_env_e; eassumption
            | apply rceq_sub_e; eassumption
            | eapply rceq_exp_e'; [ eassumption | exact Hu ] ].
  - (* ty_subst *)
    apply rceq_ty_i; apply cong_ty_subst;
      solve [ apply rceq_env_e; eassumption
            | apply rceq_sub_e; eassumption
            | eapply rceq_ty_e; eassumption ].
  - (* cmp *)
    apply rceq_sub_i; apply cong_cmp;
      solve [ apply rceq_env_e; eassumption | apply rceq_sub_e; eassumption ].
  - (* id *)
    apply rceq_sub_i; apply cong_id; apply rceq_env_e; eassumption.
  - (* info *)
    apply rceq_info_i; apply cong_info;
      solve [ apply rceq_rel_e; eassumption | apply rceq_tlvl_e; eassumption ].
  - (* next *)
    apply rceq_tlvl_i; apply cong_next; apply rceq_lvl_e; eassumption.
  - (* inf *) apply rceq_tlvl_i; reflexivity.
  - (* iota *)
    apply rceq_tlvl_i; apply cong_iota; apply rceq_lvl_e; eassumption.
  - (* L1 *) apply rceq_lvl_i; exists true; split; constructor.
  - (* L0 *) apply rceq_lvl_i; exists false; split; constructor.
  - (* irr *) apply rceq_rel_i; exists false; split; constructor.
  - (* rel *) apply rceq_rel_i; exists true; split; constructor.
Qed.

(* ---- [cterm_by]: the 28 equations ----

   7 of them live at an [El]-sort and are [exact I]: both beta rules, eta,
   [lam_rel subst], [zero subst], [suc subst] and [ltl_irr].  That is the
   whole content of design section 2 -- no equation of the theory can
   rewrite a code -- and it survived contact with the obligations
   unchanged.  The remaining 21 are the sigma laws, the four [X subst]
   commutations, and the two [tlvl] equations.  *)

(* The lifting of a substitution under a binder, as the object theory
   spells it ([DttSyntax.oLift]), interprets as [rc_nat .: (shift o s)] --
   the head slot is an [El] slot, so its junk value is invisible to
   [subeq], which is exactly why it may differ from [up]'s [rc_var 0]. *)
(* The substituted domain code that [oLift] (and the [Pi] commutations)
   name; it is exactly [oLift]'s own [Fg]. *)
Definition oCodeSub (G G' g rF lF F : term) : term :=
  oExpSubst G G' g (iCode lF) (oU G' rF lF) F.

Lemma ISub_oLift Y1 Y2 g rF lF F E E2 s br bl nF
  : IEnv Y1 E -> IEnv Y2 E2 -> ISub E E2 g s ->
    ErRel rF br -> ErLvl lF bl -> ICode E2 F nF -> ICode E (oCodeSub Y1 Y2 g rF lF F) (csub s nF) ->
    ISub (rt_El br bl (csub s nF) :: E) (rt_El br bl nF :: E2)
      (oLift Y1 Y2 g rF lF F) (rsnoc rc_nat (rcmp rshift s)).
Proof.
  intros HE HE2 Hs Hr Hl HF HFg.
  assert (ITy E (oEl Y1 rF lF (oCodeSub Y1 Y2 g rF lF F))
            (rt_El br bl (csub s nF))) as HTy
      by (econstructor; eassumption).
  assert (IEnv (oExtC Y1 rF lF (oCodeSub Y1 Y2 g rF lF F))
            (rt_El br bl (csub s nF) :: E)) as HEF
      by (unfold oExtC; econstructor; eassumption).
  unfold oLift.
  eapply isub_snoc_El.
  - exact HEF.
  - exact HE2.
  - econstructor; [ exact HEF | exact HE | exact HE2 | | exact Hs ].
    econstructor; [ exact HE | exact HTy ].
  - econstructor; eassumption.
Qed.

Lemma subeq_lift E2 s1 s2 br bl nF
  : subeq E2 s1 s2 ->
    subeq (rt_El br bl nF :: E2) (up s1) (rsnoc rc_nat (rcmp rshift s2)).
Proof.
  intros H [|k] Hk; [ cbn in Hk; discriminate | ].
  unfold up, rsnoc, rcmp; rewrite csub_rshift, (H k Hk); reflexivity.
Qed.

Lemma by_id_left X1 Y1 X2 Y2 g1 g2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    Req_sub Y1 Y2 (oCmp X1 X1 X2 (oId X1) g1) g2.
Proof.
  intros H1 H2 [E [E' [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  eapply Req_sub_mk with (E := E) (E' := E') (s1 := rcmp rid s1) (s2 := s2).
  - exact K1.
  - exact K2.
  - econstructor;
      [ exact HX1 | exact HX1 | exact HX2 | constructor; exact HX1 | exact K3 ].
  - exact K4.
  - intros k Hk; unfold rcmp; rewrite csub_id; apply K5; exact Hk.
Qed.

Lemma by_id_right X1 Y1 X2 Y2 g1 g2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    Req_sub Y1 Y2 (oCmp X1 X2 X2 g1 (oId X2)) g2.
Proof.
  intros H1 H2 [E [E' [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  eapply Req_sub_mk with (E := E) (E' := E') (s1 := rcmp s1 rid) (s2 := s2).
  - exact K1.
  - exact K2.
  - econstructor;
      [ exact HX1 | exact HX2 | exact HX2 | exact K3 | constructor; exact HX2 ].
  - exact K4.
  - intros k Hk; unfold rcmp, rid; cbn; apply K5; exact Hk.
Qed.

Lemma subeq_cmp E2 E3 sf1 sf2 sg1 sg2
  : swf E2 E3 sg2 -> subeq E2 sf1 sf2 -> subeq E3 sg1 sg2 ->
    subeq E3 (rcmp sf1 sg1) (rcmp sf2 sg2).
Proof.
  intros Hw Hf Hg k Hk; unfold rcmp.
  rewrite (Hg k Hk).
  eapply csub_ext_wf; [ apply Hw; exact Hk | exact Hf ].
Qed.

Lemma by_cmp_assoc X1 Y1 X2 Y2 X3 Y3 X4 Y4 f1 f2 g1 g2 h1 h2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_env X3 Y3 -> Req_env X4 Y4 ->
    Req_sub Y1 Y2 f1 f2 -> Req_sub Y2 Y3 g1 g2 -> Req_sub Y3 Y4 h1 h2 ->
    Req_sub Y1 Y4 (oCmp X1 X2 X4 f1 (oCmp X2 X3 X4 g1 h1))
                  (oCmp Y1 Y3 Y4 (oCmp Y1 Y2 Y3 f2 g2) h2).
Proof.
  intros H1 H2 H3 H4
    [E1 [E2 [sf1 [sf2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [E2a [E3 [sg1 [sg2 [L1 [L2 [L3 [L4 L5]]]]]]]]
    [E3a [E4 [sh1 [sh2 [M1 [M2 [M3 [M4 M5]]]]]]]].
  pose proof (IEnv_fun L1 K2) as Ha; subst E2a.
  pose proof (IEnv_fun M1 L2) as Hb; subst E3a.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  pose proof (Req_env_transfer (Req_env_sym H3) L2) as HX3.
  pose proof (Req_env_transfer (Req_env_sym H4) M2) as HX4.
  eapply Req_sub_mk with (E := E1) (E' := E4)
                         (s1 := rcmp sf1 (rcmp sg1 sh1))
                         (s2 := rcmp (rcmp sf2 sg2) sh2).
  - exact K1.
  - exact M2.
  - econstructor; [ exact HX1 | exact HX2 | exact HX4 | exact K3 | ].
    econstructor; [ exact HX2 | exact HX3 | exact HX4 | exact L3 | exact M3 ].
  - econstructor; [ exact K1 | exact L2 | exact M2 | | exact M4 ].
    econstructor; [ exact K1 | exact K2 | exact L2 | exact K4 | exact L4 ].
  - intros k Hk.
    change (rcmp sf1 (rcmp sg1 sh1) k) with (csub sf1 (csub sg1 (sh1 k))).
    rewrite csub_comp.
    change (rcmp (rcmp sf2 sg2) sh2 k) with (csub (rcmp sf2 sg2) (sh2 k)).
    rewrite (M5 k Hk).
    eapply csub_ext_wf; [ eapply (ISub_swf M4); exact Hk | ].
    eapply subeq_cmp; [ eapply ISub_swf; exact L4 | exact K5 | exact L5 ].
Qed.

Lemma by_cmp_forget X1 Y1 X2 Y2 f1 f2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 f1 f2 ->
    Req_sub Y1 oEmp (oCmp X1 X2 oEmp f1 (oForget X2)) (oForget Y1).
Proof.
  intros H1 H2 [E [E' [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  eapply Req_sub_mk with (E := E) (E' := @nil rty)
                         (s1 := rcmp s1 rforget) (s2 := rforget).
  - exact K1.
  - constructor.
  - econstructor;
      [ exact HX1 | exact HX2 | constructor | exact K3 | constructor; exact HX2 ].
  - constructor; exact K1.
  - intros k Hk; cbn in Hk; unfold isUat in Hk;
      destruct k; cbn in Hk; discriminate.
Qed.

Lemma by_id_emp_forget : Req_sub oEmp oEmp (oId oEmp) (oForget oEmp).
Proof.
  eapply Req_sub_mk with (E := @nil rty) (E' := @nil rty)
                         (s1 := rid) (s2 := rforget).
  - constructor.
  - constructor.
  - constructor; constructor.
  - constructor; constructor.
  - intros k Hk; unfold isUat in Hk; destruct k; cbn in Hk; discriminate.
Qed.

Lemma by_wkn_snoc X1 Y1 X2 Y2 i1 A1 A2 g1 g2 v1 v2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_ty Y2 A1 A2 -> Req_sub Y1 Y2 g1 g2 ->
    (USkel A2 = true -> Req_code Y1 v1 v2) ->
    Req_sub Y1 Y2
      (oCmp X1 (oExt X2 i1 A1) X2 (oSnoc X1 X2 i1 A1 g1 v1) (oWkn X2 i1 A1)) g2.
Proof.
  intros H1 H2 [E2 [T [HE2 [HA1 HA2]]]]
    [E [E2a [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]] Hv.
  pose proof (IEnv_fun K2 HE2) as Ha; subst E2a.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) HE2) as HX2.
  assert (IEnv (oExt X2 i1 A1) (T :: E2)) as HXE
      by (econstructor; [ exact HX2 | exact HA1 ]).
  destruct T as [ br bl | br bl nc ].
  - destruct (Hv (ITy_USkel HA2)) as [Ec [n [M1 [M2 M3]]]].
    pose proof (IEnv_fun M1 K1) as Hb; subst Ec.
    eapply Req_sub_mk with (E := E) (E' := E2)
                           (s1 := rcmp (rsnoc n s1) rshift) (s2 := s2).
    + exact K1.
    + exact HE2.
    + econstructor; [ exact HX1 | exact HXE | exact HX2 | | ].
      * eapply isub_snoc_U;
          [ exact HX1 | exact HX2 | exact K3 | exact HA1 | exact M2 ].
      * econstructor; [ exact HX2 | exact HA1 ].
    + exact K4.
    + intros k Hk; unfold rcmp, rshift, rsnoc; cbn; apply K5; exact Hk.
  - eapply Req_sub_mk with (E := E) (E' := E2)
                           (s1 := rcmp (rsnoc rc_nat s1) rshift) (s2 := s2).
    + exact K1.
    + exact HE2.
    + econstructor; [ exact HX1 | exact HXE | exact HX2 | | ].
      * eapply isub_snoc_El;
          [ exact HX1 | exact HX2 | exact K3 | exact HA1 ].
      * econstructor; [ exact HX2 | exact HA1 ].
    + exact K4.
    + intros k Hk; unfold rcmp, rshift, rsnoc; cbn; apply K5; exact Hk.
Qed.

Lemma by_snoc_hd X1 Y1 X2 Y2 i1 A1 A2 g1 g2 v1 v2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_ty Y2 A1 A2 -> Req_sub Y1 Y2 g1 g2 ->
    Req_code Y1 v1 v2 -> USkel A2 = true ->
    Req_code Y1
      (oExpSubst X1 (oExt X2 i1 A1) (oSnoc X1 X2 i1 A1 g1 v1) i1
         (oTySubst (oExt X2 i1 A1) X2 (oWkn X2 i1 A1) i1 A1) (oHd X2 i1 A1))
      v2.
Proof.
  intros H1 H2 [E2 [T [HE2 [HA1 HA2]]]]
    [E [E2a [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]] [Ec [n [M1 [M2 M3]]]] Hu.
  pose proof (IEnv_fun K2 HE2) as Ha; subst E2a.
  pose proof (IEnv_fun M1 K1) as Hb; subst Ec.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) HE2) as HX2.
  rewrite (ITy_USkel HA2) in Hu.
  destruct T as [ br bl | br bl nc ]; [ | discriminate ].
  assert (IEnv (oExt X2 i1 A1) (rt_U br bl :: E2)) as HXE
      by (econstructor; [ exact HX2 | exact HA1 ]).
  eapply Req_code_mk with (E := E) (n := n).
  - exact K1.
  - change n with (csub (rsnoc n s1) (rc_var 0)).
    econstructor; [ exact HX1 | exact HXE | | ].
    + eapply isub_snoc_U;
        [ exact HX1 | exact HX2 | exact K3 | exact HA1 | exact M2 ].
    + econstructor; [ exact HX2 | exact HA1 ].
  - exact M3.
Qed.

Lemma by_cmp_snoc X1 Y1 X2 Y2 X3 Y3 i1 i2 A1 A2 f1 f2 g1 g2 v1 v2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_env X3 Y3 ->
    Req_ty Y3 A1 A2 -> Req_sub Y1 Y2 f1 f2 -> Req_sub Y2 Y3 g1 g2 ->
    (USkel A2 = true -> Req_code Y2 v1 v2) ->
    Req_sub Y1 (oExt Y3 i2 A2)
      (oCmp X1 X2 (oExt X3 i1 A1) f1 (oSnoc X2 X3 i1 A1 g1 v1))
      (oSnoc Y1 Y3 i2 A2 (oCmp Y1 Y2 Y3 f2 g2)
         (oExpSubst Y1 Y2 f2 i2 (oTySubst Y2 Y3 g2 i2 A2) v2)).
Proof.
  intros H1 H2 H3 [E3 [T [HE3 [HA1 HA2]]]]
    [E1 [E2 [sf1 [sf2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [E2a [E3a [sg1 [sg2 [L1 [L2 [L3 [L4 L5]]]]]]]] Hv.
  pose proof (IEnv_fun L1 K2) as Ha; subst E2a.
  pose proof (IEnv_fun L2 HE3) as Hb; subst E3a.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  pose proof (Req_env_transfer (Req_env_sym H3) HE3) as HX3.
  destruct T as [ br bl | br bl nc ].
  - destruct (Hv (ITy_USkel HA2)) as [Ec [n [M1 [M2 M3]]]].
    pose proof (IEnv_fun M1 K2) as Hc; subst Ec.
    eapply Req_sub_mk with (E := E1) (E' := rt_U br bl :: E3)
                           (s1 := rcmp sf1 (rsnoc n sg1))
                           (s2 := rsnoc (csub sf2 n) (rcmp sf2 sg2)).
    + exact K1.
    + econstructor; [ exact HE3 | exact HA2 ].
    + econstructor; [ exact HX1 | exact HX2 | | exact K3 | ].
      * econstructor; [ exact HX3 | exact HA1 ].
      * eapply isub_snoc_U;
          [ exact HX2 | exact HX3 | exact L3 | exact HA1 | exact M2 ].
    + eapply isub_snoc_U.
      * exact K1.
      * exact HE3.
      * econstructor; [ exact K1 | exact K2 | exact HE3 | exact K4 | exact L4 ].
      * exact HA2.
      * econstructor; [ exact K1 | exact K2 | exact K4 | exact M3 ].
    + intros [|k] Hk.
      * unfold rcmp, rsnoc; cbn.
        eapply csub_ext_wf; [ eapply ICode_cwf; exact M2 | exact K5 ].
      * unfold rcmp, rsnoc; cbn.
        rewrite (L5 k Hk).
        eapply csub_ext_wf; [ eapply (ISub_swf L4); exact Hk | exact K5 ].
  - eapply Req_sub_mk with (E := E1) (E' := rt_El br bl nc :: E3)
                           (s1 := rcmp sf1 (rsnoc rc_nat sg1))
                           (s2 := rsnoc rc_nat (rcmp sf2 sg2)).
    + exact K1.
    + econstructor; [ exact HE3 | exact HA2 ].
    + econstructor; [ exact HX1 | exact HX2 | | exact K3 | ].
      * econstructor; [ exact HX3 | exact HA1 ].
      * eapply isub_snoc_El; [ exact HX2 | exact HX3 | exact L3 | exact HA1 ].
    + eapply isub_snoc_El.
      * exact K1.
      * exact HE3.
      * econstructor; [ exact K1 | exact K2 | exact HE3 | exact K4 | exact L4 ].
      * exact HA2.
    + intros [|k] Hk; [ cbn in Hk; discriminate | ].
      unfold rcmp, rsnoc; cbn.
      rewrite (L5 k Hk).
      eapply csub_ext_wf; [ eapply (ISub_swf L4); exact Hk | exact K5 ].
Qed.

Lemma by_snoc_wkn_hd X1 Y1 i1 A1 i2 A2
  : Req_env X1 Y1 -> Req_ty Y1 A1 A2 ->
    Req_sub (oExt Y1 i2 A2) (oExt Y1 i2 A2)
      (oSnoc (oExt X1 i1 A1) X1 i1 A1 (oWkn X1 i1 A1) (oHd X1 i1 A1))
      (oId (oExt Y1 i2 A2)).
Proof.
  intros H1 [E [T [HE [HA1 HA2]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) HE) as HX1.
  assert (IEnv (oExt X1 i1 A1) (T :: E)) as HXE
      by (econstructor; [ exact HX1 | exact HA1 ]).
  assert (IEnv (oExt Y1 i2 A2) (T :: E)) as HYE
      by (econstructor; [ exact HE | exact HA2 ]).
  destruct T as [ br bl | br bl nc ].
  - eapply Req_sub_mk with (E := rt_U br bl :: E) (E' := rt_U br bl :: E)
                           (s1 := rsnoc (rc_var 0) rshift) (s2 := rid).
    + exact HYE.
    + exact HYE.
    + eapply isub_snoc_U.
      * exact HXE.
      * exact HX1.
      * econstructor; [ exact HX1 | exact HA1 ].
      * exact HA1.
      * econstructor; [ exact HX1 | exact HA1 ].
    + constructor; exact HYE.
    + intros [|k] Hk; reflexivity.
  - eapply Req_sub_mk with (E := rt_El br bl nc :: E) (E' := rt_El br bl nc :: E)
                           (s1 := rsnoc rc_nat rshift) (s2 := rid).
    + exact HYE.
    + exact HYE.
    + eapply isub_snoc_El.
      * exact HXE.
      * exact HX1.
      * econstructor; [ exact HX1 | exact HA1 ].
      * exact HA1.
    + constructor; exact HYE.
    + intros [|k] Hk; [ cbn in Hk; discriminate | reflexivity ].
Qed.

Lemma by_ty_subst_id X1 Y1 i1 A1 A2
  : Req_env X1 Y1 -> Req_ty Y1 A1 A2 ->
    Req_ty Y1 (oTySubst X1 X1 (oId X1) i1 A1) A2.
Proof.
  intros H1 [E [T [HE [HA1 HA2]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) HE) as HX1.
  eapply Req_ty_mk with (E := E) (T := T).
  - exact HE.
  - rewrite <- (tsub_id T) at 1.
    econstructor; [ exact HX1 | exact HX1 | constructor; exact HX1 | exact HA1 ].
  - exact HA2.
Qed.

Lemma by_exp_subst_id X1 Y1 i1 A1 v1 v2
  : Req_env X1 Y1 -> Req_code Y1 v1 v2 ->
    Req_code Y1 (oExpSubst X1 X1 (oId X1) i1 A1 v1) v2.
Proof.
  intros H1 [E [n [HE [Hv1 Hv2]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) HE) as HX1.
  eapply Req_code_mk with (E := E) (n := n).
  - exact HE.
  - rewrite <- (csub_id n) at 1.
    econstructor; [ exact HX1 | exact HX1 | constructor; exact HX1 | exact Hv1 ].
  - exact Hv2.
Qed.

Lemma by_ty_subst_cmp X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2 i1 i2 A1 A2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_env X3 Y3 ->
    Req_sub Y1 Y2 f1 f2 -> Req_sub Y2 Y3 g1 g2 -> Req_ty Y3 A1 A2 ->
    Req_ty Y1 (oTySubst X1 X2 f1 i1 (oTySubst X2 X3 g1 i1 A1))
              (oTySubst Y1 Y3 (oCmp Y1 Y2 Y3 f2 g2) i2 A2).
Proof.
  intros H1 H2 H3
    [E1 [E2 [sf1 [sf2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [E2a [E3 [sg1 [sg2 [L1 [L2 [L3 [L4 L5]]]]]]]]
    [E3a [T [HE3 [HA1 HA2]]]].
  pose proof (IEnv_fun L1 K2) as Ha; subst E2a.
  pose proof (IEnv_fun L2 HE3) as Hb; subst E3a.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  pose proof (Req_env_transfer (Req_env_sym H3) HE3) as HX3.
  assert (tsub sf1 (tsub sg1 T) = tsub (rcmp sf2 sg2) T) as Heq.
  { assert (tsub sg1 T = tsub sg2 T) as Hg
        by (eapply tsub_ext_wf; [ eapply ITy_twf; exact HA1 | exact L5 ]).
    rewrite Hg.
    assert (tsub sf1 (tsub sg2 T) = tsub sf2 (tsub sg2 T)) as Hf.
    { eapply tsub_ext_wf; [ | exact K5 ].
      eapply twf_tsub; [ eapply ISub_swf; exact L4 | eapply ITy_twf; exact HA2 ]. }
    rewrite Hf; apply tsub_comp. }
  eapply Req_ty_mk with (E := E1) (T := tsub (rcmp sf2 sg2) T).
  - exact K1.
  - rewrite <- Heq.
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor; [ exact HX2 | exact HX3 | exact L3 | exact HA1 ].
  - econstructor; [ exact K1 | exact HE3 | | exact HA2 ].
    econstructor; [ exact K1 | exact K2 | exact HE3 | exact K4 | exact L4 ].
Qed.

Lemma by_exp_subst_cmp X1 Y1 X2 Y2 X3 Y3 f1 f2 g1 g2 i1 i2 A1 A3 A4 v1 v2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_env X3 Y3 ->
    Req_sub Y1 Y2 f1 f2 -> Req_sub Y2 Y3 g1 g2 -> Req_code Y3 v1 v2 ->
    Req_code Y1
      (oExpSubst X1 X2 f1 i1 A1 (oExpSubst X2 X3 g1 i1 A3 v1))
      (oExpSubst Y1 Y3 (oCmp Y1 Y2 Y3 f2 g2) i2 A4 v2).
Proof.
  intros H1 H2 H3
    [E1 [E2 [sf1 [sf2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [E2a [E3 [sg1 [sg2 [L1 [L2 [L3 [L4 L5]]]]]]]]
    [E3a [n [HE3 [Hv1 Hv2]]]].
  pose proof (IEnv_fun L1 K2) as Ha; subst E2a.
  pose proof (IEnv_fun L2 HE3) as Hb; subst E3a.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  pose proof (Req_env_transfer (Req_env_sym H3) HE3) as HX3.
  assert (csub sf1 (csub sg1 n) = csub (rcmp sf2 sg2) n) as Heq.
  { assert (csub sg1 n = csub sg2 n) as Hg
        by (eapply csub_ext_wf; [ eapply ICode_cwf; exact Hv1 | exact L5 ]).
    rewrite Hg.
    assert (csub sf1 (csub sg2 n) = csub sf2 (csub sg2 n)) as Hf.
    { eapply csub_ext_wf; [ | exact K5 ].
      eapply cwf_csub; [ eapply ISub_swf; exact L4 | eapply ICode_cwf; exact Hv2 ]. }
    rewrite Hf; apply csub_comp. }
  eapply Req_code_mk with (E := E1) (n := csub (rcmp sf2 sg2) n).
  - exact K1.
  - rewrite <- Heq.
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor; [ exact HX2 | exact HX3 | exact L3 | exact Hv1 ].
  - econstructor; [ exact K1 | exact HE3 | | exact Hv2 ].
    econstructor; [ exact K1 | exact K2 | exact HE3 | exact K4 | exact L4 ].
Qed.

Lemma by_U_subst X1 Y1 X2 Y2 g1 g2 i1 r1 r2 l1 l2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    (exists b, ErRel r1 b /\ ErRel r2 b) ->
    (exists b, ErLvl l1 b /\ ErLvl l2 b) ->
    Req_ty Y1 (oTySubst X1 X2 g1 i1 (oU X2 r1 l1)) (oU Y1 r2 l2).
Proof.
  intros H1 H2 [E [E2 [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [br [Hr1 Hr2]] [bl [Hl1 Hl2]].
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  eapply Req_ty_mk with (E := E) (T := rt_U br bl).
  - exact K1.
  - change (rt_U br bl) with (tsub s1 (rt_U br bl)).
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor; [ exact HX2 | exact Hr1 | exact Hl1 ].
  - econstructor; [ exact K1 | exact Hr2 | exact Hl2 ].
Qed.

Lemma by_El_subst X1 Y1 X2 Y2 g1 g2 i1 i3 r1 r2 l1 l2 c1 c2
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    (exists b, ErRel r1 b /\ ErRel r2 b) ->
    (exists b, ErLvl l1 b /\ ErLvl l2 b) ->
    Req_code Y2 c1 c2 ->
    Req_ty Y1 (oTySubst X1 X2 g1 i1 (oEl X2 r1 l1 c1))
              (oEl Y1 r2 l2 (oExpSubst Y1 Y2 g2 i3 (oU Y2 r2 l2) c2)).
Proof.
  intros H1 H2 [E [E2 [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [br [Hr1 Hr2]] [bl [Hl1 Hl2]] [E2a [n [HE2 [Hc1 Hc2]]]].
  pose proof (IEnv_fun HE2 K2) as Ha; subst E2a.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  assert (csub s1 n = csub s2 n) as Heq
      by (eapply csub_ext_wf; [ eapply ICode_cwf; exact Hc1 | exact K5 ]).
  eapply Req_ty_mk with (E := E) (T := rt_El br bl (csub s2 n)).
  - exact K1.
  - rewrite <- Heq.
    change (rt_El br bl (csub s1 n)) with (tsub s1 (rt_El br bl n)).
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor; [ exact HX2 | exact Hr1 | exact Hl1 | exact Hc1 ].
  - econstructor; [ exact K1 | exact Hr2 | exact Hl2 | ].
    econstructor; [ exact K1 | exact K2 | exact K4 | exact Hc2 ].
Qed.

Lemma by_Nat_subst X1 Y1 X2 Y2 g1 g2 i1 A1
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    Req_code Y1 (oExpSubst X1 X2 g1 i1 A1 (oNat X2)) (oNat Y1).
Proof.
  intros H1 H2 [E [E2 [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  eapply Req_code_mk with (E := E) (n := rc_nat).
  - exact K1.
  - change rc_nat with (csub s1 rc_nat).
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor; exact HX2.
  - econstructor; exact K1.
Qed.

Lemma by_Empty_subst X1 Y1 X2 Y2 g1 g2 i1 A1
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    Req_code Y1 (oExpSubst X1 X2 g1 i1 A1 (oEmpty X2)) (oEmpty Y1).
Proof.
  intros H1 H2 [E [E2 [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]].
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  eapply Req_code_mk with (E := E) (n := rc_empty).
  - exact K1.
  - change rc_empty with (csub s1 rc_empty).
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor; exact HX2.
  - econstructor; exact K1.
Qed.

(* The two [Pi] commutations.  These are the only obligations in which the
   theory's own lifting ([oLift]) has to be matched against [csub]'s [up]:
   they differ exactly at the head slot, which is an [El] slot, hence
   invisible to [subeq]. *)
Lemma by_Pi_irr_subst X1 Y1 X2 Y2 g1 g2 rF1 rF2 lF1 lF2 F1 F2 B1 B2 i1 A1 i3 A3
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    (exists b, ErRel rF1 b /\ ErRel rF2 b) ->
    (exists b, ErLvl lF1 b /\ ErLvl lF2 b) ->
    Req_code Y2 F1 F2 -> Req_code (oExtC Y2 rF2 lF2 F2) B1 B2 ->
    Req_code Y1
      (oExpSubst X1 X2 g1 i1 A1 (oPiIrr X2 rF1 lF1 F1 B1))
      (oPiIrr Y1 rF2 lF2 (oCodeSub Y1 Y2 g2 rF2 lF2 F2)
         (oExpSubst (oExtC Y1 rF2 lF2 (oCodeSub Y1 Y2 g2 rF2 lF2 F2))
            (oExtC Y2 rF2 lF2 F2) (oLift Y1 Y2 g2 rF2 lF2 F2) i3 A3 B2)).
Proof.
  intros H1 H2 [E [E2 [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [br [Hr1 Hr2]] [bl [Hl1 Hl2]] [E2a [nF [HE2 [HF1 HF2]]]]
    [EB [nB [HEB [HB1 HB2]]]].
  pose proof (IEnv_fun HE2 K2) as Ha; subst E2a.
  assert (IEnv (oExtC Y2 rF2 lF2 F2) (rt_El br bl nF :: E2)) as HX
      by (eapply IEnv_extC; [ exact K2 | exact Hr2 | exact Hl2 | exact HF2 ]).
  pose proof (IEnv_fun HEB HX) as Hb; subst EB.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  assert (ICode E (oCodeSub Y1 Y2 g2 rF2 lF2 F2) (csub s2 nF)) as HFg
      by (unfold oCodeSub; econstructor;
          [ exact K1 | exact K2 | exact K4 | exact HF2 ]).
  pose proof (ISub_oLift K1 K2 K4 Hr2 Hl2 HF2 HFg) as HL.
  assert (IEnv (oExtC Y1 rF2 lF2 (oCodeSub Y1 Y2 g2 rF2 lF2 F2))
            (rt_El br bl (csub s2 nF) :: E)) as HEF
      by (eapply IEnv_extC; [ exact K1 | exact Hr2 | exact Hl2 | exact HFg ]).
  assert (csub (up s1) nB = csub (rsnoc rc_nat (rcmp rshift s2)) nB) as HeqB
      by (eapply csub_ext_wf;
          [ eapply ICode_cwf; exact HB1 | apply subeq_lift; exact K5 ]).
  assert (csub s1 nF = csub s2 nF) as HeqF
      by (eapply csub_ext_wf; [ eapply ICode_cwf; exact HF1 | exact K5 ]).
  eapply Req_code_mk with (E := E)
    (n := rc_pi false br bl (csub s2 nF)
            (csub (rsnoc rc_nat (rcmp rshift s2)) nB)).
  - exact K1.
  - rewrite <- HeqB, <- HeqF.
    change (rc_pi false br bl (csub s1 nF) (csub (up s1) nB))
      with (csub s1 (rc_pi false br bl nF nB)).
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor;
      [ exact HX2 | exact Hr1 | exact Hl1 | exact HF1 | exact HB1 ].
  - econstructor; [ exact K1 | exact Hr2 | exact Hl2 | exact HFg | ].
    econstructor; [ exact HEF | exact HX | exact HL | exact HB2 ].
Qed.

Lemma by_Pi_rel_subst X1 Y1 X2 Y2 g1 g2 rF1 rF2 lF1 lF2 lG1 lG2
    F1 F2 B1 B2 i1 A1 i3 A3
  : Req_env X1 Y1 -> Req_env X2 Y2 -> Req_sub Y1 Y2 g1 g2 ->
    (exists b, ErRel rF1 b /\ ErRel rF2 b) ->
    (exists b, ErLvl lF1 b /\ ErLvl lF2 b) ->
    Req_code Y2 F1 F2 -> Req_code (oExtC Y2 rF2 lF2 F2) B1 B2 ->
    Req_code Y1
      (oExpSubst X1 X2 g1 i1 A1 (oPiRel X2 rF1 lF1 lG1 F1 B1))
      (oPiRel Y1 rF2 lF2 lG2 (oCodeSub Y1 Y2 g2 rF2 lF2 F2)
         (oExpSubst (oExtC Y1 rF2 lF2 (oCodeSub Y1 Y2 g2 rF2 lF2 F2))
            (oExtC Y2 rF2 lF2 F2) (oLift Y1 Y2 g2 rF2 lF2 F2) i3 A3 B2)).
Proof.
  intros H1 H2 [E [E2 [s1 [s2 [K1 [K2 [K3 [K4 K5]]]]]]]]
    [br [Hr1 Hr2]] [bl [Hl1 Hl2]] [E2a [nF [HE2 [HF1 HF2]]]]
    [EB [nB [HEB [HB1 HB2]]]].
  pose proof (IEnv_fun HE2 K2) as Ha; subst E2a.
  assert (IEnv (oExtC Y2 rF2 lF2 F2) (rt_El br bl nF :: E2)) as HX
      by (eapply IEnv_extC; [ exact K2 | exact Hr2 | exact Hl2 | exact HF2 ]).
  pose proof (IEnv_fun HEB HX) as Hb; subst EB.
  pose proof (Req_env_transfer (Req_env_sym H1) K1) as HX1.
  pose proof (Req_env_transfer (Req_env_sym H2) K2) as HX2.
  assert (ICode E (oCodeSub Y1 Y2 g2 rF2 lF2 F2) (csub s2 nF)) as HFg
      by (unfold oCodeSub; econstructor;
          [ exact K1 | exact K2 | exact K4 | exact HF2 ]).
  pose proof (ISub_oLift K1 K2 K4 Hr2 Hl2 HF2 HFg) as HL.
  assert (IEnv (oExtC Y1 rF2 lF2 (oCodeSub Y1 Y2 g2 rF2 lF2 F2))
            (rt_El br bl (csub s2 nF) :: E)) as HEF
      by (eapply IEnv_extC; [ exact K1 | exact Hr2 | exact Hl2 | exact HFg ]).
  assert (csub (up s1) nB = csub (rsnoc rc_nat (rcmp rshift s2)) nB) as HeqB
      by (eapply csub_ext_wf;
          [ eapply ICode_cwf; exact HB1 | apply subeq_lift; exact K5 ]).
  assert (csub s1 nF = csub s2 nF) as HeqF
      by (eapply csub_ext_wf; [ eapply ICode_cwf; exact HF1 | exact K5 ]).
  eapply Req_code_mk with (E := E)
    (n := rc_pi true br bl (csub s2 nF)
            (csub (rsnoc rc_nat (rcmp rshift s2)) nB)).
  - exact K1.
  - rewrite <- HeqB, <- HeqF.
    change (rc_pi true br bl (csub s1 nF) (csub (up s1) nB))
      with (csub s1 (rc_pi true br bl nF nB)).
    econstructor; [ exact HX1 | exact HX2 | exact K3 | ].
    econstructor;
      [ exact HX2 | exact Hr1 | exact Hl1 | exact HF1 | exact HB1 ].
  - econstructor; [ exact K1 | exact Hr2 | exact Hl2 | exact HFg | ].
    econstructor; [ exact HEF | exact HX | exact HL | exact HB2 ].
Qed.

Ltac use_any :=
  solve [ apply rceq_env_e; eassumption
        | apply rceq_sub_e; eassumption
        | eapply rceq_ty_e; eassumption
        | apply rceq_rel_e; eassumption
        | apply rceq_lvl_e; eassumption
        | eapply rceq_exp_e'; [ eassumption | reflexivity ] ].

Lemma by_obligation
  : forall c' name e1 e2 t s1 s2,
    In (name, term_eq_rule c' e1 e2 t) ott_dtt ->
    ceq_args (CM := RigCM) c' s1 s2 ->
    rceq_term t[/with_names_from c' s2/]
      e1[/with_names_from c' s1/] e2[/with_names_from c' s2/].
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hargs.
  decomp; try exact I.
  - (* Pi_irr subst *)
    apply rceq_exp_i; intros _; eapply by_Pi_irr_subst; use_any.
  - (* Pi_rel subst *)
    apply rceq_exp_i; intros _; eapply by_Pi_rel_subst; use_any.
  - (* Empty subst *)
    apply rceq_exp_i; intros _; eapply by_Empty_subst; use_any.
  - (* Nat subst *)
    apply rceq_exp_i; intros _; eapply by_Nat_subst; use_any.
  - (* El subst *)
    apply rceq_ty_i; eapply by_El_subst; use_any.
  - (* U subst *)
    apply rceq_ty_i; eapply by_U_subst; use_any.
  - (* snoc_wkn_hd *)
    apply rceq_sub_i; eapply by_snoc_wkn_hd; use_any.
  - (* cmp_snoc *)
    apply rceq_sub_i; eapply by_cmp_snoc;
      solve [ use_any
            | (intro Hu; eapply rceq_exp_e'; [ eassumption | exact Hu ]) ].
  - (* snoc_hd *)
    apply rceq_exp_i; intro Hu; eapply by_snoc_hd;
      solve [ use_any
            | eapply rceq_exp_e'; [ eassumption | exact Hu ]
            | exact Hu ].
  - (* wkn_snoc *)
    apply rceq_sub_i; eapply by_wkn_snoc;
      solve [ use_any
            | (intro Hu; eapply rceq_exp_e'; [ eassumption | exact Hu ]) ].
  - (* id_emp_forget *)
    apply rceq_sub_i; eapply by_id_emp_forget.
  - (* cmp_forget *)
    apply rceq_sub_i; eapply by_cmp_forget; use_any.
  - (* exp_subst_cmp *)
    apply rceq_exp_i; intro Hu; eapply by_exp_subst_cmp;
      solve [ use_any | eapply rceq_exp_e'; [ eassumption | exact Hu ] ].
  - (* exp_subst_id *)
    apply rceq_exp_i; intro Hu; eapply by_exp_subst_id;
      solve [ use_any | eapply rceq_exp_e'; [ eassumption | exact Hu ] ].
  - (* ty_subst_cmp *)
    apply rceq_ty_i; eapply by_ty_subst_cmp; use_any.
  - (* ty_subst_id *)
    apply rceq_ty_i; eapply by_ty_subst_id; use_any.
  - (* cmp_assoc *)
    apply rceq_sub_i; eapply by_cmp_assoc; use_any.
  - (* id_left *)
    apply rceq_sub_i; eapply by_id_left; use_any.
  - (* id_right *)
    apply rceq_sub_i; eapply by_id_right; use_any.
  - (* next1 *) apply rceq_tlvl_i; reflexivity.
  - (* next0 *) apply rceq_tlvl_i; reflexivity.
Qed.
