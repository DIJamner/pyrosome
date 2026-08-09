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
