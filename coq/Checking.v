
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*From excomp Require Import Utils.*)
Require Import String.
From ExtLib.Structures Require Import
     Monad MonadTrans MonadExc MonadLaws MonadPlus Monoid Functor BinOps.
From ExtLib.Data.Monads Require Import FuelMonad OptionMonad.
Require Import BinPos.
Import MonadNotation.
Local Open Scope monad_scope.

Section PartialDecisions.

  (* the final element of the PartialDecision structure *)
  Variant partial_decision (N Y : Type) : Type := yes (msg:Y) | maybe | no (msg:N).

  Definition pd_eq_fn {N Y : eqType} (a b : partial_decision N Y) : bool :=
    match a,b with
    | yes m1, yes m2 => m1 == m2
    | maybe, maybe => true
    | no m1, no m2 => m1 == m2
    | _, _ => false
    end.

  Lemma pd_eq_fn_Reflect {N Y : eqType} (a b : partial_decision N Y) : reflect (a = b) (pd_eq_fn a b).
  Proof.
    case: a; case: b => //=; try by constructor.
    all: move => m1 m2; case meq: (m2 == m1) => //=; constructor; f_equal.
    1,3:by apply /eqP.
    all: unfold not; case; move /eqP; by rewrite meq.
  Qed.
  
  Definition partial_decision_eqMixin {N Y : eqType} := Equality.Mixin (@pd_eq_fn_Reflect N Y).
  Canonical partial_decision_eqType {N Y : eqType} :=
    EqType (@partial_decision N Y) partial_decision_eqMixin.
  (*TODO: this stuff can be added for finite N,Y
  Definition partial_decision_choiceMixin := PcanChoiceMixin pcan_sdo3.
  Canonical partial_decision_choiceType := ChoiceType partial_decision partial_decision_choiceMixin.
  Definition partial_decision_countMixin := PcanCountMixin pcan_sdo3.
  Canonical partial_decision_countType := CountType partial_decision partial_decision_countMixin.
  Definition partial_decision_finMixin := PcanFinMixin pcan_sdo3.
  Canonical partial_decision_finType := FinType partial_decision partial_decision_finMixin.
   *)

  Create HintDb pd_lit discriminated.
  
  (*TODO: make a prop whose negation only holds when it is no? might overcomplicate things *)
  Definition pd_as_prop {N Y} (pd : partial_decision N Y) : Prop :=
    match pd with
    | yes _ => True
    | _ => False
    end.
  Coercion pd_as_prop : partial_decision >-> Sortclass.
  
  Variant partial_decide (P : Prop) {N Y} : partial_decision N Y -> Type :=
  | DecideY : forall (msg : Y), P -> partial_decide P (yes _ msg)
  | DecideN : forall (msg : N), ~P -> partial_decide P (no _ msg)
  | DecideM : partial_decide P (maybe _ _).
  Hint Constructors partial_decide.
  
  Definition pd_lit_and {N1 N2 Y1 Y2} sd1 sd2 : partial_decision (N1 + N2) (Y1 * Y2) :=
    match sd1, sd2 with
    | yes m1, yes m2 => yes _ (m1, m2)
    | yes _, maybe => maybe _ _
    | maybe, yes _ => maybe _ _
    | maybe, maybe => maybe _ _
     (* we make and and or left-biased *)
    | no m1, _ => no _ (inl m1)
    | _, no m2 => no _ (inr m2)
    end.

  (* TODO: define Associative over type operators, up to given isomorphism *)
  (*
  Print Associative.
  Lemma pd_lit_and_assoc : Associative pd_lit_and eq.
  Proof.
    case => //; case => //; case => //.
  Qed.
  Hint Resolve pd_lit_and_assoc : pd_lit.
  
  Lemma pd_lit_and_comm : Commutative pd_lit_and eq.
  Proof.
    case => //; case => //.
  Qed.
  Hint Resolve pd_lit_and_comm : pd_lit.

  Lemma pd_lit_and_unit : LeftUnit pd_lit_and yes eq.
  Proof.
    case => //.
  Qed.
  Hint Resolve pd_lit_and_unit : pd_lit.
*)
  
  Definition pd_lit_or {N1 N2 Y1 Y2} sd1 sd2 : partial_decision (N1 * N2) (Y1 + Y2) :=
    match sd1, sd2 with
    | no m1, no m2 => no _ (m1, m2)
    | no _, maybe => maybe _ _
    | maybe, no _ => maybe _ _
    | maybe, maybe => maybe _ _
     (* we make and and or left-biased *)
    | yes m1, _ => yes _ (inl m1)
    | _, yes m2 => yes _ (inr m2)
    end.

(*
  Lemma pd_lit_or_assoc : Associative pd_lit_or eq.
  Proof.
    case => //; case => //; case => //.
  Qed.
  Hint Resolve pd_lit_or_assoc : pd_lit.

  Lemma pd_lit_or_comm : Commutative pd_lit_or eq.
  Proof.
    case => //; case => //.
  Qed.
  Hint Resolve pd_lit_or_comm : pd_lit.
  
  Lemma pd_lit_or_unit : LeftUnit pd_lit_or no eq.
  Proof.
    case => //.
  Qed.
  Hint Resolve pd_lit_or_unit : pd_lit.
 *)

  Definition pd_lit_neg {N Y} pd : partial_decision Y N :=
    match pd with
    | yes m => no _ m
    | maybe => maybe _ _
    | no m => yes _ m
    end.

  Lemma pd_lit_neg_cancel : forall {N Y} (sd : partial_decision N Y), pd_lit_neg (pd_lit_neg sd) = sd.
  Proof. move => N Y; case => //=. Qed.

  Class PartialDecision (T : Type -> Type -> Type) : Type :=
    {
      (* force partial_decision to be final wrt instances of this class *)
      as_lit : forall {N Y}, T N Y -> partial_decision N Y;
      (* require both yes and no to be inhabited in the type *)
      (* TODO: prefix constructor instead of this one?*)
      pd_yes : forall {N Y}, Y -> T N Y;
      pd_no : forall {N Y}, N -> T N Y;
      pd_and : forall {N1 Y1 N2 Y2}, T N1 Y1 -> T N2 Y2 -> (T (N1 + N2) (Y1 * Y2))%type;
      pd_or : forall {N1 Y1 N2 Y2}, T N1 Y1 -> T N2 Y2 -> (T (N1 * N2) (Y1 + Y2))%type;
      pd_neg : forall {N Y}, T N Y -> T Y N
    }.

(*

  Definition Yes' T `{PartialDecision T} := { yes' : T | as_lit yes' = yes}.
  Definition No' T `{PartialDecision T} := { no' : T | as_lit no' = no}.
  
  Definition pd_and_Monoid T `{PartialDecision T} (yes' : Yes') : Monoid T :=
    {|
      monoid_plus := pd_and;
      monoid_unit := proj1_sig yes'
    |}.

  Definition pd_or_Monoid T `{PartialDecision T} (no' : No') : Monoid T :=
    {|
      monoid_plus := pd_or;
      monoid_unit := proj1_sig no'
    |}.*)

  (* values equal up to their decisions; TODO: map contents to unit;
     need pd to be a bifunctor
   *)
  (*
  Definition eqd T `{PartialDecision T} {N1 N2 Y1 Y2}
             (a : T N1 Y1) (b : T N2 Y2) :=
    as_lit a = as_lit b.
*)
  
  Class PartialDecisionLaws T (SD : PartialDecision T) : Type :=
    {
      pd_yes_interp : forall {N Y} (y : Y), as_lit (pd_yes y) = yes N y;
      pd_no_interp : forall {N Y} (n : N), as_lit (pd_no n) = no Y n;
      pd_and_interp
      : forall {N1 N2 Y1 Y2} (a : T N1 Y1) (b : T N2 Y2),
        as_lit (pd_and a b) = pd_lit_and (as_lit a) (as_lit b);
      pd_or_interp
      : forall {N1 N2 Y1 Y2} (a : T N1 Y1) (b : T N2 Y2),
          as_lit (pd_or a b) = pd_lit_or (as_lit a) (as_lit b);
      pd_neg_interp
      : forall {N Y} (a : T N Y),
          as_lit (pd_neg a) = pd_lit_neg (as_lit a)
    }.

  (*
  Ltac solve_pd_prop :=
    repeat intro;
    unfold eqd;
    rewrite ?pd_and_interp ?pd_or_interp;
    by auto with pd_lit.
*)

  (*TODO: these are all up to isomophism now 
    same issue as laws statements (these should prob. be the laws, and the laws proven from them*)
   
  (*
  Lemma pd_and_assoc T `{SD : PartialDecision T} `{PartialDecisionLaws T}
    : forall {N Y}, Associative pd_and (@eqd T _ N Y).
  Proof. solve_pd_prop. Qed.
    
  Lemma pd_and_comm T `{SD : PartialDecision T} `{PartialDecisionLaws T}
    : forall {N M Y}, Commutative pd_and (@eqd T _ N M Y).
  Proof. solve_pd_prop. Qed.

  Lemma pd_and_unit T `{SD : PartialDecision T} `{PartialDecisionLaws T} {N M Y} (yes' : T N M Y)
    : as_lit yes' = yes -> LeftUnit pd_and yes' (@eqd T _ N M Y).
  Proof. 
    repeat intro;
    unfold eqd;
    rewrite ?pd_and_interp ?pd_or_interp;
    auto with pd_lit.
    rewrite H0.
    by case (as_lit a).
  Qed.
  
  Lemma pd_or_assoc T `{SD : PartialDecision T} `{PartialDecisionLaws T}
    : forall {N M Y}, Associative pd_or (@eqd T _ N M Y).
  Proof. solve_pd_prop. Qed.
    
  Lemma pd_or_comm T `{SD : PartialDecision T} `{PartialDecisionLaws T}
    : forall {N M Y}, Commutative pd_or (@eqd T _ N M Y).
  Proof. solve_pd_prop. Qed.

  Lemma pd_or_unit T `{SD : PartialDecision T} `{PartialDecisionLaws T} {N M Y} (no' : T N M Y)
    : as_lit no' = no -> LeftUnit pd_or no' (@eqd T _ N M Y).
  Proof. 
    repeat intro;
    unfold eqd;
    rewrite ?pd_and_interp ?pd_or_interp;
    auto with pd_lit.
    rewrite H0.
    by case (as_lit a).
  Qed. 
   *)

  Definition try_bind_no {T M : Type -> Type -> Type} {N Y N' Y'} `{PartialDecision T}
             (pd : T N Y)
             (f : N -> M N' Y')
             (default : M N' Y') : M N' Y' :=
    match as_lit pd with
    | no m => f m
    | _ => default
    end.
  
  Definition try_bind_yes {T M : Type -> Type -> Type} {N Y N' Y'} `{PartialDecision T}
             (pd : T N Y)
             (f : Y -> M N' Y')
             (default : M N' Y') : M N' Y' :=
    match as_lit pd with
    | yes m => f m
    | _ => default
    end.
  
End PartialDecisions.

Instance Sum_PartialDecision : PartialDecision sum :=
  {
    as_lit _ _ s :=
      match s with inl m => no _ m | inr m => yes _ m end;
    pd_yes _ _ y := inr y;
    pd_no _ _ y := inl y;
    pd_and _ _ _ _ s1 s2 :=
      match s1, s2 with
      | inl m, _ => inl (inl m)
      | _, inl m => inl (inr m)
      | inr m1, inr m2 => inr (m1,m2)
      end;
    pd_or _ _ _ _ s1 s2 :=
      match s1, s2 with
      | inr m, _ => inr (inl m)
      | _, inr m => inr (inr m)
      | inl m1, inl m2 => inl (m1,m2)
      end;
    pd_neg _ _ s := match s with inl m => inr m | inr m => inl m end
  }.

Instance Sum_PartialDecisionLaws : PartialDecisionLaws Sum_PartialDecision.
Proof.
  split; move => A B //=; first [case => //= | move => C D; case => ma; case => mb //=].
Qed.

Instance Monad_FixResult : Monad FixResult :=
  {
    ret _ := Term;
    bind _ _ m f :=
      match m with
      | Term t => f t
      | Diverge => Diverge
      end
  }.

Instance MonadLaws_FixResult : MonadLaws Monad_FixResult.
Proof.
  split.
  { intros; simpl; auto. }
  { intros until aM; case: aM; simpl; auto. }
Qed.

(*Section BiFunctor.

  Class BiFunctor (F : Type -> Type -> Type) : Type :=
    {
      bifmap : forall {A B C D}, (A -> C) -> (B -> D) -> F A B -> F C D 
    }.

  (*TODO: laws*)
  

End BiFunctor.*)

Instance FixResult_PartialDecision R `{PartialDecision R}
  : PartialDecision (fun N Y => FixResult (R N Y)) :=
  {
    as_lit _ _ m :=
      match m with
      | Term t => as_lit t
      | Diverge => maybe _ _
      end;
    pd_yes _ _ y := Term (pd_yes y);
    pd_no _ _ n := Term (pd_no n);
    pd_and _ _ _ _ m1 m2 :=
      match m1, m2 with
      | Term t1, Term t2 => ret (pd_and t1 t2)
      (* TODO: not quite right; diverge does not have type T *)
      | Term t1, Diverge =>
        try_bind_no (M := fun N Y => FixResult (R N Y))
                    t1 (compose Term (compose pd_no inl)) Diverge
      | Diverge, Term t2 =>
        try_bind_no (M := fun N Y => FixResult (R N Y))
                    t2 (compose Term (compose pd_no inr)) Diverge
      | Diverge, Diverge => Diverge
      end;
    pd_or _ _ _ _ m1 m2 :=
      match m1, m2 with
      | Term t1, Term t2 => ret (pd_or t1 t2)
      | Term t1, Diverge =>
        try_bind_yes (M := fun N Y => FixResult (R N Y))
                     t1 (compose Term (compose pd_yes inl)) Diverge
      | Diverge, Term t2 => 
        try_bind_yes (M := fun N Y => FixResult (R N Y))
                     t2 (compose Term (compose pd_yes inr)) Diverge
      | Diverge, Diverge => Diverge
      end;
    pd_neg _ _ m :=
      match m with
      | Term t => ret (pd_neg t)
      | Diverge => Diverge
      end
  }.

Instance FixResult_PartialDecisionLaws R `{SDR : PartialDecision R} `{PartialDecisionLaws R}
  : PartialDecisionLaws (FixResult_PartialDecision R).
Proof.
  destruct H.
  split; auto;
    first [ move => N1 N2 Y1 Y2; case => [t1|]; case => [t2|] => //=
          | move => N Yl; case => [t1|] => //= ];
    unfold try_bind_no; unfold try_bind_yes;
      try first [case alt: (as_lit t1) => //=; by eauto
            | case alt: (as_lit t2) => //=; by eauto
            | case alt: (as_lit a) => //=; by eauto].
Qed.
    
Instance MonadTrans_GFix_Result_N (n : N) : MonadT FixResult GFix :=
  {
    lift _ m := runGFix m n
  }.

Instance MonadTransLaws_GFix_Result_N (n : N)
  : MonadTLaws Monad_FixResult Monad_GFix (MonadTrans_GFix_Result_N n).
Proof.
  split.
  { intros; simpl; eauto. }
  {
    intros until c; elim: c.
    intros.
    by simpl.
  }
Qed.

Definition GFix_Diverge {T} : GFix T := mkGFix (fun _ => Diverge).

(*TODO: rec_true and rec_and derivable; derive rec_or from monadplus?*)
Instance PartialDecision_GFix R `{PartialDecision R} (n : N)
  : PartialDecision (fun N Y => GFix (R N Y)) :=
  {
    as_lit _ _ m := as_lit (runGFix m n);
    pd_yes _ _ m := mkGFix (fun _ => pd_yes m);
    pd_no _ _ m := mkGFix (fun _ => pd_no m);
    pd_and _ _ _ _ m1 m2 := mkGFix (fun n' => pd_and (runGFix m1 n') (runGFix m2 n'));
    pd_or _ _ _ _ m1 m2 := mkGFix (fun n' => pd_or (runGFix m1 n') (runGFix m2 n'));
    pd_neg _ _ m := mkGFix (fun n' => pd_neg (runGFix m n'))
  }.

Instance PartialDecisionLaws_GFix (R : Type) `{PartialDecision R} `{PartialDecisionLaws R} (n : N)
  : PartialDecisionLaws (PartialDecision_GFix R n).
Proof.
  destruct H0.
  split;
    case => ra; case => rb;
    simpl;
    remember (ra n) as ran;
    destruct ran;
    remember (rb n) as rbn;
    destruct rbn; simpl; auto;
    by case alt: (as_lit r) => //=.
Qed.

Inductive pd_with_msg (N M Y : Type) : Type :=
| yes_msg : Y -> pd_with_msg N M Y
| maybe_msg : M -> pd_with_msg N M Y
| no_msg : N -> pd_with_msg N M Y.

(* left-biased; chooses left message on all operations*)
(*TODO: better to make N M Y monoidal, combine elements? *)
Instance PartialDecision_With_Msg {N} {M} {Y} : PartialDecision (pd_with_msg N M Y) :=
  {
    as_lit m :=
      match m with
      | yes_msg _ => yes
      | maybe_msg _ => maybe
      | no_msg _ => no
      end;
    pd_and m1 m2 :=
      match m1, m2 with
      | yes_msg msg, yes_msg _ => yes_msg _ _ msg
      | yes_msg _, maybe_msg msg => maybe_msg _ _ msg
      | maybe_msg msg, yes_msg _ => maybe_msg _ _ msg
      | maybe_msg msg, maybe_msg _ => maybe_msg _ _ msg
      | no_msg msg, _ => no_msg _ _ msg
      | _, no_msg msg => no_msg _ _ msg
    end;
    pd_or m1 m2 :=
      match m1, m2 with
      | yes_msg msg, _ => yes_msg _ _ msg
      | _, yes_msg msg => yes_msg _ _ msg
      | maybe_msg msg, _ => maybe_msg _ _ msg
      | _, maybe_msg msg => maybe_msg _ _ msg
      | no_msg msg, no_msg _ => no_msg _ _ msg
    end
  }.

Instance PartialDecisionLaws_With_Msg {N} {M} {Y} : PartialDecisionLaws (@PartialDecision_With_Msg N M Y).
Proof.
  split; case => ma; case => mb //=.
Qed.

Instance Monad_PD_With_Msg {N} {M} : Monad (pd_with_msg N M) :=
  {
    ret := yes_msg _ _;
    bind _ _ m f :=
      match m with
      | yes_msg msg => f msg
      | maybe_msg msg => maybe_msg _ _ msg
      | no_msg msg => no_msg _ _ msg
      end
  }.

(*TODO: one instance or two? if n and m are the same, two is bad *)
Instance MonadExc_PD_With_Msg {N} {M} : MonadExc (N + M) (pd_with_msg N M) :=
  {
    raise _ nm :=
      match nm with
      | inl n => no_msg _ _ n
      | inr m => maybe_msg _ _ m
      end;
    catch Y m k :=
      match m with
      | yes_msg msg => yes_msg _ _ msg
      | maybe_msg msg => k (inr msg)
      | no_msg msg => k (inl msg)
      end
  }.

(* Not defined in the library *)
Section MonadLaws.
  
  Class MonadExcLaws {m : Type -> Type} {E} (M : Monad m) (ME : MonadExc E m) : Type :=
    {
      raise_catch : forall {A} (e : E) (k : E -> m A), catch (raise e) k = k e;
      raise_bind : forall {A} {B} (e : E) (f : A -> m B), bind (raise e) f = raise e;
      catch_raise : forall {A} (v : m A) , catch v raise = v;
      catch_ret : forall {A} (a : A) (k : E -> m A), catch (ret a) k = ret a
    }.
  
End MonadLaws.  

Instance MonadExcLaws_PD_With_Msg {N} {M}
  : MonadExcLaws Monad_PD_With_Msg (@MonadExc_PD_With_Msg N M).
Proof.
  split.
  1,2: intros until e; case: e => [n | m] k => //=.
  intros until v; case: v => [y | m | n] => //=.
  intros; simpl; auto.
Qed.

(*
(*TODO: issue: bind does not get along well with parial decisions. Use relative bimonad?*)
Class RelativeBimonad (j m : Type -> Type -> Type) : Type :=
  {
    biret : forall {a b}, j a b -> m a b;
    bibind : forall {a b c d}, m a b -> (j a b -> m c d) -> m c d
  }.

Class RelativeBimonadLaws {j m : Type -> Type -> Type} `{RelativeBimonad j m} : Type :=
  {
    bibind_of_bireturn :
      forall {A B C D} (a : j A B) (f : j A B -> m C D),
        bibind (biret a) f = f a;
    bibind_associativity : 
      forall {A B C D E F} (aM:m A D) (f: j A D -> m B E) (g: j B E -> m C F),
        bibind (bibind aM f) g = bibind aM (fun a => bibind (f a) g)
  }.

Instance PD_With_Msg_RelativeBimonad {N} : RelativeBimonad sum (pd_with_msg N) :=
  {
    biret _ _ a :=
      match a with
      | inl m => maybe_msg _ _ m
      | inr y => yes_msg _ _ y
      end;
    bibind A B C D m f :=
      match m with
      | yes_msg msg => f (inr msg)
      | maybe_msg msg => maybe_msg _ _ msg
      | no_msg msg => f (inl msg)
      end
  }.
*)

(*TODO: compose monads *)
Instance MonadT_Inner {mi mo : Type -> Type} `{Monad mo} : MonadT (compose mo mi) mi :=
  { lift _ := ret }.

Instance MonadT_Outer {mi mo : Type -> Type} `{Monad mi} `{Monad mo} : MonadT (compose mo mi) mo :=
  { lift _ := fmap ret }.

(*TODO: monadT laws*)

Instance Monad_GFix_With_Msg {N} {M} : Monad (compose GFix (pd_with_msg N M)) :=
  {
    ret _ a := ret (m:=GFix) (ret a);
    bind _ _ m f :=
      mkGFix
        (fun fuel =>
           match runGFix m fuel with
           | Diverge => Diverge
           | Term (yes_msg msg) => runGFix (f msg) fuel
           | Term (maybe_msg msg) => ret (maybe_msg _ _ msg)
           | Term (no_msg msg) => ret (no_msg _ _ msg)
           end)
  }.
  
  
Fail Proof.
(*TODO: playing around with fuel *)
Inductive check_result (C : Type) (E : Type) (R : Type) : Type :=
| check_success (r : R)
| check_compute (k : nat -> check_result C E R)
| no_fuel
| check_error (c : C) (e : E).

Fixpoint cr_bind {C} {E} R1 R2 (m : check_result C E R1) f : check_result C E R2 :=
      match m with
      | check_success r => f r
      | check_compute k => check_compute (fun fuel => cr_bind _ (k fuel) f)
      | no_fuel => no_fuel _ _ _
      | check_error c e => check_error _ c e
      end.

Instance check_result_monad {C} {E} : Monad (check_result C E) :=
  {
    ret := check_success C E;
    bind := cr_bind
  }.

Fixpoint cr_catch {C} {E} {R} (m : check_result C E R) cont : check_result C E R :=
      match m with
      | check_success r => check_success _ _ r
      | check_compute k => check_compute (fun fuel => cr_catch (k fuel) cont)
      | no_fuel => no_fuel _ _ _
      | check_error c e => cont (c,e)
      end.

Instance check_result_monad_exc {C} {E}
  : MonadExc (C * E) (check_result C E) :=
  {
    raise _ p := let (c,e) := p in check_error _ c e;
    catch _ := cr_catch
  }.

Fixpoint cr_mfix {C} {E} {R1} {R2} f fuel : R1 -> check_result C E R2 :=
  match fuel with
  | 0 => fun _ => no_fuel _ _ _
  | fuel'.+1 => f (cr_mfix f fuel')
  end.

Instance check_result_monad_fix {C} {E} : MonadFix (check_result C E) :=
  {
    mfix _ _ f r1 := check_compute (fun fuel => cr_mfix f fuel r1)
  }.



(*TODO: set up for detection of the first error or all errors? run time matters for proofs *)
(*TODO: for now, left error *)
Fixpoint cr_mplus {C} {E} {R1} {R2} m1 m2 : check_result C E (R1 + R2)%type :=
  match m1, m2 with
  | check_success r1, _ => ret (inl r1)
  | _, check_success r2 => ret (inr r2)
  | check_compute k1, check_compute k2 => check_compute (fun fuel => cr_mplus (k1 fuel) (k2 fuel))
  | check_compute k, _ => check_compute (fun fuel => fmap inl (k fuel))
  | _, check_compute k => check_compute (fun fuel => fmap inr (k fuel))
  | check_error c e, _ => check_error _ c e
  | _, check_error c e => check_error _ c e
  | no_fuel, no_fuel => no_fuel _ _ _
  end.

Instance check_result_monad_plus {C} {E} : MonadPlus (check_result C E) :=
  {
    mplus _ _ := cr_mplus
  }.

Print MonadLaws.

(* Laws *)
Instance check_result_monad_laws {C} {E} : MonadLaws (@check_result_monad C E).
Proof.
  constructor; [ by eauto|].
  intros until aM.
  elim: aM => //=.
  intros.
  f_equal.
  (*TODO: need function extensionality to prove monad laws due to check_compute; waeken from eq?
    use library instead of writing? (e.g. effects as ...transformers paper?)
   *)

Fail Proof.
Notation "@@[ default ] fuel =1> fuel' ; e @@" :=
  (match fuel with
     | 0 => default
     | fuel'.+1 => e
   end).

Notation "x <-[ default ] val ; body" :=
  (match val with
   | Some x => body
   | None => default
   end) (at level 80, right associativity).


(*TODO: move error messaging code into separate file/library *)
(* Give good error messages so that users know what goes wrong
   Note: an error does not mean the term is necessarily ill-formed
   just that more fuel will not change the result
 *)
Variant wf_result : Set :=
| wf_success
| wf_no_fuel
| wf_error (s : string).

Definition wf_result_is_success r : bool :=
  match r with
  | wf_success => true
  | _ => false
  end.

Coercion wf_result_is_success : wf_result >-> bool.

Definition wf_result_seq r1 : wf_result -> wf_result :=
  match r1 with
  | wf_success => id
  | _ => fun _ => r1
  end.

Definition wf_result_alt r1 : wf_result -> wf_result :=
  match r1 with
  | wf_success => fun _ => wf_success
  (*TODO: figure out the best way to incorporate left branch's error message *)
  | _ => id
  end.

Notation "check! r1 ; r2" := (wf_result_seq r1 r2) (at level 80, right associativity).

Notation "r1 <||> r2" := (wf_result_alt r1 r2) (at level 70).

Notation "check![ es ] b1 ; r" :=
  (wf_result_seq (if b1 then wf_success else wf_error es) r)
    (at level 80, right associativity).

(*TODO: notation or fn call*)
Definition wf_result_ctx c r1 : wf_result :=
  match r1 with
  | wf_success => wf_success
  | wf_no_fuel => wf_no_fuel
  | wf_error s => wf_error (c ++ ":\n" ++ s)
  end.

Notation "ctx[ c ]" := (wf_result_ctx c).

Lemma wf_result_ctx_id c r : (ctx[c] r : bool) = (r : bool).
Proof.
  case: r; simpl; auto.
Qed.

Lemma check_passes_and r1 r2 : (check! r1 ; r2 : bool) = r1 && r2.
Proof.
  case: r1; case: r2; simpl; split; eauto.
Qed.

Lemma default_as_bool {A} (default : wf_result) (val : option A) (body : A -> wf_result)
  : (match val with
     | Some x => body x
     | None => default
     end : bool)
    = (match val with
       | Some x => (body x) : bool
       | None => default : bool
       end : bool).
Proof.
  case val; eauto.
Qed.

Lemma alt_as_or r1 r2 : (r1 <||> r2 : bool) = r1 || r2.
Proof.
  case: r1; case: r2; simpl; split; eauto.
Qed.

Lemma if_distr_bool b (r2 r3 : wf_result)
  : ((if b then r2 else r3) : bool) = if b then r2 : bool else r3 : bool.
Proof.
  case: b; auto.
Qed.

Ltac result_as_bool :=
  rewrite ?default_as_bool ?wf_result_ctx_id ?check_passes_and ?alt_as_or ?if_distr_bool;
  change (wf_success : bool) with true;
  change (wf_no_fuel : bool) with false;
  change (wf_error _ : bool) with false.

