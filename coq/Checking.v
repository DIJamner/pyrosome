
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

Section SemiDecisions.

  (* the final element of the SemiDecision structure *)
  Variant semi_decision : predArgType := yes | maybe | no.

  Definition sd2o (sd : semi_decision) : 'I_3 :=
    match sd with
    | yes => inord 0 | maybe => inord 1 | no => inord 2
    end.
  
  Definition o2sd (o : 'I_3) : option semi_decision :=
    match val o with
    | 0 => Some yes
    | 1 => Some maybe
    | 2 => Some no
    | _ => None
    end.

  Lemma pcan_sdo3 : pcancel sd2o o2sd.
  Proof. by case; rewrite /o2sd /= inordK. Qed.

  (* I want a more straightforward equality computationally *)
  Definition sd_eq_fn a b : bool :=
    match a,b with
    | yes, yes => true
    | maybe, maybe => true
    | no, no => true
    | _, _ => false
    end.

  Lemma sd_eq_fn_Reflect a b : reflect (a = b) (sd_eq_fn a b).
  Proof.
    case: a; case: b => //=; by constructor.
  Qed.
  
  Definition semi_decision_eqMixin := Equality.Mixin sd_eq_fn_Reflect.
  Canonical semi_decision_eqType := EqType semi_decision semi_decision_eqMixin.
  Definition semi_decision_choiceMixin := PcanChoiceMixin pcan_sdo3.
  Canonical semi_decision_choiceType := ChoiceType semi_decision semi_decision_choiceMixin.
  Definition semi_decision_countMixin := PcanCountMixin pcan_sdo3.
  Canonical semi_decision_countType := CountType semi_decision semi_decision_countMixin.
  Definition semi_decision_finMixin := PcanFinMixin pcan_sdo3.
  Canonical semi_decision_finType := FinType semi_decision semi_decision_finMixin.

  Create HintDb sd_lit discriminated.
  
  (*TODO: make a prop whose negation only holds when it is no? might overcomplicate things *)
  Definition sd_as_prop sd : Prop := sd = yes.
  Coercion sd_as_prop : semi_decision >-> Sortclass.

  Print Bool.reflect.
  
  Variant semi_decide (P : Prop) : semi_decision -> Set :=
  | DecideY : P -> semi_decide P yes
  | DecideN : ~P -> semi_decide P no
  | DecideM : semi_decide P maybe.
  Hint Constructors semi_decide.
  
  Definition sd_lit_and sd1 sd2 :=
    match sd1, sd2 with
    | yes, yes => yes
    | yes, maybe => maybe
    | maybe, yes => maybe
    | maybe, maybe => maybe
    | _, _ => no
    end.

  Lemma sd_lit_and_assoc : Associative sd_lit_and eq.
  Proof.
    case => //; case => //; case => //.
  Qed.
  Hint Resolve sd_lit_and_assoc : sd_lit.
  
  Lemma sd_lit_and_comm : Commutative sd_lit_and eq.
  Proof.
    case => //; case => //.
  Qed.
  Hint Resolve sd_lit_and_comm : sd_lit.

  Lemma sd_lit_and_unit : LeftUnit sd_lit_and yes eq.
  Proof.
    case => //.
  Qed.
  Hint Resolve sd_lit_and_unit : sd_lit.
  
  Definition sd_lit_or sd1 sd2 :=
    match sd1, sd2 with
    | yes, _ => yes
    | _,  yes => yes
    | maybe, _ => maybe
    | _, maybe => maybe
    | no, no => no
    end.

  Lemma sd_lit_or_assoc : Associative sd_lit_or eq.
  Proof.
    case => //; case => //; case => //.
  Qed.
  Hint Resolve sd_lit_or_assoc : sd_lit.

  Lemma sd_lit_or_comm : Commutative sd_lit_or eq.
  Proof.
    case => //; case => //.
  Qed.
  Hint Resolve sd_lit_or_comm : sd_lit.
  
  Lemma sd_lit_or_unit : LeftUnit sd_lit_or no eq.
  Proof.
    case => //.
  Qed.
  Hint Resolve sd_lit_or_unit : sd_lit.

  (*TODO: add negation*)
  Class SemiDecision (T : Type) : Type :=
    {
      (* force semi_decision to be final wrt instances of this class *)
      as_lit : T -> semi_decision;
      sd_and : T -> T -> T;
      sd_or : T -> T -> T
    }.

  Definition Yes' T `{SemiDecision T} := { yes' : T | as_lit yes' = yes}.
  Definition No' T `{SemiDecision T} := { no' : T | as_lit no' = no}.
  
  Definition sd_and_Monoid T `{SemiDecision T} (yes' : Yes') : Monoid T :=
    {|
      monoid_plus := sd_and;
      monoid_unit := proj1_sig yes'
    |}.

  Definition sd_or_Monoid T `{SemiDecision T} (no' : No') : Monoid T :=
    {|
      monoid_plus := sd_or;
      monoid_unit := proj1_sig no'
    |}.

  (* values equal up to their literal interpretations *)
  Definition eqd T `{SemiDecision T} a b := as_lit a = as_lit b.

  (*TODO: what laws do I really need/have? all up to eqd? commutativity? *)
  Class SemiDecisionLaws T (SD : SemiDecision T) : Type :=
    {
      sd_and_interp : forall a b, as_lit (sd_and a b) = sd_lit_and (as_lit a) (as_lit b);
      sd_or_interp : forall a b, as_lit (sd_or a b) = sd_lit_or (as_lit a) (as_lit b)
    }.

  Ltac solve_sd_prop :=
    repeat intro;
    unfold eqd;
    rewrite ?sd_and_interp ?sd_or_interp;
    by auto with sd_lit.
  
  Lemma sd_and_assoc T `{SD : SemiDecision T} `{SemiDecisionLaws T}
    : Associative sd_and (@eqd T _).
  Proof. solve_sd_prop. Qed.
    
  Lemma sd_and_comm T `{SD : SemiDecision T} `{SemiDecisionLaws T}
    : Commutative sd_and (@eqd T _).
  Proof. solve_sd_prop. Qed.

  Lemma sd_and_unit T `{SD : SemiDecision T} `{SemiDecisionLaws T} (yes' : T)
    : as_lit yes' = yes -> LeftUnit sd_and yes' (@eqd T _).
  Proof. 
    repeat intro;
    unfold eqd;
    rewrite ?sd_and_interp ?sd_or_interp;
    auto with sd_lit.
    rewrite H0.
    by case (as_lit a).
  Qed.
  
  
  Lemma sd_or_assoc T `{SD : SemiDecision T} `{SemiDecisionLaws T}
    : Associative sd_or (@eqd T _).
  Proof. solve_sd_prop. Qed.
    
  Lemma sd_or_comm T `{SD : SemiDecision T} `{SemiDecisionLaws T}
    : Commutative sd_or (@eqd T _).
  Proof. solve_sd_prop. Qed.

  Lemma sd_or_unit T `{SD : SemiDecision T} `{SemiDecisionLaws T} (no' : T)
    : as_lit no' = no -> LeftUnit sd_or no' (@eqd T _).
  Proof. 
    repeat intro;
    unfold eqd;
    rewrite ?sd_and_interp ?sd_or_interp;
    auto with sd_lit.
    rewrite H0.
    by case (as_lit a).
  Qed.
 

End SemiDecisions.

Instance Bool_SemiDecision : SemiDecision bool :=
  {
    as_lit b := if b then yes else no;
    sd_and b1 b2 := b1 && b2;
    sd_or b1 b2 := b1 || b2
  }.

Instance Bool_SemiDecisionLaws : SemiDecisionLaws Bool_SemiDecision.
Proof.
  split; case; case => //=.
Qed.

Instance Unit_SemiDecision : SemiDecision unit :=
  {
    as_lit _ := yes;
    sd_and _ _ := tt;
    sd_or _ _ := tt
  }.

Instance Unit_SemiDecisionLaws : SemiDecisionLaws Unit_SemiDecision.
Proof.
  split; auto.
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

Instance FixResult_SemiDecision (R : Type) `{SemiDecision R} : SemiDecision (FixResult R) :=
  {
    as_lit m :=
      match m with
      | Term t => as_lit t
      | Diverge => maybe
      end;
    sd_and m1 m2 :=
      match m1, m2 with
      | Term t1, Term t2 => ret (sd_and t1 t2)
      | Term t1, Diverge => if as_lit t1 == no then Term t1 else Diverge
      | Diverge, Term t2 => if as_lit t2 == no then Term t2 else Diverge
      | Diverge, Diverge => Diverge
      end;
    sd_or m1 m2 :=
      match m1, m2 with
      | Term t1, Term t2 => ret (sd_or t1 t2)
      | Term t1, Diverge => if as_lit t1 == no then Diverge else Term t1
      | Diverge, Term t2 => if as_lit t2 == no then Diverge else Term t2
      | Diverge, Diverge => Diverge
      end;
  }.

Instance FixResult_SemiDecisionLaws (R : Type) `{SDR : SemiDecision R} `{SemiDecisionLaws R}
  : SemiDecisionLaws (FixResult_SemiDecision R).
Proof.
  destruct H.
  split; case => [t1|]; case => [t2|] => //=.
  case alt: (as_lit t1) => //=.
  case alt: (as_lit t2) => //=.
  case alt: (as_lit t1) => //=.
  case alt: (as_lit t2) => //=.
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
Instance SemiDecision_GFix (R : Type) `{SemiDecision R} (n : N)
  : SemiDecision (GFix R) :=
  {
    as_lit m := as_lit (runGFix m n);
    sd_and m1 m2 := mkGFix (fun n' => sd_and (runGFix m1 n') (runGFix m2 n'));
    sd_or m1 m2 := mkGFix (fun n' => sd_or (runGFix m1 n') (runGFix m2 n'))
  }.

Instance SemiDecisionLaws_GFix (R : Type) `{SemiDecision R} `{SemiDecisionLaws R} (n : N)
  : SemiDecisionLaws (SemiDecision_GFix R n).
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

Inductive sd_with_msg (N M Y : Type) : Type :=
| yes_msg : Y -> sd_with_msg N M Y
| maybe_msg : M -> sd_with_msg N M Y
| no_msg : N -> sd_with_msg N M Y.

(* left-biased; chooses left message on all operations*)
(*TODO: better to make N M Y monoidal, combine elements? *)
Instance SemiDecision_With_Msg {N} {M} {Y} : SemiDecision (sd_with_msg N M Y) :=
  {
    as_lit m :=
      match m with
      | yes_msg _ => yes
      | maybe_msg _ => maybe
      | no_msg _ => no
      end;
    sd_and m1 m2 :=
      match m1, m2 with
      | yes_msg msg, yes_msg _ => yes_msg _ _ msg
      | yes_msg _, maybe_msg msg => maybe_msg _ _ msg
      | maybe_msg msg, yes_msg _ => maybe_msg _ _ msg
      | maybe_msg msg, maybe_msg _ => maybe_msg _ _ msg
      | no_msg msg, _ => no_msg _ _ msg
      | _, no_msg msg => no_msg _ _ msg
    end;
    sd_or m1 m2 :=
      match m1, m2 with
      | yes_msg msg, _ => yes_msg _ _ msg
      | _, yes_msg msg => yes_msg _ _ msg
      | maybe_msg msg, _ => maybe_msg _ _ msg
      | _, maybe_msg msg => maybe_msg _ _ msg
      | no_msg msg, no_msg _ => no_msg _ _ msg
    end
  }.

Instance SemiDecisionLaws_With_Msg {N} {M} {Y} : SemiDecisionLaws (@SemiDecision_With_Msg N M Y).
Proof.
  split; case => ma; case => mb //=.
Qed.

Instance Monad_SD_With_Msg {N} {M} : Monad (sd_with_msg N M) :=
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
Instance MonadExc_SD_With_Msg {N} {M} : MonadExc (N + M) (sd_with_msg N M) :=
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
      catch_raise : forall {A} (v : m A) , catch v raise = v
    }.
  
End MonadLaws.  

Instance MonadExcLaws_SD_With_Msg {N} {M}
  : MonadExcLaws Monad_SD_With_Msg (@MonadExc_SD_With_Msg N M).
Proof.
  split.
  1,2: intros until e; case: e => [n | m] k => //=.
  intros until v; case: v => [y | m | n] => //=.
Qed.

(*TODO: compose monads *)

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

