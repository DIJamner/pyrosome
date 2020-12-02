
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(***************
 Tactics 
****************)

Tactic Notation "intro_to" constr(ty) :=
  repeat match goal with
         | |- ty -> _ => idtac
         | |- ty _ -> _ => idtac
         | |- ty _ _-> _ => idtac
         | |- ty _ _ _ -> _ => idtac
         | |- ty _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ -> _ => idtac
         | |- ty _ _ _ _ _ _ _ -> _ => idtac
         | |- _ -> _ => intro
         | |- _ => fail 2 "could not find argument with head" ty
         end.


Ltac construct_with t :=
  constructor; apply: t; eauto.


Tactic Notation "inversion" :=
  let H := fresh in
  move => H; inversion H.

Tactic Notation "swap" :=
  let H := fresh in
  let H' := fresh in
  move => H H';
  move: H' H.
  


(****************
Definitions
*****************)

(* grouped right with the fixpoint for better decreasing argument analysis*)
Definition all2 := 
fun (S T : Type) (r : S -> T -> bool) =>
fix all2 (s : seq S) (t : seq T) {struct s} : bool :=
  match s, t with
  | [::], [::] => true
  | x :: s0, y::t0 => r x y && all2 s0 t0
  | _,_ => false
  end.

Lemma all2P {T} eqb (l1 l2 : seq T)
  : (forall e1 e2, reflect (e1 = e2) (eqb e1 e2)) ->
    reflect (l1 = l2) (all2 eqb l1 l2).
Proof.
  move => eqbP.
  elim: l1 l2.
  - case; simpl; [by constructor|].
    intros.
    constructor; eauto.
    move => H; inversion H.
  - move => a l IH.
    case; simpl.
    constructor; move => H; inversion H.
    intros.
    move: (eqbP a a0).
    case (eqb a a0); simpl.
    move: (IH l0); case:(all2 eqb l l0); simpl.
    + constructor.
      inversion IH0; inversion eqbP0; by subst.
    + constructor.
      move => lfl.
      inversion lfl.
      inversion IH0; eauto.
    + constructor; move => lfl.
      inversion lfl; inversion eqbP0; auto.
Qed.

Module OptionMonad.
  Definition check b : option unit := if b then Some tt else None.
  Notation "'do' x <<- val ; body" :=
  (match val with
   | x => body
   | _ => None
   end) (at level 88, right associativity, x pattern).
  Notation "'do' x <- val ; body" :=
  (match val with
   | Some x => body
   | _ => None
   end) (at level 88, right associativity, x pattern).
End OptionMonad.


Module PartialCompMonad.
  (* TODO: differentiate out of fuel? or just calculate enough? *)
  Definition partial_comp A := nat -> option A.
  Definition fail {A : Type} : partial_comp A := fun _ => None.
  Definition ret {A : Type} e : partial_comp A := fun _ => Some e.
  Definition check b : partial_comp unit := if b then ret tt else fail.
  Notation "'do' x <<- val ; body" :=
  (match val with
   | x => body
   | _ => fail
   end) (at level 88, right associativity, x pattern).
  Notation "'do' x <%- val ; body" :=
  (match val with
   | Some x => body
   | _ => fail
   end) (at level 88, right associativity, x pattern).
  Notation "'do' x <- val ; body" :=
  (fun fuel => match (val) fuel with
   | Some x => (body) fuel
   | _ => None
   end) (at level 88, right associativity, x pattern).
End PartialCompMonad.
Import OptionMonad.

Tactic Notation "on_bind_do" tactic(t) :=
  match goal with
  | |- context [obind _ ?e] => t e
  end.

Definition try_map {A B : Type} (f : A -> option B) (l : seq A) : option (seq B) :=
  foldr (fun e acc =>
           do accl <- acc;
             do fe <- f e;
             Some (fe::accl)
        ) (Some [::]) l.

Lemma try_map_map_distribute {A B C : Type} (f : B -> option C) (g : A -> B) l
  : try_map f (map g l) = try_map (fun x => f (g x)) l.
Proof using .
  elim: l => //=.
  intros; by rewrite H.
Qed.

Lemma omap_some {A B} (e' : B) (f : A -> B) me : Some e' = omap f me -> exists e, me = Some e.
Proof using .
  case: me => //=; eauto.
Qed.

Lemma omap_some' {A B} (e' : B) (f : A -> B) me
  : Some e' = omap f me -> exists e, Some e' = omap f (Some e).
Proof using .
  move => someeq.
  suff: exists e, me = Some e.
  move: someeq.
  swap.
  case => e ->.
  eauto.
  apply: omap_some; eauto.
Qed.

 (*Todo: whichs more useful?*)
(*Definition nth_level {A} l n : option A :=
  if n <= size l then List.nth_error l (size l - n.+1) else None.*)
Definition nth_level {A} a l n : A :=
  if n < size l then nth a l (size l - n.+1) else a.
Definition is_nth_level {A:eqType} (l : seq A) n x : bool :=
   (n < size l) && (List.nth_error l (size l - n.+1) == Some x).

Lemma is_nth_level_to_fn {A:eqType} a (l : seq A) n x
  : is_nth_level l n x -> (nth_level a l n == x).
Proof using .
  unfold nth_level; unfold is_nth_level.
  case: (n < size l); simpl; auto.
  generalize (size l - n.+1) as y.
  move => y; move: y l.
  elim; intros until l; case: l; simpl; auto.
Qed.

Lemma fn_to_is_nth_level {A:eqType} a (l : seq A) n x
  : n < size l -> is_nth_level l n x = (nth_level a l n == x).
Proof using .
  unfold nth_level; unfold is_nth_level.
  move => nlt.
  rewrite nlt; simpl.
  suff: (size l - n.+1 < size l).
  generalize (size l - n.+1) => y.
  clear nlt.
  elim: y l; intros until l; case: l; easy.
  move: nlt. generalize (size l) as sz.
  case; try easy.  
  intros.
  rewrite subSS.
  by apply sub_ord_proof.
Qed.

Lemma ListIn_in {A:eqType} (x : A) l : List.In x l -> x\in l.
Proof using .
  elim: l => //=.
  move => a l IH.
  rewrite in_cons.
  case.
  - move ->; apply /orP.
    left; by apply /eqP.
  - move /IH => IH'; apply /orP; by right.
Qed.

Lemma is_nth_level_in  {A:eqType} (l : seq A) n x
  : is_nth_level l n x -> x \in l.
Proof using .
  unfold is_nth_level; case /andP => _.
  generalize (size l - n) as m.
  move => m.
  elim: m l.
  - case; simpl; auto.
    move => a l.
    move /eqP => H.
    apply List.nth_error_In in H.
    by apply ListIn_in.
  - move => m IH; case; simpl; auto; intro_to is_true.
Qed.

Require Import String.

Definition named_list_set (A : Set) :=list (string * A).
Definition named_list (A : Type) :=list (string * A).

Fixpoint named_list_lookup {A} default (l : named_list A) (s : string) : A :=
  match l with
  | [::] => default
  | (s', v)::l' =>
    if eqb s s' then v else named_list_lookup default l' s
  end.

Fixpoint named_list_check {A : eqType} (l : named_list A) (s : string) e : bool :=
  match l with
  | [::] => false
  | (s', v)::l' =>
    if eqb s s' then v == e else named_list_check l' s e
  end.



Inductive len_eq {A} {B} : list A -> list B -> Type :=
| len_eq_nil : len_eq [::] [::]
| len_eq_cons : forall a a' l l',
    len_eq l l' -> len_eq (a::l) (a'::l').

Definition pair_map_snd {A B C} (f : B -> C) (p : A * B) :=
  let (a,b) := p in (a, f b).
Arguments pair_map_snd {A B C} f !p/.

Definition named_map {A B : Set} (f : A -> B) : named_list A -> named_list B
  := map (pair_map_snd f).
Arguments named_map {A B} f !l/.

Lemma str_eqP : forall s s', reflect (s = s') (eqb s s').
Admitted.

Canonical str_eqType := @Equality.Pack string (Equality.Mixin str_eqP).

Definition fresh {A} n (nl : named_list A) : bool :=
  ~~ (n \in map fst nl).

Arguments fresh {A} n !nl/.


Lemma fresh_tail {A} n (l1 l2 : named_list A)
  : fresh n (l1 ++ l2) -> fresh n l2.
Proof.
  elim: l1; simpl; auto.
  intros a l.
  unfold fresh; simpl; intro IH.
  rewrite !in_cons.
  move /norP => [_] //.
Qed.

Lemma fresh_neq_in {A : eqType} n l n' (t : A)
  : fresh n l -> (n',t) \in l -> ~~ (n'==n).
Proof.
  elim: l; unfold fresh; simpl.
  by cbv.
  move => [n1 t1] l IH.
  rewrite !in_cons.
  move /norP => //= [nn1 nnl].
  move /orP; case; eauto.
  {
    move /eqP.
    case.
    move -> => _.
    
    apply /negP.
    move /eqP.
    move: nn1=> /eqP.
    intros nnneq nneq.
    apply nnneq.
    by symmetry.
  }
Qed.

Lemma fresh_neq_in_fst {A : eqType} n (l : named_list A) n'
  : fresh n l -> n' \in (map fst l) -> ~~ (n'==n).
Proof using .
  elim: l; unfold fresh; simpl.
  by cbv.
  move => [n1 t1] l IH.
  rewrite !in_cons.
  move /norP => //= [nn1 nnl].
  move /orP; case; eauto.
  {
    move /eqP.
    case.
    move ->.
    
    apply /negP.
    move /eqP.
    move: nn1=> /eqP.
    intros nnneq nneq.
    apply nnneq.
    by symmetry.
  }
Qed.

Fixpoint all_fresh {A} (l : named_list A) : bool :=
  match l with
  | [::] => true
  | (n,_)::l' => (fresh n l') && (all_fresh l')
  end.

Lemma pair_fst_in {N A : eqType} l (n: N) (a : A)
  : (n,a) \in l -> n \in (map fst l).
Proof using.
  elim: l; simpl.
  { inversion. }
  {
    case.
    intros; simpl in *.
    move: H0.
    rewrite !in_cons.
    move /orP; case.
    {
      move /eqP; case => -> _.
      rewrite eq_refl; done.
    }
    {
      intros; apply /orP; auto.
    }
  }
Qed.

Lemma fresh_iff_names_eq {A B} n (l1 : named_list A) (l2 : named_list B)
  : map fst l1 = map fst l2 -> fresh n l1 = fresh n l2.
Proof using .
  elim: l1 l2; intros until l2; case: l2; intros;
    repeat match goal with
           | [H : _*_|-_]=> destruct H; simpl in *
           | [H : _::_ = _|-_] => inversion H; clear H
           | [H : _ = _::_|-_] => inversion H; clear H
           end;auto.
Qed.

Ltac break_andbs :=
  repeat match goal with
           [H : is_true(_&&_)|-_]=>
           let H' := fresh H in
           move: H => /andP [H' H]
         end.
Ltac break :=
  repeat match goal with
         | [H: _*_|-_]=> destruct H
         | [H: _/\_|-_]=> destruct H
         | [H : is_true(_&&_)|-_]=>
           let H' := fresh H in
           move: H => /andP [H' H]
         end.

Ltac break_goal :=
  repeat match goal with
         | [|- _*_]=> split
         | [|- _/\_]=> split
         | [|-is_true(_&&_)]=>
           apply /andP; split
         end.


Lemma named_map_fst_eq {A B: Set} (f : A -> B) l
  : map fst (named_map f l) = map fst l.
Proof using .  
  elim: l; intros; break; simpl in *; f_equal; auto.
Qed.
