Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Message.
Set Default Proof Mode "Classic".

Ltac2 rec head (x:constr) : constr :=
  match Unsafe.kind x with
  | Unsafe.App x _ => head x
  | _ => x
  end.

Ltac2 rec range_inclusive (a : int) (b : int) :=
  if Int.gt a b then [] else a::range_inclusive (Int.add a 1) b.

(*TODO: generalize symmetric induction to allow for these variations*)
Ltac2 constr_ind (x : constr) :=
  Std.induction true [
      {
        Std.indcl_arg := Std.ElimOnConstr (fun ()=>(x,Std.NoBindings));
        Std.indcl_eqn := None;
        Std.indcl_as := None;
        Std.indcl_in := None;                                        
    }] None.

(* TODO: pass in n or no? Does ltac2 have numgoals? *)
Ltac2 enter_n n (tac : int -> unit) :=
  Control.dispatch (List.map (fun n () => tac n) (range_inclusive 1 n)).

Ltac2 symmetric_induction (x : constr) :=
  let t := type x in
  match Unsafe.kind (head t) with
  | Unsafe.Ind ind l =>
      let ind_data := Ind.data ind in
      let constr_count := Ind.nconstructors ind_data in
      constr_ind x;
      enter_n constr_count (fun i => Std.constructor_n true i Std.NoBindings)
      (*
      iter_nz constr_count (fun i => Control.focus i 1 (fun () => Std.constructor_n true i Std.NoBindings))*)
  | _ => Control.backtrack_tactic_failure "not a value of inductive type"
  end.

Ltac symmetric_induction x :=
  let tac := ltac2:(x|- match Ltac1.to_constr x with Some cx => symmetric_induction cx | None => fail end) in
  tac x.

Ltac2 rec nonneg_int_to_nat (i : int) :=
  match Int.equal i 0 with
  | true => constr:(O)
  | false =>
      let n := nonneg_int_to_nat (Int.sub i 1) in
      constr:(S $n)
  end.

Ltac2 rec nat_to_int (n : constr) : int :=
  lazy_match! n with
  | O => 0
  | S ?n => Int.add 1 (nat_to_int n)
  end.

Variant use_constuctor_next (n : nat) A : Type := use_constr_proof  (a : A).

Lemma wrap_use_constuctor_next n A
  : use_constuctor_next n A -> A.
Proof.
  destruct 1; auto.
Qed.


Ltac2 constructor_range (x : constr) :=
  match Unsafe.kind (head x) with
  | Unsafe.Ind ind l =>
      let ind_data := Ind.data ind in
      let constr_count := Ind.nconstructors ind_data in
      (range_inclusive 1 constr_count)
  | _ => Control.backtrack_tactic_failure "not a value of inductive type"
  end.

(* TODO: pass in n or no? Does ltac2 have numgoals? *)
Ltac2 enter_counting_constructors (l : constr list) (tac : int -> unit) :=
  Control.dispatch (List.map (fun n () => tac n) (List.flat_map constructor_range l)).

Ltac2 pose_constructor_range i :=
  let n := nonneg_int_to_nat i in
  apply (@wrap_use_constuctor_next $n).


Ltac2 mutual_numbered_induction (lem : constr) (types : constr list) tac :=
  apply $lem;
  enter_counting_constructors types tac.

Ltac2 use_constructor () :=
  lazy_match! goal with
    [ |- use_constuctor_next ?n _ ] =>
      let i := nat_to_int n in
      apply use_constr_proof;
      constructor i
  end.

Hint Extern 0 (use_constuctor_next _ _) => ltac2:(use_constructor ()) : utils.


Variant ConstructorIndex (n : nat) := ConstructorIndexPf.

Ltac2 apply_indexed_constructor () :=
  lazy_match! goal with
  | [_ : ConstructorIndex ?n |- _] =>
      let i := nat_to_int n in
      econstructor i
  end.
