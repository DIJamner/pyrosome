(* A library for using hint databases to store collections of arbitrary Gallina values.
   Note that currently, each such database should stick to a single type of value.
 *)
From Stdlib Require Import Lists.List.
Import ListNotations.

From Ltac2 Require Import Ltac2 Ident Control List Bool Constr.
Set Default Proof Mode "Classic".

(* TODO: generalize tactics to allow DBs w/ more than 1 type of entry?*)
Variant entry {A} (a:A) : Prop := mkEntry.
Variant eauto_goal {A} (a:A) : Prop := mkEautoGoal.
Variant dummy_hyp {A} (a:A) : Prop := mkHyp.
Variant fresh_check {A} (a:A) : Prop := mkFreshCheck.

(* Database for facts used internally.
   Should not be added to by other files.
 *)
Create HintDb gallina_hint_db_internals discriminated.

Lemma contract_hyp {A} (a:A)
  : entry a -> fresh_check a -> eauto_goal a.
Proof. constructor. Qed.
(* Global so that the internal process always works *)
#[global] Hint Resolve contract_hyp : gallina_hint_db_internals.

Lemma to_eauto_goal {A} (a:A)
  : eauto_goal a -> dummy_hyp a.
Proof. constructor. Qed.

Ltac do_fresh_check a :=
  lazymatch goal with
  | H : dummy_hyp a |- _ => fail
  | _ => constructor
  end.
(* Global so that the internal process always works *)
#[global] Hint Extern 0 (fresh_check ?a) => do_fresh_check a : gallina_hint_db_internals.

Ltac2 Type exn ::= [ Db_not_found(string) ].

Ltac2 get_db s := 
  match Ident.of_string s with
  | Some name => name
  | None => throw (Db_not_found s)
  end.

Ltac2 enumerate_db db : unit :=
  let db_list := [get_db "nocore"; get_db "gallina_hint_db_internals"; db] in
  let body () : unit :=
    let x := open_constr:(_) in
       assert (dummy_hyp $x) >
       [ apply to_eauto_goal; now Std.eauto Std.Off None [] (Some db_list)
       | if is_evar x then fail else ()]
  in
  repeat0 body.

Ltac2 list_db_values () :=
  flat_map (fun p =>
              let (_,_,x) := p in
              lazy_match! x with
              | dummy_hyp ?a => [a]
              | _ => []
              end)
     (hyps()).

(* TODO: move to somewhere more generic*)
Ltac2 rec list_to_syntax l :=
  match l with
  | [] => '[] (*Note:could cause type inference problems in some cases*)
  | a::l =>
      let l' := list_to_syntax l in
      '($a::$l')
  end.

(*TODO: there should be a more direct way to do this.
  TODO: move to a more general file.
  Creates a new dummy goal to operate in without affecting the proof term.
  The new goal is the first one.
 *)
Ltac2 dummy_goal p :=
  unshelve (fun _ => let _ := open_constr:(_ : $p) in ()).

(*TODO: accomodate an arbitrary number of focused goals, not just 1*)
Ltac2 hint_db_list s :=
  dummy_goal constr:(True) >
    [clear; enumerate_db (get_db s) |];
  let x := (focus 1 1 (fun () => list_to_syntax (list_db_values ()))) in
  dispatch [(fun _ => exact I); (fun _ => ())];
  x.

(*
It doesn't seem like it's possible to pass strings from Ltac to Ltac2,
so we can't implement this:
Ltac hint_db_list s :=
  ltac2val:(Ltac1.of_constr (hint_db_list s)).
 *)

Ltac2 define_hint_db s :=
  let x := hint_db_list s in
  let y := eval vm_compute in $x in
  exact $y.

Module Tests.
  Create HintDb test discriminated.
  #[local] Definition tag0 := mkEntry 0.
  Hint Resolve tag0 : test.
  #[local] Definition tag1 := mkEntry 1.
  Hint Resolve tag1 : test.
  #[local] Definition tag2 := mkEntry 2.
  Hint Resolve tag2 : test.
  #[local] Definition tag3 := mkEntry 3.
  Hint Resolve tag3 : test.
  #[local] Definition tag4 := mkEntry 4.
  Hint Resolve tag4 : test.
  #[local] Definition tag5 := mkEntry 5.
  Hint Resolve tag5 : test.
  #[local] Definition tag52 := mkEntry 5.
  Hint Resolve tag52 : test.

  #[local] Definition my_db : list nat.
    ltac2:(define_hint_db "test").
  Defined.

  Goal incl my_db [5; 4; 3; 2; 1; 0].
    compute; intuition auto; [].
  Abort.

  Goal incl [5; 4; 3; 2; 1; 0] my_db.
    compute; intuition auto; [].
  Abort.
  
End Tests.

