(*********************************************
A partial recognizer for well-formed languages
**********************************************)


Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp Rule Core.

From Ltac2 Require Import Ltac2.
Require Ltac2.List Ltac2.Option Ltac2.Std.
(*TODO: copied from stdlib; need to update version?*)
Ltac2 of_goal () := Fresh.Free.of_ids (List.map (fun (id, _, _) => id) (Control.hyps ())).

Ltac2 in_goal id := Fresh.fresh (of_goal ()) id.

Ltac2 fresh s := in_goal (Option.get (Ident.of_string s)).


(* taken from https://github.com/coq/coq/issues/11641 *)
Ltac2 my_change2 (a : constr) (b : constr) :=
  ltac1:( a b |- change a with b ) (Ltac1.of_constr a) (Ltac1.of_constr b).


Ltac2 all_red_flags :=
  { Std.rBeta := true;
  Std.rMatch := true;
  Std.rFix := true;
  Std.rCofix := true;
  Std.rZeta := true;
  Std.rDelta := true;
  Std.rConst := []
}.

(*
tests whether two terms are equal,
unifying evars as necessary.
EFFECT: adds a = b as a hypothesis if true,
possibly instantiating evars in the process
 *)
Ltac2 eequal a b :=
  Control.plus
    (fun () =>
       let heq := fresh "Heq" in
       assert ($a = $b)>[solve[f_equal; eauto]|]; true)
    (fun _ => false).

Ltac2 change_cbv e :=
  my_change2 e (Std.eval_cbv all_red_flags e).

(* Attempts to clear a goal of the form
   'a \in l', unifying evars as necessary *)
Ltac2 Type exn ::= [UnifyInFailure].
Ltac2 rec unify_in () :=
  lazy_match! goal with
   | [|- is_true (?r \in ?r'::?l)] =>
      change_cbv r;
      rewrite in_cons;
      ltac1:(apply /orP);
      match eequal r r' with
      | true => left;ltac1:(by apply /eqP)
      | false => right; unify_in()
      end
   | [|- is_true (_ \in [::])] => Control.zero UnifyInFailure
   | [|- is_true (_ \in ?l)] => change_cbv l; unify_in ()
  end.

Require Import String.
  
Ltac2 try f :=
  Control.enter
    (fun () => Control.plus f (fun _ => ())).


Ltac2 goal_lang () :=
  lazy_match! goal with
  | [|- le_term ?l _ _ _ _] => l
  | [|- le_sort ?l _ _ _] => l
  | [|- wf_term ?l _ _ _] => l
  | [|- wf_sort ?l _ _] => l
  | [|- wf_rule ?l _] => l
  | [|- wf_ctx ?l _] => l
end.




Ltac2 unify_eq () :=
  match! goal with
    [|- ?a = ?b] =>
    solve[f_equal; eauto]
  end.

(* TODO: generalize over key, value types? *)
Ltac2 Type rec FinMap :=
  [ MapEmpty
  | MapCons (constr (*Coq string*), constr, FinMap)].

Ltac2 Type exn ::= [EmptyMapLookupExn].
Ltac2 rec map_lookup n m :=
  match m with
  | MapEmpty => Control.zero EmptyMapLookupExn
  | MapCons n' v m' =>
    match Constr.equal n' n with
    | true => v
    | false => map_lookup n m'
    end
  end.



(* Computes a map that has all mappings from both,
   or throws if none exists
TODO: optimize representation for this operation
 *)
Ltac2 Type exn ::= [MapMergeExn(constr, constr)].
Ltac2 rec map_merge m1 m2 :=
  match m1 with
  | MapEmpty => m2
  | MapCons k v1 m1' =>
    MapCons k v1
            (Control.plus
               (fun _ => let v2 := map_lookup k m2 in
                match Constr.equal v1 v2 with
                | true => map_merge m1' m2
                | false => Control.zero (MapMergeExn v1 v2)
                end)
               (fun ex =>
                  match ex with
                  | EmptyMapLookupExn => map_merge m1' m2
                  | _ => Control.zero ex
                  end))
  end.

Ltac2 Type exn ::= [DomainExn(constr, constr, constr)].
Ltac2 dom_exn c t := DomainExn c (Constr.type c) t.

Ltac2 Type exn ::= [ExpMatchExn(constr, constr)].
Ltac2 rec exp_match (p : constr) e :=
  lazy_match! p with
  | var ?x => MapCons x e MapEmpty
  | con ?pn ?ps =>
    (* TODO: handle when e is an existential *)
    lazy_match! e with
    | con ?n ?s =>
      match Constr.equal pn n with
      | true => exp_list_match ps s
      | false => Control.throw (ExpMatchExn p e)
      end
    | var _ => Control.throw (ExpMatchExn p e)
    | _ => Control.throw (dom_exn e constr:(exp))
      (* TODO: need to handle evars*)
    end
  | _ => Control.throw (dom_exn p constr:(exp))
  end
with exp_list_match p s :=
    lazy_match! p with
    | [::] => lazy_match! s with [::] => MapEmpty end
    | ?pe::?p' =>
      lazy_match! s with
      | ?e::?s' =>
        map_merge (exp_match pe e) (exp_list_match p' s')
      | [::] => Control.throw (ExpMatchExn p s)
      end
end.

Ltac2 sort_match p e :=
  lazy_match! p with
  | srt ?pn ?ps =>
    (* TODO: handle when e is an existential *)
    lazy_match! e with
    | srt ?n ?s =>
      match Constr.equal pn n with
      | true => exp_list_match ps s
      | false => Control.throw (ExpMatchExn p e)
      end
    | var _ => Control.throw (ExpMatchExn p e)
    | _ => Control.throw (dom_exn e constr:(exp))
      (* TODO: need to handle evars*)
    end
  | _ => Control.throw (dom_exn p constr:(exp))
  end.
  

(* Convert a map into a substition constr
   according to its output ctx constr *)
Ltac2 rec subst_of_map m c :=
  lazy_match! c with
  | [::] => constr:([::])
  | (?n,_)::?c' =>
    let v := map_lookup n m in
    let tl := subst_of_map m c' in
    constr:(($n,$v)::$tl)
  end.

Ltac2 Type exn ::= [JudgmentMismatchExn(constr, constr)].
Ltac2 apply_rule (name : constr) :=
  let l := goal_lang () in
  (* TODO: make d an evar so it isn't silently returned?*)
  let d := constr:(sort_rule [::]) in
  let r := Std.eval_cbv all_red_flags
           constr:(named_list_lookup $d $l $name) in
  lazy_match! r with
  | sort_rule ?c' =>
    lazy_match! goal with
    | [|- wf_sort ?l ?c ?t] =>
      eapply (@wf_sort_by $l $c $name) >
      [ unify_in ()|]
    | [|- ?j] =>
      Control.zero
        (JudgmentMismatchExn constr:(($name,$r)) j)
    end
  | term_rule ?c' ?t' =>
    lazy_match! goal with
    | [|- wf_term ?l ?c ?e ?t] =>
      ltac1:(l c e t t'|-
             let s := fresh "s" in
             evar (s : subst);
             replace (wf_term l c e t) with
                (wf_term l c e t'[/s/]);
            unfold s;
            clear s
            ) (Ltac1.of_constr l)
              (Ltac1.of_constr c)
              (Ltac1.of_constr e)
              (Ltac1.of_constr t)
              (Ltac1.of_constr t') >
            [ eapply (@wf_term_by $l $c $name) >
              [ unify_in () |]
            | unify_eq()]
    | [|- ?j] =>
      Control.zero
        (JudgmentMismatchExn constr:(($name,$r)) j)
    end
  | sort_le ?c' ?t1' ?t2' =>
    lazy_match! goal with
    | [|- le_sort ?l ?c ?t1 ?t2] =>
      let m := map_merge
                 (sort_match t1' t1)
                 (sort_match t2' t2) in
      let s := subst_of_map m c' in
      my_change2
        '(le_sort $l $c $t1 $t2)
        '(le_sort $l $c $t1'[/$s/] $t2'[/$s/]);
      eapply le_sort_subst;
      Control.enter
        (fun () =>
           match! goal with
           | [|- le_sort _ _ _ _] =>
             eapply le_sort_by;
             unify_in ()
           | [|- le_subst _ _ _ _ _] => ()
           | [|- _] => Control.throw Match_failure
           end)
    | [|- ?j] =>
      Control.zero
        (JudgmentMismatchExn constr:(($name,$r)) j)
    end
      
end.
(* TODO:
Check wf_sort_by.
Goal le_sort [:: [s> |-("req") #"foo" = #"bar"]] [::] (srt "foo" [::])
(srt "bar" [::]).
Proof.
  
  apply_rule constr:("req"%string).
  
  admit.
  cbv.
  unfold substable_sort.
  f_equal; eauto.
  unify_eq ().
  
TODO: deconstruct subst automatically based on c'  



Ltac2 Eval (exp_match constr:(var 1) constr:(var 2)).
Ltac2 Eval
      (exp_match constr:(con 1 [:: var 2; var 2])
                          constr:(con 1 [:: (con 2 [::]); (con 2 [::])])).


(* assumes idx <= size 
   TODO: how to handle terms that aren't listed?
   evar?
*)
Ltac2 subst_of_map m size :=
  let rec som idx acc :=
      match Int.equal idx size with
      | true => acc
      | false =>
        let v := map_lookup idx m in
        som (Int.add idx 1) constr:($v::$acc)
      end in
  som 0 constr:(@nil exp).

Ltac2 Eval (subst_of_map
              (MapCons 2 constr:(var 3)
              (MapCons 0 constr:(var 1)
              (MapCons 1 constr:(var 2) MapEmpty)))) 3.

Ltac2 max n m :=
  match Int.gt n m with
  | true => n
  | false => m
  end.

Ltac2 rec min_subst_size m :=
  match m with
  | MapEmpty => 0
  | MapCons n _ m' =>
    max (Int.add n 1) (min_subst_size m')
  end.

Require Import Ltac2.Notations.

Ltac2 rec unify_in () :=
  match! goal with
    [|- is_true (?r \in ?r'::?l)] =>
    rewrite in_cons;
    ltac1:(apply /orP);
    Control.plus
      (fun () => left;ltac1:(apply /eqP; by f_equal))
      (fun _ =>
         right; unify_in ())
end.

Ltac2 apply_term_rule n :=
  match! goal with
    [|- le_term ?l ?c ?t ?e1 ?e2 ]=>
    match! Std.eval_hnf constr:(nth_level (sort_rule [::]) $l $n) with
      term_le _ ?pe1 ?pe2 ?pt =>
      let m := subst_match constr:([:: $pt; $pe1; $pe2])
                           constr:([:: $t; $e1; $e2]) in
      let s := subst_of_map m (min_subst_size m) in
      my_change2
        constr:(le_term $l $c $t $e1 $e2)
        constr:(le_term $l $c $pt[/$s/] $pe1[/$s/] $pe2[/$s/]);
      eapply le_term_subst;
      Control.enter
        (fun () =>
           match! goal with
           | [|- le_term _ _ _ _ _] =>
             eapply le_term_by;
             unify_in ()
           | [|- le_subst _ _ _ _ _] => ()
           | [|- _] => Control.throw Match_failure
           end)
    end
end.


*)
