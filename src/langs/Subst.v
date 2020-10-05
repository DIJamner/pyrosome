
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core EasyWF.
Require Import String.

Local Notation ob := (con 0 [::]).
Local Notation hom a b := (con 1 [:: b; a]%exp_scope).
Local Notation id a := (con 2 [:: a]%exp_scope).
Local Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).

(* syntax of categories *)
Definition cat_stx : lang :=
  [::
     term_rule [:: hom 1 2; hom 0 1; ob; ob; ob]
               (hom 0 2);
     term_rule [:: ob] (hom 0 0);
     sort_rule [:: ob; ob];
     sort_rule [::]
  ].


(* TODO: put hints in right place *)

Hint Resolve type_wf_lang_recognizes : judgment.
Hint Resolve type_wf_rule_recognizes : judgment.
Hint Resolve type_wf_ctx_recognizes : judgment.
Hint Resolve type_wf_sort_recognizes : judgment.
Hint Resolve type_wf_term_recognizes : judgment.
Hint Resolve type_wf_subst_recognizes : judgment.


Definition cat_lang : lang :=
  (* compose associativity *)
  (term_le [:: hom 2 3; hom 1 2; hom 0 1; ob; ob; ob; ob]
           (cmp 0 1 3 (cmp 1 2 3 6 5) 4)
           (cmp 0 2 3 6 (cmp 0 1 2 5 4))
           (hom 0 3))::
  (* left identity *)
  (term_le [:: (hom 0 1); ob; ob]
               (cmp 0 1 1 (id 1) 2)
               2
               (hom 0 1))::
  (* right identity *)
  (term_le [:: (hom 0 1); ob; ob]
               (cmp 0 0 1 2 (id 0))
               2
               (hom 0 1))::cat_stx.


Lemma cat_lang_wf : wf_lang cat_lang.
Proof using .
  auto with judgment.
  (*recognize_lang.*)
Qed.
(*TODO: symmetry for rules;currently only go one direction *)


Lemma wf_ob c : wf_ctx cat_lang c -> wf_sort cat_lang c ob.
Proof using .
  auto with judgment.
Qed.

Local Notation ty a := (con 7 [:: a]%exp_scope).
Local Notation ty_subst a b s t := (con 8 [:: t; s; b; a]%exp_scope).
Local Notation el a t := (con 9 [:: t; a]%exp_scope).
Local Notation el_subst a b s t m := (con 10 [:: m; t; s; b; a]%exp_scope).

Local Notation emp := (con 15 [::]%exp_scope).
Local Notation forget a := (con 16 [:: a]%exp_scope).

Local Notation ext g a := (con 19 [:: a; g]%exp_scope) (*[:: ty 0; ob]*).
Local Notation snoc a b t g n := (con 20 [:: n; g; t; b; a]%exp_scope)
(*[:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]*).
Local Notation p a t := (con 21 [:: t; a]%exp_scope).
Local Notation q a t := (con 22 [:: t; a]%exp_scope).

(* convenience def to avoid repetition *)
Definition el_srt_subst a b g e :=
  (el a (ty_subst a b g e)).

Definition subst_lang : lang :=
  (term_le [:: el_srt_subst 0 1 2 3; ty 1; hom 0 1; ob; ob]
           (el_subst 0 (ext 1 3) (snoc 0 1 3 2 4)
                     (ty_subst (ext 1 3) 1 (p 1 3) 3) (q 1 3))
           4
           (el_srt_subst 0 1 2 3))::
  (term_le [:: el_srt_subst 0 1 2 3; ty 1; hom 0 1; ob; ob]
           (cmp 0 (ext 1 3) 1
                (p 1 3)
                (snoc 0 1 3 2 4))
           2
           (hom 0 1))::
  (term_rule [:: ty 0; ob]
             (el_srt_subst (ext 0 1) 0 (p 0 1) 1))::
  (term_rule [:: ty 0; ob] (hom (ext 0 1) 0))::
  (term_rule [:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]
             (hom 0 (ext 1 2)))::
  (term_rule [:: ty 0; ob] ob)::
  (term_le [::] (id emp) (forget emp) (hom emp emp))::
  (term_le [:: hom 0 1; ob; ob] (cmp 0 1 emp (forget 1) 2) (forget 0) (hom 0 emp))::
  (term_rule [:: ob] (hom 0 emp))::
  (term_rule [::] ob)::
  (* el_subst compose to sequence *)
  (term_le [:: ty 2; hom 1 2; hom 0 1; ob; ob; ob]
           (ty_subst 0 2 (cmp 0 1 2 4 3) 5)
           (ty_subst 0 1 3 (ty_subst 1 2 4 5))
           (ty 0))::
  (* id el_subst; may be the first rule that holds, but isn't recognized. *)
  (term_le [:: el 0 1; ty 0; ob] (el_subst 0 0 (id 0) 1 2) 2 (el 0 1))::
  (* ty_subst compose to sequence *)
  (term_le [:: ty 2; hom 1 2; hom 0 1; ob; ob; ob]
           (ty_subst 0 2 (cmp 0 1 2 4 3) 5)
           (ty_subst 0 1 3 (ty_subst 1 2 4 5))
           (ty 0))::
  (* id ty_subst *)
  (term_le [:: ty 0; ob] (ty_subst 0 0 (id 0) 1) 1 (ty 0))::
  (term_rule [:: el 1 3; ty 1; hom 0 1; ob; ob] (el 0 (ty_subst 0 1 2 3)))::
  (sort_rule [:: ty 0; ob])::
  (term_rule [:: ty 1; hom 0 1; ob; ob] (ty 0))::
  (sort_rule [:: ob])::cat_lang.

Require Import Setoid.

(* Tactics for easy rule application: todo;
   move to separate file
 *)

From Ltac2 Require Import Ltac2.
(* TODO: generalize over key, value types? *)
Ltac2 Type rec FinMap :=
  [ MapEmpty
  | MapCons (int, constr, FinMap)].

Ltac2 Type exn ::= [EmptyMapLookupExn].
Ltac2 rec map_lookup n m :=
  match m with
  | MapEmpty => Control.zero EmptyMapLookupExn
  | MapCons n' v m' =>
    match Int.equal n' n with
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
Ltac2 rec int_of_nat c :=
  match! c with
  | 0 => 0
  | S ?c' => Int.add 1 (int_of_nat c')
  | _ => Control.throw (dom_exn c constr:(nat)) 
  end.

Ltac2 Type exn ::= [ExpMatchExn(constr, constr)].
Ltac2 rec exp_match (p : constr) e :=
  match! p with
  | var ?x => MapCons (int_of_nat x) e MapEmpty
  | con ?pn ?ps =>
    match! e with
    | con ?n ?s =>
      match Constr.equal pn n with
      | true => subst_match ps s
      | false => Control.throw (ExpMatchExn p e)
      end
    | var _ => Control.throw (ExpMatchExn p e)
    | _ => Control.throw (dom_exn e constr:(exp))
      (* TODO: need to handle evars*)
    end
  | _ => Control.throw (dom_exn p constr:(exp))
  end
with subst_match p s :=
    match! p with
    | [::] => match! s with [::] => MapEmpty end
    | ?pe::?p' =>
      match! s with
      | ?e::?s' =>
        map_merge (exp_match pe e) (subst_match p' s')
      | [::] => Control.throw (ExpMatchExn p s)
      end
    end.

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

(* taken from https://github.com/coq/coq/issues/11641 *)
Ltac2 my_change2 (a : constr) (b : constr) :=
  ltac1:( a b |- change a with b ) (Ltac1.of_constr a) (Ltac1.of_constr b).

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



Set Default Proof Mode "Classic".
Lemma subst_lang_wf : wf_lang subst_lang.
Proof using .
  wf_lang_eauto.
  
  2:{ (* element identity substitution *)
    constructor;auto with judgment.
    
    (*TODO: should be handledby this rewriting:
      match goal with
      |- wf_term ?l ?c _ _ => 
      setoid_replace (el 0 1) with (el 0 (ty_subst 0 0 (id 0) 1))
                             using relation (le_sort l c) at 2
    end.
     *)
    apply:wf_term_conv; first by auto with judgment.
    instantiate (1:= el 0 (ty_subst 0 0 (id 0) 1)).
    auto with judgment.

    eapply sort_con_mor.
    eapply subst_cons_mor.
    eapply subst_cons_mor; try reflexivity.
    eauto with judgment.
    change ( [:: el 0 1; ty 0; ob] ) with ( [:: el 0 1]++[:: ty 0; ob] ).
    eapply le_mono_ctx.
    eapply le_term_by.
    instantiate (1:= ty 0).
    by compute.
  }
  {
    constructor; auto with judgment.
    apply: wf_term_conv; first by auto with judgment.
    instantiate (1 := (el 0 (ty_subst 0 (ext 1 3) (snoc 0 1 3 2 4) (ty_subst (ext 1 3) 1 (p 1 3) 3)))).
    apply:type_wf_term_recognizes; eauto with judgment.
    unfold el_srt_subst.
    eapply sort_con_mor.
    repeat eapply subst_cons_mor.
    auto with judgment.
    auto with judgment.
    
    eapply le_term_trans.
    instantiate (2 := ty 0); cbv.
    - symmetry (* TODO: handle in tactic *).
      instantiate (1 := ty_subst 0 1
                           (cmp 0 (ext 1 3) 1
                                (p 1 3) (snoc 0 1 3 2 4))
                           3)
      (*TODO: handle in tactic*).
      ltac2:(apply_term_rule constr:(14)).
      eauto with judgment.
    -
      (* TODO: should be handled by tactic *)
      change (ty 0)[/[:: var 0]/]
        with (ty 0)[/[:: var 3; var 2; var 1; var 0]/].
      eapply term_con_mor.
      repeat eapply subst_cons_mor;
        auto with judgment.
      instantiate (1:= hom 0 1).
      cbv.
      ltac2:(apply_term_rule constr:(23)).
      eauto with judgment.
      Unshelve.
      all: try exact (con 0 [::]).
      all: exact [::].
  }
Qed.
