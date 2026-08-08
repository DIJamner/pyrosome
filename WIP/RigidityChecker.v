(* Pattern-rigidity checker (option B) + coverage measurement over poly_full.

   A ctx var x of a term_eq_rule (c, e1, e2, t) is RIGID-SKIPPABLE when the
   sort_of atom for x can be dropped from the compiled query with soundness
   discharged by REFLEXIVITY rather than any language-level condition:

   (i)  every internal con node of the LHS pattern e1 "fits rigidly": the
        node's rule-output sort instantiated by its own args syntactically
        equals the telescope-expected sort at the node's position
        (then faithful_rep's rule-output-vs-claimed transport at that node is
        between EQUAL endpoints -> refl);
   (ii) every occurrence of x in e1 has telescope-expected sort syntactically
        equal to x's declared sort in c
        (then the covering var-leaf's use-vs-declared transport is refl).

   Root sorts don't matter: the T-form faithful_rep and the con-root covering
   variant discard them (Phase 3).  Var roots are never skipped (Defs.v).

   This file only MEASURES; the soundness refactor comes after, informed by
   the coverage numbers. *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
Import Core.Notations.

Notation lang := (@lang string).
Notation term := (@term string).
Notation sort := (@sort string).
Notation ctx := (@ctx string).
Notation rule := (@rule string).

(* ---------- syntactic equality ---------- *)
Fixpoint term_eqb (a b : term) {struct a} : bool :=
  match a, b with
  | var x, var y => String.eqb x y
  | con n s, con m u =>
      String.eqb n m
      && (fix leqb (s u : list term) : bool :=
            match s, u with
            | [], [] => true
            | e1 :: s', e2 :: u' => term_eqb e1 e2 && leqb s' u'
            | _, _ => false
            end) s u
  | _, _ => false
  end.

Definition args_eqb (s u : list term) : bool :=
  (fix leqb (s u : list term) : bool :=
     match s, u with
     | [], [] => true
     | e1 :: s', e2 :: u' => term_eqb e1 e2 && leqb s' u'
     | _, _ => false
     end) s u.

Definition sort_eqb (a b : sort) : bool :=
  match a, b with
  | scon n s, scon m u => String.eqb n m && args_eqb s u
  end.

Section WithLang.
  Context (l : lang).

  (* Walk an argument list against its telescope (mirrors wf_args_cons:
     head arg's expected sort = its telescope sort substituted by the TAIL
     pairing).  Returns (all internal con nodes fit rigidly,
                         var-occurrence expectations (x, expected sort)). *)
  Fixpoint check_term (fuel : nat) (e : term) (expected : sort)
    : bool * list (string * sort) :=
    match fuel with
    | 0 => (false, [])
    | S fuel =>
        match e with
        | var x => (true, [(x, expected)])
        | con m ss =>
            match named_list_lookup_err l m with
            | Some (term_rule cM _ tM) =>
                if Nat.eqb (List.length ss) (List.length cM)
                then
                  let fit := sort_eqb (tM [/with_names_from cM ss/]) expected in
                  let sub := check_args fuel ss cM in
                  (fit && fst sub, snd sub)
                else (false, [])
            | _ => (false, [])
            end
        end
    end
  with check_args (fuel : nat) (ss : list term) (cM : ctx)
    : bool * list (string * sort) :=
    match fuel with
    | 0 => (false, [])
    | S fuel =>
        match ss, cM with
        | [], [] => (true, [])
        | e :: ss', (_, t) :: cM' =>
            let E := t [/with_names_from cM' ss'/] in
            let r1 := check_term fuel e E in
            let r2 := check_args fuel ss' cM' in
            (fst r1 && fst r2, snd r1 ++ snd r2)
        | _, _ => (false, [])
        end
    end.

  Definition FUEL := 1000.

  (* LHS walk for a term_eq (con root; root sort discarded). *)
  Definition lhs_term_check (e1 : term) : bool * list (string * sort) :=
    match e1 with
    | con n0 s0 =>
        match named_list_lookup_err l n0 with
        | Some (term_rule cR _ _) =>
            if Nat.eqb (List.length s0) (List.length cR)
            then check_args FUEL s0 cR
            else (false, [])
        | _ => (false, [])
        end
    | var _ => (false, [])
    end.

  (* LHS walk for a sort_eq (scon root). *)
  Definition lhs_sort_check (t1 : sort) : bool * list (string * sort) :=
    match t1 with
    | scon n0 s0 =>
        match named_list_lookup_err l n0 with
        | Some (sort_rule cR _) =>
            if Nat.eqb (List.length s0) (List.length cR)
            then check_args FUEL s0 cR
            else (false, [])
        | _ => (false, [])
        end
    end.

  (* x is rigid-skippable given the walk result. *)
  Definition var_rigid (c : ctx) (occs : list (string * sort)) (x : string)
    : bool :=
    match named_list_lookup_err c x with
    | Some tx =>
        forallb (fun oe => negb (String.eqb (fst oe) x) || sort_eqb (snd oe) tx)
                occs
    | None => false
    end.

  (* Per-rule report: (rule name, nodes_ok, [(candidate var, rigid?)]).
     Candidates mirror Defs.v's skip predicate. *)
  Definition rule_report (p : string * rule)
    : option (string * bool * list (string * bool)) :=
    match snd p with
    | term_eq_rule c e1 _ _ =>
        match e1 with
        | var _ => None   (* var roots never skipped *)
        | con _ _ =>
            let '(ok, occs) := lhs_term_check e1 in
            let cands := List.nodup string_dec (fv e1) in
            let cands := List.filter (fun x => inb x (map fst c)) cands in
            Some (fst p, ok, map (fun x => (x, ok && var_rigid c occs x)) cands)
        end
    | sort_eq_rule c t1 _ =>
        let '(ok, occs) := lhs_sort_check t1 in
        let cands := List.nodup string_dec (fv_sort t1) in
        let cands := List.filter (fun x => inb x (map fst c)) cands in
        Some (fst p, ok, map (fun x => (x, ok && var_rigid c occs x)) cands)
    | _ => None
    end.

  Definition reports : list (string * bool * list (string * bool)) :=
    flat_map (fun p => match rule_report p with
                       | Some r => [r] | None => [] end) l.

  (* Aggregates. *)
  Definition n_eq_rules := List.length reports.
  Definition n_rules_nodes_ok :=
    List.length (List.filter (fun r => snd (fst r)) reports).
  Definition n_candidates :=
    fold_left Nat.add (map (fun r => List.length (snd r)) reports) 0.
  Definition n_rigid :=
    fold_left Nat.add
      (map (fun r => List.length (List.filter snd (snd r))) reports) 0.
  Definition n_rules_all_rigid :=
    List.length (List.filter (fun r => forallb snd (snd r)) reports).
  (* Failures, for inspection: (rule, nodes_ok, non-rigid candidate vars). *)
  Definition failures :=
    flat_map (fun r =>
        let bad := List.filter (fun xb => negb (snd xb)) (snd r) in
        match bad with
        | [] => []
        | _ => [(fst (fst r), snd (fst r), map fst bad)]
        end) reports.
End WithLang.

