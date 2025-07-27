Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils EGraph.Defs Monad.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Lang.SimpleVSTLC Tools.EGraph.Defs
  Tools.EGraph.Automation Tools.EGraph.Test.
Import PArith.
Import Ascii.AsciiSyntax.
Import StringInstantiation.
Import StateMonad.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Init.Nat.

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (Nat.to_uint n).

Local Open Scope string_scope.



(* ------BUILDING_TERMS_WITH_HOLES---------*)
Fixpoint Zip_two_lists (X: Type) (Y: Type) (l1: list X) (l2: list Y) : list (X * Y) :=
  match l1 with
  | nil => nil
  | cons head1 tail1 =>
    match l2 with
    | nil => nil
    | cons head2 tail2 => cons (head1, head2) (Zip_two_lists tail1 tail2)
    end
  end.

Fixpoint Find_x (Y: Type) (key: string) (l: list (string * Y)) : option Y :=
  match l with
  | nil => None
  | cons (head_x, head_y) tail => if (String.eqb key head_x) then (Some head_y) else (Find_x key tail)
  end.

Local Open Scope string_scope.

Fixpoint insert_terms_into_context
      (list_of_subterms: list term) (explicit_args: list string) (context: ctx) (prefix: string) : list term :=
  match context with
  | nil => nil
  | cons (head_name, head_sort) rest_context =>
    match (Find_x head_name (Zip_two_lists explicit_args list_of_subterms)) with
    | None => (cons (con ("?" ++ prefix ++ head_name) []) (insert_terms_into_context list_of_subterms explicit_args rest_context prefix))
    | Some t => (cons t (insert_terms_into_context list_of_subterms explicit_args rest_context prefix))
    end
  end.

Fixpoint map_indexed (X: Type) (Y: Type) (f : nat -> X -> Y) (L: list X) (start: nat)  : list Y :=
  (* Takes a list X and for each element v at index i replaces it with f (start + i) x and returns a list of such elements of type list Y*)
  match L with
  | nil => nil
  | cons head tail => cons (f start head) (map_indexed f tail (start + 1) )
  end.

Fixpoint build_term_with_holes_given_prefix (L: lang) (prefix: string) (index: nat) (t: term): term :=
  match t with
  | var _ => t
  | con name_of_rule list_of_subterms =>
      match NamedList.named_list_lookup
        (term_rule [] [] (scon "ty" []))
        L name_of_rule with
          | term_rule context explicit_args some_sort_idk =>
              con name_of_rule
                (insert_terms_into_context
                  ((map_indexed (build_term_with_holes_given_prefix L (prefix ++ (nat_to_string index) ++ "_"))) list_of_subterms 0)
                  explicit_args
                  context
                  (prefix ++ (nat_to_string index) ++ "_"))
          (* The case below never runs *)
          | _ => t
      end
  end.

Definition build_term_with_holes (L: lang) (t: term) :=
  build_term_with_holes_given_prefix L "" 0 t.

Local Open Scope string_scope.

Fixpoint get_dummy_names (t: term) : list string :=
  match t with
  | var _ => []
  | con (String "?" rest) subterms => cons (String "?" rest) (fold_right (@app string) [] (map get_dummy_names subterms))
  | con _ subterms => (fold_right (@app string) [] (map get_dummy_names subterms))
  end.
Fixpoint get_dummy_rules (dummy_names: list string) : lang :=
  match dummy_names with
  | nil => nil
  | cons head rest => cons  (head ++ "_sort", sort_rule [] []) ( cons (head, term_rule [] [] (scon (head ++ "_sort") []))  (get_dummy_rules rest))
  end.

Definition get_dummy_context (dummy_names: list string): ctx :=
  map (fun name => (name, scon "ty" [])) dummy_names.
(* ----------------------------------------*)


Local Open Scope char_scope.
Definition weight (a: atom string string) : option positive :=
match a with
| Build_atom (String "?" _) [] _ => None
| _ => Some (1 %positive)
end.


Local Open Scope string_scope.

Definition empty_egraph := (Utils.EGraph.Defs.empty_egraph (idx:=string) (default : string)
                              (symbol:=string) (symbol_map := string_trie_map)
                              (idx_map := string_trie_map) (option positive)).


Local Open Scope list_scope.

Fixpoint con_to_var (context: ctx) (t: term) : term :=
  match t with
  | con name [] =>
      if (inb name (map fst context)) then (var name) else t
  | con name subterms => con name (map (con_to_var context) subterms)
  | _ => t
  end.

Definition result_to_term (result: Result.result term) : term :=
  match result with
  | Result.Success t => t
  | _ => default
  end.
Set Printing Implicit.
About default.

Definition state_operation :=
  @saturate_until string String.eqb string_succ
(default (A:= string))
string
String.eqb string_trie_map
string_ptree_map_plus string_trie_map string_ptree_map_plus
string_list_trie_map _ (weighted_depth_analysis weight) (@PosListMap.compat_intersect)
   (
    @QueryOpt.build_rule_set string String.eqb string_succ (default (A:= string))
      string String.eqb string_trie_map string_ptree_map_plus string_trie_map
      string_ptree_map_plus string_list_trie_map inject
  )
    (Mret false) 0
    .

Definition infer (L: lang) (context: ctx) (t: term) (s: sort): term :=
  let Language_plus_rules := L ++ (ctx_to_rules context) in
  let Term_with_no_variables := (var_to_con t) in
  let term_with_holes := build_term_with_holes Language_plus_rules Term_with_no_variables in
  let new_context := context ++ get_dummy_context (get_dummy_names (term_with_holes)) in
  let dummy_rules := get_dummy_rules (get_dummy_names (term_with_holes)) in
  let '(str, inst2) := add_open_term weight (Language_plus_rules ++ dummy_rules) [] term_with_holes empty_egraph in
  let '(id_sort, inst3) := add_open_sort weight (Language_plus_rules ++ dummy_rules) [] s inst2 in
  let '(id_original_sort, inst4) := @hash_entry string String.eqb string_succ string string_trie_map string_trie_map string_list_trie_map
                                 _ (weighted_depth_analysis weight) sort_of [str] inst3 in
  let '(_, inst5) := @union string String.eqb (default (A:= string)) string string_trie_map string_trie_map string_list_trie_map
                     _ (weighted_depth_analysis weight) id_sort id_original_sort inst4 in
  let '(_, inst6) := state_operation inst5 in
  con_to_var new_context (result_to_term (extract_weighted inst3 100 str))
  .

Compute infer (stlc ++ exp_subst ++ value_subst)
            [
            ("e", scon "exp" [var "B"; con "ext" [var "A"; var "G"] ]);
            ("B", scon "ty" []);
            ("A", scon "ty" []);
            ("G", scon "env" [])
            ]

(con "lambda" [var "e"; var "A"]).

(* Eval unfold Monad.StateMonad.state in *)
(*  I don't remember what this was for? *)
(* Definition TERM_RULE :=
term_rule
           [("v", scon "val" [var "A"; var "G'"]); (
            "A", scon "ty" []); ("g", scon "sub" [var "G'"; var "G"]);
            ("G'", scon "env" []); ("G", scon "env" [])] [
           "v"; "g"] (scon "val" [var "A"; var "G"]). *)

Definition Names_for_term_rule (TERM_RULE: rule) : list string :=
  match TERM_RULE with
  | term_rule c x y =>
      map fst c
  | _ => []
  end.



Theorem check: stlc_def
	 = [
    ("STLC-beta",
         term_eq_rule
           [("v", scon "val" [var "A"; var "G"]);
            ("e", scon "exp" [var "B"; con "ext" [var "A"; var "G"]]);
            ("B", scon "ty" []); ("A", scon "ty" []); (
            "G", scon "env" [])]
           (con "app"
              [con "ret" [var "v"];
               con "ret" [con "lambda" [var "e"; var "A"]]])
           (con "exp_subst" [var "e"; con "snoc" [var "v"; con "id" []]])
           (scon "exp" [var "B"; var "G"]));

    ("exp_subst app",
         term_eq_rule
           [("g", scon "sub" [var "G"; var "G'"]); (
            "G'", scon "env" []); ("e'", scon "exp" [var "A"; var "G"]);
            ("e", scon "exp" [con "->" [var "B"; var "A"]; var "G"]);
            ("B", scon "ty" []); ("A", scon "ty" []); (
            "G", scon "env" [])]
           (con "exp_subst" [con "app" [var "e'"; var "e"]; var "g"])
           (con "app"
              [con "exp_subst" [var "e'"; var "g"];
               con "exp_subst" [var "e"; var "g"]])
           (scon "exp" [var "B"; var "G'"]));

    ("app",
         term_rule
           [("e'", scon "exp" [var "A"; var "G"]);
            ("e", scon "exp" [con "->" [var "B"; var "A"]; var "G"]);
            ("B", scon "ty" []);
            ("A", scon "ty" []);
            ("G", scon "env" [])] ["e'"; "e"] (scon "exp" [var "B"; var "G"]));

    ("val_subst lambda",
         term_eq_rule
           [("g", scon "sub" [var "G"; var "G'"]); (
            "G'", scon "env" []);
            ("e", scon "exp" [var "B"; con "ext" [var "A"; var "G"]]);
            ("B", scon "ty" []); ("A", scon "ty" []); (
            "G", scon "env" [])]
           (con "val_subst" [con "lambda" [var "e"; var "A"]; var "g"])
           (con "lambda"
              [con "exp_subst"
                 [var "e";
                  con "snoc" [con "hd" []; con "cmp" [var "g"; con "wkn" []]]];
               var "A"]) (scon "val" [con "->" [var "B"; var "A"]; var "G'"]));

    ("lambda",
         term_rule
            (* Context: *)
           [("e", scon "exp" [var "B"; con "ext" [var "A"; var "G"]]);
            ("B", scon "ty" []);
            ("A", scon "ty" []);
            ("G", scon "env" [])]

            (* Explicit arguments *)
            ["e"; "A"]

            (* Sort??? *)
           (scon "val" [con "->" [var "B"; var "A"]; var "G"]));

    ("->",
         term_rule [("t'", scon "ty" []); ("t", scon "ty" [])] [
           "t'"; "t"] (scon "ty" []))]
     .
Proof. reflexivity. Qed.


(* -----------------------Testing---------------------- *)
Compute build_term_with_holes stlc_def (con "lambda" [var "e"; var "A"]).
Compute build_term_with_holes stlc_def (con "app" [(con "lambda" [var "e"; var "A"]); var "e'"]).
Compute build_term_with_holes stlc_def (con "lambda" [var "e"; var "A"]).
(* УСПЭЭЭЭЭХ! *)
Compute build_term_with_holes stlc_def (con "lambda" [var "e"; var "A"]).
Compute build_term_with_holes stlc_def (con "lambda" [var "e"; var "A"]).
Compute build_term_with_holes stlc_def (con "lambda" [var "e"; var "A"]).
Compute build_term_with_holes stlc_def (con "lambda" [var "e"; var "A"]).
