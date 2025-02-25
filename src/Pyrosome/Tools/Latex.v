Set Implicit Arguments.

Require Import Lists.List Datatypes.String.
Import List.ListNotations.
Open Scope string.
From Utils Require Import Utils.
(*Note: technically only needs term + rules *)
From Pyrosome Require Import Theory.Core.
Import Core.Notations.

Local Notation term := (term string).
Local Notation sort := (sort string).
Local Notation ctx := (ctx string).
Local Notation rule := (rule string).
Local Notation lang := (lang string).


Import Byte.

Definition newline := Eval compute in (string_of_list_byte [x0a]).

(* Assumes names are all alphanumeric.
   constructs where this is not the case can be renamed.
 *)

Definition call f args :=
  List.fold_left append (map (fun x => "{"++x++"}") (rev args))%string f.

Goal call "\foo" ["baz"; "bar"] = "\foo{bar}{baz}".
  reflexivity.
Abort.

Notation "\ f" := ("\" ++ f)%string (at level 8).

Definition bts (b : bool) := if b then "true" else "false".

Definition blank := "--".

Definition inferrule top bot : string :=
  "\inferrule" ++ newline ++ "{ " ++ top ++"}" ++ newline ++ "{" ++ bot ++"}".

Definition ninferrule name top bot : string :=
  "\inferrule[right=" ++ name ++ "]" ++ newline ++ "{ " ++ top ++"}" ++ newline ++ "{" ++ bot ++"}".

Definition lequal a b : string :=
  a ++ " = " ++ b. 

Record rule_datum :=
  RD {
    no_parens : string;
    parens : string;
    arg_parens : list bool;
  }.

#[export] Instance rule_datum_default : WithDefault rule_datum :=
  RD default default default.

Section WithLang.
  (*Context (l : lang).*)
  Context (lang_name : string).
  (*contains the macro body and the space separation data *)
  Context (rule_data : named_list string rule_datum).

  Definition get_seps n := (named_list_lookup default rule_data n).(arg_parens).

  Definition lvar x : string := "\pyrosomeVar{" ++ x ++"}".

  (* For now, assume false.
     All elaborated terms can be unelaborated anyway.
     Context (is_elaborated : bool).*)

  Section __.
    Context (term_to_latex : term -> bool -> string).

    Definition con_to_latex space_separated n s :=
      call \n (bts space_separated::
                (map (uncurry id)
                   (combine (map term_to_latex s)
                      (get_seps n)))).
  End __.

  Fixpoint term_to_latex (e : term) (space_separated : bool) : string :=
    match e with
    | var x => lvar x
    | con n s => con_to_latex term_to_latex space_separated n s
    end%string.

  (*TODO: express sorts as judgment forms or as types?
    For a first draft: sorts as judgments.
    Sort macros take one extra argument, the term to apply them to.
    By convention, the en dash (--) is passed as the argument when the sort
    itself is the subject.
    This function generates a latex string that expects this extra argument.

    TODO: do judgments need space_separated? My instinct says no
    TODO: should pass space_separated to last argument
    TODO: should equality have its own separate one?
   *)
  Definition sort_to_latex (t : sort) (space_separated : bool) e : string :=
    let (n,s) := t in
    call (con_to_latex term_to_latex space_separated n s) [e].

  Fixpoint ctx_to_latex (c : ctx) :=
    match c with
    | [] => ""
    | [(x,A)] => sort_to_latex A false (lvar x)
    | (x,A)::c' => ctx_to_latex c' ++ "\quad"
                     ++ sort_to_latex A false (lvar x)
    end%string.

  Definition rule_to_latex n r : string :=
    match r with
    | sort_rule c args =>
        inferrule (ctx_to_latex c)
          (sort_to_latex (scon n (map var args)) false blank
             ++ "~\textit{sort}")
    | term_rule c args t =>
        inferrule (ctx_to_latex c)
          (sort_to_latex t false
          (*TODO: sort should pass space_separated to last argument of term?*)
          (term_to_latex (con n (map var args)) false))
    | sort_eq_rule c t1 t2 =>
        ninferrule n
          (ctx_to_latex c)
          (lequal (sort_to_latex t1 true blank)
                  (sort_to_latex t2 true blank)
             ++ "~\textit{sort}")
    | term_eq_rule c e1 e2 t =>
        ninferrule n
          (ctx_to_latex c)
          (sort_to_latex t false
          (*TODO: sort should pass space_separated to last argument of term?*)
             (lequal (term_to_latex e1 false)
                     (term_to_latex e1 false)))
    end.

  (*TODO: check order
    Note: does not generate the macro definitions, since those should often be separate.
   *)
  Definition lang_to_latex : lang -> string :=
    List.fold_right (fun '(n,r) acc => acc ++ rule_to_latex n r ++ newline)%string "".

  (*only goes up to 9 because latex can't handle 10*)
  Definition nat_to_digit n :=
    match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | 9 => "9"
    | _ => "ERR: latex can't handle 10+"
    end.

  Definition rule_macro n (is_sort : bool) : string :=
    let datum := named_list_lookup default rule_data n in
    (* TODO: paren arg? *)
    (* TODO: should the arg_data for sorts already have an extra entry?*)
    let arg_count := 1 + List.length datum.(arg_parens) + if is_sort then 1 else 0 in
    "\newcommand{\"++n++"}[" ++ nat_to_digit arg_count
      ++"]{\ifthenelse{#1}{" ++ datum.(parens) ++ "}{" ++ datum.(no_parens) ++"}" ++ newline.

  Definition is_sort (r : rule) :=
    match r with
    | sort_rule _ _ => true
    | _ => false
    end.


  
  (*TODO: only works up to 9 args due to latex*)
  Definition lang_macros : lang -> string :=
    fold_right (fun '(n,r) acc =>
                  match r with
                  | sort_rule _ _ => rule_macro n false
                  | term_rule _ _ _ => rule_macro n true
                  | _ => ""
                  end ++ acc)%string "".


End WithLang.



Require Coq.derive.Derive.
Require Import Pyrosome.Theory.Renaming.
Require Import coqutil.Tactics.ident_of_string.
Require Import Ltac2.Ltac2. Import Ltac2.Message.

Module Example.



Definition grp : lang :=
  {[l   
  [s|
      -----------------------------------------------
      #"G" srt
  ];
  [:| 
       -----------------------------------------------
       #"0" : #"G"
  ];
  [:| "a" : #"G", "b" : #"G"
       -----------------------------------------------
       #"+" "a" "b" : #"G"
  ];
  [:= "a" : #"G"
      ----------------------------------------------- ("id right")
      #"+" "a" #"0" = "a" : #"G"
  ];
  [:= "a" : #"G"
      ----------------------------------------------- ("id left")
      #"+" #"0" "a" = "a" : #"G"
  ];
  [:= "a" : #"G", "b" : #"G", "c" : #"G"
      ----------------------------------------------- ("assoc")
      #"+" (#"+" "a" "b") "c" = #"+" "a" (#"+" "b" "c") : #"G"
  ]
  ]}.


Definition grp' : lang :=
  Eval compute in
    (rename_lang (fun s =>
                    match s with
                    | "G" => "grpG"
                    | "0" => "grpZ"
                    | "+" => "grpplus"
                    | s => s
                    end
       ) grp).
Definition grp_fmt :=
  [("grpG", RD "#2 \in \mathbb{G}" "\left( #2 \in \mathbb{G}\right)" []);
   ("grpZ", RD "\mathbb{0}" "\mathbb{0}" []);
   ("grpplus", RD "#2 + #3" "\left(#2 + #3\right)" [true;true])
  ].

#[local] Definition x := Eval compute in (lang_macros grp_fmt grp').
#[local] Definition y := Eval compute in (lang_to_latex grp_fmt grp').


Ltac2 print_unquoted s :=
  let s' := string_of_constr_string s in
  Message.print (Message.of_string s').

Ltac print_unquoted :=
  ltac2:(s |- print_unquoted (Option.get (Ltac1.to_constr s))).


Local Set Default Proof Mode "Classic".

(*
Goal False.
  print_unquoted x;
    print_unquoted y.
  Fail.
  Import Byte.
  Compute (string_of_list_byte [x7]).
  print_unquoted "\n".
  y.
*)

(*  Compute (lang_to_latex stlc).*)

End Example.
