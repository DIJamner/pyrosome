Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import CompilerDefs Core Elab SimpleVSubst SimpleVSTLC Matches SimpleVSum SimpleVProd.
Import Core.Notations.

Require Coq.derive.Derive.


Definition subst_eval_ctx_def : lang :=
  {[l
  [s| "G" : #"env", "A" : #"ty", "B" : #"ty"
      -----------------------------------------------
      #"Ectx" "G" "A" "B" srt
  ];
  [:| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"[ ]" : #"Ectx" "G" "A" "A"
  ];       
  [:| "G" : #"env", "A" : #"ty", "B" : #"ty",
      "E" : #"Ectx" "G" "A" "B",
      "e" : #"exp" "G" "A"
      -----------------------------------------------
      #"plug" "E" "e" : #"exp" "G" "B"
  ];
  [:= "G" : #"env", "A" : #"ty",
      "e" : #"exp" "G" "A"
      ----------------------------------------------- ("plug hole")
      #"plug" #"[ ]" "e" = "e" : #"exp" "G" "A"
  ]]}.
       
Derive eval_ctx
       SuchThat (elab_lang_ext (exp_subst ++ value_subst) subst_eval_ctx_def eval_ctx)
       As eval_ctx_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve eval_ctx_wf : elab_pfs.


Definition Estlc_def :lang :=  
  {[l
  [:| "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "E" : #"Ectx" "G" "C" (#"->" "A" "B"),
      "e'" : #"exp" "G" "A"
      -----------------------------------------------
      #"Eapp_l" "E" "e'" : #"Ectx" "G" "C" "B"
  ];
  [:= "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "E" : #"Ectx" "G" "C" (#"->" "A" "B"),
       "e'" : #"exp" "G" "A",
       "e" : #"exp" "G" "C"
       ----------------------------------------------- ("plug app_l")
       #"plug" (#"Eapp_l" "E" "e'") "e"
       = #"app" (#"plug" "E" "e") "e'"
      : #"exp" "G" "B"
  ];
  [:| "G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "C" : #"ty",
       "v" : #"val" "G" (#"->" "A" "B"),
       "E" : #"Ectx" "G" "C" "A"
       -----------------------------------------------
       #"Eapp_r" "v" "E" : #"Ectx" "G" "C" "B"
  ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "C" : #"ty",
      "E" : #"Ectx" "G" "C" "A",
      "v" : #"val" "G" (#"->" "A" "B"),
      "e" : #"exp" "G" "C"
      ----------------------------------------------- ("plug app_r")
      #"plug" (#"Eapp_r" "v" "E") "e"
      = #"app" (#"ret" "v") (#"plug" "E" "e")
      : #"exp" "G" "B"
  ]]}.


Derive Estlc
       SuchThat (elab_lang_ext (eval_ctx ++ stlc ++ exp_subst++ value_subst) Estlc_def Estlc)
       As Estlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve Estlc_wf : elab_pfs.


Record string_subst := make_subst {
    from : string;
    to : string
}.

Record evctx_renamings := make_renamings {
                             evctx : string_subst;
                             vals : list string_subst
                           }.

Definition substitute_sort (H_ty : string) (t : sort) : sort :=
  match t with
  | scon "exp" [A; G] => scon "Ectx" [A; var H_ty; G]
  | _ => t
  end.

Definition substitute_ctx_sort (renamings : evctx_renamings) (H_ty term_name : string) (s : sort) (ctx_exp : bool) : list (string * sort) :=
  if renamings.(evctx).(from) =? term_name then
    match s with
    | scon "exp" [A; G] =>
        let Ectx_exp := (renamings.(evctx).(to), substitute_sort H_ty s) in
        let ty_exp := (H_ty, scon "ty" []) in
        match ctx_exp with
        | false => [Ectx_exp; ty_exp]
        | true => [(renamings.(evctx).(from), scon "exp" [var H_ty; G]); Ectx_exp; ty_exp]
                   end
    | _ => []
    end
  else
    let replace_val := find (fun s => eqb term_name s.(from)) renamings.(vals) in
    match replace_val with
    | Some replace_val =>
      match s with
      | scon "exp" [G; A] => [(replace_val.(to), scon "val" [G; A])]
      | _ => []
      end
    | None => [(term_name, s)]
    end.



Fixpoint substitute_eval_ctx_in_ctx (renamings : evctx_renamings) (H_ty : string) (c : ctx) (ctx_exp : bool) : ctx :=
  match c with
  | [] => []
  | (n, s) :: c' => substitute_ctx_sort renamings H_ty n s ctx_exp ++ substitute_eval_ctx_in_ctx renamings H_ty c' ctx_exp
  end.

Definition ascii_uppercase (a : ascii) : ascii :=
  if andb (leb a "z") (leb "a" a)
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

Fixpoint to_uppercase (str : string) : string :=
  match str with
  | EmptyString => EmptyString
  | String a str' => String (ascii_uppercase a) (to_uppercase str')
  end.

Definition rename_variable (renamings : evctx_renamings) (s : string) : string :=
  if eqb s renamings.(evctx).(from)
  then renamings.(evctx).(to)
  else
    match find (fun x => eqb s x.(from)) renamings.(vals) with
    | Some replace_val => replace_val.(to)
    | None => s
    end.

Definition substitute_eval_ctx_in_args (renamings : evctx_renamings) (args : list string) : list string :=
  map (rename_variable renamings) args.


Definition generate_eval_ctx_term_rule (renamings : evctx_renamings) (H_ty : string) (r : rule) : option rule :=
  match r with
  | term_rule c args t => let c' := substitute_eval_ctx_in_ctx renamings H_ty c false in 
                         let args' := substitute_eval_ctx_in_args renamings args in
                         let t' := substitute_sort H_ty t in
                         Some (term_rule c' args' t')
  | _ => None
  end.

Definition generate_plug_term_left (renamings : evctx_renamings) (term_name : string) (args : list string) : term :=
  con "plug" [var renamings.(evctx).(from); con term_name (map var (substitute_eval_ctx_in_args renamings args))]
.

Definition plug_arg_to_term (renamings : evctx_renamings) (arg : string) : term :=
  if renamings.(evctx).(from) =? arg then
    con "plug" [var renamings.(evctx).(from); var renamings.(evctx).(to)]
  else
    let val := find (fun s => eqb arg s.(from)) renamings.(vals) in
    match val with
    | Some val => con "ret" [var val.(to)]
    | None => var arg
    end.

Definition generate_plug_term_right (renamings : evctx_renamings) (original_name : string) (args : list string) : term :=
  con original_name (map (plug_arg_to_term renamings) args).


Definition generate_eval_ctx_plug_rule (renamings : evctx_renamings) (original_name term_name H_ty : string) (r : rule) : option rule :=
  match r with
  | term_rule c args t =>
      let c' := substitute_eval_ctx_in_ctx renamings H_ty c true in
      let sl := generate_plug_term_left renamings term_name args in
      let sr := generate_plug_term_right renamings original_name args in
      Some (term_eq_rule c' sl sr t)
  | _ => None
  end.

Definition simple_generate_eval_ctx_lang'  (renamings : evctx_renamings) (term_name n : string) (r : rule) : lang :=
  let context := match r with
                 | term_rule c _ _ => c
                 | _ => []
                 end in
  let H_ty := choose_fresh "C" context in
  let term_rule := generate_eval_ctx_term_rule renamings H_ty r in
  let plug_rule := generate_eval_ctx_plug_rule renamings n term_name H_ty r in
  match term_rule, plug_rule with
  | Some tr, Some pr  => [(append "plug " term_name, pr); (term_name, tr)]
  | _, _ => []
  end.

Definition empty_renaming := make_renamings (make_subst "" "") [].

Fixpoint get_renamings (hint : list string) (original : list string) : evctx_renamings :=
  match hint with
  | [] => empty_renaming (* One case here is that original is nonempty, should error be raised? *)
  | new :: hint' =>
      match original with
      | [] => empty_renaming (* This means something went wrong, perhaps an error should be raised *)
      | old :: original' =>
          if eqb new old
          then get_renamings hint' original'
          else
            let (ctx, vals) := get_renamings hint' original' in
            let first_letter := substring 0 1 new in
            if eqb first_letter "v"
            then make_renamings ctx (make_subst old new :: vals)
            else if eqb first_letter (to_uppercase first_letter)
                 then make_renamings (make_subst old new) vals
                 else make_renamings ctx vals
      end
  end.

Definition simple_generate_eval_ctx_lang (hint : list string) (term_name : string) (rule : string * rule) :=
  match rule with
  | (n, term_rule c args t) =>
    let renamings := get_renamings hint args in
    simple_generate_eval_ctx_lang' renamings term_name n (term_rule c args t)
  | _ => []
  end.

Fixpoint eval_ctx_lang (hints : list (string * string * list string)) (l : lang) :=
  match hints with
  | (old_name, term_name, hint) :: hints' =>
      let new_rules :=
        match find (fun x => match x with (n, r) => n =? old_name end) l with
        | Some (n, r) => simple_generate_eval_ctx_lang hint term_name (n, r)
        | None => []
        end
      in
      new_rules ++ eval_ctx_lang hints' l
  | [] => []
  end.
    
Definition Eapp_l_hint := ["e'"; "E"].
Definition Eapp_r_hint := ["E"; "v"].

Definition Estlc_hints := [("app", "Eapp_l", Eapp_l_hint);
    ("app", "Eapp_r", Eapp_r_hint)].

Definition auto_Estlc_def :=
  eval_ctx_lang Estlc_hints stlc_def.

Derive Estlc'
       SuchThat (elab_lang_ext (eval_ctx ++ stlc ++ exp_subst++ value_subst) auto_Estlc_def Estlc')
       As Estlc_wf'.
Proof. auto_elab. Qed.
#[export] Hint Resolve Estlc_wf : elab_pfs.


(* Sum Language *)
Definition Esum_def := eval_ctx_lang [("case", "Ecase", ["case_r"; "case_l"; "E"])] sum_def.

Derive Esum
       SuchThat (elab_lang_ext (eval_ctx ++ sum ++ exp_subst ++ value_subst) Esum_def Esum)
       As Esum_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve Esum_wf : elab_pfs.

(* Prod Language *)
Definition Eprod_def := eval_ctx_lang [("pair", "Epair_l", ["e2"; "E1"])
                       ; ("pair", "Epair_r", ["E2"; "v1"])
                       ; (".1", "E.1", ["E"])
                       ; (".2", "E.2", ["E"])] prod_def.

Derive Eprod
       SuchThat (elab_lang_ext (eval_ctx ++ prod ++ exp_subst ++ value_subst) Eprod_def Eprod)
       As Eprod_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve Eprod_wf : elab_pfs.

Locate term.




Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | 1 => {{e #"wkn"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Definition bind_k n e A k :=
  {{e #"blk_subst" (#"snoc" {wkn_n n} (#"cont" {A} {k})) {e} }}.
Arguments bind_k n e A k/.

Definition ovar n :=
    {{e #"val_subst" {wkn_n n} #"hd" }}.  

Definition original_app_rule_term : term := 
  (bind_k 1 (var "e") {{e #"neg" (#"prod" "A" (#"neg" "B"))}}
    (bind_k 2 (var "e'") (var "A")
    {{e #"jmp" {ovar 1} (#"pair" {ovar 0} {ovar 2}) }})).

Definition original_app_rule : compiler_case string :=
  term_case ["e'"; "e"; "B"; "A"; "G"] original_app_rule_term.

Definition app_compiler : compiler string :=
  [("app", original_app_rule)].

Compute original_app_rule.


Check bind_k.

Inductive bind_term : Type :=
| bvar : string -> bind_term
| bcon : string -> list bind_term -> bind_term
| bbind_k : nat -> bind_term -> bind_term -> bind_term -> bind_term
.

Fixpoint match_wkn_n (t : term) : option nat :=
  match t with
  | con "id" [] => Some 0
  | con "wkn" [] => Some 1
  | con "cmp" [t'; con "wkn" []] =>
      match match_wkn_n t' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.


Fixpoint term_to_bind_term (t : term) : bind_term :=
  match t with
  | var v => bvar v
  | con "blk_subst" l => 
      let default := bcon "blk_subst" (map (fun x => term_to_bind_term x) l) in
      match l with
      | [e; s] =>
        match s with
        | con "snoc" [con "cont" [k; A]; w] =>
            match match_wkn_n w with
            | None => default
            | Some n =>
                let e := term_to_bind_term e in
                let A := term_to_bind_term A in
                let k := term_to_bind_term k in
                bbind_k n e A k
            end
        | _ => default
        end
      | _ => default
      end
  | con n l => bcon n (map (fun x => term_to_bind_term x) l)
  end.



Compute term_to_bind_term original_app_rule_term.

Fixpoint bind_term_to_term (t : bind_term) : term :=
  match t with
  | bvar v => var v
  | bcon n l => con n (map (fun x => bind_term_to_term x) l)
  | bbind_k n e A k =>
      let e := bind_term_to_term e in
      let A := bind_term_to_term A in
      let k := bind_term_to_term k in
      {{e #"blk_subst" (#"snoc" {wkn_n n} (#"cont" {A} {k})) {e} }}
  end.

Compute bind_term_to_term (term_to_bind_term original_app_rule_term).
Compute original_app_rule_term.

Fixpoint substitute_ctx_bind_term (renamings : evctx_renamings) (e : bind_term) :=
  match e with
  | bvar n => bvar (rename_variable renamings n)
  | bcon l args => bcon l (map (substitute_ctx_bind_term renamings) args)
  | bbind_k n e' A k =>
      let A' := substitute_ctx_bind_term renamings A in
      let k' := substitute_ctx_bind_term renamings k in
      let e'' := match e' with
                | bvar v => 
                    match find (fun x => eqb v x.(from)) renamings.(vals) with
                    | Some replace_val =>
                        let v := replace_val.(to) in
                        term_to_bind_term {{e #"jmp" #"hd" (#"val_subst" #"wkn" v)}}
                    | None => substitute_ctx_bind_term renamings e'
                    end
                 | _ => substitute_ctx_bind_term renamings e'
                 end
      in
      bbind_k n e'' A' k'
  end.


Definition substitute_ctx_term (renamings : evctx_renamings) (e : term) :=
  bind_term_to_term (substitute_ctx_bind_term renamings (term_to_bind_term e)).


Definition simple_generate_eval_ctx_compiler_case'  (renamings : evctx_renamings) (case : compiler_case string) : option (compiler_case string) :=
  match case with
  | sort_case _ _ => None
  | term_case args e => let args' := substitute_eval_ctx_in_args renamings args in
                       let e' := substitute_ctx_term renamings e in
                       Some (term_case args' e')
  end.

Definition simple_generate_eval_ctx_compiler_case (hint : list string) (case : compiler_case string) (lang_rule : rule) : option (compiler_case string) :=
  match lang_rule with
  | term_rule n args _ => let renamings := get_renamings hint args in
                         simple_generate_eval_ctx_compiler_case' renamings case
  | _ => None
  end.

Definition to_named_list {A : Type} (n : string) (x : option A) : named_list A :=
  match x with
  | Some x' => [(n, x')]
  | None => []
  end.


Fixpoint eval_ctx_compiler (hints : list (string * string * list string)) (c : compiler string) (l : lang) : compiler string :=
  match hints with
  | (old_name, term_name, hint) :: hints' =>
      let new_rules :=
        match find (fun x => match x with (n, r) => n =? old_name end) l with
        | Some (rn, r) =>
            match find (fun x => match x with (n, r) => n =? old_name end) c with
            | Some (cn, cr) => to_named_list term_name (simple_generate_eval_ctx_compiler_case hint cr r)
            | None => []
            end
        | None => []
        end
      in
      new_rules ++ eval_ctx_compiler hints' c l
  | [] => []
  end.

Compute eval_ctx_compiler Estlc_hints app_compiler stlc_def.
