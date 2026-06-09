Set Implicit Arguments.

From coqutil Require Import Datatypes.String Map.Interface.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils EGraph.Defs Monad Lens.
From Pyrosome Require Import Theory.Core Elab.Elab
  Elab.PreTerm Elab.PreRule
  Compilers.Compilers
  Tools.Matches Tools.EGraph.Defs
  Tools.EGraph.Automation
  Tools.PosRenaming.
From Utils.EGraph Require Import Semantics.
From Utils Require Import TrieMap PosListMap.
(* [Require] (not [Import]) so its positive-only notations don't shadow the
   string ones used here for building. *)
From Pyrosome.Tools.EGraph Require PosInferEngine.
Import PArith.
Import Ascii.AsciiSyntax.
Import StringInstantiation.
Import StateMonad.
From Stdlib Require Numbers.DecimalString.


Local Notation named_list := (@named_list string).
Local Notation named_map := (@named_map string).
Local Notation term := (@term string).
Local Notation ctx := (@ctx string).
Local Notation sort := (@sort string).
Local Notation subst := (@subst string).
Local Notation rule := (@rule string).
Local Notation lang := (@lang string).


Local Notation preterm := (@preterm string).
Local Notation prectx := (@prectx string).
Local Notation presort := (@presort string).
Local Notation prerule := (@prerule string).
Local Notation prelang := (@prelang string).

(* TODO: make all of this use something other than strings *)

Definition nat_to_string (n : nat) : string :=
  DecimalString.NilZero.string_of_uint (Nat.to_uint n).

Fixpoint Find_x (Y: Type) (key: string) (l: list (string * Y)) : option Y :=
  match l with
  | nil => None
  | cons (head_x, head_y) tail => if (String.eqb key head_x) then (Some head_y) else (Find_x key tail)
  end.

(* ------BUILDING_TERMS_and_SORTS_WITH_HOLES---------*)
Local Open Scope string_scope.

Fixpoint get_dummy_rules (dummy_names: list string) : lang :=
  match dummy_names with
  | nil => nil
  | cons head rest => cons  (head ++ "_sort", sort_rule [] []) ( cons (head, term_rule [] [] (scon (head ++ "_sort") []))  (get_dummy_rules rest))
  end.
Definition get_dummy_context (dummy_names: list string): ctx :=
  map (fun name => (name, scon "ty" [])) dummy_names.
(* ----------------------------------------*)



(* Newtype for clear typeclass inference*)
Record ident := { get_ident : string }.

Definition log {M L} `{StateMonad (list L) M} (new_log : list L) : M unit :=
  @!let log <- get_state in
    (set_state (new_log++log)%list).

(*TODO: Move? multiple variants exist *)
Definition gensym {M} `{StateMonad ident M} `{StateMonad (list (string * rule)) M}
  : M string :=
  @!let s <- get_state in
    let _ <- log (get_dummy_rules [s.(get_ident)]) in
    let _ <- set_state (Build_ident (string_succ s.(get_ident))) in
    ret s.(get_ident).


Section Inner.
  Context (pre_var_to_con : preterm -> preterm).
  Definition pre_var_to_con_arg (a : string* preterm + preterm) :=
    match a with
    | inr e => inr (pre_var_to_con e)
    | inl (x,e) => inl (x, pre_var_to_con e)
    end.
End Inner.

Fixpoint pre_var_to_con (t : preterm) :=
  match t with
  | pre_var x => pre_con x []
  | pre_con n s => pre_con n (map (pre_var_to_con_arg pre_var_to_con) s)
  end.

Definition presort_var_to_con (t : presort) :=
  match t with
  | pre_scon n s => pre_scon n (map (pre_var_to_con_arg pre_var_to_con) s)
  end.

(*
Definition gen_dummy_rules {M} `{StateMonad (list ident) M}
  : M _ :=
  @!let s <- get_state in
    ret (get_dummy_rules (map get_ident s)). *)

(*Parameterized by M for later convenience*)
Section __.
  Context {M} `{StateMonad ident M}
  `{StateMonad (list (string * rule)) M}.

  Section Inner.
    Context (build_term_with_holes : preterm -> M term).
    
    (* Separated out for the termination checker*)
    Fixpoint insert_trailing_holes (c_names : list string)
      : M (list term) :=
      match c_names with
      | [] => Mret []
      | x::c_names' =>
          @! let s' <- insert_trailing_holes c_names' in
            let  x_sym <- gensym in
            ret (con x_sym [] :: s')
      end.

    Section Inner2.
      Context (insert_arg_holes_rest : list string ->
                                       list string -> M (list term))
        (e_name : string)
        (e_holes : term).
      (* Separated out for the termination checker*)
      Fixpoint insert_next_arg (c_names e_args : list string)
          : M (list term) :=
          match c_names, e_args with
          | [], _ | _, [] => Mret default (* should not happen *)
          | x::c_names', y::e_args' =>
              if eqb x y then
                @! let s'' <- insert_arg_holes_rest c_names' e_args' in
                  ret (e_holes :: s'')
              else 
                @! let s'' <- insert_next_arg c_names' e_args in
                  let x_sym <- gensym in
                  ret (con x_sym [] :: s'')
          end.
      
      (* Separated out for the termination checker*)
      Definition insert_next_implicit_arg (c_names e_args : list string)
          : M (list term) :=
          match c_names with
          | [] => Mret default (* should not happen *)
          | x::c_names' =>
              if eqb x e_name then
                @! let s'' <- insert_arg_holes_rest c_names' e_args in
                  ret (e_holes :: s'')
              else
                @! let s'' <- insert_next_arg c_names' e_args in
                  let x_sym <- gensym in
                  ret (con x_sym [] :: s'')
          end.
    End Inner2.      
    
    Fixpoint insert_arg_holes
      (s : list (string * PreTerm.preterm string + PreTerm.preterm string))
      (c_names e_args : list string)
      : M (list term) :=
      match s with
      | [] => insert_trailing_holes c_names
      | inr e::s' =>
          @!let {M} e_holes <- build_term_with_holes e in
            (insert_next_arg (insert_arg_holes s') e_holes c_names e_args)
      | inl (x,e)::s' =>
          @!let {M} e_holes <- build_term_with_holes e in
            (insert_next_implicit_arg (insert_arg_holes s')
               x e_holes c_names e_args)
      end.
  End Inner.
  
  Fixpoint build_term_with_holes (t: preterm)
    : M term :=
    match t with
    | pre_var x => Mret (var x)
    | pre_con name_of_rule s =>
        @! let l <- get_state in
        match NamedList.named_list_lookup_err l name_of_rule with
        | Some (term_rule context explicit_args _) =>
            @! let {M} s_holes <- insert_arg_holes build_term_with_holes
                               s (map fst context) explicit_args in
              ret con name_of_rule s_holes
        (* The case below never runs *)
        | _ => Mret default
        end
    end.

  Definition build_sort_with_holes (s: presort)
    : M sort :=
    match s with
    | pre_scon name_of_rule s =>
        @! let l <- get_state in
        match NamedList.named_list_lookup_err l name_of_rule with
        | Some (sort_rule context explicit_args) =>
            @!let s_holes <- insert_arg_holes build_term_with_holes
                               s (map fst context) explicit_args in
              ret scon name_of_rule s_holes
        (* The case below never runs *)
        | _ => Mret default
        end
    end.

  Local Open Scope list_scope.
  Fixpoint build_ctx_with_holes (context: prectx)
    : M _ :=
    (* takes a pre-elaboration context and a language it type-checks in.
    outputs a context with holes and an extended language with the dummy rule and the additional context rules *)
    match context with
    | nil => Mret nil
    | (name_n, s) :: context =>
        @!let elab_context <- build_ctx_with_holes context in
          let s_with_no_variables := presort_var_to_con s in
          let s_holes <- build_sort_with_holes s_with_no_variables in
          let _ <- log [(name_n, term_rule [] [] s_holes)] in
          ret ((name_n , s_holes) :: elab_context)
    end.

  (* To be used when the context is already elaborated.
     TODO: rules technically in the wrong order.
   *)
  Definition ctx_rules : ctx -> lang :=
    named_map (fun t => term_rule [] [] (sort_var_to_con t)).
  
End __.

Local Open Scope string_scope.
(* Injection rules *)
Fixpoint equalize_terms (args inj_args : list string) : list (clause string string) :=
  match args with
  | [] => []
  | arg_name::args =>
      if inb arg_name inj_args then (eq_clause (arg_name++"1") (arg_name++"2")) :: equalize_terms args inj_args
      else equalize_terms args inj_args
  end.

(* Assumes r is a term rule or sort rule *)
Definition injection_rule_from_name_and_rule (name: string) inj_args (r: rule) : sequent string string :=
  (*TODO: fresh name for atom_ret*)
  let ret_name := name ++" cong_ret" in
  let context := get_ctx r in
  let args := map fst context in
  let arguments1 := (map (fun x => (fst x) ++ "1") context) in
  let arguments2 := (map (fun x => (fst x) ++ "2") context) in
  {|
    seq_assumptions :=
      [atom_clause (Build_atom name arguments1 ret_name);
       atom_clause (Build_atom name arguments2 ret_name)];
    seq_conclusions := equalize_terms args inj_args
  |}.

Definition build_injection_rule (L: lang) (schema: string * list string): sequent string string :=
  let (name, inj_args) := schema in
  match Find_x name L with
  | Some r =>
    injection_rule_from_name_and_rule name inj_args r
  | None => Build_sequent _ _ default default
  end.
Definition build_injection_rules (schemas: list (string * list string)) (L: lang): list (sequent string string) :=
  map (build_injection_rule L) schemas.
(* ----------------------------- *)


(* ============================================================
   Running the e-graph computation over positive indices.

   The build (hole-insertion) phase runs over strings so we can gensym
   readable hole names; then we rename the whole problem (language, context,
   conclusion, injection sequents) into [positive] and run the actual
   saturation/extraction in PosInferEngine, finally unrenaming the result.
   This mirrors Defs.PositiveInstantiation, which renames into positives to
   use the fast positive tries.
   ============================================================ *)

Local Open Scope list_scope.

(* The conclusion of a rule, with gensym'd holes, over strings. *)
Variant str_payload :=
  | sp_sort
  | sp_term (t : sort)
  | sp_sort_eq (t1 t2 : sort)
  | sp_term_eq (e1 e2 : term) (t : sort).

Definition get_ctx (r : prerule) :=
  match r with
  | presort_rule c _ | preterm_rule c _ _ | presort_eq_rule c _ _ |
    preterm_eq_rule c _ _ _ => c
  end.

(* The build phase reuses the lens-based fresh-name (ident) and language
   (list (string*rule)) state; it never touches the e-graph, so the [egraph]
   field is left as the empty graph. *)
Record infer_state : Type :=
  {
    infer_fresh : ident;
    infer_lang : list (string * rule);
    egraph : instance;
  }.

Instance infer_state_fresh : Lens infer_state ident :=
  {
    lens_get := infer_fresh;
    lens_set s i := Build_infer_state i s.(infer_lang) s.(egraph);
  }.
Instance infer_state_infer_lang : Lens infer_state (list (string * rule)) :=
  {
    lens_get := infer_lang;
    lens_set s l := Build_infer_state s.(infer_fresh) l s.(egraph);
  }.
Instance infer_state_egraph : Lens infer_state instance :=
  {
    lens_get := egraph;
    lens_set s g := Build_infer_state s.(infer_fresh) s.(infer_lang) g;
  }.

Definition init_infer_state (l : lang) : infer_state :=
  Build_infer_state (Build_ident "?") l empty_egraph.

(* Phase 1: build the context and conclusion with holes, accumulating the
   dummy/context rules into the language.  Returns the extended language, the
   context-with-holes, and the conclusion payload (all over strings). *)
Definition build_problem (l : lang) (r : prerule)
  : lang * named_list sort * str_payload :=
  let comp : state infer_state (named_list sort * str_payload) :=
    @! let ctx_holes <- build_ctx_with_holes (get_ctx r) in
      let payload <-
        match r return state infer_state str_payload with
        | presort_rule _ _ => @! ret sp_sort
        | preterm_rule _ _ t =>
            @! let t' <- build_sort_with_holes (presort_var_to_con t) in
              ret (sp_term t')
        | presort_eq_rule _ t1 t2 =>
            @! let t1' <- build_sort_with_holes (presort_var_to_con t1) in
              let t2' <- build_sort_with_holes (presort_var_to_con t2) in
              ret (sp_sort_eq t1' t2')
        | preterm_eq_rule _ e1 e2 t =>
            @! let t' <- build_sort_with_holes (presort_var_to_con t) in
              let e1' <- build_term_with_holes (pre_var_to_con e1) in
              let e2' <- build_term_with_holes (pre_var_to_con e2) in
              ret (sp_term_eq e1' e2' t')
        end in
      ret (ctx_holes, payload)
  in
  let '(res, s) := comp (init_infer_state l) in
  (s.(infer_lang), fst res, snd res).

(* ---- renaming into positives ---- *)

(* Reserve [xH] for sort_of (PosInferEngine uses it as the special symbol),
   so allocation starts at 2, matching Defs.PositiveInstantiation. *)
Definition init_renaming : renaming string :=
  {| p_to_v := map.empty; v_to_p := []; next_id := 2%positive |}.

Definition rename_atom (a : atom string string)
  : state (renaming string) (atom positive positive) :=
  @! let f <- to_p a.(atom_fn) in
    let args <- list_Mmap to_p a.(atom_args) in
    let r <- to_p a.(atom_ret) in
    ret (Build_atom f args r).

Definition rename_clause (c : clause string string)
  : state (renaming string) (clause positive positive) :=
  match c with
  | eq_clause x y =>
      @! let x' <- to_p x in
        let y' <- to_p y in
        ret (eq_clause x' y')
  | atom_clause a =>
      @! let a' <- rename_atom a in
        ret (atom_clause a')
  end.

Definition rename_sequent (s : sequent string string)
  : state (renaming string) (sequent positive positive) :=
  @! let asm <- list_Mmap rename_clause s.(seq_assumptions) in
    let concl <- list_Mmap rename_clause s.(seq_conclusions) in
    ret (Build_sequent _ _ asm concl).

Definition rename_ctx_holes (ch : named_list sort)
  : state (renaming string) (list (positive * Term.sort positive)) :=
  list_Mmap (fun '(n,s) =>
               @! let n' <- to_p n in
                 let s' <- rename_sort s in
                 ret (n', s')) ch.

Definition rename_str_payload (p : str_payload)
  : state (renaming string) PosInferEngine.payload :=
  match p with
  | sp_sort => @! ret PosInferEngine.pp_sort
  | sp_term t =>
      @! let t' <- rename_sort t in ret (PosInferEngine.pp_term t')
  | sp_sort_eq t1 t2 =>
      @! let t1' <- rename_sort t1 in
        let t2' <- rename_sort t2 in
        ret (PosInferEngine.pp_sort_eq t1' t2')
  | sp_term_eq e1 e2 t =>
      @! let t' <- rename_sort t in
        let e1' <- rename_term e1 in
        let e2' <- rename_term e2 in
        ret (PosInferEngine.pp_term_eq e1' e2' t')
  end.

(* A renamed positive is a hole iff its original string starts with "?"
   (gensym'd names and their dummy sorts). *)
Definition is_hole (rn : renaming string) (p : positive) : bool :=
  match of_p rn p with
  | String "?" _ => true
  | _ => false
  end.

(* ---- inference of a single rule ---- *)

Definition infer_rule (l : lang) inj_rules (r : prerule) : rule :=
  let '(l_full, ctx_holes, payload) := build_problem l r in
  let rename_all : state (renaming string)
                     (_ * _ * PosInferEngine.payload * _) :=
    @! let l_pos <- rename_lang l_full in
      let ctx_pos <- rename_ctx_holes ctx_holes in
      let payload_pos <- rename_str_payload payload in
      let inj_pos <- list_Mmap rename_sequent
                       (build_injection_rules inj_rules l_full) in
      ret (l_pos, ctx_pos, payload_pos, inj_pos)
  in
  let '(tmp, rn) := rename_all init_renaming in
  let '(l_pos, ctx_pos, payload_pos, inj_pos) := tmp in
  let dec := PosInferEngine.run_infer (PosInferEngine.mk_weight (is_hole rn))
               l_pos inj_pos ctx_pos payload_pos in
  let args := match r with
              | presort_rule _ a | preterm_rule _ a _ => a
              | _ => []
              end in
  match dec with
  | PosInferEngine.pd_sort c => sort_rule (unrename_ctx rn c) args
  | PosInferEngine.pd_term c t =>
      term_rule (unrename_ctx rn c) args (unrename_sort rn t)
  | PosInferEngine.pd_sort_eq c t1 t2 =>
      sort_eq_rule (unrename_ctx rn c) (unrename_sort rn t1) (unrename_sort rn t2)
  | PosInferEngine.pd_term_eq c e1 e2 t =>
      term_eq_rule (unrename_ctx rn c) (unrename_term rn e1)
        (unrename_term rn e2) (unrename_sort rn t)
  end.

Fixpoint infer_lang_ext l_base (l : prelang) inj_rules :=
  match l with
  | [] => []
  | (n,r)::l =>
      (* inj_rules may include a superset of the rules of l, but that's ok *)
      let l' := infer_lang_ext l_base l inj_rules in
      let r' := infer_rule (l'++l_base) inj_rules r in
      (n,r')::l'
  end.

Definition infer_lang_ext_simple l_base (l : lang) inj_rules :=
  infer_lang_ext l_base (of_lang l) inj_rules.

Section __.
  Context (tgt:lang).
  Notation compile_ctx :=
    (compile_ctx (tgt_Model := @syntax_model _ _)).
  Notation compile :=
    (compile (tgt_Model := @syntax_model _ _)).
  Notation compile_sort :=
    (compile_sort (tgt_Model := @syntax_model _ _)).
  Notation compiler_case :=
    (@compiler_case string term sort).
  (* takes in a prelab cc and an elaborated rule r *)
  Definition infer_compiler_case_simple
    cmp (cc : compiler_case) r inj_rules :=
    match cc,r with
    | sort_case cnames t, sort_rule c _ =>
        let c' := (compile_ctx cmp c) in
        let c'_rules := ctx_rules c' in
        (* rename to the names from the rule *)
        let t' := t[/combine cnames (map var (map fst c))/] in
        (* phase 1: register c'_rules in the language, build the sort holes *)
        let comp1 : state infer_state sort :=
          @! let _ <- log c'_rules in
            (build_sort_with_holes (presort_var_to_con (of_sort t')))
        in
        let '(t_holes, s1) := comp1 (init_infer_state tgt) in
        let l_full := s1.(infer_lang) in
        let rename_all : state (renaming string) _ :=
          @! let l_pos <- rename_lang l_full in
            let c'_pos <- rename_ctx c' in
            let t_pos <- rename_sort t_holes in
            let inj_pos <- list_Mmap rename_sequent
                             (build_injection_rules inj_rules l_full) in
            ret (l_pos, c'_pos, t_pos, inj_pos)
        in
        let '(tmp, rn) := rename_all init_renaming in
        let '(l_pos, c'_pos, t_pos, inj_pos) := tmp in
        let out' := unrename_sort rn
                      (PosInferEngine.run_compile_sort
                         (PosInferEngine.mk_weight (is_hole rn))
                         l_pos inj_pos c'_pos t_pos) in
        (* rename back to the compiler case names *)
        let out := out' [/combine (map fst c) (map var cnames)/] in
        sort_case cnames out
    | term_case cnames e, term_rule c _ t =>
        let c' := (compile_ctx cmp c) in
        let c'_rules := ctx_rules c' in
        (* rename to the names from the rule *)
        let e' := e[/combine cnames (map var (map fst c))/] in
        let comp1 : state infer_state term :=
          @! let _ <- log c'_rules in
            (build_term_with_holes (pre_var_to_con (of_term e')))
        in
        let '(e_holes, s1) := comp1 (init_infer_state tgt) in
        let l_full := s1.(infer_lang) in
        let t_sort := sort_var_to_con (compile_sort cmp t) in
        let rename_all : state (renaming string) _ :=
          @! let l_pos <- rename_lang l_full in
            let c'_pos <- rename_ctx c' in
            let tsort_pos <- rename_sort t_sort in
            let e_pos <- rename_term e_holes in
            let inj_pos <- list_Mmap rename_sequent
                             (build_injection_rules inj_rules l_full) in
            ret (l_pos, c'_pos, tsort_pos, e_pos, inj_pos)
        in
        let '(tmp, rn) := rename_all init_renaming in
        let '(l_pos, c'_pos, tsort_pos, e_pos, inj_pos) := tmp in
        let out' := unrename_term rn
                      (PosInferEngine.run_compile_term
                         (PosInferEngine.mk_weight (is_hole rn))
                         l_pos inj_pos c'_pos tsort_pos e_pos) in
        (* rename back to the compiler case names *)
        let out := out' [/combine (map fst c) (map var cnames)/] in
        term_case cnames out
    | _,_ => sort_case [] default (* failure case *)
    end.

  Fixpoint infer_compiler_simple cmp_pre cmp src inj_rules :=
    match cmp,src with
    | [], [] => []
    | (n,cc)::cmp', (n',r)::src' =>
        if eqb n n'
        then let ecmp' :=
               infer_compiler_simple cmp_pre cmp' src' inj_rules
             in
             let ecc := infer_compiler_case_simple
                          (ecmp'++cmp_pre) cc r inj_rules in
             (n,ecc)::ecmp'
        (* must be an equation *)
        else infer_compiler_simple cmp_pre cmp src' inj_rules
    | _, _ => [] (*Failure case. TODO: better errors *)
    end.

End __.
