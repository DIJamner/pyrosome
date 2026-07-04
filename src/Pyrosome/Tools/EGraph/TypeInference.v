Set Implicit Arguments.

From coqutil Require Import Datatypes.String Map.Interface Datatypes.Result.
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
From Utils Require Import TrieMap PosListMap FullPosTrie FullPosTrieConv.
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

(* The per-constructor schema above can only express injectivity of a single
   language constructor [c] -- the congruence rule [c args1 = r -> c args2 = r ->
   args1 = args2].  Some sound facts an inference needs are not of this shape.

   In particular, recovering an implicit environment through the linear [ext G A
   := conc G (only A)] means inverting a [conc], and [conc] is *not* injective
   ([conc emp G = G]), so an injectivity schema for it would be unsound.  But
   [conc] *is* cancellative: environments form the free monoid on the [only A]
   generators, so [conc Z A = conc Z B -> A = B] (left) and [conc A Z = conc B Z
   -> A = B] (right) are both true theorems.  These are what actually let the
   engine recover the implicit env -- via the equation between two [conc]s that
   share one factor (which factor is shared depends on the rule; empirically the
   env is recovered from [blk (conc G H)]-style result sorts, where [H] is the
   shared left factor, so LEFT cancellation is the one that fires).

   The engine's injection input is therefore just a function [lang -> list
   sequent] -- "the injection sequents to run against this language".  The common
   case is [build_injection_rules schemas] (name-based congruence rules); to add
   explicit sound sequents a caller writes [fun L => build_injection_rules
   schemas L ++ extra_seqs], concatenating them onto [build_injection_rules]'s
   result.  ([of_lang]-style schema building stays per-rule, since it looks up
   constructor contexts in the language as it grows.) *)

(* Cancellation sequents for a binary operation [f] (sound whenever [f] is
   cancellative, e.g. concatenation on a free monoid).  Left: from [f Z A = f Z
   B] conclude [A = B]; right: from [f A Z = f B Z] conclude [A = B].  Synthetic
   e-class names use a space (as [injection_rule_from_name_and_rule] does for its
   [cong_ret]) so they cannot collide with source variables. *)
Definition left_cancellation_seq (f : string) : sequent string string :=
  {|
    seq_assumptions :=
      [atom_clause (Build_atom f ["Z"; "A"] (f ++ " lcancel_ret"));
       atom_clause (Build_atom f ["Z"; "B"] (f ++ " lcancel_ret"))];
    seq_conclusions := [eq_clause "A" "B"]
  |}.
Definition right_cancellation_seq (f : string) : sequent string string :=
  {|
    seq_assumptions :=
      [atom_clause (Build_atom f ["A"; "Z"] (f ++ " rcancel_ret"));
       atom_clause (Build_atom f ["B"; "Z"] (f ++ " rcancel_ret"))];
    seq_conclusions := [eq_clause "A" "B"]
  |}.
(* ----------------------------- *)


(* The e-graph engine, ported from the deleted string version to [positive]
   indices so it runs over the fast positive tries (sharing
   Defs.PositiveInstantiation's instantiation, [sort_of = xH]).  Each definition
   below is the positive analogue of the like-named string one.  [infer_*] build
   the problem over strings (so gensym keeps making readable "?"-holes), rename
   it into positives, run this engine, and unrename.  Parameterized by the
   extraction [weight], supplied once the caller knows which positives are holes. *)

(* The positive analogue of the string [weight]: holes (and [sort_of]) get
   infinite weight (None) so extraction never picks them, everything else 1. *)
Definition mk_weight (is_hole : positive -> bool)
  : atom positive positive -> option positive :=
  fun a =>
    if Pos.eqb a.(atom_fn) PosListMap.sort_of then None
    else match a.(atom_args) with
         | [] => if is_hole a.(atom_fn) then None else Some 1%positive
         | _ => Some 1%positive
         end.

Section WithWeight.
  Local Open Scope positive.

  Local Notation atom := (atom positive positive).
  Local Notation instance := (Defs.instance positive positive trie_map trie_map
                                (@FullPosTrie.full_pos_trie_map) (option positive)).
  Local Notation sequent := (sequent positive positive).
  Local Notation term := (@Term.term positive).
  Local Notation sort := (@Term.sort positive).
  Local Notation ctx := (@Term.ctx positive).
  Local Notation lang := (@Rule.lang positive).
  (* [named_list] stays the file-scope string notation; inside the section we
     write [@named_list positive _] explicitly.  [sort_of = xH] is shared with
     Defs.PositiveInstantiation, so inference runs the same compiled rules as
     egraph_sound. *)
  Local Notation sort_of := PosListMap.sort_of.

  Context (weight : atom -> option positive).

  Definition empty_egraph : instance :=
    Defs.empty_egraph (idx:=positive) (default:positive) (symbol:=positive)
      (symbol_map:=trie_map) (idx_map:=trie_map)
      (idx_trie:=(@FullPosTrie.full_pos_trie_map)) (option positive).

  Definition add_open_term (l : lang) :=
    Defs.add_open_term (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_size_analysis weight) true.

  Definition add_open_sort (l : lang) :=
    Defs.add_open_sort (V:=positive) (V_map:=trie_map) Pos.succ sort_of l
      (H:=weighted_size_analysis weight) true.

  Definition update_entry (a : atom) : state instance unit :=
    Defs.update_entry (idx:=positive) (symbol:=positive)
      (H:=weighted_size_analysis weight) a.

  (* Add a term with holes, and assert that its sort is [sort_id].  This is the
     residue of the string [add_elab_term_to_egraph] once hole-building has been
     split off into the (string) build phase. *)
  Definition add_elab_term (l : lang) (e : term) (sort_id : positive)
    : state instance positive :=
    @! let t_id <- add_open_term l true [] e in
      let _ <- update_entry (Build_atom sort_of [t_id] sort_id) in
      ret t_id.

  Notation extract_weighted :=
    (Defs.extract_weighted (V:=positive) (V_map:=trie_map)
       (V_trie:=(@FullPosTrie.full_pos_trie_map))).

  (* The constant rules of [l] (those with empty context), compiled to
     sequents. *)
  Definition const_rules (l : lang) : list sequent :=
    flat_map (fun '(n,r) =>
                match rule_to_log_rule trie_map _ Pos.succ sort_of l
                        (analysis_result:=unit) 1000%nat n r with
                | Result.Success s => [s]
                | Result.Failure _ => []
                end)
      (filter (fun '(n,r) => inclb (get_ctx r) []) l).

  (* The EQUATIONS of [l] (any context), compiled to sequents.  Unlike the
     injectivity/cancellation sequents -- which only conclude equalities between
     existing e-classes (merge-only) -- these are the full equational theory
     ([rule_to_log_rule] turns each [_eq_rule] into a rule that matches its LHS
     and introduces its RHS, merging the two).  They let inference reason UP TO
     the theory (e.g. re-associating/normalizing [conc] so a buried factor gets
     exposed for cancellation), at the cost of possible saturation blow-up
     (bounded by the 1000-iteration fuel below). *)
  Definition eq_rules (l : lang) : list sequent :=
    flat_map (fun '(n,r) =>
                match rule_to_log_rule trie_map _ Pos.succ sort_of l
                        (analysis_result:=unit) 1000%nat n r with
                | Result.Success s => [s]
                | Result.Failure _ => []
                end)
      (filter (fun '(n,r) => match r with
                             | sort_eq_rule _ _ _ | term_eq_rule _ _ _ _ => true
                             | _ => false
                             end) l).

  (* Run the saturation, given the language [l] and the precompiled injection
     sequents [inj_seqs]. *)
  Definition state_operation (l : lang) (inj_seqs : list sequent)
    : state instance bool :=
    (* epoch leb [Pos.leb]: proper semi-naive evaluation, which is complete and
       more efficient.  (The string engine ran naive only because string_succ's
       little-endian suffix has no cheap <=; positive has a real order.) *)
    @saturate_until positive Pos.eqb Pos.succ (default (A:=positive))
      Pos.leb
      positive trie_map ptree_map_plus trie_map ptree_map_plus
      (@FullPosTrie.full_pos_trie_map) (option positive)
      (weighted_size_analysis weight) (@fpt_spaced_intersect)
      1000%nat
      0%nat (* window *)
      (@QueryOpt.build_rule_set positive Pos.eqb Pos.succ (default (A:=positive))
         positive trie_map ptree_map_plus trie_map
         (@FullPosTrie.full_pos_trie_map) 1000%nat
         (inj_seqs ++ eq_rules l ++ const_rules l))
      (Mret false) 1000%nat.

  (* ---- decoding ---- *)

  Fixpoint con_to_var (context : ctx) (t : term) : term :=
    match t with
    | con name [] =>
        if (inb name (map fst context)) then (var name) else t
    | con name subterms => con name (map (con_to_var context) subterms)
    | _ => t
    end.

  Definition result_to_term (r : Result.result term) : term :=
    match r with
    | Result.Success t => t
    | _ => default
    end.

  Definition term_to_sort (t : term) : sort :=
    match t with
    | var x => scon x []
    | con n s => scon n s
    end.

  Definition decode_term (context : ctx) (graph : instance) (t_id : positive) : term :=
    con_to_var context (result_to_term (extract_weighted graph 1000%nat t_id)).

  Definition decode_sort (context : ctx) (graph : instance) (t_id : positive) : sort :=
    term_to_sort (decode_term context graph t_id).

  Fixpoint decode_ctx (graph : instance) (ids : list (positive * positive)) : ctx :=
    match ids with
    | [] => []
    | (x,x_id)::ids =>
        let context := decode_ctx graph ids in
        (x, decode_sort context graph x_id)::context
    end.

  (* ---- running the pipeline: [infer_rule_egraph] + [decode_rule], fused into
     one entry point per rule shape (the match on the rule lives in [infer_rule]
     below, as it did in the string [infer_rule_egraph]). ---- *)

  (* Add the context holes, returning their e-class ids (the positive
     [add_ctx_with_holes_to_egraph]). *)
  Definition add_ctx (l : lang) (ctx_holes : list (positive * sort))
    : state instance (list (positive * positive)) :=
    list_Mmap (fun '(n,s) =>
                 @! let x <- add_open_sort l true [] s in ret (n, x)) ctx_holes.

  (* Run an add-computation on a fresh e-graph, saturate, and return its result
     together with the final graph (to decode from). *)
  Definition saturated {A} (l : lang) (inj_seqs : list sequent)
    (add : state instance A) : A * instance :=
    let comp : state instance A :=
      @! let a <- add in
        let _ <- state_operation l inj_seqs in
        ret a in
    comp empty_egraph.

  Definition run_infer_sort (l : lang) (inj_seqs : list sequent)
    (ctx_holes : list (positive * sort)) : ctx :=
    let '(c_ids, g) := saturated l inj_seqs (add_ctx l ctx_holes) in
    decode_ctx g c_ids.

  Definition run_infer_term (l : lang) (inj_seqs : list sequent)
    (ctx_holes : list (positive * sort)) (t : sort) : ctx * sort :=
    let '((c_ids, t_id), g) := saturated l inj_seqs
         (@! let c_ids <- add_ctx l ctx_holes in
             let t_id <- add_open_sort l true [] t in
             ret (c_ids, t_id)) in
    let c := decode_ctx g c_ids in
    (c, decode_sort c g t_id).

  Definition run_infer_sort_eq (l : lang) (inj_seqs : list sequent)
    (ctx_holes : list (positive * sort)) (t1 t2 : sort) : ctx * sort * sort :=
    let '((c_ids, t1_id, t2_id), g) := saturated l inj_seqs
         (@! let c_ids <- add_ctx l ctx_holes in
             let t1_id <- add_open_sort l true [] t1 in
             let t2_id <- add_open_sort l true [] t2 in
             ret (c_ids, t1_id, t2_id)) in
    let c := decode_ctx g c_ids in
    (c, decode_sort c g t1_id, decode_sort c g t2_id).

  Definition run_infer_term_eq (l : lang) (inj_seqs : list sequent)
    (ctx_holes : list (positive * sort)) (e1 e2 : term) (t : sort)
    : ctx * term * term * sort :=
    let '((c_ids, t_id, e1_id, e2_id), g) := saturated l inj_seqs
         (@! let c_ids <- add_ctx l ctx_holes in
             let t_id <- add_open_sort l true [] t in
             let e1_id <- add_elab_term l e1 t_id in
             let e2_id <- add_elab_term l e2 t_id in
             ret (c_ids, t_id, e1_id, e2_id)) in
    let c := decode_ctx g c_ids in
    (c, decode_term c g e1_id, decode_term c g e2_id, decode_sort c g t_id).

  (* Compiler-case entry points: the decoding context [c'] is given (the
     already-compiled target context), rather than inferred. *)
  Definition run_compile_sort (l : lang) (inj_seqs : list sequent)
    (c' : ctx) (t : sort) : sort :=
    let '(x, g) := saturated l inj_seqs (add_open_sort l true [] t) in
    decode_sort c' g x.

  Definition run_compile_term (l : lang) (inj_seqs : list sequent)
    (c' : ctx) (t_sort : sort) (e : term) : term :=
    let '(x, g) := saturated l inj_seqs
         (@! let t_id <- add_open_sort l true [] t_sort in
             let x <- add_elab_term l e t_id in
             ret x) in
    decode_term c' g x.

End WithWeight.


(* Bridge: build the problem over strings, rename into positives, run the engine
   above, unrename the result. *)

Local Open Scope list_scope.

(* The build phase reuses the lens-based fresh-name (ident) and language
   (list (string*rule)) state; it never touches the e-graph (that is now the
   engine's job, post-rename). *)
Record infer_state : Type :=
  {
    infer_fresh : ident;
    infer_lang : list (string * rule);
  }.

Instance infer_state_fresh : Lens infer_state ident :=
  {
    lens_get := infer_fresh;
    lens_set s i := Build_infer_state i s.(infer_lang);
  }.
Instance infer_state_infer_lang : Lens infer_state (list (string * rule)) :=
  {
    lens_get := infer_lang;
    lens_set s l := Build_infer_state s.(infer_fresh) l;
  }.

Definition init_infer_state (l : lang) : infer_state :=
  Build_infer_state (Build_ident "?") l.

(* ---- renaming into positives ---- *)

(* Reserve [xH] for sort_of (the engine uses it as the special symbol), so
   allocation starts at 2, matching Defs.PositiveInstantiation. *)
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

(* The part of the problem common to every rule shape: the language and the
   context holes.  Renamed first so the per-shape conclusion (renamed next in
   [infer_rule]) and the injection sequents (renamed last) keep a fixed
   allocation order. *)
Definition rename_lang_ctx (l_full : lang) (ctx_holes : named_list sort)
  : state (renaming string)
      (Rule.lang positive * list (positive * Term.sort positive)) :=
  @! let l_pos <- rename_lang l_full in
    let ctx_pos <- rename_ctx_holes ctx_holes in
    ret (l_pos, ctx_pos).

Definition rename_inj (l_full : lang)
  (inj_rules : lang -> list (sequent string string))
  : state (renaming string) (list (sequent positive positive)) :=
  list_Mmap rename_sequent (inj_rules l_full).

(* A renamed positive is a hole iff its original string starts with "?"
   (gensym'd names and their dummy sorts). *)
Definition is_hole (rn : renaming string) (p : positive) : bool :=
  match of_p rn p with
  | String "?" _ => true
  | _ => false
  end.

(* ---- inference of a single rule ---- *)

(* Match on the rule shape once -- exactly as the string [infer_rule_egraph]
   did -- and for each shape: build the ctx + conclusion holes over strings
   (sharing one [infer_state] run so gensym keeps allocating fresh names),
   rename language/ctx/conclusion/injections into positives (in that fixed
   order), run the matching engine entry point, and unrename. *)
Definition infer_rule_gen (l : lang)
  (inj_rules : lang -> list (sequent string string)) (r : prerule) : rule :=
  match r with
  | presort_rule c args =>
      let '(ctx_holes, s) :=
        build_ctx_with_holes c (init_infer_state l) in
      let l_full := s.(infer_lang) in
      let '((lc, inj_pos), rn) :=
        (@! let lc <- rename_lang_ctx l_full ctx_holes in
            let inj_pos <- rename_inj l_full inj_rules in
            ret (lc, inj_pos)) init_renaming in
      let '(l_pos, ctx_pos) := lc in
      let c' := run_infer_sort (mk_weight (is_hole rn)) l_pos inj_pos ctx_pos in
      sort_rule (unrename_ctx rn c') args
  | preterm_rule c args t =>
      let '((ctx_holes, t_holes), s) :=
        (@! let ctx_holes <- build_ctx_with_holes c in
            let t_holes <- build_sort_with_holes (presort_var_to_con t) in
            ret (ctx_holes, t_holes)) (init_infer_state l) in
      let l_full := s.(infer_lang) in
      let '((lc, t_pos, inj_pos), rn) :=
        (@! let lc <- rename_lang_ctx l_full ctx_holes in
            let t_pos <- rename_sort t_holes in
            let inj_pos <- rename_inj l_full inj_rules in
            ret (lc, t_pos, inj_pos)) init_renaming in
      let '(l_pos, ctx_pos) := lc in
      let '(c', t') :=
        run_infer_term (mk_weight (is_hole rn)) l_pos inj_pos ctx_pos t_pos in
      term_rule (unrename_ctx rn c') args (unrename_sort rn t')
  | presort_eq_rule c t1 t2 =>
      let '((ctx_holes, t1_holes, t2_holes), s) :=
        (@! let ctx_holes <- build_ctx_with_holes c in
            let t1_holes <- build_sort_with_holes (presort_var_to_con t1) in
            let t2_holes <- build_sort_with_holes (presort_var_to_con t2) in
            ret (ctx_holes, t1_holes, t2_holes)) (init_infer_state l) in
      let l_full := s.(infer_lang) in
      let '((lc, t1_pos, t2_pos, inj_pos), rn) :=
        (@! let lc <- rename_lang_ctx l_full ctx_holes in
            let t1_pos <- rename_sort t1_holes in
            let t2_pos <- rename_sort t2_holes in
            let inj_pos <- rename_inj l_full inj_rules in
            ret (lc, t1_pos, t2_pos, inj_pos)) init_renaming in
      let '(l_pos, ctx_pos) := lc in
      let '(c', s1, s2) :=
        run_infer_sort_eq (mk_weight (is_hole rn)) l_pos inj_pos ctx_pos t1_pos t2_pos in
      sort_eq_rule (unrename_ctx rn c') (unrename_sort rn s1) (unrename_sort rn s2)
  | preterm_eq_rule c e1 e2 t =>
      let '((ctx_holes, t_holes, e1_holes, e2_holes), s) :=
        (@! let ctx_holes <- build_ctx_with_holes c in
            let t_holes <- build_sort_with_holes (presort_var_to_con t) in
            let e1_holes <- build_term_with_holes (pre_var_to_con e1) in
            let e2_holes <- build_term_with_holes (pre_var_to_con e2) in
            ret (ctx_holes, t_holes, e1_holes, e2_holes)) (init_infer_state l) in
      let l_full := s.(infer_lang) in
      let '((lc, t_pos, e1_pos, e2_pos, inj_pos), rn) :=
        (@! let lc <- rename_lang_ctx l_full ctx_holes in
            let t_pos <- rename_sort t_holes in
            let e1_pos <- rename_term e1_holes in
            let e2_pos <- rename_term e2_holes in
            let inj_pos <- rename_inj l_full inj_rules in
            ret (lc, t_pos, e1_pos, e2_pos, inj_pos)) init_renaming in
      let '(l_pos, ctx_pos) := lc in
      let '(c', e1', e2', t') :=
        run_infer_term_eq (mk_weight (is_hole rn)) l_pos inj_pos ctx_pos e1_pos e2_pos t_pos in
      term_eq_rule (unrename_ctx rn c') (unrename_term rn e1')
        (unrename_term rn e2') (unrename_sort rn t')
  end.

(* Single-rule inference under name-based schemas only (the common case);
   preserves the original [infer_rule] interface, e.g. for [Interactive.v]. *)
Definition infer_rule (l : lang) (schemas : list (string * list string))
  (r : prerule) : rule :=
  infer_rule_gen l (build_injection_rules schemas) r.

Fixpoint infer_lang_ext_gen l_base (l : prelang)
  (inj_rules : lang -> list (sequent string string)) :=
  match l with
  | [] => []
  | (n,r)::l =>
      (* inj_rules may include a superset of the rules of l, but that's ok *)
      let l' := infer_lang_ext_gen l_base l inj_rules in
      let r' := infer_rule_gen (l'++l_base) inj_rules r in
      (n,r')::l'
  end.

Definition infer_lang_ext_simple_gen l_base (l : lang)
  (inj_rules : lang -> list (sequent string string)) :=
  infer_lang_ext_gen l_base (of_lang l) inj_rules.

(* Schema-only wrappers preserving the original interface. *)
Definition infer_lang_ext l_base (l : prelang)
  (schemas : list (string * list string)) :=
  infer_lang_ext_gen l_base l (build_injection_rules schemas).

Definition infer_lang_ext_simple l_base (l : lang)
  (schemas : list (string * list string)) :=
  infer_lang_ext_simple_gen l_base l (build_injection_rules schemas).

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
    cmp (cc : compiler_case) r
    (inj_rules : lang -> list (sequent string string)) :=
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
            let inj_pos <- rename_inj l_full inj_rules in
            ret (l_pos, c'_pos, t_pos, inj_pos)
        in
        let '(tmp, rn) := rename_all init_renaming in
        let '(l_pos, c'_pos, t_pos, inj_pos) := tmp in
        let out' := unrename_sort rn
                      (run_compile_sort (mk_weight (is_hole rn))
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
            let inj_pos <- rename_inj l_full inj_rules in
            ret (l_pos, c'_pos, tsort_pos, e_pos, inj_pos)
        in
        let '(tmp, rn) := rename_all init_renaming in
        let '(l_pos, c'_pos, tsort_pos, e_pos, inj_pos) := tmp in
        let out' := unrename_term rn
                      (run_compile_term (mk_weight (is_hole rn))
                         l_pos inj_pos c'_pos tsort_pos e_pos) in
        (* rename back to the compiler case names *)
        let out := out' [/combine (map fst c) (map var cnames)/] in
        term_case cnames out
    | _,_ => sort_case [] default (* failure case *)
    end.

  Fixpoint infer_compiler_simple_gen cmp_pre cmp src
    (inj_rules : lang -> list (sequent string string)) :=
    match cmp,src with
    | [], [] => []
    | (n,cc)::cmp', (n',r)::src' =>
        if eqb n n'
        then let ecmp' :=
               infer_compiler_simple_gen cmp_pre cmp' src' inj_rules
             in
             let ecc := infer_compiler_case_simple
                          (ecmp'++cmp_pre) cc r inj_rules in
             (n,ecc)::ecmp'
        (* must be an equation *)
        else infer_compiler_simple_gen cmp_pre cmp src' inj_rules
    | _, _ => [] (*Failure case. TODO: better errors *)
    end.

  (* Schema-only wrapper preserving the original interface. *)
  Definition infer_compiler_simple cmp_pre cmp src
    (schemas : list (string * list string)) :=
    infer_compiler_simple_gen cmp_pre cmp src (build_injection_rules schemas).

End __.
