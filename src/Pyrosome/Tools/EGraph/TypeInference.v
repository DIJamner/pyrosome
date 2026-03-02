Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils EGraph.Defs Monad Lens.
From Pyrosome Require Import Theory.Core Elab.Elab
  Elab.PreTerm Elab.PreRule
  Compilers.Compilers
  Tools.Matches Tools.EGraph.Defs
  Tools.EGraph.Automation.
Require Import Utils.EGraph.Semantics.
Import PArith.
Import Ascii.AsciiSyntax.
Import StringInstantiation.
Import StateMonad.
Require Import Coq.Strings.String.
Require Coq.Numbers.DecimalString.


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
      Fixpoint insert_next_implicit_arg (c_names e_args : list string)
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

Local Open Scope char_scope.
Definition weight (a: atom string string) : option positive :=
match a with
| Build_atom (String "?" _) [] _ => None
| Build_atom "@sort_of"%string _ _ => None
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
Definition con_to_var_sort (context: ctx) (t: sort) : sort :=
  match t with
  | scon name subterms => scon name (map (con_to_var context) subterms)
  end.
Definition result_to_term (result: Result.result term) : term :=
  match result with
  | Result.Success t => t
  | _ => default
  end.
Definition result_to_sort (result: Result.result sort) : sort :=
  match result with
  | Result.Success s => s
  | _ => default
  end.
Definition term_to_sort (t: term) : sort :=
  match t with
  | var x => scon x []
  | con n s => scon n s
  end.

Definition const_rules (l: lang) :=
  (map (uncurry (rule_to_log_rule string_trie_map _
                   string_succ sort_of l (analysis_result:=unit) 1000))
  (filter (fun '(n,r) => inclb (get_ctx r) []) l)).


(* TODO: is this only running the injection rules???
   Needs to at least also run all constant rules,
   also equations.

   TODO: rename
 *)
Definition state_operation (L: lang) (inj_rules: list (string * list string)) :=
  @saturate_until string String.eqb string_succ
    (default (A:= string))
    string
    string_trie_map
    string_ptree_map_plus string_trie_map string_ptree_map_plus
    string_list_trie_map (option positive) (weighted_depth_analysis weight) (@PosListMap.compat_intersect)
    1000
    (
    @QueryOpt.build_rule_set string String.eqb string_succ (default (A:= string))
      string  string_trie_map string_ptree_map_plus string_trie_map
      string_list_trie_map 1000  (build_injection_rules inj_rules L
                                    ++ const_rules L)
    )
    (Mret false) 1000.

Definition state_operation_testing (L: lang) (inj_rules: list (string * list string)) f1 f2 :=
  @saturate_until string String.eqb string_succ
    (default (A:= string))
    string
    string_trie_map
    string_ptree_map_plus string_trie_map string_ptree_map_plus
    string_list_trie_map (option positive) (weighted_depth_analysis weight) (@PosListMap.compat_intersect)
    f1
    (
    @QueryOpt.build_rule_set string String.eqb string_succ (default (A:= string))
      string  string_trie_map string_ptree_map_plus string_trie_map
      string_list_trie_map 1000 (build_injection_rules inj_rules L
                                   ++ const_rules L)
    )
    (Mret false) f2.

(* Breaking up egraph operations: *)

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

(* assumes l contains the context rules *)
(*TODO: always take in a sort id?*)
Definition add_elab_term_to_egraph (t: preterm) (sort_id: string)
  : state infer_state string :=
  let term_with_no_variables := (pre_var_to_con t) in
  @!let term_with_holes <- build_term_with_holes term_with_no_variables in
    let l <- get_state in
    let t_id <- state_embed (add_open_term weight l true [] term_with_holes) in
    let _ <- state_embed (update_entry (Build_atom sort_of [t_id] sort_id)) in
    ret t_id.

Definition infer_add_open_sort s :=
  @!let l <- get_state in
    (state_embed (add_open_sort weight l true [] s)).

(* assumes l contains the context rules *)
Definition add_elab_sort_to_egraph (s:presort)
  : state infer_state _ :=
  let sort_with_no_variables := (presort_var_to_con s) in
  @!let sort_with_holes <- build_sort_with_holes sort_with_no_variables in
    (infer_add_open_sort sort_with_holes).

Definition add_ctx_with_holes_to_egraph (context: ctx)
  : state infer_state _ :=
  (* takes a context with holes and a language it type checks in.
      adds the sorts in the context to the egraph.
      Returns a map from pyrosome (not egraph) variables to sort ids
      Note: Mmap is in the wrong direction,
      so it might not be sound to fuse this
      with building the context with holes
   *)
  list_Mmap (fun '(n, s) => Mbind (fun str => Mret (n, str))
                              (infer_add_open_sort s))
    context.
    
(* INFERENCE: *)
(*
Definition infer_term (L: lang) inj_rules (context: ctx) (t: term) (s: sort) :=
  let Language_plus_rules := L ++ (ctx_to_rules context) in
  (*TODO: what is this and why did I use it? 
  let new_context := context ++ get_dummy_context (get_dummy_names_from_term (term_with_holes)) in
   *)
  (*TODO: check that add_sort doesn't need dummy rules (it shouldn't)*)
  let '(t_id, counter, graph) :=
    (@! let {stateT string (state instance)} sort_id <- lift (add_open_sort weight Language_plus_rules true [] (sort_var_to_con s)) in
       let {stateT string (state instance)} (t_id, dummy_rules) <-
             add_elab_term_to_egraph Language_plus_rules t sort_id in
      let _ <- lift (state_operation Language_plus_rules inj_rules) in
      ret {stateT string (state instance)} t_id) "?" empty_egraph
  in
  con_to_var context (result_to_term (extract_weighted graph 1000 t_id)).
*)

Variant egraph_rule_ids :=
  | sort_rule_ids (c_ids : named_list string) (args : list string)
  | term_rule_ids (c_ids : named_list string) (args : list string) (t_id : string)
  | sort_eq_rule_ids (c_ids : named_list string) (t_id1 t_id2 : string)
  | term_eq_rule_ids (c_ids : named_list string) (e_id1 e_id2 t_id : string).

Definition decode_term context graph t_id :=
  con_to_var context (result_to_term (extract_weighted graph 1000 t_id)).

Definition decode_sort context graph t_id :=
  term_to_sort (decode_term context graph t_id).

Fixpoint decode_ctx graph ids :=
  match ids with
  | [] => []
  | (x,x_id)::ids =>
      let context := decode_ctx graph ids in
      (x, decode_sort context graph x_id)::context
  end.

Definition get_ctx (r : prerule) :=
  match r with
  | presort_rule c _ | preterm_rule c _ _ | presort_eq_rule c _ _ |
    preterm_eq_rule c _ _ _ => c
  end.

(*TODO: use state composed w/ writer for dummy rules?*)
Definition infer_rule_egraph (l: lang) inj_rules (r : prerule) :=
  let context := get_ctx r in
  let comp : state infer_state _ :=
    @!
      let context_with_holes <- build_ctx_with_holes context in
      let c_ids <- add_ctx_with_holes_to_egraph context_with_holes in
      let res <- match r with
                 | presort_rule _ args => @!ret sort_rule_ids c_ids args
                 | preterm_rule _ args t => 
                     @!let t_id <- add_elab_sort_to_egraph t in
                       ret term_rule_ids c_ids args t_id
                 | presort_eq_rule _ t1 t2 => 
                     @!let t1_id <- add_elab_sort_to_egraph t1 in
                       let t2_id <- add_elab_sort_to_egraph t2 in
                       ret sort_eq_rule_ids c_ids t1_id t2_id
                 | preterm_eq_rule _ e1 e2 t => 
                     @!let t_id <- add_elab_sort_to_egraph t in
                       let e1_id <- add_elab_term_to_egraph e1 t_id in
                       let e2_id <- add_elab_term_to_egraph e2 t_id in
                       ret (term_eq_rule_ids c_ids e1_id e2_id t_id)  
                 end
      in
      let l <- get_state (S:= lang) in
      let _ <- state_embed (state_operation l inj_rules) in
      ret res
          
  in
  comp (Build_infer_state (Build_ident "?") l empty_egraph).


Definition infer_rule_egraph_testing_initial (l: lang) r :=
  let context := get_ctx r in
  let comp : state infer_state _ :=
    @!
      let context_with_holes <- build_ctx_with_holes context in
      let c_ids <- add_ctx_with_holes_to_egraph context_with_holes in
      let res <- match r with
                 | presort_rule _ args => @!ret sort_rule_ids c_ids args
                 | preterm_rule _ args t => 
                     @!let t_id <- add_elab_sort_to_egraph t in
                       ret term_rule_ids c_ids args t_id
                 | presort_eq_rule _ t1 t2 => 
                     @!let t1_id <- add_elab_sort_to_egraph t1 in
                       let t2_id <- add_elab_sort_to_egraph t2 in
                       ret sort_eq_rule_ids c_ids t1_id t2_id
                 | preterm_eq_rule _ e1 e2 t => 
                     @!let t_id <- add_elab_sort_to_egraph t in
                       let e1_id <- add_elab_term_to_egraph e1 t_id in
                       let e2_id <- add_elab_term_to_egraph e2 t_id in
                       ret (term_eq_rule_ids c_ids e1_id e2_id t_id)  
                 end
      in
      ret res
                
  in
  comp (Build_infer_state (Build_ident "?") l empty_egraph).
    
Definition decode_rule ids graph :=
  match ids with
  | sort_rule_ids c_ids args =>
      let c := decode_ctx graph c_ids in
      sort_rule c args
  | term_rule_ids c_ids args t_id =>
      let c := decode_ctx graph c_ids in
      let t := decode_sort c graph t_id in
      term_rule c args t
  | sort_eq_rule_ids c_ids t1_id t2_id => 
      let c := decode_ctx graph c_ids in
      let t1 := decode_sort c graph t1_id in
      let t2 := decode_sort c graph t2_id in
      sort_eq_rule c t1 t2
  | term_eq_rule_ids c_ids e1_id e2_id t_id => 
      let c := decode_ctx graph c_ids in
      let t := decode_sort c graph t_id in
      let e1 := decode_term c graph e1_id in
      let e2 := decode_term c graph e2_id in
      term_eq_rule c e1 e2 t
  end.

Definition infer_rule (l: lang) inj_rules (r : prerule) :=
  let '(ids, s) := infer_rule_egraph l inj_rules r in
  decode_rule ids s.(egraph).

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
  (* TODO: add precompilers, def that allows annotations *)
  Definition infer_compiler_case_simple
    cmp (cc : compiler_case) r inj_rules :=
    let initial := (Build_infer_state (Build_ident "?")
                      tgt empty_egraph) in
    match cc,r with
    | sort_case cnames t, sort_rule c _ => 
        let c' := (compile_ctx cmp c) in
        let c'_rules := ctx_rules c' in
        let comp : state infer_state _ :=
          @!
            let _ <- log c'_rules in
            let x <- add_elab_sort_to_egraph (of_sort t) in
            let l <- get_state (S:= lang) in
            let _ <- state_embed (state_operation l inj_rules) in
            ret x
        in
        let (x,s) := comp initial in
        sort_case cnames (decode_sort c' s.(egraph) x)
    | term_case cnames e, term_rule c _ t =>
        let c' := (compile_ctx cmp c) in
        let c'_rules := ctx_rules c' in
        let comp : state infer_state _ :=
          @!let _ <- log c'_rules in
            let l <- get_state (S:= lang) in
            let t_id <-
                  state_embed
                    (add_open_sort weight l true []
                       (sort_var_to_con (compile_sort cmp t))) in
            let x <- add_elab_term_to_egraph (of_term e) t_id in
            let l <- get_state (S:= lang) in
            let _ <- state_embed (state_operation l inj_rules) in
            ret x
        in
        let (x,s) := comp initial in
        term_case cnames (decode_term c' s.(egraph) x)
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


(*
Definition infer_sort (L: lang) inj_rules (context: ctx) (s: sort) : sort :=
  let Language_plus_rules := L ++ (ctx_to_rules context) in
  (*TODO: what is this and why did I use it? 
  let new_context := context ++ get_dummy_context (get_dummy_names_from_term (term_with_holes)) in
 *)
  (*TODO: check that add_sort doesn't need dummy rules (it shouldn't)*)
  let '(t_id, counter, graph) :=
    (@! let {stateT string (state instance)} (t_id, dummy_rules) <-
             add_elab_sort_to_egraph Language_plus_rules s in
      let _ <- lift (state_operation Language_plus_rules inj_rules) in
      ret {stateT string (state instance)} t_id) "?" empty_egraph
  in
  term_to_sort (con_to_var context (result_to_term (extract_weighted graph 1000 t_id))).

Fixpoint infer_ctx (L: lang) inj_rules (context: ctx) : ctx :=
  match context with
  | nil => nil
  | (n, s) :: rest =>
    let elab_rest := (infer_ctx L inj_rules rest) in
      (n, (infer_sort L inj_rules elab_rest s)) :: elab_rest
  end.
*)
