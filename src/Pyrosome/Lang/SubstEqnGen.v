Require Import Datatypes.String Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches
  Tools.EGraph.TypeInference
  Tools.Interactive
  Elab.PreTerm Elab.PreRule
  Lang.Subst.

(*TODO: code duplication across various substitution languages; fix *)

Definition definitely_fresh (s : string) (l : list string) :=
  let len := List.fold_left Nat.max (map String.length l) 0 in
  String.append s (string_of_list_ascii (repeat ("'"%char : ascii) len)).

Definition choose_fresh (s : string) (c:ctx) :=
  if negb (inb s (map fst c)) then s else definitely_fresh s (map fst c).

Import PreRule.Notations Core.Notations.


(*pre-elab version
 *)
Definition under' g :=
  {{pe #"snoc" (#"cmp" #"wkn" {inr g}) #"hd" }}.

(*TODO: complicaed for dep types.
  Need a subst on hd?
 *)
Definition under G G' A g :=
  let gA := {{e #"ty_subst" {G} {G'} {g} {A} }} in
  let extG := {{e #"ext" {G} {gA} }} in
  {{e #"snoc" {extG} {G'} {A}
      (#"cmp" {extG} {G} {G'} (#"wkn" {G} {gA}) {g})
      (#"hd" {G} {gA}) }}.

Definition get_subst_constr s :=
  match s with
  | "exp" => Some "exp_subst"
  | "ty" => Some "ty_subst"
  | _ => None
  end.

Section GenRHSSubterms.
  Context (G' G : string)
          (g : string).

  (*TODO: careful! _ in patterns does bad things (treated as a var)
   document &/or fix

   Given an env G0 with either emp or G as the root,
   constructs an env G0' with G' as the root, the same extensions,
   and a substitution g : sub G0' G0.

   TODO: for dependent calculus, needs to wrap the A in substs
   *)
  Fixpoint gen_arg_subst s :=
    match s with
    | {{e#"emp"}} => Some (var G', {{e#"forget" G' }})
    | var G0 => if G =? G0 then Some (var G', var g) else None
    | {{e#"ext" {G0} {A} }} =>
        @!let (G0',g') <- gen_arg_subst G0 in
          let A0 := {{e #"ty_subst" {G0'} {G0} {g'} {A} }} in
          ret ({{e#"ext" {G0'} {A0} }}, under G0' G0 A g')
    | _ => None
    end.  
  
  Fixpoint gen_rhs_subterms (c : ctx) : option _ :=
    match c with      
    | [(_(*G*), s)] => Some [var G']
    | (n,t)::c' =>
        let (name, s) := t in
        match s, get_subst_constr name with
        | [G0], Some subst_constr =>           
            @!let (G0',s) <- gen_arg_subst G0 in
              let e := {{e #subst_constr {G0'} {G0} {s} n }} in
              let subterms <- gen_rhs_subterms c' in
              ret e::subterms
        | [A;G0], Some subst_constr =>            
            @!let (G0',s) <- gen_arg_subst G0 in
              (*let A0 := {{e #"ty_subst" {G0'} {G0} {s} {A} }} in*)
              let e := {{e #subst_constr {G0'} {G0} {s} {A} n }} in
              let subterms <- gen_rhs_subterms c' in
              ret e::subterms
        | _, None =>
            @!let subterms <- gen_rhs_subterms c' in
              ret (var n)::subterms
        | _, Some _ => None (*indicates an error in the language*)
        end
    | _ => None (* Missing context! shouldn't happen*)
    end.
End GenRHSSubterms.

Definition substable_constr name (c : ctx) (t : sort) : option _ :=
  let G' := choose_fresh "G'" c in
  let g := choose_fresh "g" c in
  let blank_term := con name (map var (map fst c)) in
  let (s_name, s_args) := t in
  @!let subst_constr <- get_subst_constr s_name in
  match s_args with
  (*TODO: assumes arbitrary G below the line. Is that the behavior I want or can I generalize?*)
  | [A; var G] =>
      let c' := (g,{{s#"sub" G' G }})
                  ::(G', {{s#"env"}})
                  ::c in
      let lhs := {{e #subst_constr G' G g {A} {blank_term} }} in
      @!let rhs_subterms <- gen_rhs_subterms G' G g c in
      let rhs := con name rhs_subterms in
      let t' := scon s_name [{{e#"ty_subst" G' G g {A} }}; var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      (Some (append name " subst",subst_rule))
  (*TODO: duplicated work for blocks since there is no A*)
  | [var G] =>
      let c' := (g,{{s#"sub" G' G }})
                  ::(G', {{s#"env"}})
                  ::c in
      let lhs := {{e #subst_constr G' G g {blank_term} }} in
      @!let rhs_subterms <- gen_rhs_subterms G' G g c in
      let rhs := con name rhs_subterms in
      let t' := scon s_name [var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      (Some (append name " subst",subst_rule))
  | _ => None
  end.

Ltac gen_subst :=
  lazymatch goal with
    |- wf_lang_ext ((?n,term_rule ?c _ ?t)::_) _ =>
      let mrule := eval vm_compute in
      (substable_constr n c t)
        in
        lazymatch mrule with
        | Some ?rule => push_rule rule
        | None => fail "Failed to generate substitution rule. TODO: improve message"
        end
  end.

