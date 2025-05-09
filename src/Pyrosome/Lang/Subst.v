Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).


Definition subst_def : lang :=
  {[l   
  [s|
      -----------------------------------------------
      #"env" srt
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      #"sub" "G" "G'" srt                     
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       #"id" : #"sub" "G" "G"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" "G1" "G3"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" #"id" = "f" : #"sub" "G" "G'"
  ]; 
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"sub" "G" "G'"
  ];
   [:= "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" "G1" "G2",
         "g" : #"sub" "G2" "G3",
         "h" : #"sub" "G3" "G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h" : #"sub" "G1" "G4"
  ]; 
  [s| "G" : #"env" 
      -----------------------------------------------
      #"ty" "G" srt
  ];

  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty" "G'"
       -----------------------------------------------
       #"ty_subst" "g" "A" : #"ty" "G"
  ];
  [:= "G" : #"env", "A" : #"ty" "G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" "A" = "A" : #"ty" "G"
  ]; 
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty" "G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" "f" (#"ty_subst" "g" "A")
       = #"ty_subst" (#"cmp" "f" "g") "A"
       : #"ty" "G1"
  ];



    
  [s| "G" : #"env", "A" : #"ty" "G"
      -----------------------------------------------
      #"exp" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty" "G'", "v" : #"exp" "G'" "A"
       -----------------------------------------------
       #"exp_subst" "g" "v" : #"exp" "G" (#"ty_subst" "g" "A")
  ];
  [:= "G" : #"env", "A" : #"ty" "G", "v" : #"exp" "G" "A"
       ----------------------------------------------- ("exp_subst_id")
       #"exp_subst" #"id" "v" = "v" : #"exp" "G" "A"
  ]; 
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty" "G3", "v" : #"exp" "G3" "A"
       ----------------------------------------------- ("exp_subst_cmp")
       #"exp_subst" "f" (#"exp_subst" "g" "v")
       = #"exp_subst" (#"cmp" "f" "g") "v"
       : #"exp" "G1" (#"ty_subst" (#"cmp" "f" "g") "A")
  ];

    
  [:| 
      -----------------------------------------------
      #"emp" : #"env"
  ];
  [:| "G" : #"env" 
      -----------------------------------------------
      #"forget" : #"sub" "G" #"emp"
  ];
  [:= "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" "g" #"forget" = #"forget" : #"sub" "G" #"emp"
  ];
  [:= 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ];
  [:| "G" : #"env", "A": #"ty" "G"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty" "G'",
      "g" : #"sub" "G" "G'",
      "v" : #"exp" "G" (#"ty_subst" "g" "A") (*we restrict substitutions to values *)
       -----------------------------------------------
       #"snoc" "g" "v" : #"sub" "G" (#"ext" "G'" "A")
  ];

  [:| "G" : #"env", "A" : #"ty" "G"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" "G" "A") "G"
  ];
  [:| "G" : #"env", "A" : #"ty"("G")
       -----------------------------------------------
       #"hd" : #"exp" (#"ext" "G" "A") (#"ty_subst" #"wkn" "A")
  ];
  [:= "G" : #"env", "G'" : #"env",
      "g" : #"sub" "G" "G'",
      "A" : #"ty" "G'",
      "v" : #"exp" "G" (#"ty_subst" "g" "A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" "g" "v") #"wkn" = "g" : #"sub" "G" "G'"
  ];
   [:= "G" : #"env", "G'" : #"env",
       "g" : #"sub" "G" "G'",
       "A" : #"ty" "G'",
       "v" : #"exp" "G" (#"ty_subst" "g" "A")
       ----------------------------------------------- ("snoc_hd")
       #"exp_subst" (#"snoc" "g" "v") (@"hd" @("A":= "A")) = "v"
       : #"exp" "G" (#"ty_subst" "g" "A")
  ];
   [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3",
       "A" : #"ty" "G3",
       "v" : #"exp" "G2" (#"ty_subst" "g" "A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" "f" (#"snoc" "g" "v")
       = #"snoc" (#"cmp" "f" "g") (#"exp_subst" "f" "v")
       : #"sub" "G1" (#"ext" "G3" "A")
   ];
    
    [:= "G" : #"env", "A" : #"ty" "G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"snoc" #"wkn" #"hd" = #"id" : #"sub" (#"ext" "G" "A") (#"ext" "G" "A")
   ]
  ]}.

#[local] Definition id_inst_for_db := inst_for_db "id".
#[export] Hint Resolve id_inst_for_db : injective_con.
#[local] Definition emp_inst_for_db := inst_for_db "emp".
#[export] Hint Resolve emp_inst_for_db : injective_con.
#[local] Definition forget_inst_for_db := inst_for_db "forget".
#[export] Hint Resolve forget_inst_for_db : injective_con.
#[local] Definition ext_inst_for_db := inst_for_db "ext".
#[export] Hint Resolve ext_inst_for_db : injective_con.
#[local] Definition snoc_inst_for_db := inst_for_db "snoc".
#[export] Hint Resolve snoc_inst_for_db : injective_con.
#[local] Definition wkn_inst_for_db := inst_for_db "wkn".
#[export] Hint Resolve wkn_inst_for_db : injective_con.
#[local] Definition hd_inst_for_db := inst_for_db "hd".
#[export] Hint Resolve hd_inst_for_db : injective_con.

Derive subst_lang
       SuchThat (elab_lang_ext [] subst_def subst_lang)
       As subst_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve subst_lang_wf : elab_pfs.

(*TODO: code duplication across various substitution languages; fix *)

Fixpoint notinb (s : string) (l : list string) :=
  match l with
  | [] => true
  | s'::l' => if eqb s s' then false else notinb s l'
  end.

Definition definitely_fresh (s : string) (l : list string) :=
  let len := List.fold_left Nat.max (map String.length l) 0 in
  String.append s (string_of_list_ascii (repeat ("'"%char : ascii) len)).

Definition choose_fresh (s : string) (c:ctx) :=
  if notinb s (map fst c) then s else definitely_fresh s (map fst c).

(*TODO: duplicated*)
Definition under s :=
  {{e #"snoc" (#"cmp" #"wkn" {s}) #"hd"}}.

Definition get_subst_constr s :=
  match s with
  | "exp" => Some "exp_subst"
  | "ty" => Some "ty_subst"
  | _ => None
  end.

Section GenRHSSubterms.
  Context (G : string)
          (g : string).

  (*TODO: careful! _ in patterns does bad things (treated as a var)
   document &/or fix *)
  Fixpoint gen_arg_subst s :=
    match s with
    | {{e#"emp"}} => {{e#"forget"}}
    | var G' => if G =? G' then var g else {{e#"ERR1"}}
    | {{e#"ext" {s'} {_} }} => under (gen_arg_subst s')
    | _ => {{e#"ERR2" {s} }}
    end.
  
  Fixpoint gen_rhs_subterms c args {struct c} :=
    match c, args with
    | (n1,t)::c', n2::args' =>
      if n1 =? n2
      then
        match t with
        | scon name [G']
        | scon name [_;G'] =>
          match get_subst_constr name with
          | Some subst_constr =>
            let s := gen_arg_subst G' in
            let e := {{e #subst_constr {s} n1 }} in
            e::(gen_rhs_subterms c' args')
          | _ => (var n1)::(gen_rhs_subterms c' args')
          end
        | _ => (var n1)::(gen_rhs_subterms c' args')
        end
      else gen_rhs_subterms c' args
    | _, _ => []
    end.
End GenRHSSubterms.

Definition substable_constr name c args t : option lang :=
  match t with
  (*TODO: assumes arbitrary G below the line. Is that the behavior I want or can I generalize?*)
  | scon s [A; var G] =>
    match get_subst_constr s with
    | Some subst_constr =>      
      let constr_rule := term_rule c args t in
      let G' := choose_fresh "G'" c in
      let g := choose_fresh "g" c in
      let c' := (g,{{s#"sub" G' G }})
                  ::(G', {{s#"env"}})
                  ::c in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr g {blank_term} }} in
      let rhs := con name (gen_rhs_subterms G g c args) in
      let t' := scon s [{{e#"ty_subst" g {A} }}; var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  (*TODO: duplicated work for blocks since there is no A*)
  | scon s [var G] =>
    match get_subst_constr s with
    | Some subst_constr =>      
      let constr_rule := term_rule c args t in
      let G' := choose_fresh "G'" c in
      let g := choose_fresh "g" c in
      let c' := (g,{{s#"sub" G' G }})
                  ::(G', {{s#"env"}})
                  ::c in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr g {blank_term} }} in
      let rhs := con name (gen_rhs_subterms G g c args) in
      let t' := scon s [var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  | _ => None
  end.

Definition sc '(n,r) :=
  match r with
  |term_rule c args t =>
   match substable_constr n c args t with
   | Some l => l
   | None => [(n,r)]
   end
  | r => [(n,r)]
  end.


Notation "'{[l/subst' r1 ; .. ; r2 ]}" :=
  (List.flat_map sc (cons r2 .. (cons r1 nil) ..))%rule
  (format "'[' {[l/subst '[hv' r1 ; '/' .. ; '/' r2 ']' ]} ']'") : lang_scope.
