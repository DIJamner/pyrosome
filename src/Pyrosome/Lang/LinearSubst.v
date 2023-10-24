Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
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


Definition linear_value_subst_def : lang :=
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
       #"id" "G" : #"sub" "G" "G"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" "G1" "G3"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" (#"id" "G'") = "f" : #"sub" "G" "G'"
  ];
  [:= "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" (#"id" "G") "f" = "f" : #"sub" "G" "G'"
  ];
  [:= "G1" : #"env",
      "G2" : #"env",
      "G3" : #"env",
      "G4" : #"env",
      "f" : #"sub" "G1" "G2",
      "g" : #"sub" "G2" "G3",
      "h" : #"sub" "G3" "G4"
      ----------------------------------------------- ("cmp_assoc")
      #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h"
      : #"sub" "G1" "G4"
  ];
  [s|
      -----------------------------------------------
      #"ty" srt
  ];
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"val" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty", "v" : #"val" "G'" "A"
       -----------------------------------------------
       #"val_subst" "g" "v" : #"val" "G" "A"
  ];
  [:= "G" : #"env", "A" : #"ty", "e" : #"val" "G" "A"
       ----------------------------------------------- ("val_subst_id")
       #"val_subst" (#"id" "G") "e" = "e" : #"val" "G" "A"
  ];
  [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty", "v" : #"val" "G3" "A"
       ----------------------------------------------- ("val_subst_cmp")
       #"val_subst" "f" (#"val_subst" "g" "v")
       = #"val_subst" (#"cmp" "f" "g") "v"
       : #"val" "G1" "A"
  ];

  [:| -----------------------------------------------
      #"emp" : #"env"
  ];
  [:| "G" : #"env", "A": #"ty"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ];

  [:| "G": #"env", "H": #"env"
      -----------------------------------------------
      #"conc" "G" "H": #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("conc_emp")
      #"conc" "G" #"emp" = "G" : #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("emp_conc")
      #"conc" #"emp" "G" = "G" : #"env"
  ];
  [:= "G": #"env", "H": #"env", "A": #"ty"
      ----------------------------------------------- ("conc_ext_right")
      #"conc" "G" (#"ext" "H" "A") =
      #"ext" (#"conc" "G" "H") "A" : #"env"
  ];
  [:= "G1": #"env", "G2": #"env", "G3": #"env"
      ----------------------------------------------- ("conc_assoc")
      #"conc" (#"conc" "G1" "G2") "G3" =
      #"conc" "G1" (#"conc" "G2" "G3") : #"env"

  ];

  [:| "G": #"env", "G'": #"env",
      "H": #"env", "H'": #"env",
      "g": #"sub" "G" "G'",
      "h": #"sub" "H" "H'"
      -----------------------------------------------
      #"csub" "g" "h":
      #"sub" (#"conc" "G" "H") (#"conc" "G'" "H'")
  ];
  [:= "G": #"env", "G'": #"env",
      "g": #"sub" "G" "G'"
      ----------------------------------------------- ("csub_emp")
      #"csub" "g" (#"id" #"emp") = "g":
      #"sub" "G" "G'"
  ];
  [:= "G": #"env", "H": #"env"
      ----------------------------------------------- ("csub_id")
      #"csub" (#"id" "G") (#"id" "H") = #"id" (#"conc" "G" "H") :
      #"sub" (#"conc" "G" "H") (#"conc" "G" "H")
  ];
  [:= "G1": #"env", "G1'": #"env", "g1": #"sub" "G1" "G1'",
      "G2": #"env", "G2'": #"env", "g2": #"sub" "G2" "G2'",
      "G3": #"env", "G3'": #"env", "g3": #"sub" "G3" "G3'"
      ----------------------------------------------- ("csub_assoc")
      #"csub" (#"csub" "g1" "g2") "g3" =
      #"csub" "g1" (#"csub" "g2" "g3") :
      #"sub" (#"conc" "G1" (#"conc" "G2" "G3"))
             (#"conc" "G1'" (#"conc" "G2'" "G3'"))

  ];
  [:= "G1": #"env", "G2": #"env", "G3": #"env",
      "H1": #"env", "H2": #"env", "H3": #"env",
      "g1": #"sub" "G1" "G2", "g2": #"sub" "G2" "G3",
      "h1": #"sub" "H1" "H2", "h2": #"sub" "H2" "H3"
      ----------------------------------------------- ("csub_subst_cmp")
      #"csub" (#"cmp" "g1" "g2") (#"cmp" "h1" "h2") =
      #"cmp" (#"csub" "g1" "h1") (#"csub" "g2" "h2"):
      #"sub" (#"conc" "G1" "H1") (#"conc" "G3" "H3")
  ];

  [:|  "A" : #"ty"
       -----------------------------------------------
       #"hd" "A" : #"val" (#"ext" #"emp" "A") "A"
  ];

  [:| "G" : #"env",
      "A" : #"ty",
      "v" : #"val" "G" "A" (*we restrict substitutions to values *)
       -----------------------------------------------
       #"vsub" "v" : #"sub" "G" (#"ext" #"emp" "A")
  ];

  [:= "A" : #"ty"
      ----------------------------------------------- ("vsub_hd")
      #"vsub" (#"hd" "A") = #"id" (#"ext" #"emp" "A") :
      #"sub" (#"ext" #"emp" "A") (#"ext" #"emp" "A")
  ];

  (* explicit substitution for env*)
  (* [:= "G": #"env", "H": #"env",
      "X": #"env", "Y": #"env"
      ----------------------------------------------- ("env_exch")
      #"conc" (#"conc" (#"conc" "G" "X") "Y") "H" =
      #"conc" (#"conc" (#"conc" "G" "Y") "X") "H" : #"env"
  ]; *)
  [:| "G": #"env", "X": #"env", "Y": #"env", "H": #"env"
      -----------------------------------------------
      #"exch" "G" "X" "Y" "H":
      #"sub" (#"conc" (#"conc" (#"conc" "G" "X") "Y") "H")
             (#"conc" (#"conc" (#"conc" "G" "Y") "X") "H")
  ];
  [:= "G": #"env", "X": #"env", "Y": #"env", "H": #"env",
      "G'": #"env", "X'": #"env", "Y'": #"env", "H'": #"env",
      "g": #"sub" "G" "G'",
      "x": #"sub" "X" "X'",
      "y": #"sub" "Y" "Y'",
      "h": #"sub" "H" "H'"
      ----------------------------------------------- ("exch_cmp")
      #"cmp" (#"exch" "G" "X" "Y" "H")
             (#"csub" (#"csub" (#"csub" "g" "y") "x" ) "h") =
      #"cmp" (#"csub" (#"csub" (#"csub" "g" "x") "y" ) "h")
             (#"exch" "G'" "X'" "Y'" "H'") :
      #"sub" (#"conc" (#"conc" (#"conc" "G" "X") "Y") "H")
             (#"conc" (#"conc" (#"conc" "G'" "Y'") "X'") "H'")
  ]
  (* [:= "G": #"env", "H": #"env",
      "V": #"env", "W": #"env",
      "A": #"ty", "B": #"ty",
      "v": #"val" "V" "A",
      "w": #"val" "W" "B"
      ----------------------------------------------- ("snoc_exch")
      #"cmp" (#"csub" (#"snoc" (#"snoc" #"id" "v") "w") #"id")
             (#"exch" "G" "H" "A" "B") =
      #"csub" (#"snoc" (#"snoc" #"id" "w") "v") #"id" :
      #"sub" (#"conc" (#"conc" (#"conc" "G" "V") "W") "H")
             (#"conc" (#"ext" (#"ext" "G" "B") "A") "H")
  ] *)

  ]}.

#[export] Hint Resolve (inst_for_db "emp") : injective_con.
#[export] Hint Resolve (inst_for_db "ext") : injective_con.
#[export] Hint Resolve (inst_for_db "vsub") : injective_con.

(*TODO: use elab_lang notation?*)
Derive linear_value_subst
       SuchThat (elab_lang_ext [] linear_value_subst_def linear_value_subst)
       As linear_value_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve linear_value_subst_wf : elab_pfs.


Definition linear_exp_subst_def : lang :=
  {[l
    [s| "G" : #"env", "A" : #"ty"
        -----------------------------------------------
        #"exp" "G" "A" srt
    ];
    [:| "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
        "A" : #"ty", "e" : #"exp" "G'" "A"
        -----------------------------------------------
        #"exp_subst" "g" "e" : #"exp" "G" "A"
    ];
    [:= "G" : #"env", "A" : #"ty", "e" : #"exp" "G" "A"
        ----------------------------------------------- ("exp_subst_id")
        #"exp_subst" (#"id" "G") "e" = "e" : #"exp" "G" "A"
    ];
    [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
        "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
        "A" : #"ty", "e" : #"exp" "G3" "A"
        ----------------------------------------------- ("exp_subst_cmp")
        #"exp_subst" "f" (#"exp_subst" "g" "e")
        = #"exp_subst" (#"cmp" "f" "g") "e"
        : #"exp" "G1" "A"
    ];
    [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
        -----------------------------------------------
        #"ret" "v" : #"exp" "G" "A"
    ];
    [:= "G1" : #"env", "G2" : #"env",
        "g" : #"sub" "G1" "G2",
        "A" : #"ty", "v" : #"val" "G2" "A"
        ----------------------------------------------- ("exp_subst_ret")
        #"exp_subst" "g" (#"ret" "v")
        = #"ret" (#"val_subst" "g" "v")
        : #"exp" "G1" "A"
    ]
  ]}.


Derive linear_exp_subst
       SuchThat (elab_lang_ext linear_value_subst linear_exp_subst_def linear_exp_subst)
       As linear_exp_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve linear_exp_subst_wf : elab_pfs.

Definition linear_block_subst_def : lang :=
  {[l
    [s| "G" : #"env"
        -----------------------------------------------
        #"blk" "G" srt
    ];
    [:| "G" : #"env", "G'" : #"env",
        "g" : #"sub" "G" "G'",
        "e" : #"blk" "G'"
        -----------------------------------------------
        #"blk_subst" "g" "e" : #"blk" "G"
    ];
    [:= "G" : #"env", "e" : #"blk" "G"
        ----------------------------------------------- ("blk_subst_id")
        #"blk_subst" (#"id" "G") "e" = "e" : #"blk" "G"
    ];
    [:= "G1" : #"env", "G2" : #"env", "G3" : #"env",
        "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
         "e" : #"blk" "G3"
        ----------------------------------------------- ("blk_subst_cmp")
        #"blk_subst" "f" (#"blk_subst" "g" "e")
        = #"blk_subst" (#"cmp" "f" "g") "e"
        : #"blk" "G1"
    ]
  ]}.


Derive linear_block_subst
       SuchThat (elab_lang_ext linear_value_subst linear_block_subst_def linear_block_subst)
       As linear_block_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve linear_block_subst_wf : elab_pfs.

Definition definitely_fresh (s : string) (l : list string) :=
  let len := List.fold_left Nat.max (map String.length l) 0 in
  String.append s (string_of_list_ascii (repeat ("'"%char : ascii) len)).

Definition choose_fresh (s : string) (c : ctx) :=
  if negb (inb s (map fst c)) then s else definitely_fresh s (map fst c).

Definition only t := {{e #"ext" #"emp" {t} }}.

Definition under s t :=
  {{e #"csub" {s} (#"id" {only t})}}.

Definition get_subst_constr s :=
  match s with
  | "blk" => Some "blk_subst"
  | "exp" => Some "exp_subst"
  | "val" => Some "val_subst"
  | _ => None
  end.

Fixpoint subst_for Gs gs G' :=
    match Gs, gs with
    | G::Gs', g::gs' =>
      if G =? G'
      then var g
      else subst_for Gs' gs' G'
    | _, _ => {{e#"ERR1"}}
    end.


Section GenRHSSubterms.
  Context (Gs : list string)
          (gs : list string).

  (*TODO: careful! _ in patterns does bad things (treated as a var)
   document &/or fix *)
  Fixpoint gen_arg_subst s :=
    match s with
    | {{e#"emp"}} => {{e #"id" #"emp"}}
    | var G' => subst_for Gs gs G'
    | {{e#"ext" {s'} {t} }} => under (gen_arg_subst s') t
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

Fixpoint get_envs G :=
    match G with
    | var H => [H]
    | {{e#"conc" {H1} {H2} }} => get_envs H1 ++ get_envs H2
    | _ => []
    end.

Definition lower_ascii a :=
    ascii_of_nat (nat_of_ascii a + 32).

Fixpoint lower G :=
    match G with
    | "" => ""
    | String a s => String (lower_ascii a) (lower s)
    end.

Fixpoint make_fresh_subs Gs c :=
    match Gs with
    | [] => ([], [], c)
    | G::Gs' =>
      let G' := choose_fresh (G ++ "'") c in
      let g  := choose_fresh (lower G) c in
      let c' := (g,{{s#"sub" G' G}})
                  ::(G', {{s#"env"}})
                  ::c in
      let '(G's', gs', c'') := make_fresh_subs Gs' c' in
      (G'::G's', g::gs', c'')
    end.

Fixpoint make_g G gs :=
    match G, gs with
    | var H, h::gs' => ({{e h}}, gs')
    | {{e#"conc" {H1} {H2} }}, _ =>
        let (h1, gs') := make_g H1 gs in
        let (h2, gs'') := make_g H2 gs' in
        ({{e#"csub" {h1} {h2} }}, gs'')
    | _, _ => ({{e#"ERR3" }}, [])
    end.

(* TODO: don't reduplicate code *)
Fixpoint make_G' G G's :=
    match G, G's with
    | var H, H'::G's' => ({{e H'}}, G's')
    | {{e#"conc" {H1} {H2} }}, _ =>
        let (H1', G's') := make_G' H1 G's in
        let (H2', G's'') := make_G' H2 G's' in
        ({{e#"conc" {H1'} {H2'} }}, G's'')
    | _, _ => ({{e#"ERR3" }}, [])
    end.

Definition substable_constr name c args t : option lang :=
  match t with
  | scon s [A; G] =>
    match get_subst_constr s with
    | Some subst_constr =>
      let constr_rule := term_rule c args t in
      let Gs := get_envs G in
      let '(G's, gs, c') := make_fresh_subs Gs c in
      let (g, _) := make_g G gs in
      let (G', _) := make_G' G G's in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr {g} {blank_term} }} in
      let rhs := con name (gen_rhs_subterms Gs gs c args) in
      let t' := scon s [A; G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  | _ => None
  end.

Definition sc '(n,r) :=
  match r with
  | term_rule c args t =>
   match substable_constr n c args t with
   | Some l => l
   | None => [(n,r)]
   end
  | r => [(n,r)]
  end.

Notation "'{[l/lin_subst' r1 ; .. ; r2 ]}" :=
  (List.flat_map sc (cons r2 .. (cons r1 nil) ..))%rule
  (format "'[' {[l/lin_subst '[hv' r1 ; '/' .. ; '/' r2 ']' ]} ']'") : lang_scope.

