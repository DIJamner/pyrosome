Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Exp Rule ARule Tactics Decidable.
From Named Require ICore.
Import ICore.IndependentJudgment.
Import Exp.Notations ARule.Notations. (* TODO: Rule.Notations.*)
Require Import String.

Require Import Named.Recognizers.

Set Default Proof Mode "Ltac2".




(*Notation ob := (con 0 [::]).
Notation hom a b := (con 1 [:: b; a]%exp_scope).
Notation id a := (con 2 [:: a]%exp_scope).
Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).*)       

(* syntax of categories *)
Definition cat_lang : lang :=
  [::
     [:> "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" %"G1" %"G2",
         "g" : #"sub" %"G2" %"G3",
         "h" : #"sub"%"G3" %"G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" %"f" (#"cmp" %"g" %"h") = #"cmp" (#"cmp" %"f" %"g") %"h" : #"sub" %"G1" %"G4"
  ];  
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" %"f" = %"f" : #"sub" %"G"%"G'"
  ];
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
      ----------------------------------------------- ("id_right")
      #"cmp" %"f" #"id" = %"f" : #"sub" %"G" %"G'"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" %"G1" %"G3"
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       #"id" : #"sub" %"G" %"G"
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      #"sub" "G" "G'" srt                     
  ];
  [s|
      -----------------------------------------------
      #"env" srt
  ]
  ]%arule.

Section InferSub.

  Context (subst_lang_el_ty : ctx -> exp (*G*) -> exp (*e*) -> exp).

  
  Fixpoint sub_decompose g f : exp :=
    if f == g then {{e #"id"}}
    else match f with
         | con "cmp" [:: h; f'] =>
           {{e #"cmp" {sub_decompose g f'} {h} }}
         | _ => {{e #"ERR"}}
         end.

  (*Only works sometimes; not guaranteed to be correct *)
  Definition ty_decompose g A :=
    if g == {{e #"id"}} then A
    else match A with
         | con "ty_subst" [:: A; g'] =>
           {{e #"ty_subst" {sub_decompose g g'} {A} }}
         | _ => {{e #"ERR: ty_decompose"}}
         end.

  Fixpoint cat_lang_sub_r c e G_l : exp :=
    match e with
    | con "id" [::] => G_l
    | con "cmp" [:: g; f] =>
      let G_lf := cat_lang_sub_r c f G_l in
      let G_lg := cat_lang_sub_r c g G_lf in
      G_lg
    | con "wkn" [::] =>
      match G_l with
      | con "ext" [:: _;G_r] => G_r
      | _ => {{e #"ERR"}}
      end
    | con "snoc" [:: e; f] =>
      let G' := cat_lang_sub_r c f G_l in
      let Af := subst_lang_el_ty c G' e in
      {{e #"ext" {G'} {ty_decompose f Af} }}
    | var x =>
      match named_list_lookup {{s #"ERR"}} c x with
      | scon "sub" [:: G; _] => G
      | _ => {{e #"ERR"}}
      end
    | _ => {{e #"ERR"}}
    end.

End InferSub.
  
Fixpoint subst_lang_el_ty c G e : exp :=
  match e,G with
  | var x,_ => 
    match named_list_lookup {{s #"ERR not in c"}} c x with
    | scon "el" [:: t; _] => t
    | _ => {{e #"ERR sort from c not in subst lang"}}
    end
  | con "hd" [::], con "ext" [:: A; G'] =>
    {{e #"ty_subst" #"wkn" %"A" }}
  | con "el_subst" [:: e'; g], _ =>
    let G' := cat_lang_sub_r subst_lang_el_ty c g G in
    let A := subst_lang_el_ty c G' e' in
    {{e #"ty_subst" {g} {A} }}
  | _, _ => {{e #"ERR: not in subst lang" }}
  end.


Instance rec_cat_lang : LangRecognize cat_lang :=
  { le_sort_dec := generic_sort_dec_fuel 10 cat_lang;
    decide_le_sort := @generic_decide_le_sort 10 cat_lang;
    term_args_elab c s name t := 
      match name, t, s with
      | "id", scon "sub" [:: _; G],_ => [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r subst_lang_el_ty c f G1 in
        [:: g; f; G3; G2; G1]
      | _,_,_ => s
      end%string;
    sort_args_elab c s _ := s
  }.

Lemma cat_lang_wf : wf_lang cat_lang.
Proof.
  apply (@decide_wf_lang _ _ 100).
  vm_compute; reflexivity.
Qed.

Definition subst_lang' : lang :=
 [::[:> 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ];
  [:> "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" %"g" #"forget" = #"forget" : #"sub" %"G" #"emp"
  ];
  [:| "G" : #"env" 
      -----------------------------------------------
      #"forget" : #"sub" %"G" #"emp"
  ];
  [:| 
      -----------------------------------------------
      #"emp" : #"env"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3", "e" : #"el" %"G3" %"A"
       ----------------------------------------------- ("el_subst_cmp")
       #"el_subst" %"f" (#"el_subst" %"g" %"e")
       = #"el_subst" (#"cmp" %"f" %"g") %"e"
       : #"el" %"G1" (#"ty_subst" (#"cmp" %"f" %"g") %"A")
  ]; 
  [:> "G" : #"env", "A" : #"ty" %"G", "e" : #"el" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"el" %"G" %"A"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" %"f" (#"ty_subst" %"g" %"A")
       = #"ty_subst" (#"cmp" %"f" %"g") %"A"
       : #"ty" %"G1"
  ];              
  [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" %"A" = %"A" : #"ty" %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'", "e" : #"el" %"G'" %"A"
       -----------------------------------------------
       #"el_subst" "g" "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
  ];
  [s| "G" : #"env", "A" : #"ty"(%"G")
      -----------------------------------------------
      #"el" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'"
       -----------------------------------------------
       #"ty_subst" "g" "A" : #"ty" %"G"
  ];
  [s| "G" : #"env" 
      -----------------------------------------------
      #"ty" "G" srt
  ]]%arule++cat_lang.


Instance rec_subst_lang' : LangRecognize subst_lang' :=
  {  le_sort_dec := generic_sort_dec_fuel 10 subst_lang';
    decide_le_sort := @generic_decide_le_sort 10 subst_lang';
    term_args_elab c s name t := 
      match name, t, s with
      | "forget", scon "sub" [:: _; G],_ => [:: G]
      | "id", scon "sub" [:: _; G],_ => [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r subst_lang_el_ty c f G1 in
        [:: g; f; G3; G2; G1]
      | "ty_subst", scon "ty" [:: G], [:: A; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        [:: A; g; G'; G]
      | "el_subst", scon "el" [:: (con "ty_subst" [:: A; f]); G], [:: e; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        (* need to pull a g substitution off of f;
           first run f to simplify
         *)
        let f' := term_par_step_n subst_lang' f 100 in
        let f'' := sub_decompose g f' in
        [:: e; (con "ty_subst" [:: A; f'']); g; G'; G]
      (* special case for id subst since it can disappear; only works if g ~ id*)
      | "el_subst", scon "el" [:: A; G], [:: e; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        (* need to pull a g substitution off of f;
           first run f to simplify
         *)
        [:: e; A; g; G'; G]
      | _,_,_ => s
      end%string;
    sort_args_elab c s _ := s
  }.
    


Lemma subst_lang'_wf : wf_lang subst_lang'.
Proof.
  apply (@decide_wf_lang _ _ 100); vm_compute; reflexivity.
Qed.


Definition subst_lang : lang :=
   [::[:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"id" = #"snoc" #"wkn" #"hd" : #"sub" (#"ext" %"G" %"A") (#"ext" %"G" %"A")
   ];
   [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3",
       "e" : #"el" %"G2" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" %"f" (#"snoc" %"g" %"e")
       = #"snoc" (#"cmp" %"f" %"g") (#"el_subst" %"f" %"e")
       : #"sub" %"G1" (#"ext" %"G3" %"A")
   ];
   [:> "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'",
       "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("snoc_hd")
       #"el_subst" (#"snoc" %"g" %"e") #"hd" = %"e"
       : #"el" %"G" (#"ty_subst" %"g" %"A")
  ];
  [:> "G" : #"env", "G'" : #"env",
      "g" : #"sub" %"G" %"G'",
      "A" : #"ty" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" %"g" %"e") #"wkn" = %"g" : #"sub" %"G" %"G'"
  ];
  [:| "G" : #"env", "A" : #"ty"(%"G")
       -----------------------------------------------
       #"hd" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"A")
  ];
  [:| "G" : #"env", "A" : #"ty" %"G"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" %"G" %"A") %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty" %"G'",
      "g" : #"sub" %"G" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       -----------------------------------------------
       #"snoc" "g" "e" : #"sub" %"G" (#"ext" %"G'" %"A")
  ];
  [:| "G" : #"env", "A": #"ty" %"G"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
   ]]%arule++subst_lang'.
 
Instance rec_subst_lang : LangRecognize subst_lang :=
  {  le_sort_dec := generic_sort_dec_fuel 10 subst_lang;
    decide_le_sort := @generic_decide_le_sort 10 subst_lang;
    term_args_elab c s name t := 
      match name, t, s with
      | "forget", scon "sub" [:: _; G],_ => [:: G]
      | "id", scon "sub" [:: _; G],_ => [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r subst_lang_el_ty c f G1 in
        [:: g; f; G3; G2; G1]
      | "ty_subst", scon "ty" [:: G], [:: A; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        [:: A; g; G'; G]
      | "el_subst", scon "el" [:: _; G], [:: e; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        let A := subst_lang_el_ty c G' e in
        [:: e; A; g; G'; G]
      | "snoc", scon "sub" [:: con "ext" [:: A; G']; G], [:: e; g] =>
        [:: e; g; A; G'; G]
      | "wkn", scon "sub" [:: G; con "ext" [:: A; _]], [::] =>
        [:: A; G]
      | "hd", scon "el" [:: _; con "ext" [:: A; G]], [::] =>
        [:: A; G]
      | _,_,_ => s
      end%string;
    sort_args_elab c s _ := s
  }.
  
Lemma subst_lang_wf : wf_lang subst_lang.
Proof.
  apply (@decide_wf_lang _ _ 100).
  vm_compute.
  reflexivity.
Qed.
