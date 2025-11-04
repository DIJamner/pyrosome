Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.
From Pyrosome.Lang Require Import SimpleVSTLC. 
(* From Pyrosome.Lang Require Import UTLC. 
(* think I need to run make command (for just this file ideally) *)
 *)

(* Compute value_subst_def. 
Locate term.  *)
Definition utlc_bool_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env"
      -----------------------------------------------
      #"uT" : #"val" "G" #"*"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"uF" : #"val" "G" #"*"
  ];
  [:| "G" : #"env",
      "e" : #"exp" "G" #"*"
      -----------------------------------------------
      #"bool?" "e" : #"exp" "G" #"*"
  ];
  [:=
      ----------------------------------------------- ("bool?-true")
      #"bool?" (#"ret" #"uT") 
      = #"ret" #"uT" : #"exp" "G" #"*"
  ];
  [:=
      ----------------------------------------------- ("bool?-false")
      #"bool?" (#"ret" #"uF") 
      = #"ret" #"uT" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*"
      ----------------------------------------------- ("bool?-func")
      #"bool?" (#"ulambda" "e") 
      = #"ret" #"uF" : #"exp" "G" #"*"
  ];
  [:| "G" : #"env",
      "cond" : #"exp" "G" #"*",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      -----------------------------------------------
      #"uif" "cond" "e2" "e3" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      ----------------------------------------------- ("uif-true")
      #"uif" (#"ret" #"uT") "e2" "e3" 
      = "e2" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      ----------------------------------------------- ("uif-false")
      #"uif" (#"ret" #"uF") "e2" "e3" 
      = "e3" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      ----------------------------------------------- ("uif-func")
      #"uif" (#"ret" #"ulambda" #"e") "e2" "e3" 
      = "e3" : #"exp" "G" #"*"
  ] (* alternative: error expression. What to do when error gets to typed context?
        Have to be able to have any type *)
  ]}.

Derive utlc_bool
       SuchThat (elab_lang_ext (utlc++exp_subst++value_subst) utlc_bool_def utlc_bool)
       As utlc_bool_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_bool_wf : elab_pfs.


Definition mlc_bool_def : lang :=
  {[l/subst [exp_subst++value_subst] 
  [:| "G" : #"env",
      "A" : #"ty",
      "cond" : #"exp" "G" #"*",
      "e2" : #"exp" "G" "A",
      "e3" : #"exp" "G" "A"
      -----------------------------------------------
      #"uif" "cond" "e2" "e3" : #"exp" "G" "A"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      ----------------------------------------------- ("mif-true")
      #"uif" (#"ret" #"uT") "e2" "e3" 
      = "e2" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      ----------------------------------------------- ("mif-false")
      #"uif" (#"ret" #"uF") "e2" "e3" 
      = "e3" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      ----------------------------------------------- ("mif-func")
      #"uif" (#"ret" #"ulambda" #"e") "e2" "e3" 
      = "e3" : #"exp" "G" #"*"
  ] (* alternative: error expression. What to do when error gets to typed context?
        Have to be able to have any type *)
    (* EXAMPLES OF TYPE CASING *)
    [:| "G" : #"env",
        "cond" : #"ty",
        "A" : #"ty",
        "e1" : #"exp" "G" "A",
        "e2" : #"exp" "G" "A",
        "e3" : #"exp" "G" "A"
        -----------------------------------------------
        #"type case" "cond" "e1" "e2" "e3"  : #"exp" "G" "A"
    ];
    [:= "G" : #"env",
        "cond" : #"ty",
        "A" : #"ty",
        "e1" : #"exp" "G" "A",
        "e2" : #"exp" "G" "A",
        "e3" : #"exp" "G" "A"
        ----------------------------------------------- ("type case bool")
        #"type case" #"bool" "e1" "e2" "e3"  
        = "e2" : #"exp" "G" "A"
    ]
  ]}.
(* CHANGEHGANGEHGANGEHGANGE *)
Derive utlc_bool
        SuchThat (elab_lang_ext (utlc++exp_subst++value_subst) utlc_bool_def utlc_bool)
        As utlc_bool_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_bool_wf : elab_pfs.
(* accompanying story: boundaries aren't really necessary to do multilanguages
because they can be expressed in terms of more primitive features, but we can do mif *)

(* story: we have the uif, and then we can just compile to mif *)

(* so make new language with these below in the object language. That's gonna be the boundary language *)
(* equations will look a lot like matthews and findler eqns. Start with lump embedding stuff *)
(* lump embedding is 12:5, says like boundaries cancel *)
(* only rule for expression boundary is boundary_e ret is same as ret boundary_v *)
(* for value boundary, say that cancel if types are the same *)
(* what to do with not matched boundary? raise error (see paper notes) *)

(* compiler will be type case—doing a case on the type—looks similar to the below but in the object language *)

(* high level multilanguage which has boundaries—has set of eqns that fully describe the boundaries *)
(* low level multilanguage which has type cases—this is the one with mif *)


(* everytyhig will be v boudnaries (evantuaully) *)
Definition dtt_e {G : term} (x : term) (Ty : term) : Ty :=
  match Ty with
  | {{e #"*"}} => x (* this is how you put pyrosome things in gallina *)
  | {{e #"bool"}} => match x with
                     | {{e #"ret" {v} }} => {{e #"ret" {dtt_v v Ty} }} (* THATS IT FOR e boundreis *)
                     | _ => {{e #"if" {dtt_e x Ty} #"ret" #"T" #"ret" #"F" }}
                     end
  (* OL if/else, with x as condition *)
  | {{e #"->" {A} {B} }} => {{e #"ret" #"lambda" {A} {dtt_e {{e #"uapp" (#"val_subst" #"wkn" {x}) {ttd_e {{e #"hd"}} A} }} B} }}
  (* {#"lambda" A (dyn_to_typed (#"app" (#"val_subst" #"wkn" x) (typed_to_dyn #"hd" A)) B)} *)
  end. 


Definition ttd_e {G : term} (x : term) (T : term) : T :=
  match T with
  | {{e #"*"}} => x
  | {{e #"bool"}} => match x with
                     | {{e #"ret" {v} }} => {{e #"ret" {ttd_v v Ty} }}
                     | _ => {{e #"uif" {ttd_e x Ty} #"ret" #"uT" #"ret" #"uF" }}
                     end
  | {{e #"->" {A} {B} }} => {{e #"ret" #"ulambda" {ttd_e {{e #"app" (#"val_subst" #"wkn" {x}) {dtt_e {{e #"hd"}} A} }} B} }}
  end. 

Definition dtt_v {G : term} (x : term) (Ty : term) : Ty :=
  match Ty with
  | {{e #"*"}} => x
  | {{e #"bool"}} => match x with
                            (* these go in the high level multilanguage. mismatches will all be errors *)
                            (* error will be in high level multilanguage and low level multilanguage *)
                     | {{e #"uT"}} => {{e #"T"}}
                     | {{e #"uF"}} => {{e #"F"}}
                     | _           => {{e #"F"}}
                     end
  | {{e #"->" {A} {B} }} => {{e #"lambda" {A} {dtt_e {{e #"uapp" (#"val_subst" #"wkn" #"ret" {x}) {ttd_e {{e #"hd"}} A} }} B} }}
  end. 

Definition ttd_v {G : term} (x : term) (Ty : term) : Ty :=
  match Ty with
  | {{e #"*"}} => x
  | {{e #"bool"}} => match x with
                     | {{e #"T"}} => {{e #"uT"}}
                     | {{e #"F"}} => {{e #"uF"}}
                     | _          => {{e #"uF"}}
                     end
  | {{e #"->" {A} {B} }} => {{e #"ulambda" {ttd_e {{e #"app" (#"val_subst" #"wkn" #"ret" {x}) {dtt_e {{e #"hd"}} A} }} B} }}
  end. 