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
From Pyrosome.Lang Require Import UTLC. 
From Pyrosome.Lang Require Import STLCBool. 
From Pyrosome.Lang Require Import UTLCBool. 

Definition hml_def : lang :=
  {[l/subst [exp_subst++value_subst] 
    [:| "G" : #"env",
        "A" : #"ty",
        "e" : #"exp" "G" "A"
        -----------------------------------------------
        #"ttd" "A" "e" : #"exp" "G" #"*"
    ];
    [:| "G" : #"env",
        "A" : #"ty",
        "e" : #"exp" "G" #"*"
        -----------------------------------------------
        #"dtt" "A" "e" : #"exp" "G" "A"
    ];
    [:| "G" : #"env",
        "A" : #"ty",
        "v" : #"val" "G" "A"
        -----------------------------------------------
        #"ttd" "A" "v" : #"val" "G" #"*"
    ];
    [:| "G" : #"env",
        "A" : #"ty",
        "v" : #"val" "G" #"*"
        -----------------------------------------------
        #"dtt" "A" "v" : #"val" "G" "A"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("dtt ret comm")
        #"dtt" "A" (#"ret" "v") =
        #"ret" (#"dtt" "A" "v") : #"exp" "G" "A"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "v" : #"val" "G" "A"
        ----------------------------------------------- ("ttd ret comm")
        #"ttd" "A" (#"ret" "v") =
        #"ret" (#"ttd" "A" "v") : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("dtt star")
        #"dtt" #"*" "v" =
        "v" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("ttd star")
        #"ttd" #"*" "v" =
        "v" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt True")
        #"dtt" #"bool" #"uT" =
        #"T" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt False")
        #"dtt" #"bool" #"uF" =
        #"F" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd True")
        #"ttd" #"bool" #"T" =
        #"uT" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd False")
        #"ttd" #"bool" #"F" =
        #"uF" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("dtt func")
        #"dtt" (#"->" "A" "B") "v" =
        #"lambda" "A" (#"dtt" "B" (#"uapp" (#"val_subst" #"wkn" #"ret" "v") (#"ttd" "A" #"hd"))) :
        #"val" "G" (#"->" "A" "B")
    ]
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" (#"->" "A" "B")
        ----------------------------------------------- ("ttd func")
        #"ttd" (#"->" "A" "B") "v" =
        #"lambda" "A" (#"ttd" "B" (#"app" (#"val_subst" #"wkn" #"ret" "v") (#"dtt" "A" #"hd"))) :
        #"val" "G" #"*"
    ]
    [:= "G" : #"env",
        "v" : #"val" "G" "XXX",
        "B" : #"ty"
        ----------------------------------------------- ("dtt func")
        #"ttd" (#"->" "A" "B") "v" =
        #"lambda" "A" (#"ttd" "B" (#"app" (#"val_subst" #"wkn" #"ret" "v") (#"dtt" "A" #"hd"))) :
        #"val" "G" #"*"
    ]
    (* RULES HERE *)
    (* This is the stuff that's basically the same as Matthews and Findler *)
  ]}.
Derive hml
        SuchThat (elab_lang_ext (stlc_bool ++ 
                                utlc_bool_uif ++ 
                                exp_subst++value_subst) 
                hml_def hml)
        As hml_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve hml_wf : elab_pfs.



Definition lml_def : lang :=
  {[l/subst [exp_subst++value_subst] 
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
        ----------------------------------------------- ("type case star")
        #"type case" #"*" "e1" "e2" "e3"  
        = "e1" : #"exp" "G" "A"
    ]
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
    [:= "G" : #"env",
        "cond" : #"ty",
        "A" : #"ty",
        "t1" : #"ty",
        "t2" : #"ty",
        "e1" : #"exp" "G" "A",
        "e2" : #"exp" "G" "A",
        "e3" : #"exp" "G" "A"
        ----------------------------------------------- ("type case func")
        #"type case" (#"->" "t1" "t2") "e1" "e2" "e3"  
        = "e3" : #"exp" "G" "A"
    ]
  ]}.
Derive lml
        SuchThat (elab_lang_ext (stlc_bool ++ 
                                utlc_bool_mif ++ 
                                exp_subst++value_subst) 
                lml_def lml)
        As lml_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve lml_wf : elab_pfs.
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