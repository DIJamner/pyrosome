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

(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Definition boundaries_def : lang :=
  {[l/subst [exp_subst++value_subst] 
    [:| "G" : #"env",
        "A" : #"ty",
        "e" : #"exp" "G" "A"
        -----------------------------------------------
        #"ttd_e" "A" "e" : #"exp" "G" #"*"
    ];
    [:| "G" : #"env",
        "A" : #"ty",
        "e" : #"exp" "G" #"*"
        -----------------------------------------------
        #"dtt_e" "A" "e" : #"exp" "G" "A"
    ];
    [:| "G" : #"env",
        "A" : #"ty",
        "v" : #"val" "G" "A"
        -----------------------------------------------
        #"ttd_v" "A" "v" : #"val" "G" #"*"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "v" : #"val" "G" "A"
        ----------------------------------------------- ("ttd ret comm")
        #"ttd_e" "A" (#"ret" "v") =
        #"ret" (#"ttd_v" "A" "v") : #"exp" "G" #"*"
    ]; (* need comm rule iff we have diff e and v boundaries *)
    [:= "G" : #"env",
        "e" : #"exp" "G" #"*"
        ----------------------------------------------- ("dtt star")
        #"dtt_e" #"*" "e" =
        "e" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("ttd star")
        #"ttd_v" #"*" "v" =
        "v" : #"val" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt True")
        #"dtt_e" #"bool" (#"ret" #"uT") =
        #"ret" #"T" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt False")
        #"dtt_e" #"bool" (#"ret" #"uF") =
        #"ret" #"F" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd True")
        #"ttd_v" #"bool" #"T" =
        #"uT" : #"val" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd False")
        #"ttd_v" #"bool" #"F" =
        #"uF" : #"val" "G" #"*"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("dtt func")
        #"dtt_e" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"lambda" "A" (#"dtt_e" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ret" (#"ttd_v" "A" #"hd"))))) :
        #"exp" "G" (#"->" "A" "B")
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" (#"->" "A" "B")
        ----------------------------------------------- ("ttd func")
        #"ttd_v" (#"->" "A" "B") "v" =
        #"ulambda" (#"ttd_e" "B" (#"app" (#"ret" (#"val_subst" #"wkn" "v")) (#"dtt_e" "A" (#"ret" #"hd")))) :
        #"val" "G" #"*"
    ];
    [:= "G" : #"env",
        "e" : #"exp" (#"ext" "G" #"*") #"*"
        ----------------------------------------------- ("dtt ulambda mismatch")
        #"dtt_e" #"bool" (#"ret" (#"ulambda" "e")) =
        #"Error" #"bool" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty"
        ----------------------------------------------- ("dtt uT mismatch")
        #"dtt_e" (#"->" "A" "B") (#"ret" #"uT") =
        #"Error" (#"->" "A" "B") : #"exp" "G" (#"->" "A" "B")
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty"
        ----------------------------------------------- ("dtt uF mismatch")
        #"dtt_e" (#"->" "A" "B") (#"ret" #"uF") =
        #"Error" (#"->" "A" "B") : #"exp" "G" (#"->" "A" "B")
    ]
  ]}.
Derive boundaries
        SuchThat (elab_lang_ext (utlc ++ 
                                stlc ++ 
                                stlc_bool ++
                                utf ++
                                usubst ++
                                exp_subst++value_subst) 
                boundaries_def boundaries)
        As boundaries_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve boundaries_wf : elab_pfs.



Definition type_casing_def : lang :=
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
        "A" : #"ty",
        "e1" : #"exp" "G" "A",
        "e2" : #"exp" "G" "A",
        "e3" : #"exp" "G" "A"
        ----------------------------------------------- ("type case star")
        #"type case" #"*" "e1" "e2" "e3"  
        = "e1" : #"exp" "G" "A"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "e1" : #"exp" "G" "A",
        "e2" : #"exp" "G" "A",
        "e3" : #"exp" "G" "A"
        ----------------------------------------------- ("type case bool")
        #"type case" #"bool" "e1" "e2" "e3"  
        = "e2" : #"exp" "G" "A"
    ];
    [:= "G" : #"env",
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
Derive type_casing
        SuchThat (elab_lang_ext (stlc_bool ++ 
                                stlc ++
                                usubst ++ 
                                exp_subst++value_subst) 
                type_casing_def type_casing)
        As type_casing_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve type_casing_wf : elab_pfs.

(* The actual multilanguages *)
Definition shared_fragment := 
            boolhuh ++ 
            utf_uapp_ulambda ++ utlc ++ utf ++ usubst ++
            stlc_bool ++ stlc ++
            exp_subst ++ value_subst.

Definition high_level_multilanguage := 
            boundaries ++ uif ++ shared_fragment.

Definition low_level_multilanguage :=
            type_casing ++ mif ++ shared_fragment.

Definition h2l : compiler :=
    match # from high_level_multilanguage with
    | {{e #"uT"}} => {{e #"uT"}}
    | {{e #"uF"}} => {{e #"uF"}}
    | {{e #"T"}} => {{e #"T"}}
    | {{e #"F"}} => {{e #"F"}}
    | {{e #"Error" "A"}} => {{e #"Error" "A"}}
    | {{e #"ret" "v"}} => {{e #"ret" {h2l {{e "v"}} } }}
    | {{e #"lambda" "A" "e"}} => {{e #"lambda" "A" {h2l {{e "e"}} } }}
    | {{e #"app" "e" "e'"}} => {{e #"app" {h2l {{e "e"}} } {h2l {{e "e'"}} } }}
    | {{e #"ulambda" "e"}} => {{e #"ulambda" {h2l {{e "e"}} } }}
    | {{e #"uapp" "e" "e'"}} => {{e #"uapp" {h2l {{e "e"}} } {h2l {{e "e'"}} } }}
    | {{e #"bool?" "e"}} => {{e #"bool?" {h2l {{e "e"}} } }}
    | {{e #"if" "c" "thn" "els"}} => {{e #"if" {h2l "c"} {h2l "thn"} {h2l "els"} }}
    | {{e #"uif" "c" "thn" "els"}} => {{e #"mif" {h2l "c"} {h2l "thn"} {h2l "els"} }}
    | {{e #"dtt_e" "A" "e"}} => {{e #"type case" "A" 
                                    {h2l {{e "e"}} } 
                                    (#"mif" {h2l {{e "e"}} } (#"ret" "T") (#"ret" "F")) 
                                    {h2l {{e #"ret" (#"lambda" "A" (#"dtt_e" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ret" (#"ttd_v" "A" #"hd"))))) }} } 
                                }}
    (* missing ttd *)
    end. 



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