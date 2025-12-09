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

From Pyrosome.Lang Require Import PolySubst. 

From Pyrosome.Compilers Require Import Parameterizer. 
(* copied from LinearCPS.v *)
From Pyrosome Require Import Compilers.Compilers Elab.ElabCompilers.
Import CompilerDefs.Notations. (* for `match # from high_level_multilanguage with` *)
(* CompilerDefs, for preserving_compiler_ext, is already imported. Prolly through something else. *)

Definition boundaries_def : lang :=
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
    [:= "G" : #"env",
        "e" : #"exp" "G" #"*"
        ----------------------------------------------- ("dtt star")
        #"dtt" #"*" "e" =
        "e" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "e" : #"exp" "G" #"*"
        ----------------------------------------------- ("ttd star")
        #"ttd" #"*" "e" =
        "e" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt True")
        #"dtt" #"bool" (#"ret" #"uT") =
        #"ret" #"T" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("dtt False")
        #"dtt" #"bool" (#"ret" #"uF") =
        #"ret" #"F" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd True")
        #"ttd" #"bool" (#"ret" #"T") =
        #"ret" #"uT" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env"
        ----------------------------------------------- ("ttd False")
        #"ttd" #"bool" (#"ret" #"F") =
        #"ret" #"uF" : #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" #"*"
        ----------------------------------------------- ("dtt func")
        #"dtt" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"lambda" "A" (#"dtt" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ttd" "A" (#"ret" #"hd"))))) :
        #"exp" "G" (#"->" "A" "B")
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty",
        "v" : #"val" "G" (#"->" "A" "B")
        ----------------------------------------------- ("ttd func")
        #"ttd" (#"->" "A" "B") (#"ret" "v") =
        #"ret" (#"ulambda" (#"ttd" "B" (#"app" (#"ret" (#"val_subst" #"wkn" "v")) (#"dtt" "A" (#"ret" #"hd"))))) :
        #"exp" "G" #"*"
    ];
    [:= "G" : #"env",
        "e" : #"exp" (#"ext" "G" #"*") #"*"
        ----------------------------------------------- ("dtt ulambda mismatch")
        #"dtt" #"bool" (#"ret" (#"ulambda" "e")) =
        #"Error" #"bool" : #"exp" "G" #"bool"
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty"
        ----------------------------------------------- ("dtt uT mismatch")
        #"dtt" (#"->" "A" "B") (#"ret" #"uT") =
        #"Error" (#"->" "A" "B") : #"exp" "G" (#"->" "A" "B")
    ];
    [:= "G" : #"env",
        "A" : #"ty",
        "B" : #"ty"
        ----------------------------------------------- ("dtt uF mismatch")
        #"dtt" (#"->" "A" "B") (#"ret" #"uF") =
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



(* Definition type_casing_def : lang :=
  {[l/subst [exp_subst++value_subst] 
    [:| "D" : #"ty_env",
        "G" : #"env" "D",
        "cond" : #"ty" "D",
        "A" : #"ty" "D",
        "e1" : #"exp" "D" "G" "A",
        "e2" : #"exp" "D" "G" "A",
        "e3" : #"exp" (#"ext" (#"ext" "D")) "G" "A" (* needs to have extneded type environment *)
        -----------------------------------------------
        #"type case" "cond" "e1" "e2" "e3"  : #"exp" "D" "G" "A"
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
        = #"exp_subst" (#"snoc" #"ty_id" "t1" "t2") "e3" : #"exp" "D" "G" "A"
        (* = "e3" : #"exp" "G" "A"  *)
        (* gonna have a type level substitution on e3 that'll plug t1 and t2 in *)
        (* some page in the paper they sent you has a rule like this *)
    ]
  ]}. *)
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
        (* gonna have a type level substitution on e3 that'll plug t1 and t2 in *)
        (* some page in the paper they sent you has a rule like this *)
    ]
  ]}.

(* Compute type_casing_def.  *)
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
            boolhuh ++ (* think abt why can't compile s*)
            utf_uapp_ulambda ++ utlc ++ utf ++ usubst ++
            stlc_bool ++ stlc ++
            exp_subst ++ value_subst.
Hint Unfold shared_fragment : auto_elab. 

(* figured out the issue: it was a notation issue. *)
Definition test1 := preserving_compiler_ext. (* from CompilerDefs *)
(* Locate preserving_compiler_ext.  *)
Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
(preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

Lemma shared_fragment_compiles : preserving_compiler_ext shared_fragment [] (id_compiler shared_fragment) shared_fragment.
Proof. 
    unfold shared_fragment. 
    apply id_compiler_preserving; prove_from_known_elabs.
    (* below is to prove goal `Eqb_ok string_Eqb`. *)
    unfold Eqb_ok. intros. destruct (eqb a b) eqn:EQB. 
    - apply String.eqb_eq. apply EQB. 
    - unfold eqb in *. unfold string_Eqb in EQB. 
        unfold not. intros. apply String.eqb_eq in H. rewrite H in EQB. discriminate EQB. 
Qed. 
Hint Resolve shared_fragment_compiles : auto_elab. 

Definition high_level_multilanguage := 
            boundaries ++ uif ++ shared_fragment.
Hint Unfold high_level_multilanguage : auto_elab. 

Definition low_level_multilanguage :=
            type_casing ++ mif ++ shared_fragment.
Hint Unfold high_level_multilanguage : auto_elab. 

(* Print boolhuh.  *)
(* here you can see implicit argumetns *)

(* compiler *)

Local Notation compiler := (compiler string). 
Definition h2l_def : compiler :=
    match # from high_level_multilanguage with
    | {{e #"uif" "G" "c" "thn" "els"}} => {{e #"mif" "c" "thn" "els" }}
    | {{e #"dtt" "G" "C" "e"}} => {{e #"type case" "C" (* diff from A below. TAKE CARE OF A AND B *)
                                    "e" 
                                    (#"mif" "e" (#"ret" #"T") (#"ret" #"F")) 
                                    (#"ret" (#"lambda" "A" (#"dtt" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ttd" "A" (#"ret" #"hd")))))) 
                                    }}
    | {{e #"ttd" "G" "A" "e"}} => {{e #"type case" "A" 
                                    "e"
                                    (#"if" "e" (#"ret" #"uT") (#"ret" #"uF")) 
                                    (#"ret" (#"ulambda" (#"ttd" "B" (#"app" (#"ret" (#"val_subst" #"wkn" "v")) (#"dtt" "A" (#"ret" #"hd")))))) 
                                    }}
    (* order of implicit vars is order of context vars *)
    end. 

Definition five := 5. 

(* in case needed, defined in Tools.Matches, Elab.ElabCompilers *)
(* semantic properties are in SemanticsPreservingDefs.v *)

(* Locate elab_preserving_compiler. 
Locate auto_elab_compiler.  *)

(* Derive h2l *)

Derive h2l 
        SuchThat (elab_preserving_compiler 
                    (id_compiler shared_fragment)
                    low_level_multilanguage
                    h2l_def
                    h2l
                    (boundaries ++ uif)
                    ) 
        As h2l_preserving. 
Proof. unfold low_level_multilanguage. 
        unfold shared_fragment. 
        auto_elab_compiler. 
Admitted. 


(* proof mirrors language proof *)
(* Derive h2l
       SuchThat (elab_preserving_compiler [] (* compiler root: for base language *)
                                          low_level_multilanguage (* target language—ALL of it *)
                                          h2l_def
                                          h2l
                                          high_level_multilanguage) (* source  *) 
                                          (* ideally, only boundaries ++ uif *)
       As h2l_preserving.
Proof. unfold low_level_multilanguage. unfold high_level_multilanguage. 
        unfold shared_fragment. 
        auto_elab_compiler. 
Admitted.  *)
#[export] Hint Resolve h2l_preserving : elab_pfs.

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

(* 
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
  end.  *)
  Definition three := 3.