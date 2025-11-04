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
  ]
  ]}.

Derive utlc_bool
       SuchThat (elab_lang_ext (utlc++exp_subst++value_subst) utlc_bool_def utlc)
       As utlc_bool_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_bool_wf : elab_pfs.

Definition dyn_to_typed {G : term} (x : term) (T : term) : T :=
  match T with
  | {{e #"*"}} => x (* this is how you put pyrosome things in gallina *)
  | {{e #"bool"}} => OL if/else, with x as condition
  | {{e #"->" {A} {B}}} => {#"lambda" A (dyn_to_typed (#"app" (#"val_subst" #"wkn" x) (typed_to_dyn #"hd" A)) B)}
  end. 


Definition typed_to_dyn {G : term} (x : term) (T : term) : T :=
  match T with
  | {{e #"*"}} => x (* this is how you put pyrosome things in gallina *)
  | {{e #"bool"}} => OL if/else, with x as condition
  | {{e #"->" {A} {B}}} => {#"lambda" A (dyn_to_typed (#"app" (#"val_subst" #"wkn" x) (typed_to_dyn #"hd" A)) B)}
  end. 