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

(* Compute value_subst_def. 
Locate term.  *)
Definition utlc_def : lang :=
  {[l/subst [utlc++exp_subst++value_subst] 
  (* does putting UTLC there make it so I only have to define the new things? *)
  [:| "G" : #"env"
      -----------------------------------------------
      #"uT" : #"val" "G" #"*"
  ];
  [:| "G" : #"env"
      -----------------------------------------------
      #"uF" : #"val" "G" #"*"
  ];
  [:| "G" : #"env",
      "v" : #"val" "G" #"*"
      -----------------------------------------------
      #"bool?" "v" : #"exp" "G" #"*"
  ];
  [:|
      -----------------------------------------------
      #"bool?" #"uT" = #"uT" (* left is an expression, but right is a value; fix by wrapping right side with #"ret"? *)
      (* also have a syntax error I'm not sure how to get rid of *)
  ];
  [:|
      -----------------------------------------------
      #"bool?" #"uF" = #"uT"
  ];
  [:| "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*"
      -----------------------------------------------
      #"bool?" (#"ulambda" "e") = #"uF"
  ];
  [:| "G" : #"env",
      "cond" : #"val" "G" #"*",
      "e2" : #"exp" "G" #"*",
      "e3" : #"exp" "G" #"*"
      -----------------------------------------------
      #"uif" "cond" "e2" "e3" : #"exp" "G" #"*"
  ];
  [:| "G" : #"env",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      -----------------------------------------------
      #"uif" #"uT" "e2" "e3" = "e2"
  ];
  [:| "G" : #"env",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      -----------------------------------------------
      #"uif" #"uF" "e2" "e3" = "e3"
  ];
  [:| "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "e2" : #"exp" "G" "*",
      "e3" : #"exp" "G" "*"
      -----------------------------------------------
      #"uif" (#"ret" #"ulambda" #"e") "e2" "e3" = "e3"
  ];
  ]}.

Derive utlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) utlc_def utlc)
       As utlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_wf : elab_pfs.

Definition dyn_to_typed {G : term} (x : term) (T : term) : T :=
  match T with
  | {{e #"*"}} => x (* this is how you put pyrosome things in gallina *)
  | {{e #"bool"}} => OL if/else, with x as condition
  | {{e #"->" {A} {B}}} => {#"lambda" A (dyn_to_typed (#"app" (#"val_subst" #"wkn" x) (typed_to_dyn #"hd" A)) B)}
  end. 