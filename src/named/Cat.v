Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Definition cat_lang : lang :=
  {[l  
   [s|
      -----------------------------------------------
      #"ob" srt
   ];
   [s| "A" : #"ob", "B" : #"ob" 
       -----------------------------------------------
       #"arr" "A" "B" srt                     
   ];
   [:| "G" : #"ob" 
       -----------------------------------------------
       #"id" : #"arr" "G" "G"
   ];
   [:| "G1" : #"ob", "G2" : #"ob", "G3" : #"ob",
       "f" : #"arr" "G1" "G2",
       "g" : #"arr" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"arr" "G1" "G3"
   ];
   [:= "G" : #"ob", "G'" : #"ob", "f" : #"arr" "G" "G'"
       ----------------------------------------------- ("id_right")
       #"cmp" "f" #"id" = "f" : #"arr" "G" "G'"
   ];  
   [:= "G" : #"ob", "G'" : #"ob", "f" : #"arr" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"arr" "G" "G'"
   ];
   [:= "G1" : #"ob",
       "G2" : #"ob",
       "G3" : #"ob",
       "G4" : #"ob",
       "f" : #"arr" "G1" "G2",
       "g" : #"arr" "G2" "G3",
       "h" : #"arr" "G3" "G4"
       ----------------------------------------------- ("cmp_assoc")
       #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h" : #"arr" "G1" "G4"
  ] ]}.

(*TODO: separate cat lang and share amongst var. users *)
Derive cat_elab
       SuchThat (Pre.elab_lang [] cat_lang cat_elab)
       As cat_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cat_lang_wf : elab_pfs.
