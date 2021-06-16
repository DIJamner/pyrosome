Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab SimpleVSubst SimpleVSTLC Matches SimpleEvalCtx.
Import Core.Notations.

Require Coq.derive.Derive.

Set Default Proof Mode "Classic".

(*depends on subst*)
Definition bool_lang_def :=
  [
    (*TODO: add if; add subst rules*)
    [:| "G" : #"env"
        -----------------------------------------------
        #"false" : #"val" "G" #"bool"
     ];
    [:| "G" : #"env"
        -----------------------------------------------
        #"true" : #"val" "G" #"bool"
     ];
    [:| 
        -----------------------------------------------
        #"bool" : #"ty"
  ]]%rule.

Derive bool_lang
       SuchThat (Pre.elab_lang (exp_subst ++ value_subst) bool_lang_def bool_lang)
       As bool_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve bool_lang_wf : elab_pfs.


(*depends on bool, eval_ctx*)
Definition global_cell_def :=
  [
  [:= "S" : #"val" #"emp" #"bool",
      "v" : #"val" #"emp" #"bool",
      "A" : #"ty",            
      "E" : #"Ectx" #"emp" #"bool" "A"
      ----------------------------------------------- ("eval_swap")
      #"mk_config" "S" (#"plug" "E" (#"swap" "v"))
      = #"mk_config" "v" (#"plug" "E" (#"ret" "S"))
      : #"config" "A"
  ];
  [:= "S" : #"val" #"emp" #"bool",
      "A" : #"ty",            
      "E" : #"Ectx" #"emp" #"bool" "A"
      ----------------------------------------------- ("eval_get")
      #"mk_config" "S" (#"plug" "E" #"get")
      = #"mk_config" "S" (#"plug" "E" (#"ret" "S"))
      : #"config" "A"
  ];
    [:| "S" : #"val" #"emp" #"bool",
        "A" : #"ty", "e" : #"exp" #"emp" "A"                    
       -----------------------------------------------
       #"mk_config" "S" "e" : #"config" "A"
  ];
    [s| "A" : #"ty"                   
       -----------------------------------------------
       #"config" "A" srt
  ];
  [:= "G" : #"env",
      "v" : #"val" "G" #"bool",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("swap_subst")
      #"exp_subst" "g" (#"swap" "v")
      = #"swap" (#"val_subst" "g" "v")
      : #"exp" "G'" #"bool"
  ];
  [:= "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("get_subst")
      #"exp_subst" "g" (#"get") = #"get" : #"exp" "G'" #"bool"
  ];
  [:| "G" : #"env", "v" : #"val" "G" #"bool"
       -----------------------------------------------
       #"swap" "v" : #"exp" "G" #"bool"
  ];
     [:| "G" : #"env"
       -----------------------------------------------
       #"get" : #"exp" "G" #"bool"
  ]]%rule.

Derive global_cell
       SuchThat (Pre.elab_lang (bool_lang ++ eval_ctx ++ (exp_subst ++ value_subst))
                               global_cell_def
                               global_cell)
       As global_cell_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve global_cell_wf : elab_pfs.


