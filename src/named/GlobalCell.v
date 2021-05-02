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
Definition bool_lang :=
  [
    (*TODO: add if; add subst rules*)
    [:| "G" : #"env"
        -----------------------------------------------
        #"false" : #"val" %"G" #"bool"
     ];
    [:| "G" : #"env"
        -----------------------------------------------
        #"true" : #"val" %"G" #"bool"
     ];
    [:| 
        -----------------------------------------------
        #"bool" : #"ty"
  ]]%arule.

Derive bool_elab
       SuchThat (Pre.elab_lang subst_elab bool_lang bool_elab)
       As bool_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve bool_lang_wf : elab_pfs.


(*depends on bool, eval_ctx*)
Definition global_cell :=
  [
  [:> "S" : #"val" #"emp" #"bool",
      "v" : #"val" #"emp" #"bool",
      "A" : #"ty",            
      "E" : #"Ectx" #"emp" #"bool" %"A"
      ----------------------------------------------- ("eval_swap")
      #"mk_config" %"S" (#"plug" %"E" (#"swap" %"v"))
      = #"mk_config" %"v" (#"plug" %"E" (#"ret" %"S"))
      : #"config" %"A"
  ];
  [:> "S" : #"val" #"emp" #"bool",
      "A" : #"ty",            
      "E" : #"Ectx" #"emp" #"bool" %"A"
      ----------------------------------------------- ("eval_get")
      #"mk_config" %"S" (#"plug" %"E" #"get")
      = #"mk_config" %"S" (#"plug" %"E" (#"ret" %"S"))
      : #"config" %"A"
  ];
    [:| "S" : #"val" #"emp" #"bool",
        "A" : #"ty", "e" : #"el" #"emp" %"A"                    
       -----------------------------------------------
       #"mk_config" "S" "e" : #"config" %"A"
  ];
    [s| "A" : #"ty"                   
       -----------------------------------------------
       #"config" "A" srt
  ];
  [:> "G" : #"env",
      "v" : #"val" %"G" #"bool",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("swap_subst")
      #"el_subst" %"g" (#"swap" %"v")
      = #"swap" (#"val_subst" %"g" %"v")
      : #"el" %"G'" #"bool"
  ];
  [:> "G" : #"env",
      "G'" : #"env",
      "g" : #"sub" %"G'" %"G"
      ----------------------------------------------- ("get_subst")
      #"el_subst" %"g" (#"get") = #"get" : #"el" %"G'" #"bool"
  ];
  [:| "G" : #"env", "v" : #"val" %"G" #"bool"
       -----------------------------------------------
       #"swap" "v" : #"el" %"G" #"bool"
  ];
     [:| "G" : #"env"
       -----------------------------------------------
       #"get" : #"el" %"G" #"bool"
  ]]%arule.

Derive global_cell_elab
       SuchThat (Pre.elab_lang (bool_elab ++ eval_ctx_elab ++ subst_elab)
                               global_cell
                               global_cell_elab)
       As global_cell_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve global_cell_wf : elab_pfs.


