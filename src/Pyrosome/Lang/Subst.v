Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core Elab.Elab
  Tools.Matches Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference
  Elab.PreTerm Elab.PreRule.



Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).

Notation preterm := (@preterm string).
Notation prectx := (@prectx string).
Notation presort := (@presort string).
Notation prerule := (@prerule string).
Notation prelang := (@prelang string).


Section __.
  Import PreRule.Notations.

Definition subst_def : prelang :=
  {[l   
  {[r
      -----------------------------------------------
      #"env" srt
  ]};
  {[r "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      #"sub" "G" "G'" srt                     
  ]};
  {[r "G" : #"env" 
       -----------------------------------------------
       #"id" : #"sub" "G" "G"
  ]};
  {[r "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" "G1" "G3"
  ]};
  {[r "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" #"id" = "f" : #"sub" "G" "G'"
  ]}; 
  {[r "G" : #"env", "G'" : #"env", "f" : #"sub" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"sub" "G" "G'"
  ]};
   {[r "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" "G1" "G2",
         "g" : #"sub" "G2" "G3",
         "h" : #"sub" "G3" "G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h" : #"sub" "G1" "G4"
  ]}; 
  {[r "G" : #"env" 
      -----------------------------------------------
      #"ty" "G" srt
  ]};

  {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty" "G'"
       -----------------------------------------------
       #"ty_subst" "g" "A" : #"ty" "G"
  ]};
  {[r "G" : #"env", "A" : #"ty" "G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" "A" = "A" : #"ty" "G"
  ]}; 
  {[r "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty" "G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" "f" (#"ty_subst" "g" "A")
       = #"ty_subst" (#"cmp" "f" "g") "A"
       : #"ty" "G1"
  ]};



    
  {[r "G" : #"env", "A" : #"ty" "G"
      -----------------------------------------------
      #"exp" "G" "A" srt
  ]};
  {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'",
       "A" : #"ty" "G'", "v" : #"exp" "G'" "A"
       -----------------------------------------------
       #"exp_subst" "g" "v" : #"exp" "G" (#"ty_subst" "g" "A")
  ]};
  {[r "G" : #"env", "A" : #"ty" "G", "v" : #"exp" "G" "A"
       ----------------------------------------------- ("exp_subst_id")
       #"exp_subst" #"id" "v" = "v" : #"exp" "G" "A"
  ]}; 
  {[r "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2", "g" : #"sub" "G2" "G3",
       "A" : #"ty" "G3", "v" : #"exp" "G3" "A"
       ----------------------------------------------- ("exp_subst_cmp")
       #"exp_subst" "f" (#"exp_subst" "g" "v")
       = #"exp_subst" (#"cmp" "f" "g") "v"
       : #"exp" "G1" (#"ty_subst" (#"cmp" "f" "g") "A")
  ]};

    
  {[r 
      -----------------------------------------------
      #"emp" : #"env"
  ]};
  {[r "G" : #"env" 
      -----------------------------------------------
      #"forget" : #"sub" "G" #"emp"
  ]};
  {[r "G" : #"env", "G'" : #"env", "g" : #"sub" "G" "G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" "g" #"forget" = #"forget" : #"sub" "G" #"emp"
  ]};
  {[r 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ]};
  {[r "G" : #"env", "A": #"ty" "G"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ]};
  {[r "G" : #"env", "G'" : #"env", "A" : #"ty" "G'",
      "g" : #"sub" "G" "G'",
      (* TODO: debug why I need this annotation *)
      "v" : #"exp" "G" (#"ty_subst" ["G'":="G'"] "g" "A")
       -----------------------------------------------
       #"snoc" "g" "v" : #"sub" "G" (#"ext" "G'" "A")
  ]};

  {[r "G" : #"env", "A" : #"ty" "G"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" "G" "A") "G"
  ]};
  {[r "G" : #"env", "A" : #"ty"("G")
       -----------------------------------------------
       #"hd" : #"exp" (#"ext" "G" "A") (#"ty_subst" #"wkn" "A")
  ]};
  {[r "G" : #"env", "G'" : #"env",
      "g" : #"sub" "G" "G'",
      "A" : #"ty" "G'",
      (* TODO: debug why I need this annotation *)
      "v" : #"exp" "G" (#"ty_subst" ["G'":="G'"] "g" "A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" "g" "v") (#"wkn" ["A":= "A"]) = "g" : #"sub" "G" "G'"
  ]};
   {[r "G" : #"env", "G'" : #"env",
       "g" : #"sub" "G" "G'",
       "A" : #"ty" "G'",
      (* TODO: debug why I need this annotation *)
       "v" : #"exp" "G" (#"ty_subst" ["G'":="G'"] "g" "A")
       ----------------------------------------------- ("snoc_hd")
       #"exp_subst" (#"snoc" "g" "v") (#"hd" ["A":= "A"]) = "v"
       : #"exp" "G" (#"ty_subst" "g" "A")
  ]};
   {[r "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" "G1" "G2",
       "g" : #"sub" "G2" "G3",
       "A" : #"ty" "G3",
       "v" : #"exp" "G2" (#"ty_subst" "g" "A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" "f" (#"snoc" "g" "v")
       = #"snoc" (#"cmp" "f" "g") (#"exp_subst" "f" "v")
       : #"sub" "G1" (#"ext" "G3" "A")
   ]};
    
    {[r "G" : #"env", "A" : #"ty" "G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"snoc" #"wkn" #"hd" = #"id" : #"sub" (#"ext" "G" "A") (#"ext" "G" "A")
   ]}
  ]}.

End __.

Definition subst_injectivity :=
  [("hd", ["A"; "G"]); ("wkn", ["A"; "G"]); ("snoc", ["v"; "A"; "g"; "G'"; "G"]); ("ext", ["A"; "G"]);
   ("forget", ["G"]); ("emp", []); ("ty", ["G"]); ("ty_subst", ["G"]);
   ("exp_subst", ["G"]); ("exp", ["A"; "G"]);
   ("cmp", ["G3"; "G1"]); ("id", ["G"]); ("sub", ["G'"; "G"]); ("env", [])].

#[local] Definition id_inst_for_db := inst_for_db "id".
#[export] Hint Resolve id_inst_for_db : injective_con.
#[local] Definition emp_inst_for_db := inst_for_db "emp".
#[export] Hint Resolve emp_inst_for_db : injective_con.
#[local] Definition forget_inst_for_db := inst_for_db "forget".
#[export] Hint Resolve forget_inst_for_db : injective_con.
#[local] Definition ext_inst_for_db := inst_for_db "ext".
#[export] Hint Resolve ext_inst_for_db : injective_con.
#[local] Definition snoc_inst_for_db := inst_for_db "snoc".
#[export] Hint Resolve snoc_inst_for_db : injective_con.
#[local] Definition wkn_inst_for_db := inst_for_db "wkn".
#[export] Hint Resolve wkn_inst_for_db : injective_con.
#[local] Definition hd_inst_for_db := inst_for_db "hd".
#[export] Hint Resolve hd_inst_for_db : injective_con.

Definition subst_lang :=
  Eval vm_compute in
    (infer_lang_ext [] subst_def
       subst_injectivity).

Lemma subst_lang_wf : wf_lang_ext [] subst_lang.
Proof. compute_wf_lang. Qed.
#[local] Definition subst_entry := lang_entry subst_lang_wf.
#[export] Hint Resolve subst_entry : wf_lang_db.
