Set Implicit Arguments.

Require Import Ascii Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Theory.Renaming
  Tools.Matches Compilers.Parameterizer
  Lang.GenericSubst.
Import Core.Notations.

Require Coq.derive.Derive.


Definition cat_def : lang _ :=
  {[l  
  [s|
      -----------------------------------------------
      #"obj" srt
  ];
  [s| "G" : #"obj", "G'" : #"obj" 
      -----------------------------------------------
      #"arr" "G" "G'" srt                     
  ];
  [:| "G" : #"obj" 
       -----------------------------------------------
       #"id" : #"arr" "G" "G"
  ];
  [:| "G1" : #"obj", "G2" : #"obj", "G3" : #"obj",
       "f" : #"arr" "G1" "G2",
       "g" : #"arr" "G2" "G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"arr" "G1" "G3"
  ];
  [:= "G" : #"obj", "G'" : #"obj", "f" : #"arr" "G" "G'"
      ----------------------------------------------- ("id_right")
      #"cmp" "f" #"id" = "f" : #"arr" "G" "G'"
  ]; 
  [:= "G" : #"obj", "G'" : #"obj", "f" : #"arr" "G" "G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" "f" = "f" : #"arr" "G" "G'"
  ];
   [:= "G1" : #"obj",
         "G2" : #"obj",
         "G3" : #"obj",
         "G4" : #"obj",
         "f" : #"arr" "G1" "G2",
         "g" : #"arr" "G2" "G3",
         "h" : #"arr" "G3" "G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" "f" (#"cmp" "g" "h") = #"cmp" (#"cmp" "f" "g") "h" : #"arr" "G1" "G4"
   ]
  ]}.



Require Import Coq.derive.Derive.

Derive cat
       SuchThat (elab_lang_ext [] cat_def cat)
       As cat_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve cat_wf : elab_pfs.

(* TODO: beyond this point there are some category-theoretic
   names that could be used but which I would get wrong in choosing.
 *)
Definition obj_consumer_def : lang _ :=
  {[l
  [s| "G" : #"obj"
      -----------------------------------------------
      #"unit" "G" srt
  ]
  ]}.


Derive obj_consumer
       SuchThat (elab_lang_ext cat obj_consumer_def obj_consumer)
       As obj_consumer_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve obj_consumer_wf : elab_pfs.

Definition unit_action_def : lang _ :=
  {[l
  [:| "G" : #"obj", "G'" : #"obj", "g" : #"arr" "G" "G'",
       "u" : #"unit" "G'"
       -----------------------------------------------
       #"act" "g" "u" : #"unit" "G"
  ];
  [:= "G" : #"obj", "u" : #"unit" "G"
       ----------------------------------------------- ("act_id")
       #"act" #"id" "u" = "u" : #"unit" "G"
  ]; 
  [:= "G1" : #"obj", "G2" : #"obj", "G3" : #"obj",
       "f" : #"arr" "G1" "G2", "g" : #"arr" "G2" "G3",
       "u" : #"unit" "G3"
       ----------------------------------------------- ("act_cmp")
       #"act" "f" (#"act" "g" "u")
       = #"act" (#"cmp" "f" "g") "u"
       : #"unit" "G1"
  ]
  ]}.

Derive unit_action
       SuchThat (elab_lang_ext (obj_consumer++cat) unit_action_def unit_action)
       As unit_action_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_action_wf : elab_pfs.


Definition unit_cartesian_def : lang _ :=
{[l
  [:| 
      -----------------------------------------------
      #"emp" : #"obj"
  ];
  [:| "G" : #"obj"
      -----------------------------------------------
      #"forget" : #"arr" "G" #"emp"
  ];
  [:= "G" : #"obj", "G'" : #"obj", "g" : #"arr" "G" "G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" "g" #"forget" = #"forget" : #"arr" "G" #"emp"
  ];
  [:= 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"arr" #"emp" #"emp"
  ];
  [:| "G" : #"obj"
       -----------------------------------------------
       #"ext" "G" : #"obj"
  ];
  [:| "G" : #"obj", "G'" : #"obj",
      "g" : #"arr" "G" "G'",
      "u" : #"unit" "G"
       -----------------------------------------------
       #"snoc" "g" "u" : #"arr" "G" (#"ext" "G'")
  ];
  [:| "G" : #"obj"
       -----------------------------------------------
       #"wkn" : #"arr" (#"ext" "G") "G"
  ];
  [:| "G" : #"obj"
       -----------------------------------------------
       #"hd" : #"unit" (#"ext" "G")
  ];
   [:= "G" : #"obj", "G'" : #"obj",
      "g" : #"arr" "G" "G'",
      "u" : #"unit" "G"
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" "g" "u") #"wkn" = "g" : #"arr" "G" "G'"
  ];
   [:= "G" : #"obj", "G'" : #"obj",
       "g" : #"arr" "G" "G'",
       "u" : #"unit" "G"
       ----------------------------------------------- ("snoc_hd")
       #"act" (#"snoc" "g" "u") #"hd" = "u"
       : #"unit" "G"
  ];
   [:= "G1" : #"obj", "G2" : #"obj", "G3" : #"obj",
       "f" : #"arr" "G1" "G2",
       "g" : #"arr" "G2" "G3",
       "u" : #"unit" "G2"
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" "f" (#"snoc" "g" "u")
       = #"snoc" (#"cmp" "f" "g") (#"act" "f" "u")
       : #"arr" "G1" (#"ext" "G3")
   ];
      [:= "G" : #"obj"
       ----------------------------------------------- ("snoc_wkn_hd")
        #"snoc" #"wkn" #"hd" = #"id" : #"arr" (#"ext" "G") (#"ext" "G")
   ]
]}.


Derive unit_cartesian
  SuchThat (elab_lang_ext (unit_action++obj_consumer++cat)
              unit_cartesian_def unit_cartesian)
       As unit_cartesian_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve unit_cartesian_wf : elab_pfs.


(*TODO: careful; parameterize doesn't check freshness*)
Definition elt_cartesian_rename (n : string) : string :=
  match n with
  | "unit" => "elt"
  | "u" => "v"
  | _ => n
  end.


#[local] Definition elt_cartesian_in := (rename_lang elt_cartesian_rename
            (unit_cartesian ++ unit_action ++ obj_consumer)).
#[local] Definition elt_cartesian_ps := (elab_param "A" elt_cartesian_in
                           [("ext", Some 0); ("elt",Some 0)]).


(* TODO: beyond this point there are some category-theoretic
   names that could be used but which I would get wrong in choosing.
 *)
Definition typed_consumer : lang _ :=
  Eval compute in
  (parameterize_lang "A" {{s #"ty"}}
     elt_cartesian_ps
     (rename_lang elt_cartesian_rename (obj_consumer))).

  
Definition elt_action :=
  Eval compute in
  (parameterize_lang "A" {{s #"ty"}}
     elt_cartesian_ps
     (rename_lang elt_cartesian_rename (unit_action))).
                      
Definition elt_cartesian :=
  Eval compute in
  (parameterize_lang "A" {{s #"ty"}}
     elt_cartesian_ps
     (rename_lang elt_cartesian_rename unit_cartesian)).


Definition typed_consumer_def :=
  Eval compute in Rule.hide_lang_implicits
                    (typed_consumer
                       ++[("ty",sort_rule [] [])]++cat)
                    typed_consumer.

Definition elt_action_def :=
  Eval compute in Rule.hide_lang_implicits
                    (elt_action++typed_consumer
                       ++[("ty",sort_rule [] [])]++cat)
                    elt_action.

Definition elt_cartesian_def :=
  Eval compute in Rule.hide_lang_implicits
                    (elt_cartesian++elt_action++typed_consumer
                       ++[("ty",sort_rule [] [])]++cat)
                    elt_cartesian.

Lemma simple_sort_wf {V} `{Eqb V} (n : V)
  : wf_lang_ext [] [(n,sort_rule [] [])].
Proof.
  constructor;
    basic_core_crush.
Qed.
#[export] Hint Resolve simple_sort_wf : elab_pfs.

Lemma typed_consumer_wf
  : elab_lang_ext ([("ty",sort_rule [] [])]++cat)
      typed_consumer_def typed_consumer.
Proof. auto_elab. Qed.
#[export] Hint Resolve typed_consumer_wf : elab_pfs.

Lemma elt_action_wf
  : elab_lang_ext (typed_consumer++[("ty",sort_rule [] [])]++cat)
      elt_action_def elt_action.
Proof. auto_elab. Qed.
#[export] Hint Resolve elt_action_wf : elab_pfs.

Lemma elt_cartesian_wf
  : elab_lang_ext (elt_action++typed_consumer++[("ty",sort_rule [] [])]++cat)
      elt_cartesian_def elt_cartesian.
Proof. auto_elab. Qed.
#[export] Hint Resolve elt_cartesian_wf : elab_pfs.

(*TODO: fix construction*)
Definition value_subst :=
  rename_lang
    (fun n =>
       match n with
       | "obj" => "env"
       | "arr" => "sub"
       | "elt" => "val"
       | String "a" (String "c" (String "t" s)) => ("val_subst" ++ s)%string
       (*needed for injectivity; currently not sufficient, but not important*)
       | "env" => "_env"
       | "sub" => "_sub"
       | "val_subst" => "_val_subst"
       | String "_"%char _ => ("_"++n)%string
       (**)
       | _ => n
       end)
    (elt_cartesian++elt_action++typed_consumer++cat)
    ++ [("ty",sort_rule [] [])].


Definition value_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    value_subst
                    value_subst.

Lemma value_subst_wf
  : elab_lang_ext [] value_subst_def value_subst.
Proof. auto_elab. Qed.
#[export] Hint Resolve value_subst_wf : elab_pfs.

Definition exp_subst_base :=
  rename_lang
    (fun n =>
       match n with
       | "obj" => "env"
       | "arr" => "sub"
       | "elt" => "exp"
       | "v" => "e"
       | String "a" (String "c" (String "t" s)) => ("exp_subst" ++ s)%string
       (*needed for injectivity; currently not sufficient, but not important*)
       | "env" => "_env"
       | "sub" => "_sub"
       | "val_subst" => "_val_subst"
       | String "_"%char _ => ("_"++n)%string
       (**)
       | _ => n
       end)
    (elt_action++typed_consumer).


Definition exp_subst_base_def :=
  Eval compute in Rule.hide_lang_implicits
                    (exp_subst_base ++ value_subst)
                    exp_subst_base.

Lemma exp_subst_base_wf
  : elab_lang_ext (value_subst)
      exp_subst_base_def exp_subst_base.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_subst_base_wf : elab_pfs.



Definition exp_ret_def : lang _ :=
  {[l/subst [(exp_subst_base++value_subst)]
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
    ] ]}.

Derive exp_ret
  SuchThat (elab_lang_ext (exp_subst_base++value_subst)
              exp_ret_def exp_ret)
       As exp_ret_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ret_wf : elab_pfs.

(* TODO: note about ordering: have to gen G subst coherence rules
   before parameterizing w/ D?
 *)
(*
issue: if  I parameterize elt_action as normal, what to do about G, A?
-both should be parameterized by D
-both should have substs applied to them by coherence rules

For now: writing one manually to see how it goes
*)
                           
Definition val_parameterized :=
  Eval compute in
    let ps := (elab_param "D" value_subst
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps value_subst.

Definition exp_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (exp_ret ++ exp_subst_base ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base).



Definition val_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (val_parameterized
                       ++[("ty_env",sort_rule [] [])])
                    val_parameterized.

Definition exp_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (exp_parameterized
                       ++val_parameterized
                       ++[("ty_env",sort_rule [] [])])
                    exp_parameterized.

Lemma val_parameterized_wf
  : elab_lang_ext [("ty_env",sort_rule [] [])]
      val_parameterized_def
      val_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve val_parameterized_wf : elab_pfs.

Lemma exp_parameterized_wf
  : elab_lang_ext (val_parameterized++[("ty_env",sort_rule [] [])])
      exp_parameterized_def
      exp_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_parameterized_wf : elab_pfs.


(*TODO: how to remove obj from cat the right way? issue: lang containing*)
(*TODO: split into envs and (ty lang in terms of parameterized val_subst)*)

Definition ty_env_lang :=
  rename_lang
    (fun n =>
       match n with
       | "obj" => "ty_env"
       | "arr" => "ty_sub"
       | "act" => "ty_subst"
       | "unit" => "ty"
       | "u" => "A"
       | "g"
       | "f"
       | "h" => n 
       | String "G"%char s => String "D" s
       (*needed for injectivity*)
       | "env" => "_env"
       | "subst" => "_subst"
       (**)
       | _ => ("ty_"++ n)%string
       end) cat.

Definition ty_subst_lang :=
  rename_lang
    (fun n =>
       match n with
       | "obj" => "ty_env"
       | "arr" => "ty_sub"
       | "act" => "ty_subst"
       | "unit" => "ty"
       | "u" => "A"
       | "g"
       | "f"
       | "h" => n 
       | String "G"%char s => String "D" s
       (*needed for injectivity*)
       | "env" => "_env"
       | "subst" => "_subst"
       (**)
       | _ => ("ty_"++ n)%string
       end)
    (unit_cartesian ++ unit_action).



Definition ty_env_def :=
  Eval compute in Rule.hide_lang_implicits
                    ty_env_lang
                    ty_env_lang.

Definition ty_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (ty_subst_lang++ exp_parameterized++val_parameterized++ty_env_lang)
                    ty_subst_lang.

Lemma ty_env_wf
  : elab_lang_ext [] ty_env_def ty_env_lang.
Proof. auto_elab. Qed.
#[export] Hint Resolve ty_env_wf : elab_pfs.


Lemma ty_subst_wf
  : elab_lang_ext (val_parameterized ++ ty_env_lang) ty_subst_def ty_subst_lang.
Proof. auto_elab. Qed.
#[export] Hint Resolve ty_subst_wf : elab_pfs.

Definition env_ty_subst_rename :=
    (fun n =>
       match n with
       | "obj" => "ty_env"
       | "arr" => "ty_sub"
       | "act" => "env_ty_subst"
       | "unit" => "env"
       | "u" => "G"
       | "g"
       | "f"
       | "h" => n 
       | String "G"%char s => String "D" s
       | "act_cmp" => "env_ty_act_cmp"
       | "act_id" => "env_ty_act_id"
       (*needed for injectivity*)
       | "env" => "_env"
       | "subst" => "_subst"
       (**)
       | _ => ("ty_"++ n)%string
       end).

(*TODO: autogenerate coherence rules*)
Definition env_ty_subst :=
  Eval compute in
    (rename_lang env_ty_subst_rename (unit_action)).


Definition env_ty_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (env_ty_subst++
                       ty_subst_lang++val_parameterized++ty_env_lang)
                    (env_ty_subst).

Lemma env_ty_subst_wf
  : elab_lang_ext (ty_subst_lang++val_parameterized++ty_env_lang)
      env_ty_subst_def
      (env_ty_subst).
Proof. auto_elab. Qed.
#[export] Hint Resolve env_ty_subst_wf : elab_pfs.

Definition val_ty_subst_def : lang _ :=
  {[l
    [:| "D" : #"ty_env",
           "D'" : #"ty_env",
           "g" : #"ty_sub" "D" "D'",
           "G" : #"env" "D'",
           "A" : #"ty" "D'",
           "v" : #"val" "D'" "G" "A" 
           -----------------------------------------------
           #"val_ty_subst" "g" "v"
           : #"val" "D" (#"env_ty_subst" "g" "G") (#"ty_subst" "g" "A")
    ];
    [:| "D" : #"ty_env",
           "D'" : #"ty_env",
           "g" : #"ty_sub" "D" "D'",
           "G" : #"env" "D'",
           "G'" : #"env" "D'",
           "v" : #"sub" "D'" "G" "G'" 
           -----------------------------------------------
           #"sub_ty_subst" "g" "v"
           : #"sub" "D" (#"env_ty_subst" "g" "G") (#"env_ty_subst" "g" "G'")
       ]
  ]}.

Derive val_ty_subst
  SuchThat (elab_lang_ext (env_ty_subst
                             ++ty_subst_lang
                             ++val_parameterized
                             ++ty_env_lang)
      val_ty_subst_def
      val_ty_subst)
       As val_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve val_ty_subst_wf : elab_pfs. 

Definition exp_ty_subst_def : lang _ :=
  {[l
       [:| "D" : #"ty_env",
           "D'" : #"ty_env",
           "g" : #"ty_sub" "D" "D'",
           "G" : #"env" "D'",
           "A" : #"ty" "D'",
           "e" : #"exp" "D'" "G" "A" 
           -----------------------------------------------
           #"exp_ty_subst" "g" "e"
           : #"exp" "D" (#"env_ty_subst" "g" "G") (#"ty_subst" "g" "A")
       ]
      ]}.

Derive exp_ty_subst
  SuchThat (elab_lang_ext (env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
      exp_ty_subst_def
      exp_ty_subst)
       As exp_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ty_subst_wf : elab_pfs. 


Definition val_param_substs_def :=
  Eval compute in
    eqn_rules type_subst_mode (val_ty_subst ++ env_ty_subst
                                 ++ val_parameterized ++ ty_subst_lang)
   val_parameterized_def.
             
Derive val_param_substs
  SuchThat (elab_lang_ext (val_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++val_parameterized
                             ++ty_env_lang)
              val_param_substs_def
              val_param_substs)
  As val_param_substs_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve val_param_substs_wf : elab_pfs.

Definition exp_param_substs_def :=
  Eval compute in
    eqn_rules type_subst_mode (exp_ty_subst++val_ty_subst
                                 ++env_ty_subst++exp_parameterized
                                 ++val_parameterized ++ty_subst_lang)
   exp_parameterized_def.
             
Derive exp_param_substs
  SuchThat (elab_lang_ext (val_param_substs
                             ++exp_ty_subst
                             ++val_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
              exp_param_substs_def
              exp_param_substs)
  As exp_param_substs_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_param_substs_wf : elab_pfs.

Local Open Scope lang_scope.
Definition poly_def : lang _ :=
  {[l (*l/subst TODO: psubst*)
  [:| "D" : #"ty_env", "A" : #"ty" (#"ty_ext" "D")
      -----------------------------------------------
      #"All" "A" : #"ty" "D"
  ];
    (*TODO: autogenerate:*)
    [:= "D" : #"ty_env",
              "A" : #"ty" (#"ty_ext" "D"),
              "D'" : #"ty_env",
              "d" : #"ty_sub" "D'" "D"
              ----------------------------------------------- ("ty_subst All")
              #"ty_subst" "d" (#"All" "A")
               = #"All" (#"ty_subst" (#"ty_snoc" (#"ty_cmp" #"ty_wkn" "d") #"ty_hd") "A")
               : #"ty" "D'"
          ];
    [:| "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" (#"ty_ext" "D"),
       "e" : #"exp" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") "A"
       -----------------------------------------------
       #"Lam" "e" : #"val" "D" "G" (#"All" "A")
  ];
  [:| "D" : #"ty_env",
      "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
       "e" : #"exp" "D" "G" (#"All" "A"),
       "B" : #"ty" "D"
       -----------------------------------------------
       #"@" "e" "B"
       : #"exp" "D" "G"
         (#"ty_subst" (#"ty_snoc" #"ty_id" "B") "A")
  ];
  [:=  "D" : #"ty_env",
      "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
       "e" : #"exp" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") "A",
       "B" : #"ty" "D"
      ----------------------------------------------- ("Lam-beta")
      #"@" (#"ret" (#"Lam" "e")) "B"
      = #"exp_ty_subst" (#"ty_snoc" #"ty_id" "B") "e"
      : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "B") "A")
  ];
    [:= "D" : #"ty_env",
       "G" : #"env" "D",
       "A" :  #"ty" (#"ty_ext" "D"),
       "e" : #"exp" (#"ty_ext" "D") (#"env_ty_subst" #"ty_wkn" "G") "A",
       "G'" : #"env" "D", "g" : #"sub" "D" "G'" "G"
       ----------------------------------------------- ("subst Lam")
       #"val_subst" "g" (#"Lam" "e")
       = #"Lam" (#"exp_subst" (#"sub_ty_subst" #"ty_wkn" "g") "e") : #"val" "D" "G'" (#"All" "A")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "e" : #"exp" "D" "G" (#"All" "A"),
        "B" : #"ty" "D",
        "G'" : #"env" "D", "g" : #"sub" "D" "G'" "G"
       ----------------------------------------------- ("subst @")
       #"exp_subst" "g" (#"@" "e" "B")
       = #"@" (#"exp_subst" "g" "e") "B" : #"exp" "D" "G'" (#"ty_subst" (#"ty_snoc" #"ty_id" "B") "A")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "v" : #"val" "D" "G" (#"All" "A")
        ----------------------------------------------- ("Lam-eta")
        #"Lam" (#"@" (#"ret" (#"val_ty_subst" #"ty_wkn" "v")) #"ty_hd")
        = "v"
        : #"val" "D" "G" (#"All" "A")
  ]
  ]}.

(*TODO: add in*)
  Eval compute in
    eqn_rules type_subst_mode (exp_ty_subst++val_ty_subst
                                 ++env_ty_subst++exp_parameterized
                                 ++val_parameterized ++ty_subst_lang)
    poly_def.


#[local] Definition ty_id_inst_for_db := inst_for_db "ty_id".
#[local] Definition ty_emp_inst_for_db := inst_for_db "ty_emp".
#[local] Definition ty_forget_inst_for_db := inst_for_db "ty_forget".
#[local] Definition ty_ext_inst_for_db := inst_for_db "ty_ext".
#[local] Definition ty_snoc_inst_for_db := inst_for_db "ty_snoc".
#[local] Definition ty_wkn_inst_for_db := inst_for_db "ty_wkn".
#[local] Definition ty_hd_inst_for_db := inst_for_db "ty_hd".
#[local] Definition id_inst_for_db := inst_for_db "id".
#[local] Definition emp_inst_for_db := inst_for_db "emp".
#[local] Definition forget_inst_for_db := inst_for_db "forget".
#[local] Definition ext_inst_for_db := inst_for_db "ext".
#[local] Definition snoc_inst_for_db := inst_for_db "snoc".
#[local] Definition wkn_inst_for_db := inst_for_db "wkn".
#[local] Definition hd_inst_for_db := inst_for_db "hd".
#[local] Definition ret_inst_for_db := inst_for_db "ret".
#[local] Definition All_inst_for_db := inst_for_db "All".
  
#[export] Hint Resolve ty_id_inst_for_db : injective_con.
#[export] Hint Resolve ty_emp_inst_for_db : injective_con.
#[export] Hint Resolve ty_forget_inst_for_db : injective_con.
#[export] Hint Resolve ty_ext_inst_for_db : injective_con.
#[export] Hint Resolve ty_snoc_inst_for_db : injective_con.
#[export] Hint Resolve ty_wkn_inst_for_db : injective_con.
#[export] Hint Resolve ty_hd_inst_for_db : injective_con.
#[export] Hint Resolve id_inst_for_db : injective_con.
#[export] Hint Resolve emp_inst_for_db : injective_con.
#[export] Hint Resolve forget_inst_for_db : injective_con.
#[export] Hint Resolve ext_inst_for_db : injective_con.
#[export] Hint Resolve snoc_inst_for_db : injective_con.
#[export] Hint Resolve wkn_inst_for_db : injective_con.
#[export] Hint Resolve hd_inst_for_db : injective_con.
#[export] Hint Resolve ret_inst_for_db : injective_con.
#[export] Hint Resolve All_inst_for_db : injective_con.

Derive poly
  SuchThat (elab_lang_ext (exp_param_substs
                             ++ exp_ty_subst
                             ++ val_param_substs
                             ++ val_ty_subst
                             ++env_ty_subst
                             ++ty_subst_lang
                             ++exp_parameterized++val_parameterized
                             ++ty_env_lang)
              poly_def poly)
       As poly_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve poly_wf : elab_pfs. 


Definition block_subst : lang _ :=
  rename_lang
    (fun n =>
       match n with
       | "obj" => "env"
       | "arr" => "sub"
       | String "a" (String "c" (String "t" s)) => ("blk_subst" ++ s)%string
       | "unit" => "blk"
       | "id" => "id"
       | "cmp" => "cmp"
       | "u" => "e"
       | String "G"%char _
       | "g"
       | "f"
       | "h" => n 
       (*needed for injectivity*)
       | "env" => "_env"
       | "subst" => "_subst"
       (**)
       | _ => ("blk_"++ n)%string
       end)
    (unit_action++obj_consumer).


Definition block_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (block_subst ++ value_subst)
                    block_subst.

Lemma block_subst_wf
  : elab_lang_ext value_subst
      block_subst_def block_subst.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_subst_wf : elab_pfs.

                        
Definition block_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (block_subst
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (block_subst).


Definition block_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (block_parameterized++val_parameterized
                       ++ty_env_lang)
                    block_parameterized.

Lemma block_parameterized_wf
  : elab_lang_ext (val_parameterized++ty_env_lang)
      block_parameterized_def
      block_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_parameterized_wf : elab_pfs.

(*
Lemma env_ty_subst_wf'
  : elab_lang_ext (block_and_val_parameterized++ty_env_lang)
      env_ty_subst_def
      (env_ty_subst).
Proof. auto_elab. Qed.
#[export] Hint Resolve env_ty_subst_wf' : elab_pfs.
*)


Definition block_ty_subst_def : lang _ :=
  {[l
       [:| "D" : #"ty_env",
           "D'" : #"ty_env",
           "g" : #"ty_sub" "D" "D'",
           "G" : #"env" "D'",
           "e" : #"blk" "D'" "G"
           -----------------------------------------------
           #"blk_ty_subst" "g" "e"
           : #"blk" "D" (#"env_ty_subst" "g" "G")
       ];
    [:| "D" : #"ty_env",
           "D'" : #"ty_env",
           "g" : #"ty_sub" "D" "D'",
           "G" : #"env" "D'",
           "A" : #"ty" "D'",
           "v" : #"val" "D'" "G" "A" 
           -----------------------------------------------
           #"val_ty_subst" "g" "v"
           : #"val" "D" (#"env_ty_subst" "g" "G") (#"ty_subst" "g" "A")
    ];
    [:| "D" : #"ty_env",
           "D'" : #"ty_env",
           "g" : #"ty_sub" "D" "D'",
           "G" : #"env" "D'",
           "G'" : #"env" "D'",
           "v" : #"sub" "D'" "G" "G'" 
           -----------------------------------------------
           #"sub_ty_subst" "g" "v"
           : #"sub" "D" (#"env_ty_subst" "g" "G") (#"env_ty_subst" "g" "G'")
       ]
      ]}.

Derive block_ty_subst
  SuchThat (elab_lang_ext (env_ty_subst
                             ++ ty_subst_lang
                             ++block_parameterized
                             ++ val_parameterized
                             ++ty_env_lang)
      block_ty_subst_def
      block_ty_subst)
       As block_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_ty_subst_wf : elab_pfs. 


Definition block_param_substs_def :=
  Eval compute in
  eqn_rules type_subst_mode (val_param_substs
                               ++block_ty_subst++env_ty_subst
                               ++block_parameterized
                               ++val_parameterized++ty_subst_lang)
    block_parameterized_def.
             
Derive block_param_substs
  SuchThat (elab_lang_ext (val_param_substs
                             ++block_ty_subst
                             ++env_ty_subst
                             ++block_parameterized
                             ++ty_subst_lang
                             ++val_parameterized
                             ++ty_env_lang)
              block_param_substs_def
              block_param_substs)
  As block_param_substs_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_param_substs_wf : elab_pfs.
