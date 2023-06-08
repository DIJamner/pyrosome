Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import Ascii String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Theory.Renaming
  Tools.Matches Compilers.Parameterizer.
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
    (unit_cartesian ++ unit_action++obj_consumer++cat).



Definition ty_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (ty_subst_lang)
                    ty_subst_lang.

Lemma ty_subst_wf
  : elab_lang_ext [] ty_subst_def ty_subst_lang.
Proof. auto_elab. Qed.
(*apply Renaming.rename_lang_mono.
2:now prove_from_known_elabs.
(*TODO: injectivity machinery*)
Admitted.*)
#[export] Hint Resolve ty_subst_wf : elab_pfs.

Definition val_subst :=
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
    (elt_cartesian++elt_action++typed_consumer++cat).


Definition val_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (val_subst++[("ty",sort_rule [] [])])
                    val_subst.

Lemma val_subst_wf
  : elab_lang_ext [("ty",sort_rule [] [])] val_subst_def val_subst.
Proof. auto_elab. Qed.
#[export] Hint Resolve val_subst_wf : elab_pfs.

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
                    (exp_subst_base ++ val_subst++[("ty",sort_rule [] [])])
                    exp_subst_base.

Lemma exp_subst_base_wf
  : elab_lang_ext (val_subst++[("ty",sort_rule [] [])])
      exp_subst_base_def exp_subst_base.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_subst_base_wf : elab_pfs.

Definition definitely_fresh (s : string) (l : list string) :=
  let len := List.fold_left Nat.max (map String.length l) 0 in
  String.append s (string_of_list_ascii (repeat ("'"%char : ascii) len)).

Definition choose_fresh (s : string) (c:ctx string) :=
  if negb (inb s (map fst c)) then s else definitely_fresh s (map fst c).

(*TODO: duplicated*)
Definition under s :=
  {{e #"snoc" (#"cmp" #"wkn" {s}) #"hd"}}.

Definition get_subst_constr s :=
  match s with
  | "exp" => Some "exp_subst"
  | "val" => Some "val_subst"
  | "blk" => Some "blk_subst"
  | _ => None
  end.

Section GenRHSSubterms.
  Context (G : string)
          (g : string).

  (*TODO: careful! _ in patterns does bad things (treated as a var)
   document &/or fix *)
  Fixpoint gen_arg_subst s :=
    match s with
    | {{e#"emp"}} => {{e#"forget"}}
    | var G' => if G =? G' then var g else {{e#"ERR1"}}
    | {{e#"ext" {s'} {_} }} => under (gen_arg_subst s')
    | _ => {{e#"ERR2" {s} }}
    end.
  
  Fixpoint gen_rhs_subterms c args {struct c} :=
    match c, args with
    | (n1,t)::c', n2::args' =>
      if n1 =? n2
      then
        match t with
        | scon name [G']
        | scon name [_;G'] =>
          match get_subst_constr name with
          | Some subst_constr =>
            let s := gen_arg_subst G' in
            let e := {{e #subst_constr {s} n1 }} in
            e::(gen_rhs_subterms c' args')
          | _ => (var n1)::(gen_rhs_subterms c' args')
          end
        | _ => (var n1)::(gen_rhs_subterms c' args')
        end
      else gen_rhs_subterms c' args
    | _, _ => []
    end.
End GenRHSSubterms.

Definition substable_constr name c args t : option (lang _) :=
  match t with
  (*TODO: assumes arbitrary G below the line. Is that the behavior I want or can I generalize?*)
  | scon s [A; var G] =>
    match get_subst_constr s with
    | Some subst_constr =>      
      let constr_rule := term_rule c args t in
      let G' := choose_fresh "G'" c in
      let g := choose_fresh "g" c in
      let c' := (g,{{s#"sub" G' G }})
                  ::(G', {{s#"env"}})
                  ::c in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr g {blank_term} }} in
      let rhs := con name (gen_rhs_subterms G g c args) in
      let t' := scon s [A; var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  (*TODO: duplicated work for blocks since there is no A*)
  | scon s [var G] =>
    match get_subst_constr s with
    | Some subst_constr =>      
      let constr_rule := term_rule c args t in
      let G' := choose_fresh "G'" c in
      let g := choose_fresh "g" c in
      let c' := (g,{{s#"sub" G' G }})
                  ::(G', {{s#"env"}})
                  ::c in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr g {blank_term} }} in
      let rhs := con name (gen_rhs_subterms G g c args) in
      let t' := scon s [var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  | _ => None
  end.

Definition sc '(n,r) :=
  match r with
  |term_rule c args t =>
   match substable_constr n c args t with
   | Some l => l
   | None => [(n,r)]
   end
  | r => [(n,r)]
  end.


Notation "'{[l/subst' r1 ; .. ; r2 ]}" :=
  (List.flat_map sc (cons r2 .. (cons r1 nil) ..))%rule
  (format "'[' {[l/subst '[hv' r1 ; '/' .. ; '/' r2 ']' ]} ']'") : lang_scope.


Definition exp_ret_def : lang _ :=
  {[l/subst
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
    ] ]}.



Derive exp_ret
  SuchThat (elab_lang_ext (exp_subst_base++val_subst++[("ty",sort_rule [] [])])
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
                           
Definition exp_and_val_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (exp_ret ++ exp_subst_base
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base ++ val_subst).


Definition exp_and_val_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (exp_and_val_parameterized
                       ++ty_subst_lang)
                    exp_and_val_parameterized.

Lemma exp_and_val_parameterized_wf
  : elab_lang_ext ty_subst_lang
      exp_and_val_parameterized_def
      exp_and_val_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_and_val_parameterized_wf : elab_pfs.

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


(*TODO: add & generate coherence rules*)
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


Definition env_ty_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (env_ty_subst++
                       exp_and_val_parameterized
                       ++ty_subst_lang)
                    (env_ty_subst).


Lemma env_ty_subst_wf
  : elab_lang_ext (exp_and_val_parameterized++ty_subst_lang)
      env_ty_subst_def
      (env_ty_subst).
Proof. auto_elab. Qed.
#[export] Hint Resolve env_ty_subst_wf : elab_pfs.  


Derive exp_ty_subst
  SuchThat (elab_lang_ext (env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
      exp_ty_subst_def
      exp_ty_subst)
       As exp_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ty_subst_wf : elab_pfs. 

Definition poly_def : lang _ :=
  {[l/subst
  [:| "D" : #"ty_env", "A" : #"ty" (#"ty_ext" "D")
      -----------------------------------------------
      #"All" "A" : #"ty" "D"
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
  ]
    (*
  [:= "D" : #"ty_env",
      "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
       "v" : #"val" "D" "G" (#"All" "A")
        ----------------------------------------------- ("Lam-eta")
      #"Lam" (#"@" (#"ret" "v") (#"ret" #"ty_hd"))
      = "v"
      : #"val" "D" "G" (#"All" "A")
  ] *)
  ]}.


Derive poly
  SuchThat (elab_lang_ext (exp_ty_subst
                             ++env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
              poly_def poly)
       As poly_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ty_subst_wf : elab_pfs. 


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
    ( unit_action++obj_consumer).


Definition block_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (block_subst ++ val_subst ++[("ty",sort_rule [] [])])
                    block_subst.

Lemma block_subst_wf
  : elab_lang_ext (val_subst ++[("ty",sort_rule [] [])])
      block_subst_def block_subst.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_subst_wf : elab_pfs.


                        
Definition block_and_val_parameterized :=
  Eval compute in
    let ps := (elab_param "D" (block_subst
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("blk",Some 1)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (block_subst ++ val_subst).


Definition block_and_val_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (block_and_val_parameterized
                       ++ty_subst_lang)
                    block_and_val_parameterized.

Lemma block_and_val_parameterized_wf
  : elab_lang_ext ty_subst_lang
      block_and_val_parameterized_def
      block_and_val_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_and_val_parameterized_wf : elab_pfs.


(*
Fixpoint find_differing {X A} `{Eqb X} `{Eqb A} `{WithDefault A}
  (l1 l2 : @NamedList.named_list X A) :=
  match l1 with
  | [] => []
  | p::l1 =>
      (if inb p l2
       then []
       else [[snd p;named_list_lookup default l2 (fst p)]])
        ++find_differing l1 l2
  end.

Eval vm_compute in (find_differing (exp_subst_base ++
                    val_subst ++
                    [("ty",sort_rule [] [])])
         (SimpleVSubst.exp_subst ++ SimpleVSubst.value_subst)).
Eval vm_compute in (find_differing blk_subst SimpleVSubst.block_subst).
*)
