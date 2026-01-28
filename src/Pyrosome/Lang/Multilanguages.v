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
From Pyrosome.Lang Require Import Bool. 

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
Derive boundaries  (* need polymorphic versions of all these *)
        SuchThat (elab_lang_ext (utlc ++ 
                                stlc ++ 
                                typed_bool ++
                                untyped_bool ++
                                usubst ++
                                exp_subst++value_subst) 
                boundaries_def boundaries)
        As boundaries_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve boundaries_wf : elab_pfs.


Fixpoint ty_wkn_n n :=
  match n with
  | 0 => {{e #"ty_id"}}
  | 1 => {{e #"ty_wkn"}}
  | S n' =>
    {{e #"ty_cmp" #"ty_wkn" {ty_wkn_n n'} }}
  end.

Definition ty_ovar n :=
    {{e #"ty_subst" {ty_wkn_n n} #"ty_hd" }}.  



(* The polymorphic languages *)
(* TODO: prove well-formed *)

(* NOTE: the following is abstracted from the definition of stlc_parameterized in PolyCompilers.v *)
Definition parameterize_wrapper (l : lang) : lang := 
    let ps := (elab_param "D" (l ++ exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps l.

Local Definition evp'_general (l : lang) : lang := 
    let ps := (elab_param "D" (l ++exp_ret ++ exp_subst_base
                                 ++ value_subst)
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base ++ value_subst).

Ltac solve_parameterize_wrapper l := (* comments are copied over from PolyCompilers.v*)
  change (exp_parameterized++val_parameterized) with (evp'_general l);
  (*TODO: phrase exp_and_val_parameterized as parameterized in definition*)
  (*TODO: need to strengthen parameterization pl w/ add'l language?
    Currently cheating.
   *)
  eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    [repeat t';  constructor (*TODO: include in t'*)
    | now prove_from_known_elabs..
    | vm_compute; exact I].

Definition stlc_parameterized := parameterize_wrapper stlc. 

Lemma stlc_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      stlc_parameterized.
Proof. solve_parameterize_wrapper stlc. Qed.
#[export] Hint Resolve stlc_parameterized_wf : elab_pfs.

Definition typed_bool_parameterized := parameterize_wrapper typed_bool. 

Lemma typed_bool_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      typed_bool_parameterized.
Proof. solve_parameterize_wrapper typed_bool. Qed.
#[export] Hint Resolve typed_bool_parameterized_wf : elab_pfs.

Definition usubst_parameterized := parameterize_wrapper usubst. 

Lemma usubst_parameterized_wf
  : wf_lang_ext ((exp_parameterized ++ val_parameterized) ++ ty_env_lang)
      usubst_parameterized.
Proof. solve_parameterize_wrapper usubst. Qed.
#[export] Hint Resolve usubst_parameterized_wf : elab_pfs.


(* this has the type substitution stuff *)
(* Print PolySubst.  *)
(* list of languages that a poly language depends on:
    exp_param_substs ++
    exp_ty_subst ++
    val_param_substs ++
    val_ty_subst ++
    env_ty_subst ++
    ty_subst_lang ++
    exp_parameterized ++ val_parameterized ++ ty_env_lang
*)
(* Compute poly_def.  *)

Definition type_casing_def : lang :=
  {[l
    [:| "D" : #"ty_env",
        "G" : #"env" "D",
        "cond" : #"ty" "D", (* is mu *)
        "A" : #"ty" (#"ty_ext" "D"), (* this is sigma *)
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A"), (* substitute identity type for all except the last (which is A), which we change to star *)
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "A"),
        "e3" : #"exp" "D" "G" (#"All" (#"All" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" {ty_ovar 0} {ty_ovar 1})) "A"))) (* look at arrow case in 134 *)
        -----------------------------------------------
        #"typerec" "cond" "A" "e1" "e2" "e3"  : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "cond") "A") (* verbos way of writing the [u/t]sigma in the rule on 134 *)
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "A"),
        "e3" : #"exp" "D" "G" (#"All" (#"All" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" {ty_ovar 0} {ty_ovar 1})) "A")))
        ----------------------------------------------- ("typerec star")
        #"typerec" #"*" "A" "e1" "e2" "e3"  
        = "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "A"),
        "e3" : #"exp" "D" "G" (#"All" (#"All" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" {ty_ovar 0} {ty_ovar 1})) "A")))
        ----------------------------------------------- ("typerec bool")
        #"typerec" #"bool" "A" "e1" "e2" "e3"  
        = "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "A")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "t1" : #"ty" (#"ty_ext" (#"ty_ext" "D")),
        "t2" : #"ty" (#"ty_ext" (#"ty_ext" (#"ty_ext" "D"))),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "A"),
        "e3" : #"exp" "D" "G" (#"All" (#"All" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" {ty_ovar 0} {ty_ovar 1})) "A")))
        ----------------------------------------------- ("typerec func")
        #"typerec" (#"->" "t1" "t2") "A" "e1" "e2" "e3"  
        = #"@" (#"@" "e3" "t1") "t2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" "t1" "t2")) "A")
    ];
    [:= "D" : #"ty_env",
        "G" : #"env" "D",
        "cond" : #"ty" "D",
        "A" : #"ty" (#"ty_ext" "D"),
        "e1" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"*") "A"),
        "e2" : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" #"bool") "A"),
        "e3" : #"exp" "D" "G" (#"All" (#"All" (#"ty_subst" (#"ty_snoc" #"ty_id" (#"->" {ty_ovar 0} {ty_ovar 1})) "A"))),
        "G'" : #"env" "D",
        "g" : #"sub" "D" "G'" "G"
        ----------------------------------------------- ("exp_subst typerec")
        #"exp_subst" "g" (#"typerec" "cond" "A" "e1" "e2" "e3")
        = #"typerec" "cond" "A" (#"exp_subst" "g" "e1") (#"exp_subst" "g" "e2") (#"exp_subst" "g" "e3")
        : #"exp" "D" "G" (#"ty_subst" (#"ty_snoc" #"ty_id" "cond") "A")
    ]

    (* [:= "G" : #"env",  (* the old function rule, for reference *)
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
    ] *)
  ]}.

  Compute type_casing_def. 

(* Compute type_casing_def.  *)
Derive type_casing
        SuchThat (elab_lang_ext (
                                typed_bool_parameterized ++ 
                                stlc_parameterized ++ 
                                usubst_parameterized ++ 
                                poly ++ 
                                exp_param_substs ++
                                exp_ty_subst ++
                                val_param_substs ++
                                val_ty_subst ++
                                env_ty_subst ++
                                ty_subst_lang ++
                                exp_parameterized ++ val_parameterized ++ ty_env_lang
                                (* typed_bool ++ 
                                stlc ++
                                usubst ++ 
                                exp_subst++value_subst *)
                                ) 
                type_casing_def type_casing)
        As type_casing_wf.
Proof. 
    
    auto_elab. Qed. 
#[export] Hint Resolve type_casing_wf : elab_pfs.
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
    ... (* this is just an example of what it will look like *)
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



(* The actual multilanguages *)
Definition shared_fragment := 
            boolhuh ++ (* think abt why can't compile s*)
            utlc_bool ++ utlc ++ untyped_bool ++ usubst ++
            typed_bool ++ stlc ++
            exp_subst ++ value_subst.
Hint Unfold shared_fragment : auto_elab. 

(* figured out the issue: it was a notation issue. *)
Definition test1 := preserving_compiler_ext. (* from CompilerDefs *)
(* Locate preserving_compiler_ext.  *)
Local Notation preserving_compiler_ext tgt cmp_pre cmp src := (* copied from Paramaterizer, 2523 *)
(preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).

Definition shared_fragment_compiler := id_compiler shared_fragment. 

Lemma shared_fragment_compiles : preserving_compiler_ext shared_fragment [] shared_fragment_compiler shared_fragment.
Proof. 
    unfold shared_fragment. 
    apply id_compiler_preserving; prove_from_known_elabs. 
    typeclasses eauto. 
Qed. 
Hint Resolve shared_fragment_compiles : auto_elab. 

Definition source_multilanguage := 
            boundaries ++ uif ++ shared_fragment.
Hint Unfold source_multilanguage : auto_elab. 

Definition target_multilanguage :=
            type_casing ++ mif ++ shared_fragment.
Hint Unfold target_multilanguage : auto_elab. 

(* Print boolhuh.  *)
(* here you can see implicit arguments *)

(* compiler *)

Local Notation compiler := (compiler string). 
Definition multilang_compiler_def : compiler :=
    match # from (boundaries ++ uif) with
    | {{e #"uif" "G" "c" "thn" "els"}} => {{e #"mif" "c" "thn" "els" }}
    | {{e #"dtt" "G" "C" "e"}} => {{e #"type case" "C" (* diff from A below. TAKE CARE OF A AND B *)
                                    "e" 
                                    (#"mif" "e" (#"ret" #"T") (#"ret" #"F")) 
                                    (#"Error" "C")
                                    (* (#"ret" (#"lambda" "A" (#"dtt" "B" (#"uapp" (#"ret" (#"val_subst" #"wkn" "v")) (#"ttd" "A" (#"ret" #"hd"))))))  *)
                                    }}
    | {{e #"ttd" "G" "C" "e"}} => {{e #"type case" "C"  (* rewrite with convoy pattern focus on bool *)
                                    "e"
                                    (#"if" "e" (#"ret" #"uT") (#"ret" #"uF")) 
                                    (#"Error" "C")
                                    (* (#"ret" (#"ulambda" (#"ttd" "B" (#"app" (#"ret" (#"val_subst" #"wkn" "v")) (#"dtt" "A" (#"ret" #"hd"))))))  *)
                                    }}
    (* order of implicit vars is order of context vars *)
    end. 

(* in case needed, defined in Tools.Matches, Elab.ElabCompilers *)
(* semantic properties are in SemanticsPreservingDefs.v *)

(* Locate elab_preserving_compiler. 
Locate auto_elab_compiler.  *)

Derive multilang_compiler 
        SuchThat (elab_preserving_compiler 
                    shared_fragment_compiler
                    target_multilanguage
                    multilang_compiler_def
                    multilang_compiler
                    (boundaries ++ uif)
                    ) 
        As multilang_compiler_preserving. 
Proof. unfold low_level_multilanguage. 
        unfold shared_fragment. 
        unfold shared_fragment_compiler. 
        auto_elab_compiler. 



    (****** BEGIN In STUFF *)
        cleanup_elab_after setup_elab_compiler.
        1-3: shelve. 

        - repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
        - repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
        - repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
        - repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
        - repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
        - repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
        - cbv [map combine fst]. 
            (* cbv with brackets does _only_ those things. with the minus it does all but those htings. *)

        (* cbn_elab_goal. *)

        lazymatch goal with
        | |- elab_term ?l ?ctx ?e ?ee ?t =>
        let ctx' := eval cbv-[ann_cons annotation] in ctx in
        let e' := eval cbv-[ann_cons annotation] in e in
        let ee' := eval cbv-[ann_cons annotation] in ee in
        let t' := eval cbv-[ann_cons annotation] in t in
        change_no_check (elab_term l ctx' e' ee' t')
        end. 
        repeat t. 
        
        (****** END In STUFF *)
        
        
        cbn_elab_goal. 
        
        (* convoy pattern *)
        
        auto_elab_compiler. 
        1 : {
            cbv -[In]. (* for in goals, this gives what you're trying to prove *)
            Print auto_elab_compiler. 
        }
        3 : { admit. }
        4 : { 
                inversion h2l. 
                Compute shared_fragment.  
            }
        (* is the name of a rule (replaces left to right)  *)

        Locate shared_fragment. 
        (* look at heap proofs, delete cleanup elab after *)
        (* cleanup elab after are good for well formed terms *)
        (* if you see elab_term, that means something is not done type inference *)
        4 :{}
Abort. 


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
        lazymatch goal with 
        | |- ?G => idtac G
        end. 
Admitted. 
#[export] Hint Resolve h2l_preserving : elab_pfs. *)

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