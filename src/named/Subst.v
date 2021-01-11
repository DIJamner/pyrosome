Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Exp Rule ARule Tactics Decidable.
From Named Require ICore.
Import ICore.IndependentJudgment.
Import Exp.Notations ARule.Notations. (* TODO: Rule.Notations.*)
Require Import String.

Require Import Named.Recognizers.

Set Default Proof Mode "Ltac2".




(*Notation ob := (con 0 [::]).
Notation hom a b := (con 1 [:: b; a]%exp_scope).
Notation id a := (con 2 [:: a]%exp_scope).
Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).*)       

(* syntax of categories *)
Definition cat_lang : lang :=
  [::
     [:> "G1" : #"env",
         "G2" : #"env",
         "G3" : #"env",
         "G4" : #"env",
         "f" : #"sub" %"G1" %"G2",
         "g" : #"sub" %"G2" %"G3",
         "h" : #"sub"%"G3" %"G4"
         ----------------------------------------------- ("cmp_assoc")
         #"cmp" %"f" (#"cmp" %"g" %"h") = #"cmp" (#"cmp" %"f" %"g") %"h" : #"sub" %"G1" %"G4"
  ];  
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("id_left")
       #"cmp" #"id" %"f" = %"f" : #"sub" %"G"%"G'"
  ];
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub" %"G" %"G'"
      ----------------------------------------------- ("id_right")
      #"cmp" %"f" #"id" = %"f" : #"sub" %"G" %"G'"
  ];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3"
       -----------------------------------------------
       #"cmp" "f" "g" : #"sub" %"G1" %"G3"
  ];
  [:| "G" : #"env" 
       -----------------------------------------------
       #"id" : #"sub" %"G" %"G"
  ];
  [s| "G" : #"env", "G'" : #"env" 
      -----------------------------------------------
      #"sub" "G" "G'" srt                     
  ];
  [s|
      -----------------------------------------------
      #"env" srt
  ]
  ]%arule.

Print LangRecognize.

Fixpoint cat_lang_sub_r c e G_l : exp :=
  match e with
  | con "id" [::] => G_l
  | con "cmp" [:: g; f] =>
    let G_lf := cat_lang_sub_r c f G_l in
    let G_lg := cat_lang_sub_r c g G_lf in
    G_lg
  | var x =>
    match named_list_lookup {{s #"ERR"}} c x with
    | scon "sub" [:: G; _] => G
    | _ => {{e #"ERR"}}
    end
  | _ => {{e #"ERR"}}
  end.
  
#[refine]
Instance rec_cat_lang : LangRecognize cat_lang :=
  { le_sort_dec _ _ t1 t2 := t1 == t2;
    term_args_elab c s name t := 
      match name, t, s with
      | "id", scon "sub" [:: _; G],_ => [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r c f G1 in
        [:: g; f; G3; G2; G1]
      | _,_,_ => s
      end%string;
    sort_args_elab c s _ := s
  }.
Proof.
  {
    intros n c t1 t2 _ _ _.
    ltac1:(move /eqP ->).
    apply le_sort_refl.
  }
Defined.

Lemma cat_lang_wf : wf_lang cat_lang.
Proof.
  apply (@decide_wf_lang _ _ 100).
  vm_compute; reflexivity.
Qed.

Derive elab_cat_lang
       SuchThat (elab_lang cat_lang elab_cat_lang)
       As elab_cat_lang_pf.
Proof.
  repeat (elab (fun () => reflexivity)).
Qed. 

Instance elab_cat_lang_inst : Elaborated cat_lang :=
  {
  elaboration := elab_cat_lang;
  elab_pf := elab_cat_lang_pf;
  }.


Definition subst_lang' : lang :=
 [::[:> 
      ----------------------------------------------- ("id_emp_forget")
      #"id" = #"forget" : #"sub" #"emp" #"emp"
  ];
  [:> "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'"
       ----------------------------------------------- ("cmp_forget")
       #"cmp" %"g" #"forget" = #"forget" : #"sub" %"G" #"emp"
  ];
  [:| "G" : #"env" 
      -----------------------------------------------
      #"forget" : #"sub" %"G" #"emp"
  ];
  [:| 
      -----------------------------------------------
      #"emp" : #"env"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3", "e" : #"el" %"G3" %"A"
       ----------------------------------------------- ("el_subst_cmp")
       #"el_subst" (#"cmp" %"f" %"g") %"e"
       = #"el_subst" %"f" (#"el_subst" %"g" %"e")
       : #"el" %"G1" (#"ty_subst" (#"cmp" %"f" %"g") %"A")
  ]; 
  [:> "G" : #"env", "A" : #"ty" %"G", "e" : #"el" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"el" %"G" %"A"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3"
       ----------------------------------------------- ("ty_subst_cmp")
       #"ty_subst" (#"cmp" %"f" %"g") %"A"
       = #"ty_subst" %"f" (#"ty_subst" %"g" %"A")
       : #"ty" %"G1"
  ];              
  [:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("ty_subst_id")
       #"ty_subst" #"id" %"A" = %"A" : #"ty" %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'", "e" : #"el" %"G'" %"A"
       -----------------------------------------------
       #"el_subst" "g" "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
  ];
  [s| "G" : #"env", "A" : #"ty"(%"G")
      -----------------------------------------------
      #"el" "G" "A" srt
  ];
  [:| "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'"
       -----------------------------------------------
       #"ty_subst" "g" "A" : #"ty" %"G"
  ];
  [s| "G" : #"env" 
      -----------------------------------------------
      #"ty" "G" srt
  ]]%irule++cat_lang.

Derive elab_subst_lang'
       SuchThat (elab_lang subst_lang' elab_subst_lang')
       As elab_subst_lang'_pf.
Proof.
  repeat (elab(fun () => reflexivity )).
  {
    eapply Core.le_sort_refl'; repeat (elab(fun()=> reflexivity)).
    eapply (Core.le_term_by' "ty_subst_id"%string); repeat (elab (fun()=>reflexivity)).
  }
  {    
    eapply Core.le_sort_refl'; repeat (elab (fun()=>reflexivity)).
    symmetry.
    eapply (Core.le_term_by' "ty_subst_cmp"%string); repeat (elab (fun()=>reflexivity)).
  }
Qed.

Instance elab_subst_lang'_inst : Elaborated subst_lang' :=
  {
  elaboration := elab_subst_lang';
  elab_pf := elab_subst_lang'_pf;
  }.


(****************************
 Nth-tail section; TODO: is any of this needed?
                            *)

Lemma nth_tail_nil {A} n : @nth_tail A n [::] = [::].
Proof.
  destruct n; simpl; reflexivity.
Qed.

Definition is_fst {A : eqType} (l:list A) (e:A) : bool :=
  match l with
  | [::] => false
  | e'::_ => e == e'
  end.

Arguments is_fst {A} !l/.

(*Temporary, just for the following lemma:*)
Arguments nth_tail {A} !n l/.
Lemma elab_lang_cons'_helper
  : forall (l : named_list rule) (el : ARule.lang) (name : string) 
           (r : rule) (er : ARule.rule),
    fresh name l ->
    (* TODO: is_fst for lang?; need eqtype for IExp; just get rid of iexp?*)
    is_fst el (name,er) ->
    elab_lang l (nth_tail 1 el) ->
    elab_rule (nth_tail 1 el) r er ->
    elab_lang ((name,r)::l) el.
Proof.
  intros l el.
  revert l.
  destruct el.
  {
    intros.
    vm_compute in H0.
    inversion H0.
  }
  {
    intros.
    simpl in H0,H1,H2.
    ltac1:(move: H0 => /eqP H0).
    subst.
    constructor; auto.
  }
Qed.

Lemma nth_tail_S_cons {A} n (e:A) l : nth_tail n.+1 (e::l) = nth_tail n l.
Proof.
  reflexivity.
Qed.      

Lemma nth_tail_add1 {A} n (l:list A) : nth_tail 1 (nth_tail n l) = nth_tail (n.+1) l.
Proof.
  revert l; induction n; intros.
  { reflexivity. }
  { destruct l.
    { reflexivity. }
    { rewrite !nth_tail_S_cons.
      rewrite IHn.
      reflexivity.
    }
  }
Qed.    

Lemma elab_lang_cons' n l el name r er
  : fresh name l ->
    (* TODO: is_fst for lang?; need eqtype for IExp; just get rid of iexp?*)
    is_fst (nth_tail n el) (name,er) ->
    elab_lang l (nth_tail n.+1 el) ->
    elab_rule (nth_tail n.+1 el) r er ->
    elab_lang ((name,r)::l) (nth_tail n el).
Proof.
  intros.
  eapply (@elab_lang_cons'_helper l (nth_tail n el));
    rewrite ?nth_tail_add1; eauto.
Qed.


Arguments nth_tail : simpl never.

(****************
 end nth_tail
*)

Definition subst_lang : lang :=
   [::[:> "G" : #"env", "A" : #"ty" %"G"
       ----------------------------------------------- ("snoc_wkn_hd")
       #"id" = #"snoc" #"wkn" #"hd" : #"sub" (#"ext" %"G" %"A") (#"ext" %"G" %"A")
   ];
   [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3",
       "A" : #"ty" %"G3",
       "e" : #"el" %"G2" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" %"f" (#"snoc" %"g" %"e")
       = #"snoc" (#"cmp" %"f" %"g") (#"el_subst" %"f" %"e")
       : #"sub" %"G1" (#"ext" %"G3" %"A")
   ];
   [:> "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty" %"G'",
       "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       ----------------------------------------------- ("snoc_hd")
       #"el_subst" (#"snoc" %"g" %"e") #"hd" = %"e"
       : #"el" %"G" (#"ty_subst" %"g" %"A")
  ];
  [:> "G" : #"env", "G'" : #"env",
      "g" : #"sub" %"G" %"G'",
      "A" : #"ty" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" %"g" %"e") #"wkn" = %"g" : #"sub" %"G" %"G'"
  ];
  [:| "G" : #"env", "A" : #"ty"(%"G")
       -----------------------------------------------
       #"hd" : #"el" (#"ext" %"G" %"A") (#"ty_subst" #"wkn" %"A")
  ];
  [:| "G" : #"env", "A" : #"ty" %"G"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" %"G" %"A") %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty" %"G'",
      "g" : #"sub" %"G" %"G'",
      "e" : #"el" %"G" (#"ty_subst" %"g" %"A")
       -----------------------------------------------
       #"snoc" "g" "e" : #"sub" %"G" (#"ext" %"G'" %"A")
  ];
  [:| "G" : #"env", "A": #"ty" %"G"
       -----------------------------------------------
       #"ext" "G" "A" : #"env"
  ]]%irule++subst_lang'.

Derive elab_subst_lang
       SuchThat (elab_lang subst_lang elab_subst_lang)
       As elab_subst_lang_pf.
Proof.
  repeat (elab(fun()=>
       lazy_match! goal with
       | [|-Core.le_sort _ _ (Exp.scon ?name _) _] => eapply (@Core.le_sort_refl' $name)
       | [|-Core.le_sort _ _ _ (Exp.scon ?name _)] => eapply (@Core.le_sort_refl' $name)
       | [|-Core.le_term _ _ _ _ (Exp.var _)] => reflexivity
       | [|-Core.le_term _ _ _ (Exp.var _) _] => reflexivity
       | [|-Core.le_term _ _ _ (Exp.con "ext" _) _] => eapply (@Core.le_term_refl' "ext"%string)
       | [|-Core.le_term _ _ _ _ (Exp.con "ext" _)] => eapply (@Core.le_term_refl' "ext"%string)
       | [|-Core.le_term _ _ _
                         (Exp.con "ty_subst" [:: _; ?g; ?gg'; ?gg])
                         (Exp.con "ty_subst" [:: _; ?g; ?gg'; ?gg])] =>
          eapply (@Core.le_term_refl' "ty_subst"%string)
               end)).
  (*TODO: why is this not done already?*)
  Focus 3.
  reflexivity.
  
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).

  Focus 2.
  elab(fun()=>()).

  Focus 5.
  reflexivity.
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).

  Focus 2.
  elab(fun()=>()).

  Focus 5.
  reflexivity.
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  simpl.

  reflexivity.
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  {
    eapply Core.le_term_trans.
    symmetry.
    eapply (@Core.le_term_by' "ty_subst_cmp"%string);elab(fun()=>reflexivity).
    eapply (Core.le_term_refl');elab(fun()=>easy_le_tac()).
  }
  
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).

  reflexivity.
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).

  symmetry.
  eapply (@Core.le_term_by' "ty_subst_cmp"%string);elab(fun()=>reflexivity).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
  elab(fun()=>()).
Qed.

 
    
Instance elab_subst_lang_inst : Elaborated subst_lang :=
  {
  elaboration := elab_subst_lang;
  elab_pf := elab_subst_lang_pf;
  }.
