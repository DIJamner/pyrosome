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
  
Instance rec_cat_lang : LangRecognize cat_lang :=
  { le_sort_dec := generic_sort_dec_fuel 10 cat_lang;
    decide_le_sort := @generic_decide_le_sort 10 cat_lang;
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

Lemma cat_lang_wf : wf_lang cat_lang.
Proof.
  apply (@decide_wf_lang _ _ 100).
  vm_compute; reflexivity.
Qed.

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
       #"el_subst" %"f" (#"el_subst" %"g" %"e")
       = #"el_subst" (#"cmp" %"f" %"g") %"e"
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
       #"ty_subst" %"f" (#"ty_subst" %"g" %"A")
       = #"ty_subst" (#"cmp" %"f" %"g") %"A"
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
  ]]%arule++cat_lang.


(* combines le_sort_by and le_sort_subst *)
Lemma le_sort_by' name l c : forall c' e1 e2 s1 s2 e1' e2',
    [s> !c' 
         ----------------------------------------------- (name)
         {e1} = {e2} ]%arule \in l ->
    len_eq s1 c' ->
    len_eq s2 c' -> 
    e1' = e1[/with_names_from c' s1/] ->
    e2' = e2[/with_names_from c' s2/] ->
    le_subst l c c' (with_names_from c' s1) (with_names_from c' s2) ->
    le_sort l c e1' e2'.
Proof using .
  intros.
  rewrite H2; clear H2.
  rewrite H3; clear H3.
  eapply le_sort_subst>[| eapply le_sort_by; eauto].
  auto.
Qed.

(* combines le_term_by and le_term_subst *)
Lemma le_term_by' name l c : forall c' t e1 e2 s1 s2 t' e1' e2',
    [:> !c' 
        ----------------------------------------------- (name)
        {e1} = {e2} : {t}]%arule \in l ->
    len_eq s1 c' ->
    len_eq s2 c' ->                          
    t' = t[/with_names_from c' s2/] ->
    e1' = e1[/with_names_from c' s1/] ->
    e2' = e2[/with_names_from c' s2/] ->
      le_subst l c c' (with_names_from c' s1) (with_names_from c' s2) ->
    le_term l c t' e1' e2'.
Proof using .
  intros.
  rewrite H2; clear H2.
  rewrite H3; clear H3.
  rewrite H4; clear H4.
  eapply le_term_subst>[| eapply le_term_by; eauto].
  auto.
Qed.
(*

(*TODO: temp; needs improvement*)
Lemma le_sort_refl' name l c args : forall c' s1 s2 e1' e2',
    (name, sort_rule c' args) \in l ->
    len_eq s1 c' ->
    len_eq s2 c' ->
    len_eq s1 args ->
    e1' = scon name s1 ->
    e2' = scon name s2 ->
    le_subst l c c' (with_names_from c' s1) (with_names_from c' s2) ->
    le_sort l c e1' e2'.
Proof using .
Admitted.
  

Lemma nth_tail_in_bound {A : eqType} (e:A) m n l
        : m <= n -> e \in nth_tail n l -> e \in nth_tail m l.
Admitted.
 *)

Fixpoint sub_decompose g f : exp :=
  if f == g then {{e #"id"}}
  else match f with
       | con "cmp" [:: h; f'] =>
         {{e #"cmp" {sub_decompose g f'} {h} }}
       | _ => {{e #"ERR"}}
       end.

(* TODO: the right way to do the elab is some bidirectional thing 
   I think. For now special casing el_subst
*)         
Instance rec_subst_lang' : LangRecognize subst_lang' :=
  {  le_sort_dec := generic_sort_dec_fuel 10 subst_lang';
    decide_le_sort := @generic_decide_le_sort 10 subst_lang';
(*  le_sort_dec n c t1 t2 :=
      (t1 == t2) ||
      ((n <= 6) &&
       (c == [:: ("e"%string, {{s#"el" %"G3" %"A"}}); ("A"%string, {{s#"ty" %"G3"}});
        ("g"%string, {{s#"sub" %"G2" %"G3"}}); ("f"%string, {{s#"sub" %"G1" %"G2"}}); 
       ("G3"%string, {{s#"env"}}); ("G2"%string, {{s#"env"}}); ("G1"%string, {{s#"env"}})])&&
       (t1=={{s#"el" %"G1" (#"ty_subst" %"f" (#"ty_subst" %"g" %"A"))}})&&
       (t2=={{s#"el" %"G1" (#"ty_subst" (#"cmp" %"f" %"g") %"A")}}));*)
    term_args_elab c s name t := 
      match name, t, s with
      | "forget", scon "sub" [:: _; G],_ => [:: G]
      | "id", scon "sub" [:: _; G],_ => [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r c f G1 in
        [:: g; f; G3; G2; G1]
      | "ty_subst", scon "ty" [:: G], [:: A; g] =>
        let G' := cat_lang_sub_r c g G in
        [:: A; g; G'; G]
      | "el_subst", scon "el" [:: (con "ty_subst" [:: A; f]); G], [:: e; g] =>
        let G' := cat_lang_sub_r c g G in
        (* need to pull a g substitution off of f;
           first run f to simplify
         *)
        let f' := term_par_step_n subst_lang' f 100 in
        let f'' := sub_decompose g f' in
        [:: e; (con "ty_subst" [:: A; f'']); g; G'; G]
      (* special case for id subst since it can disappear; only works if g ~ id*)
      | "el_subst", scon "el" [:: A; G], [:: e; g] =>
        let G' := cat_lang_sub_r c g G in
        (* need to pull a g substitution off of f;
           first run f to simplify
         *)
        [:: e; A; g; G'; G]
      | _,_,_ => s
      end%string;
    sort_args_elab c s _ := s
  }.
(*
Proof.
  {
    intros n c t1 t2 _ _ _.
    ltac1:(move /orP => []).
    {
      ltac1:(move /eqP ->);
        apply le_sort_refl.
    }
    {
      ltac1:(move => /andP [] /andP [] /andP [nlt] /eqP -> /eqP -> /eqP ->).
      eapply (le_sort_refl' (name:="el"%string)).
      ltac1:(simple eapply nth_tail_in_bound); eauto.
      match!goal with
      | [|- is_true((?n,?e)\in ?l)]=>
        (*TODO: this can be improved a bit*)
        assert ($e = named_list_lookup $e $l $n); cbv; solve[auto]
      end.
      repeat constructor.
      repeat constructor.
      repeat constructor.
      reflexivity.
      reflexivity.
      {
        constructor.
        constructor.
        constructor.
        {
          simpl.
          apply le_term_refl.
        }
        {
          eapply (le_term_by' (name:="ty_subst_cmp"%string)); eauto.
          
          ltac1:(simple eapply nth_tail_in_bound); eauto.
          match!goal with
          | [|- is_true((?n,?e)\in ?l)]=>
            (*TODO: this can be improved a bit*)
            assert ($e = named_list_lookup $e $l $n); cbv; solve[auto]
          end.
          repeat constructor.
          repeat constructor.
          reflexivity.
          reflexivity.
          reflexivity.
          simpl.
          repeat (constructor>[| eapply le_term_refl]).
          constructor.
        }
      }
    }
  }
  Unshelve.
  exact ({{e%"ERR"}}).
  exact ({{e%"ERR"}}).
Defined.
*)
    
Lemma unfold_wf_term_dec l lr n c name s t fuel'
  : wf_term_dec lr  n c (con name s) t (S fuel')
    = match named_list_lookup_err (nth_tail n l) name with
      | Some (term_rule c' args t') =>
        let es := @term_args_elab l lr c s name t in
        (wf_sort_dec lr n c t'[/with_names_from c' es/] fuel') &&
        (le_sort_dec n c t'[/with_names_from c' es/] t) &&
        (wf_args_dec lr n c s args es c' fuel')
      | _ => false
      end.
Proof.
  reflexivity.
Qed.

Lemma unfold_wf_args_dec l (lr : LangRecognize l) n c s args es c' fuel'
  : wf_args_dec lr n c s args es c' (S fuel') =
         match c',es, args, s with
         | [::], [::], [::], [::] => true
         | [::], _, _, _ => false
         | (name,t)::c'', [::], _, _ => false
         | (name,t)::c'', e::es', [::], [::] =>
           (wf_term_dec lr n c e t[/with_names_from c'' es'/] fuel') &&
           (wf_args_dec lr n c [::] [::] es' c'' fuel')
         | (name,t)::c'', e::es', name'::args', e'::s' =>
           if name == name'
           then (e == e') &&
                (wf_term_dec lr n c e t[/with_names_from c'' es'/] fuel') &&
                (wf_args_dec lr n c s' args' es' c'' fuel')
           else (wf_term_dec lr n c e t[/with_names_from c'' es'/] fuel') &&
                (wf_args_dec lr n c s args es' c'' fuel')
         | _,_,_,_ => false (*TODO?*)
         end.
Proof.
  reflexivity.
Qed.

Lemma subst_lang'_wf : wf_lang subst_lang'.
Proof.
  apply (@decide_wf_lang _ _ 100); vm_compute; reflexivity.
Qed.


(*
Fixpoint subst_lang'_reduce_sub e : exp :=
  match e with
  | con "cmp" [::g; f] =>
    match subst_lang'_reduce_sub g, subst_lang'_reduce_sub f with
    | con "id" [::], f' => f'
    | g', con "id" [::] => g'
    | g',f' => (*TODO: incomplete; cmp assoc*) {{e #"cmp" {f'} {g'} }}
    end
  (* TODO: incomplete*)
  | _ => e
  end.

Fixpoint subst_lang'_reduce_ty e : exp :=
  match e with
  | con "ty_subst" [:: A; g] =>
    match subst_lang'_reduce_sub g, subst_lang'_reduce_ty A with
    | con "id" [::], A' => A'
    | g', con "ty_subst" [:: B; f] =>
      let gf := subst_lang'_reduce_sub {{e #"cmp" {g} {f} }} in
      {{e #"ty_subst" {gf} {B} }}
    | g', A' => {{e #"ty_subst" {g'} {A'} }}
    end
  (* TODO: incomplete*)
  | _ => e
  end.
*)
(* TODO: congruence is trickier for this version*)
(*
Lemma subst_lang'_reduce_sub_le c e t
  : wf_term subst_lang' c e t ->
    le_term subst_lang' c t e (subst_lang'_reduce_sub e).
Proof.
  induction e.
  { intros _; simpl; eapply le_term_refl. }
  {
    ltac1:(case neq: (n == "cmp")%string).
    {
      ltac1:(move: neq => /eqP ->).
      repeat (destruct l;
              try (solve[intros; simpl; eapply le_term_refl])).
      destruct H.
      destruct H0.
      destruct H1.
      Search _ le_term.
      apply Tactics.le_term_refl'.
      
    }
    {
      simpl.
      destruct l; simpl.
      { intros; simpl; eapply le_term_refl. }
*)
(*
  
#[refine]
Instance rec_subst_lang' : LangRecognize subst_lang' :=
  { le_sort_dec _ _ t1 t2 :=
      match t1,t2 with
      | scon "ty" [::A1; G1], scon "ty" [::A2; G2] =>
        (G1 == G2)&&(subst_lang'_reduce_ty A1 == subst_lang'_reduce_ty A2)
      | _, _ => t1 == t2
      end;
      (* TODO: extend *)
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
*)

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
  ]]%arule++subst_lang'.

Eval compute in (term_par_step_n subst_lang
                               {{e #"el_subst" (#"snoc" (#"snoc" (#"snoc" #"forget" %"y") %"x") %"e")
                                   (#"el_subst" #"wkn" (#"el_subst" #"wkn" #"hd"))}} 7).
