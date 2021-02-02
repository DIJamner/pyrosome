Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils Monad.
From Named Require Import Exp ARule ImCore Pf Interactive.
Import Exp.Notations ARule.Notations.
Require Import String.


Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

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

Set Default Proof Mode "Classic".

(*TODO: move somewhere? need to deal w/ cat_lang *)
Ltac nth_tail_show_hd :=
  erewrite nth_tail_show_hd;[cbn[nth cat_lang]| by compute].


Ltac store_bound_comp_as Hcmp :=
  match goal with
    [|- context ctx [Mbind ?f ?comp] ]=>
    let cmp := fresh "comp" in
    remember comp as cmp eqn:Hcmp;
    let comp' := eval hnf in comp in
    change (cmp = comp') in Hcmp
  end.


Ltac store_bound_comp_as_in Hcmp H :=
  match type of H with
    context ctx [Mbind ?f ?comp]=>
    let cmp := fresh "comp" in
    remember comp as cmp eqn:Hcmp in H;
    let comp' := eval hnf in comp in
    change (cmp = comp') in Hcmp
  end.

(*TODO: get "global" working*)
Opaque Mbind Mret.

(*TODO: make a derive version*)
Lemma cat_lang_ok : find_wf_lang_elaboration cat_lang.
Proof.
  unfold find_wf_lang_elaboration.
  enter_interactive.
  rewrite <-(@nth_tail_0 _ cat_lang) at 1.
  nth_tail_show_hd.
  repeat process_interactive.
  {
    instantiate_term hd (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd0 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  {
    instantiate_term hd1 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd2 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  {
    instantiate_term hd3 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd4 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  { instantiate_term hd5 (pvar "G1").
    vm_compute; eauto.
  }    
  repeat process_interactive.
  {
    instantiate_term hd6 (pvar "G2").
    vm_compute; eauto.
  }    
  repeat process_interactive.
  {
    instantiate_term hd7 (pvar "G4").
    vm_compute; eauto.
  }    
  repeat process_interactive.
  {
    instantiate_term hd8 (pcon "sub" [:: pvar "G2"; pvar "G1"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  
  {
    instantiate_term hd9 (pvar "G2").
    vm_compute; eauto.
  }    
  repeat process_interactive.
  {
    instantiate_term hd10 (pvar "G3").
    vm_compute; eauto.
  }    
  repeat process_interactive.
  {
    instantiate_term hd11 (pvar "G4").
    vm_compute; eauto.
  }    
  repeat process_interactive.
  {
    instantiate_term hd12 (pcon "sub" [:: pvar "G3"; pvar "G2"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd13 (pcon "sub" [:: pvar "G4"; pvar "G3"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd14 (pcon "sub" [:: pvar "G4"; pvar "G2"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd15 (pcon "sub" [:: pvar "G4"; pvar "G1"]).
    vm_compute.
    reflexivity.
  }
  {
    instantiate_term hd16 (pvar "G1").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd17 (pvar "G3").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd18 (pvar "G4").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd19 (pvar "G1").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd20 (pvar "G2").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd21 (pvar "G3").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd22 (pcon "sub" [:: pvar "G2"; pvar "G1"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd23 (pcon "sub" [:: pvar "G3"; pvar "G2"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd24 (pcon "sub" [:: pvar "G3"; pvar "G1"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd25 (pcon "sub" [:: pvar "G4"; pvar "G3"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd26 (pcon "sub" [:: pvar "G4"; pvar "G1"]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd27 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd28 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  {
    instantiate_term hd29 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd30 (pcon "env" [::]).
    vm_compute.
    reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd31 (pvar "G").
    vm_compute.
    eexists; reflexivity.
  }
  repeat process_interactive.
  {
    instantiate_term hd32 (pvar "G").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd33 (pvar "G'").
    vm_compute.
    eauto.
  }
  repeat process_interactive.
  {
    instantiate_term hd32 (pvar "G").
    vm_compute.
    eauto.
  }
    cbn.
  process_interactive.
  process_interactive.
  process_interactive.
  rewrite Mbind_assoc.
  
  process_interactive.
  rewrite Mbind_assoc.
  process_interactive.
  rewrite Mbind_assoc.
  rewrite Mbind_assoc.
  lazymatch goal with
   | [|- context ctx [focus ?comp] ]=>
     let comp' := eval hnf in comp in
         idtac comp' end.
         lazymatch comp' with
         | Mbind ?g (Mbind ?f ?cmp) ?tl =>
           idtac f
         end
  end.
  
  process_interactive.
  lazymatch goal with
  | [|- context out_ctx
                [Mbind ?f ?cmp ?tl] ]=>
    lazymatch cmp with
      context in_ctx [focus ?a] =>
      lazymatch type of tl with
      | list ?Q =>
      let hd := fresh "hd" in evar (hd : Q);
    let tl' := fresh "tl" in evar (tl' : list Q);
    instantiate_term tl (hd::tl')
      end
    end
  end.
  let x := context ctx [focus (f a)] in
      change x
  store_bound_comp_as Hcmp.
  store_bound_comp_as_in Hcmp0 Hcmp.
  store_bound_comp_as_in Hcmp1 Hcmp0.
  store_bound_comp_as_in Hcmp2 Hcmp1.
  rewrite Hcmp2 in Hcmp1.
  clear Hcmp2.
  rewrite monad_bind_ret in Hcmp1.
  store_bound_comp_as_in Hcmp2 Hcmp1.
  store_bound_comp_as_in Hcmp3 Hcmp2.
  rewrite monad_bind_ret in Hcmp3.
  pose (p := Mbind
            (fun s : seq exp =>
             Mbind (fun pe : pf => do ret [:: pe])
               (elab_term (nth_tail 1 cat_lang)
                  {{c"G1" : #"env",
                     "G2" : #"env",
                     "G3" : #"env",
                     "G4" : #"env",
                     "f" : #"sub" %"G1" %"G2",
                     "g" : #"sub" %"G2" %"G3"}} {{e%"G3"}}
                  {{s#"env"}} [/with_names_from (@nil (string *exp)) s /]))
            (lift
               (synth_wf_args (synth_wf_term (nth_tail 1 cat_lang)) [::]
                  {{c"G1" : #"env",
                     "G2" : #"env",
                     "G3" : #"env",
                     "G4" : #"env",
                     "f" : #"sub" %"G1" %"G2",
                     "g" : #"sub" %"G2" %"G3"}} {{c }}))).
  let x := eval hnf in p in idtac x.
  store_bound_comp_as_in Hcmp4 Hcmp3.
  rewrite Hcmp2 in Hcmp1.
  clear Hcmp2.
  rewrite monad_bind_ret in Hcmp1.
  
  Transparent elab_lang.
  hnf.
  unfold elab_lang.
  store_bound_comp_as Hcmp.
  unfold elab_rule in Hcmp.
  store_bound_comp_as_in Hcmp0 Hcmp.
  unfold elab_ctx in Hcmp0.
  unfold elab_sort.
  cbv match beta.
  match goal with
    [|- context ctx [named_list_lookup_err
                       (nth_tail ?n ?l) ?s]] =>
    let r := eval compute in (named_list_lookup_err
                                (nth_tail n l) s) in
    let x := context ctx [r] in
    change x; cbn
  end.
  rewrite !monad_bind_ret.
  process_interactive.
  simpl.
  cbn [elab_lang].
  pose (tst := nth_tail 1 cat_lang).
  
  unfold elab_lang.
  TODO: best way to reduce to first ask?
  
  
  process_interactive.

Derive cat_lang_pf SuchThat (Some cat_lang = synth_wf_lang cat_lang_pf) As cat_lang_pf_ok.
Proof.
  assert (elab_lang_structure cat_lang cat_lang_pf) > [ repeat constructor | ].
  cbn.
  match! goal with
  | [|- context c[?s \notin ?l]] =>
     let e:= Std.eval_vm None constr:($s \notin $l) in
     change ($c e)
  end.
  ltac1:(break_monadic_do).
  }
    auto with imcore.

Section InferSub.

  Context (subst_lang_el_ty : ctx -> exp (*G*) -> exp (*e*) -> exp).

  
  Fixpoint sub_decompose g f : exp :=
    if f == g then {{e #"id"}}
    else match f with
         | con "cmp" [:: h; f'] =>
           {{e #"cmp" {sub_decompose g f'} {h} }}
         | _ => {{e #"ERR"}}
         end.

  (*Only works sometimes; not guaranteed to be correct *)
  Definition ty_decompose g A :=
    if g == {{e #"id"}} then A
    else match A with
         | con "ty_subst" [:: A; g'] =>
           {{e #"ty_subst" {sub_decompose g g'} {A} }}
         | _ => {{e #"ERR: ty_decompose"}}
         end.

  Fixpoint cat_lang_sub_r c e G_l : exp :=
    match e with
    | con "id" [::] => G_l
    | con "cmp" [:: g; f] =>
      let G_lf := cat_lang_sub_r c f G_l in
      let G_lg := cat_lang_sub_r c g G_lf in
      G_lg
    | con "wkn" [::] =>
      match G_l with
      | con "ext" [:: _;G_r] => G_r
      | _ => {{e #"ERR"}}
      end
    | con "snoc" [:: e; f] =>
      let G' := cat_lang_sub_r c f G_l in
      let Af := subst_lang_el_ty c G' e in
      {{e #"ext" {G'} {ty_decompose f Af} }}
    | var x =>
      match named_list_lookup {{s #"ERR"}} c x with
      | scon "sub" [:: G; _] => G
      | _ => {{e #"ERR"}}
      end
    | _ => {{e #"ERR"}}
    end.

End InferSub.
  
Fixpoint subst_lang_el_ty c G e : exp :=
  match e,G with
  | var x,_ => 
    match named_list_lookup {{s #"ERR not in c"}} c x with
    | scon "el" [:: t; _] => t
    | _ => {{e #"ERR sort from c not in subst lang"}}
    end
  | con "hd" [::], con "ext" [:: A; G'] =>
    {{e #"ty_subst" #"wkn" %"A" }}
  | con "el_subst" [:: e'; g], _ =>
    let G' := cat_lang_sub_r subst_lang_el_ty c g G in
    let A := subst_lang_el_ty c G' e' in
    {{e #"ty_subst" {g} {A} }}
  | _, _ => {{e #"ERR: not in subst lang" }}
  end.

Import OptionMonad.

Instance rec_cat_lang : LangRecognize cat_lang :=
  { le_sort_dec := generic_sort_dec_fuel 10 cat_lang;
    decide_le_sort := @generic_decide_le_sort 10 cat_lang;
    term_args_elab c s name t := 
      match name, t, s with
      | "id", scon "sub" [:: _; G],_ => do ret [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r subst_lang_el_ty c f G1 in
        do ret [:: g; f; G3; G2; G1]
      | _,_,_ => do ret s
      end%string;
    sort_args_elab c s _ := do ret s
  }.

Lemma cat_lang_wf : wf_lang cat_lang.
Proof.
    apply (decide_wf_lang (fuel:=100));
    vm_compute; constructor.
Qed.


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
  ];
  [:> 
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
 
Instance rec_subst_lang : LangRecognize subst_lang :=
  {  le_sort_dec := generic_sort_dec_fuel 10 subst_lang;
    decide_le_sort := @generic_decide_le_sort 10 subst_lang;
    term_args_elab c s name t := 
      match name, t, s with
      | "forget", scon "sub" [:: _; G],_ => do ret [:: G]
      | "id", scon "sub" [:: _; G],_ => do ret [:: G]
      | "cmp", scon "sub" [:: G3; G1], [:: g; f] =>
        let G2 := cat_lang_sub_r subst_lang_el_ty c f G1 in
        do ret [:: g; f; G3; G2; G1]
      | "ty_subst", scon "ty" [:: G], [:: A; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        do ret [:: A; g; G'; G]
      | "el_subst", scon "el" [:: _; G], [:: e; g] =>
        let G' := cat_lang_sub_r subst_lang_el_ty c g G in
        let A := subst_lang_el_ty c G' e in
        do ret [:: e; A; g; G'; G]
      | "snoc", scon "sub" [:: con "ext" [:: A; G']; G], [:: e; g] =>
        do ret [:: e; g; A; G'; G]
      | "wkn", scon "sub" [:: G; con "ext" [:: A; _]], [::] =>
        do ret [:: A; G]
      | "hd", scon "el" [:: _; con "ext" [:: A; G]], [::] =>
        do ret [:: A; G]
      | _,_,_ => do ret s
      end%string;
    sort_args_elab c s _ := do ret s
  }.
  
Lemma subst_lang_wf : wf_lang subst_lang.
Proof.
    apply (decide_wf_lang (fuel:=100));
    vm_compute; constructor.
Qed.
