
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Utils Require Import Utils.
From Named Require Import Exp Rule Core.
Require Import String.




(*Notation ob := (con 0 [::]).
Notation hom a b := (con 1 [:: b; a]%exp_scope).
Notation id a := (con 2 [:: a]%exp_scope).
Notation cmp a b c f g := (con 3 [:: f; g; c; b; a]%exp_scope).*)       

(* syntax of categories *)
Definition cat_lang : lang :=
  [::
     [:> "G1" : #"env", "G2" : #"env", "G3" : #"env", "G4" : #"env",
         "f" : #"sub"(%"G1",%"G2"), "g" : #"sub"(%"G2",%"G3"), "h" : #"sub"(%"G3",%"G4")
      |- ("cmp_assoc") #"cmp"(%"G1", %"G2", %"G4", %"f",
                              #"cmp"(%"G2",%"G3",%"G4", %"g",%"h"))
         = #"cmp"(%"G1", %"G3", %"G4", #"cmp"(%"G1",%"G2",%"G3", %"f",%"g"), %"h")
         : #"sub"(%"G1",%"G4")];  
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub"(%"G",%"G'")
   |- ("id_left") #"cmp"(%"G", %"G", %"G'", #"id"(%"G"), %"f") = %"f" : #"sub"(%"G",%"G'")];
  [:> "G" : #"env", "G'" : #"env", "f" : #"sub"(%"G",%"G'")
   |- ("id_right") #"cmp"(%"G", %"G'", %"G'", %"f", #"id"(%"G'")) = %"f" : #"sub"(%"G",%"G'")];
  [:| "G1" : #"env", "G2" : #"env", "G3" : #"env",
      "f" : #"sub"(%"G1", %"G2"),
      "g" : #"sub"(%"G2", %"G3")
   |- "cmp" : #"sub"(%"G1",%"G3")];
  [:| "G" : #"env" |- "id" : #"sub" (%"G", %"G")];
  [s| "G" : #"env", "G'" : #"env" |- "sub"];
  [s| |- "env"]
  ].

Definition var_lang : lang :=
  [::
     [:| "G" : #"env", "t" : #"ty",
         "v" : #"var"(%"G", %"t"),
         "_" : #"Pf"(#"var_in"(%"G", %"t", %"v"))
      |- "v-ref" : #"el"(%"G", %"t")];
     [:| "G" : #"env", "t" : #"ty"(%"G"), "s" : #"string"
      |- "v" : #"var"(%"G", %"t")]; 
     [s| "G" : #"env", "t" : #"ty"(%"G") |- "var"];
     (*TODO: elements of string sort and matching*)
     [s| |- "string"]].


Notation ty a := (con 7 [:: a]%exp_scope).
Notation ty_subst a b s t := (con 8 [:: t; s; b; a]%exp_scope).
Notation el a t := (con 9 [:: t; a]%exp_scope).
Notation el_subst a b s t m := (con 10 [:: m; t; s; b; a]%exp_scope).

 Notation emp := (con 15 [::]%exp_scope).
Notation forget a := (con 16 [:: a]%exp_scope).

Notation ext g a := (con 19 [:: a; g]%exp_scope) (*[:: ty 0; ob]*).
Notation snoc a b t g n := (con 20 [:: n; g; t; b; a]%exp_scope)
(*[:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]*).
Notation p a t := (con 21 [:: t; a]%exp_scope).
Notation q a t := (con 22 [:: t; a]%exp_scope).

(* convenience def to avoid repetition *)
Definition el_srt_subst a b g e :=
  (el a (ty_subst a b g e)).

Definition subst_lang : lang :=
  (term_le [:: ty 0; ob]
              (id (ext 0 1))
              (snoc (ext 0 1) 0 1 (p 0 1) (q 0 1))
              (hom (ext 0 1) (ext 0 1)))::
   (term_le [:: el_srt_subst 1 2 3 5;
               ty 2; hom 0 1; hom 1 2; ob; ob; ob]
        (cmp 0 1 (ext 2 5) (snoc 1 2 5 3 6) 4)
        (snoc 0 2 5
              (cmp 0 1 2 3 4)
              (el_subst 0 1 4 (ty_subst 1 2 3 5) 6))
        (hom 0 (ext 2 5)))::
  (term_le [:: el_srt_subst 0 1 2 3; ty 1; hom 0 1; ob; ob]
           (el_subst 0 (ext 1 3) (snoc 0 1 3 2 4)
                     (ty_subst (ext 1 3) 1 (p 1 3) 3) (q 1 3))
           4
           (el_srt_subst 0 1 2 3))::
  (term_le [:: el_srt_subst 0 1 2 3; ty 1; hom 0 1; ob; ob]
           (cmp 0 (ext 1 3) 1
                (p 1 3)
                (snoc 0 1 3 2 4))
           2
           (hom 0 1))::
  (term_rule [:: ty 0; ob]
             (el_srt_subst (ext 0 1) 0 (p 0 1) 1))::
  (term_rule [:: ty 0; ob] (hom (ext 0 1) 0))::
  (term_rule [:: el 0 (ty_subst 0 1 3 2); hom 0 1; ty 1; ob; ob]
             (hom 0 (ext 1 2)))::
  (term_rule [:: ty 0; ob] ob)::
  (term_le [::] (id emp) (forget emp) (hom emp emp))::
  (term_le [:: hom 0 1; ob; ob] (cmp 0 1 emp (forget 1) 2) (forget 0) (hom 0 emp))::
  (term_rule [:: ob] (hom 0 emp))::
  (term_rule [::] ob)::
  (* el_subst compose to sequence *)
  (term_le [:: ty 2; hom 1 2; hom 0 1; ob; ob; ob]
           (ty_subst 0 2 (cmp 0 1 2 4 3) 5)
           (ty_subst 0 1 3 (ty_subst 1 2 4 5))
           (ty 0))::
  (* id el_subst; may be the first rule that holds, but isn't recognized. *)
  (term_le [:: el 0 1; ty 0; ob] (el_subst 0 0 (id 0) 1 2) 2 (el 0 1))::
  (* ty_subst compose to sequence *)
  (term_le [:: ty 2; hom 1 2; hom 0 1; ob; ob; ob]
           (ty_subst 0 2 (cmp 0 1 2 4 3) 5)
           (ty_subst 0 1 3 (ty_subst 1 2 4 5))
           (ty 0))::
  (* id ty_subst *)
  (term_le [:: ty 0; ob] (ty_subst 0 0 (id 0) 1) 1 (ty 0))::
  (term_rule [:: el 1 3; ty 1; hom 0 1; ob; ob] (el 0 (ty_subst 0 1 2 3)))::
  (sort_rule [:: ty 0; ob])::
  (term_rule [:: ty 1; hom 0 1; ob; ob] (ty 0))::
  (sort_rule [:: ob])::cat_lang.

Require Import Setoid.



Lemma subst_lang_wf : wf_lang subst_lang.
Proof using .
  wf_lang_eauto.

  {
    constructor; eauto with judgment.
  ltac2:(apply_term_constr()).
  repeat eapply wf_subst_cons; eauto with judgment.
  cbv.
  eapply wf_term_conv.
  eauto with judgment.
  ltac2:(apply_term_constr()).
  repeat eapply wf_subst_cons; eauto with judgment.
  eapply sort_con_mor.
  cbv.
  eapply le_subst_cons.
  2:{
    (* TODO: automate: *)
    instantiate (1 := ty 0).
    cbv.
    Eval cbv in (nth_level (sort_rule [::]) subst_lang 14).
    symmetry.
    ltac2:(apply_term_rule constr:(14)).
    eauto with judgment.
  }
  eauto with judgment.
  }  
  {
    constructor; auto with judgment.
    apply: wf_term_conv; first by auto with judgment.
    instantiate (1 := (el 0 (ty_subst 0 (ext 1 3) (snoc 0 1 3 2 4) (ty_subst (ext 1 3) 1 (p 1 3) 3)))).
    apply:type_wf_term_recognizes; eauto with judgment.
    unfold el_srt_subst.
    eapply sort_con_mor.
    repeat eapply subst_cons_mor.
    auto with judgment.
    auto with judgment.
    
    eapply le_term_trans.
    instantiate (2 := ty 0); cbv.
    - symmetry (* TODO: handle in tactic *).
      instantiate (1 := ty_subst 0 1
                           (cmp 0 (ext 1 3) 1
                                (p 1 3) (snoc 0 1 3 2 4))
                           3)
      (*TODO: handle in tactic*).
      ltac2:(apply_term_rule constr:(14)).
      eauto with judgment.
    -
      (* TODO: should be handled by tactic *)
      change (ty 0)[/[:: var 0]/]
        with (ty 0)[/[:: var 3; var 2; var 1; var 0]/].
      eapply term_con_mor.
      repeat eapply subst_cons_mor;
        auto with judgment.
      instantiate (1:= hom 0 1).
      cbv.
      ltac2:(apply_term_rule constr:(23)).
      eauto with judgment.
  }
  { (* element identity substitution *)
    constructor;auto with judgment.
    
    (*TODO: should be handledby this rewriting:
      match goal with
      |- wf_term ?l ?c _ _ => 
      setoid_replace (el 0 1) with (el 0 (ty_subst 0 0 (id 0) 1))
                             using relation (le_sort l c) at 2
    end.
     *)
    apply:wf_term_conv; first by auto with judgment.
    instantiate (1:= el 0 (ty_subst 0 0 (id 0) 1)).
    auto with judgment.

    eapply sort_con_mor.
    eapply subst_cons_mor.
    eapply subst_cons_mor; try reflexivity.
    eauto with judgment.
    change ( [:: el 0 1; ty 0; ob] ) with ( [:: el 0 1]++[:: ty 0; ob] ).
    eapply le_mono_ctx.
    eapply le_term_by.
    instantiate (1:= ty 0).
    by compute.
  }
  Unshelve.
  all: try exact (con 0 [::]).
  all: exact [::].
Qed.

