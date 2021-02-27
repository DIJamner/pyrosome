Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Exp ARule ImCore Pf.
Import Exp.Notations ARule.Notations.
Require Import String.


Require Coq.derive.Derive.

Set Default Proof Mode "Ltac2".

Set Default Proof Mode "Classic".


Definition subst_lang : lang :=
   [::[:> "G" : #"env", "A" : #"ty"
       ----------------------------------------------- ("snoc_wkn_hd")
        #"snoc" #"wkn" #"hd" = #"id" : #"sub" (#"ext" %"G" %"A") (#"ext" %"G" %"A")
   ];
   [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2",
       "g" : #"sub" %"G2" %"G3",
       "A" : #"ty",
       "v" : #"val" %"G2" %"A"
       ----------------------------------------------- ("cmp_snoc")
       #"cmp" %"f" (#"snoc" %"g" %"v")
       = #"snoc" (#"cmp" %"f" %"g") (#"val_subst" %"f" %"v")
       : #"sub" %"G1" (#"ext" %"G3" %"A")
   ];
   [:> "G" : #"env", "G'" : #"env",
       "g" : #"sub" %"G" %"G'",
       "A" : #"ty",
       "v" : #"val" %"G" %"A"
       ----------------------------------------------- ("snoc_hd")
       #"val_subst" (#"snoc" %"g" %"v") #"hd" = %"v"
       : #"val" %"G" %"A"
  ];
  [:> "G" : #"env", "G'" : #"env",
      "g" : #"sub" %"G" %"G'",
      "A" : #"ty",
      "v" : #"val" %"G" %"A"
      ----------------------------------------------- ("wkn_snoc")
      #"cmp" (#"snoc" %"g" %"v") #"wkn" = %"g" : #"sub" %"G" %"G'"
  ];
  [:| "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"hd" : #"val" (#"ext" %"G" %"A") %"A"
  ];
  [:| "G" : #"env", "A" : #"ty"
       -----------------------------------------------
       #"wkn" : #"sub" (#"ext" %"G" %"A") %"G"
  ];
  [:| "G" : #"env", "G'" : #"env", "A" : #"ty",
      "g" : #"sub" %"G" %"G'",
      "e" : #"val" %"G" %"A" (*we restrict substitutions to values *)
       -----------------------------------------------
       #"snoc" "g" "e" : #"sub" %"G" (#"ext" %"G'" %"A")
  ];
  [:| "G" : #"env", "A": #"ty"
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
  [:> "G1" : #"env", "G2" : #"env",
       "g" : #"sub" %"G1" %"G2",
       "A" : #"ty", "v" : #"val" %"G2" %"A"
       ----------------------------------------------- ("el_subst_ret")
       #"el_subst" %"g" (#"ret" %"v")
       = #"ret" (#"val_subst" %"g" %"v")
       : #"el" %"G1" %"A"
  ];
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" %"G" %"A"
       -----------------------------------------------
       #"ret" "v" : #"el" %"G" %"A"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty", "v" : #"val" %"G3" %"A"
       ----------------------------------------------- ("val_subst_cmp")
       #"val_subst" %"f" (#"val_subst" %"g" %"v")
       = #"val_subst" (#"cmp" %"f" %"g") %"v"
       : #"val" %"G1" %"A"
  ]; 
  [:> "G" : #"env", "A" : #"ty", "e" : #"val" %"G" %"A"
       ----------------------------------------------- ("val_subst_id")
       #"val_subst" #"id" %"e" = %"e" : #"val" %"G" %"A"
  ]; 
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty", "v" : #"val" %"G'" %"A"
       -----------------------------------------------
       #"val_subst" "g" "v" : #"val" %"G" %"A"
  ];
  [:> "G1" : #"env", "G2" : #"env", "G3" : #"env",
       "f" : #"sub" %"G1" %"G2", "g" : #"sub" %"G2" %"G3",
       "A" : #"ty", "e" : #"el" %"G3" %"A"
       ----------------------------------------------- ("el_subst_cmp")
       #"el_subst" %"f" (#"el_subst" %"g" %"e")
       = #"el_subst" (#"cmp" %"f" %"g") %"e"
       : #"el" %"G1" %"A"
  ]; 
  [:> "G" : #"env", "A" : #"ty", "e" : #"el" %"G" %"A"
       ----------------------------------------------- ("el_subst_id")
       #"el_subst" #"id" %"e" = %"e" : #"el" %"G" %"A"
  ]; 
  [:| "G" : #"env", "G'" : #"env", "g" : #"sub" %"G" %"G'",
       "A" : #"ty", "e" : #"el" %"G'" %"A"
       -----------------------------------------------
       #"el_subst" "g" "e" : #"el" %"G" %"A"
  ]; 
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"val" "G" "A" srt
  ];
  [s| "G" : #"env", "A" : #"ty"
      -----------------------------------------------
      #"el" "G" "A" srt
  ];
  [s|  
      -----------------------------------------------
      #"ty" srt
  ];
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
   ]]%arule.


Import OptionMonad.
Definition simple_subst_to_pf_ty (e:exp) : option pf :=
  match e with
  | var x => Some (pvar x)
  | _ => None
  end.


Fixpoint simple_subst_to_pf_env (e:exp) : option pf :=
  match e with
  | var x => Some (pvar x)
  | con "emp" [::] => Some (pcon "emp" [::])
  | con "ext" [:: A; G] =>
    do pa <- simple_subst_to_pf_ty A;
       pG <- simple_subst_to_pf_env G;
       ret (pcon "ext" [:: pa; pG])
  | _ => None
  end.

Definition simple_subst_to_pf_sort (t:sort) : option pf :=
  match t with
  | scon "env" [::] => Some (pcon "env" [::])
  | scon "ty" [::] => Some (pcon "ty" [::])
  | scon "sub" [:: G'; G] =>
    do pG' <- simple_subst_to_pf_env G';
       pG <- simple_subst_to_pf_env G;
       ret (pcon "sub" [:: pG'; pG])
  | scon "el" [:: A; G] =>
    do pa <- simple_subst_to_pf_ty A;
       pG <- simple_subst_to_pf_env G;
       ret (pcon "el" [:: pa; pG])
  | scon "val" [:: A; G] =>
    do pa <- simple_subst_to_pf_ty A;
       pG <- simple_subst_to_pf_env G;
       ret (pcon "val" [:: pa; pG])
  | _ => None
  end.

Fixpoint simple_subst_to_pf_sub (c : pf_ctx) (e :exp) G_l : option (pf * pf) :=
  match e with
  | var x =>
    do (pcon "sub" [:: G_r;_]) <- named_list_lookup_err c x;
       ret (pvar x, G_r)
  | con "id" [::] =>
    do ret (pcon "id" [:: G_l], G_l)
  | con "cmp" [:: g; f] =>
    do (p_f,G_fr) <- simple_subst_to_pf_sub c f G_l;
       (p_g, G_gr) <- simple_subst_to_pf_sub c g G_fr;
       ret (pcon "cmp" [:: p_g; p_f; G_gr; G_fr; G_l], G_gr)
  | con "forget" [::] =>
    do ret (pcon "forget" [:: G_l], pcon "emp" [::])
  | con "snoc" [:: e; f] =>
    do (p_f,G_fr) <- simple_subst_to_pf_sub c f G_l;
       (p_e, pA) <- simple_subst_to_pf_val c e G_l;
       ret (pcon "snoc" [:: p_e; p_f; pA; G_fr; G_l], pcon "ext" [:: pA; G_fr])
  | con "wkn" [::] =>
    do (pcon "ext" [:: A; G]) <- Some G_l;
       ret (pcon "wkn" [:: A; G], G)
  | _ => None
  end
with simple_subst_to_pf_val c e G : option (pf * pf) :=
       match e with
       | var x =>
         do (pcon "val" [:: A; _]) <- named_list_lookup_err c x;
         ret (pvar x, A)
       | con "val_subst" [:: e; f] =>
         do (p_f,G_fr) <- simple_subst_to_pf_sub c f G;
            (p_e, pA) <- simple_subst_to_pf_val c e G_fr;
            ret (pcon "val_subst" [:: p_e; pA; p_f; G_fr; G], pA)
      | con "hd" [::] =>
        do (pcon "ext" [:: A; G]) <- Some G;
           ret (pcon "hd" [:: A; G], A)
       | _ => None
       end
with simple_subst_to_pf_el c e G : option (pf * pf) :=
       match e with
       | var x =>
         do (pcon "el" [:: A; _]) <- named_list_lookup_err c x;
         ret (pvar x, A)
       | con "el_subst" [:: e; f] =>
         do (p_f,G_fr) <- simple_subst_to_pf_sub c f G;
            (p_e, pA) <- simple_subst_to_pf_el c e G_fr;
            ret (pcon "el_subst" [:: p_e; pA; p_f; G_fr; G], pA)
      | con "ret" [:: v] =>
        do (pv,A) <- simple_subst_to_pf_val c v G;
           ret (pcon "ret" [:: pv; A; G], A)
       | _ => None
       end.


Definition simple_subst_to_pf_term (c : pf_ctx) (e :exp) t : option pf :=
  match t with
  | pcon "env" [::] => simple_subst_to_pf_env e
  | pcon "ty" [::] => simple_subst_to_pf_ty e
  | pcon "sub" [:: _ ; G_l] =>
    do (p,_) <- simple_subst_to_pf_sub c e G_l;
       ret p
  | pcon "el" [:: _ ; G] =>
    do (p,_) <- simple_subst_to_pf_el c e G;
       ret p
  | pcon "val" [:: _ ; G] =>
    do (p,_) <- simple_subst_to_pf_val c e G;
       ret p
  | _ => None
  end.

Fixpoint simple_subst_to_pf_ctx (c : ctx) : option pf_ctx :=
  match c with
  | [::] => do ret [::]
  | (n,t)::c' =>
    do pc' <- simple_subst_to_pf_ctx c';
       pt <- simple_subst_to_pf_sort t;
       ret (n,pt)::pc'
  end.

Definition simple_subst_to_pf_rule (r : rule) : option rule_pf :=
  match r with
  | sort_rule c args =>
    do pc <- simple_subst_to_pf_ctx c;
    ret sort_rule_pf pc args
  | term_rule c args t =>
    do pt <- simple_subst_to_pf_sort t;
       pc <- simple_subst_to_pf_ctx c;
    ret term_rule_pf pc args pt
  | sort_le c t1 t2 =>
    do pt1 <- simple_subst_to_pf_sort t1;
       pt2 <- simple_subst_to_pf_sort t2;
       pc <- simple_subst_to_pf_ctx c;
    ret sort_le_pf pc pt1 pt2
  | term_le c e1 e2 t =>
    do pt <- simple_subst_to_pf_sort t;
       pc <- simple_subst_to_pf_ctx c;
       pe1 <- simple_subst_to_pf_term pc e1 pt;
       pe2 <- simple_subst_to_pf_term pc e2 pt;
    ret term_le_pf pc pe1 pe2 pt
end.

Fixpoint simple_subst_to_pf_lang (l : lang) : option pf_lang :=
  match l with
  | [::] => do ret [::]
  | (n,r)::l' =>
    do pl' <- simple_subst_to_pf_lang l';
       pr <- simple_subst_to_pf_rule r;
       ret (n,pr)::pl'
  end.


Ltac prove_wf_with_fn f :=
  match goal with
  | [|- wf_lang ?l] =>
    remember (f l) as mp eqn:Heqmp;
    vm_compute in Heqmp;
    match goal with
      [ H : _ = Some ?pl|-_] =>
      pose (p:=pl); clear H;
      apply (@synth_wf_lang_related p)
    end
  | [|- wf_sort _ _ ?t] =>
    remember (simple_subst_to_pf_sort t) as mp eqn:Heqmp;
      vm_compute in Heqmp;
    match goal with
      [ H : _ = Some ?pl|-_] =>
      pose (p:=pl); clear H;
        apply (synth_wf_sort_related _ (p:= p))
    end
  end;
  by compute.

Definition vsubst_elab :=
  Eval compute in
  match simple_subst_to_pf_lang (nth_tail 0 subst_lang) with
  | Some l => l
  | None => [::]
  end.
Goal match vsubst_elab with [::] => False | _ => True end.
    by compute.
Qed.

Lemma simplesubst_wf : wf_lang subst_lang.
Proof.
  prove_wf_with_fn simple_subst_to_pf_lang.
Qed.

