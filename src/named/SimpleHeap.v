Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core ElabWithPrefix
     SimpleVSubst Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Definition nat_lang_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"nat" srt
  ];
  [:|  
       -----------------------------------------------
       #"0" : #"nat"
  ];
  [:|  "n": #"nat"
       -----------------------------------------------
       #"1+" "n" : #"nat"
  ];
  [s|  "n": #"nat", "m": #"nat"
       -----------------------------------------------
       #"neq" "n" "m" srt
  ];
  [:|  "n": #"nat"
       -----------------------------------------------
       #"neq_0_l" : #"neq" #"0" (#"1+" "n")
  ];
  [:|  "n": #"nat"
       -----------------------------------------------
       #"neq_0_r" : #"neq" (#"1+" "n") #"0"
  ];
  [:|  "n": #"nat", "m": #"nat",
       "p" : #"neq" "n" "m"
       -----------------------------------------------
       #"neq_1+" "p" : #"neq" (#"1+" "n") (#"1+" "m")
  ]
  ]}.


Derive nat_lang
       SuchThat (Pre.elab_lang []
                               nat_lang_def
                               nat_lang)
       As nat_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_lang_wf : elab_pfs.

(*TODO: heap rules depend on inequality? not if it's ordered access *)
Definition heap_def : lang :=
  {[l
  
  [s|
      -----------------------------------------------
      #"heapty" srt
  ];
  [s| "HT" : #"heapty"
      -----------------------------------------------
      #"heap" "HT" srt
  ];
  [:| 
       -----------------------------------------------
       #"empty_ty" : #"heapty"
  ];
  [:| 
       -----------------------------------------------
       #"empty" : #"heap" #"empty_ty"
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty"
       -----------------------------------------------
       #"hset_ty" "HT" "n" "A" : #"heapty"
  ];
  [:|  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "A" : #"ty",
       "v" : #"val" #"emp" "A"
       -----------------------------------------------
       #"hset" "H" "n" "v" : #"heap" (#"hset_ty" "HT" "n" "A")
  ];
  [:=  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "B" : #"ty" (*TODO: make A A or A B?*)
       ----------------------------------------------- ("heap_ty_shadow")
       #"hset_ty" (#"hset_ty" "HT" "n" "A") "n" "B"
       = #"hset_ty" "HT" "n" "B"
   : #"heapty"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "A" : #"ty",
       "v" : #"val" #"emp" "A",
       "v'" : #"val" #"emp" "A"
       ----------------------------------------------- ("heap_shadow")
       #"hset" (#"hset" "H" "n" "v") "n" "v'"
       = #"hset" "H" "n" "v'"
   : #"heap" (#"hset_ty" "HT" "n" "A")
  ];
  [:=  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "m" : #"nat",
       "B" : #"ty",
       "p_neq" : #"neq" "n" "m"
       ----------------------------------------------- ("heap_ty_comm")
       #"hset_ty" (#"hset_ty" "HT" "n" "A") "m" "B"
       = #"hset_ty" (#"hset_ty" "HT" "m" "B") "n" "A"
   : #"heapty"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "A" : #"ty",
       "v" : #"val" #"emp" "A",
       "m" : #"nat",
       "B" : #"ty",
       "v'" : #"val" #"emp" "B",
       "p_neq" : #"neq" "n" "m"
       ----------------------------------------------- ("heap_comm")
       #"hset" (#"hset" "H" "n" "v") "m" "v'"
       = #"hset" (#"hset" "H" "m" "v'") "n" "v"
   : #"heap" (#"hset_ty" (#"hset_ty" "HT" "m" "B") "n" "A")
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "H" : #"heap" (#"hset_ty" "HT" "n" "A")
       -----------------------------------------------
       #"hget" "n" "H" : #"val" #"emp" "A"
  ];
  [:=  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "H" : #"heap" "HT",
       "v" : #"val" #"emp" "A"
       ----------------------------------------------- ("heap_get_found")
       #"hget" "n" (#"hset" "H" "n" "v") = "v" : #"val" #"emp" "A"
  ]
   (*TODO: add hget_missed? *)
  ]}.


(*TODO: duplicated; move to matches*)
Ltac unify_evar_fst_eq :=
  match goal with
  | [|- (let (x,_) := ?p in x) = ?y] =>
    let p':= open_constr:((y,_:term)) in
    unify p p';
    compute;
    reflexivity
  end.
Ltac unify_var_names s c :=
  let H' := fresh in
  assert (len_eq s c) as H';
  [ solve[repeat constructor]| clear H'];
  assert (map fst s = map fst c) as H';
  [ compute; repeat f_equal; unify_evar_fst_eq| clear H'].


Ltac eredex_steps_with lang name :=
  let mr := eval compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_:subst) in
          first [unify_var_names s c | fail 100 "could not unify var names"];
          first [ replace (eq_term l c' t e1 e2)
                    with (eq_term l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [| f_equal; compute; reflexivity (*TODO: is this general?*)]
                | fail 100 "could not replace with subst"];
          eapply (@eq_term_subst l c' s s c);
          [ try solve [cleanup_auto_elab]
          | eapply eq_subst_refl; try solve [cleanup_auto_elab]
          | eapply (@eq_term_by l c name tp e1p e2p); try solve [cleanup_auto_elab]]
        end
      | None =>
        fail 100 "rule not found in lang"
      end.

Derive heap
       SuchThat (Pre.elab_lang (nat_lang ++ value_subst)
                               heap_def
                               heap)
       As heap_wf.
Proof.
  setup_elab_lang.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  {
    break_elab_rule.
    eredex_steps_with heap "heap_ty_comm".
    repeat apply wf_subst_cons.
    constructor.
    all: try cleanup_auto_elab.
    eapply wf_term_var with (n := "p_neq").
    cleanup_auto_elab.
  }
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]);
    try apply eq_term_refl; cleanup_auto_elab.
  Unshelve.
  all:try apply eq_term_refl; cleanup_auto_elab.
Qed.
#[export] Hint Resolve heap_wf : elab_pfs.

(*simple heap operations w/axioms avoiding an explicit heap 
  TODO: depends on let, unit, natural numbers, nat-as-exp
*)
Definition heap_ops : lang :=
  {[l
  [:|  "n" : #"natural",
       "G" : #"env",
       "A" : #"ty",
       "e" : #"exp" "G" #"nat"
       -----------------------------------------------
       #"set" "n" "e" : #"exp" "G" #"unit"
  ];
  [:|  "n" : #"natural",
       "G" : #"env"
       -----------------------------------------------
       #"get" "n" : #"exp" "HT" "G" #"nat"
  ];
  [:=  "HT" : #"heapty",
       "n" : #"natural",
       "m" : #"natural",
       "G" : #"env",
       "A" : #"ty",
       "e" : #"val" #"G" "A"
       ----------------------------------------------- ("get comm")
       #"let" (#"get" "n") (#"let" (#"get" "m") "e")
       = #"let" (#"get" "m")
          (#"let" (#"get" "n")
            (#"exp_subst" (#"snoc" (#"snoc" #"id" #"hd") (#"val_subst" #"wkn" #"hd")) "e"))
       : #"exp" "HT" "G" "A"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"natural",
       "G" : #"env"
       ----------------------------------------------- ("set eta")
       #"set" "n" (#"get" "n") = #"tt" : #"exp" "HT" "G" "unit"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "G" : #"env",
       "A" : #"ty",
       "v" : #"val" "HT" "G" (#"lookup_ty" "HT" "n")
       ----------------------------------------------- ("set beta")
       #"let" (#"set" "n" "v") (#"let" (#"get" "n") "e")
       = #"let" (#"set" "n" "v") (#"exp_subst" (#"snoc" (#"snoc" #"id" "v") #"hd") "e")
       : #"exp" "HT" "G" "A"
  ]

  ]}.


(**)
Definition heap_ops : lang :=
  {[l
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "G" : #"env",
       "A" : #"ty",
       "v" : #"val" "G" "A" (*TODO: works? emp here is no good*)
       -----------------------------------------------
       #"set" "n" "v" : #"exp" (#"hset_ty" "HT" "n" "A") "G" #"unit"
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "G" : #"env"
       -----------------------------------------------
       #"get" "n" : #"exp" "HT" "G" (#"lookup_ty" "HT" "n")
  ];
  [:=  "HT" : #"heapty",
       "n" : #"nat",
       "m" : #"nat",
       "G" : #"env",
       "A" : #"ty",
       "e" : #"val" #"G" "A",
       ----------------------------------------------- ("get comm")
       #"let" (#"get" "n") (#"let" (#"get" "m") "e")
       = #"let" (#"get" "m") (#"let" (#"get" "n") "e")
       : #"exp" "HT" "G" "A"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "G" : #"env"
       ----------------------------------------------- ("set eta")
       (#"set" "n" (#"get" "n")) = #"tt" : #"exp" "HT" "G" "unit"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "G" : #"env",
       "A" : #"ty",
       "v" : #"val" "HT" "G" (#"lookup_ty" "HT" "n")
       ----------------------------------------------- ("set beta")
       #"let" (#"set" "n" "v") (#"let" (#"get" "n") "e")
       = #"let" (#"set" "n" "v") (#"exp_subst" (#"snoc" (#"snoc" #"id" "v") #"hd") "e")
       : #"exp" "HT" "G" "A"
  ];

    ]}.
  [:|  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "A" : #"ty",
       "v" : #"val" #"emp" "A"
       -----------------------------------------------
       #"hset" "H" "n" "v" : #"heap" (#"hset_ty" "HT" "n" "A")
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "A" : #"ty",
       "v" : #"val" #"emp" "A",
       "v'" : #"val" #"emp" "A"
       ----------------------------------------------- ("heap_shadow")
       #"alloc" (#"hset" "H" "n" "v") "n" "v'"
       = #"hset" "H" "n" "v'"
   : #"heap" (#"hset_ty" "HT" "n" "A")
  ];
  [:=  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "m" : #"nat",
       "B" : #"ty",
       "p_neq" : #"neq" "n" "m"
       ----------------------------------------------- ("heap_ty_comm")
       #"hset_ty" (#"hset_ty" "HT" "n" "A") "m" "B"
       = #"hset_ty" (#"hset_ty" "HT" "m" "B") "n" "A"
   : #"heapty"
  ];
  [:=  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "n" : #"nat",
       "A" : #"ty",
       "v" : #"val" #"emp" "A",
       "m" : #"nat",
       "B" : #"ty",
       "v'" : #"val" #"emp" "B",
       "p_neq" : #"neq" "n" "m"
       ----------------------------------------------- ("heap_comm")
       #"hset" (#"hset" "H" "n" "v") "m" "v'"
       = #"hset" (#"hset" "H" "m" "v'") "n" "v"
   : #"heap" (#"hset_ty" (#"hset_ty" "HT" "m" "B") "n" "A")
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "H" : #"heap" (#"hset_ty" "HT" "n" "A")
       -----------------------------------------------
       #"hget" "n" "H" : #"val" #"emp" "A"
  ];
      

  [:|  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "A" : #"ty",
       "n" : #"nat",
       "n_A_pf" : #"nth_ty" "HT" "n" "A"
       -----------------------------------------------
       #"hget" "H" "n" : #"val" #"emp" "A"
  ];
  [:|  "HT" : #"heapty",
       "H" : #"heap" "HT",
       "A" : #"ty",
       "n" : #"nat",
       "n_A_pf" : #"nth_ty" "HT" "n" "A",           
       "v" : #"val" #"emp" #"A"
       -----------------------------------------------
       #"hset" "H" "n" "v" : #"heap" "HT"
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty",
       "p" : #"nth_ty" "HT" "n" "A",
       -----------------------------------------------
       #"wkn_nth_ty" "p" : #"nth_ty" (#"hcons_ty" #"HT" "B") "n" "A"
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "p" : #"heapty_size" "HT" "n",
       "A" : #"ty"
       -----------------------------------------------
       #"nth_ty_hd" "p" : #"nth_ty" (#"hcons_ty" "HT" "A") "n" "A"
  ];
  [s|  "HT" : #"heapty",
       "n" : #"nat",
       "A" : #"ty"
       -----------------------------------------------
       #"nth_ty" "HT" "n" "A" srt
  ];
  [:|  "HT" : #"heapty",
       "n" : #"nat",
       "p" : #"heapty_size" "HT" "n",
       "A" : #"ty"
       -----------------------------------------------
       #"size_1+" "p" : #"heapty_size" (#"hcons_ty" #"HT" "A") (#"1+" "n")
  ];
  [:|  
       -----------------------------------------------
       #"size_0" : #"heapty_size" #"empty_ty" "0"
  ];
  [s|  "HT" : #"heapty",
       "n" : #"nat"
       -----------------------------------------------
       #"heapty_size" "HT" "n" srt
  ];
