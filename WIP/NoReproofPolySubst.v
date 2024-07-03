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


(* TOOD: use a fn like this an a generic theorem

 *)
Definition underscore_rename (l : named_list string string) (n : string) : string :=
  match n with
  | String "_" s => "__" ++ s
  | _ =>     
      match named_list_lookup_err l n with
      | Some x => x
      | None => if inb n (map snd l) then String "_" n else n
      end
  end.


Definition no_underscore s :=
  match s with
  | String "_" _ => false
  | _ => true
  end.

(*TODO: move all to Utils*)
Local Hint Rewrite Is_true_forallb : utils.

Lemma pair_snd_in
  : forall (S A : Type) (l : named_list S A) (n : S) (a : A),
    In (n, a) l -> In a (map snd l).
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Local Hint Resolve pair_snd_in : utils.

Lemma In_nodup_codomain_same A B (l : list (A*B)) k1 k2 v
  : NoDup (map snd l) ->
    In (k1, v) l ->
    In (k2, v) l ->
    k1 = k2.
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush;
    safe_invert H;
    intuition eauto.
  all: exfalso.
  all: eauto using pair_snd_in.
Qed.


Lemma invert_string_cons c s c' s'
  : String c s = String c' s' <-> c = c' /\ s = s'.
Proof. prove_inversion_lemma. Qed.
Local Hint Rewrite invert_string_cons : utils.


Lemma invert_Ascii  b1 b2 b3 b4 b5 b6 b7 b8 b1' b2' b3' b4' b5' b6' b7' b8'
  : Ascii b1 b2 b3 b4 b5 b6 b7 b8 = Ascii b1' b2' b3' b4' b5' b6' b7' b8'
    <-> b1 = b1' /\ b2 = b2'/\ b3 = b3' /\ b4 = b4'/\ b5 = b5'/\ b6 = b6'/\ b7 = b7'/\ b8 = b8'.
Proof. prove_inversion_lemma. Qed.
Local Hint Rewrite invert_Ascii : utils.

Lemma underscore_rename_injective l 
  : Is_true (no_dupb (map snd l) && forallb no_underscore (map snd l)) ->
    Injective (underscore_rename l).
Proof.
  intro Hdup.
  basic_utils_crush.
  eapply use_no_dupb in H; try typeclasses eauto.
  intros a b.
  unfold underscore_rename.
  repeat (case_match; subst; try now (intros; subst; eauto)).
  all: intros; subst.
  all: repeat lazymatch goal with
         | H : Some _ = named_list_lookup_err _ _ |- _ =>
             eapply named_list_lookup_err_in in H (*
         | H : None = named_list_lookup_err _ _ |- _ =>
             eapply named_list_lookup_none in H*)
         | H : In (_, String "_" _) ?l,
             Hall : all _ (map snd ?l) |- _ =>
             eapply pair_snd_in in H;
             eapply in_all in H; eauto;
             cbn in H;
             tauto
         | H : In (_, "__" ++ _)%string ?l,
             Hall : all _ (map snd ?l) |- _ =>
             eapply pair_snd_in in H;
             eapply in_all in H; eauto;
             cbn in H;
             tauto
         end.
  all: eauto using In_nodup_codomain_same.
  all: basic_goal_prep;basic_utils_crush.
Qed.

Definition flip {A B} (x : A * B) := (snd x, fst x).

Definition underscore_rename_inverse (l : named_list string string) (n : string) : string :=
  match n with
  | String "_" s => s
  | _ =>     
      match named_list_lookup_err (map flip l) n with
      | Some x => x
      | None => n
      end
  end.

Ltac case_match' :=
  match goal with
  | |- context [ match ?e with
                 | _ => _
                 end ] => let e' := fresh in
                          remember e as e'; destruct e'
  | H : context [ match ?e with
                 | _ => _
                 end ] |- _  => let e' := fresh in
                          remember e as e'; destruct e'
  end.

Lemma in_map_flip A B (a:A) (b:B) l
  : In (a,b) (map flip l) <-> In (b,a) l.
Proof.
  unfold flip.
  induction l; basic_goal_prep;basic_utils_crush.
Qed.
Local Hint Rewrite in_map_flip : utils.

(*TODO: backport imporved statement*)
Lemma named_list_lookup_none
     : forall {S} [A : Type] (l : named_list S A) s `{Eqb_ok S},       
       None = named_list_lookup_err l s -> forall a, ~ In (s, a) l.
Proof.
  intros.
  eapply named_list_lookup_none; eauto.
Qed.

Lemma underscore_rename_inverse_spec1 l n
  : Is_true (no_dupb (map snd l) && forallb no_underscore (map snd l)) ->
    underscore_rename_inverse l (underscore_rename l n) = n.
Proof.
  intro Hdup.
  basic_utils_crush.
  eapply use_no_dupb in H; try typeclasses eauto.
  unfold underscore_rename_inverse, underscore_rename.
  (*issue: doesn't hit innermost match*)
  intros.
  repeat (case_match'; subst; eauto).
  all: repeat lazymatch goal with
         | H : Some _ = named_list_lookup_err _ _ |- _ =>
             eapply named_list_lookup_err_in in H
         | H : In (_, String "_" _) ?l,
             Hall : all _ (map snd ?l) |- _ =>
             eapply pair_snd_in in H;
             eapply in_all in H; eauto;
             cbn in H;
             tauto
         | H : In (_, "__" ++ _)%string ?l,
             Hall : all _ (map snd ?l) |- _ =>
             eapply pair_snd_in in H;
             eapply in_all in H; eauto;
             cbn in H;
             tauto
         end.
  all: rewrite ?in_map_flip in *.
  all: eauto using In_nodup_codomain_same.
  all: try congruence.
  all: autorewrite with bool utils in *.
  all: basic_goal_prep; subst.
  all: try now (exfalso; eauto using pair_snd_in).
  all: try lazymatch goal with 
       | H : None = named_list_lookup_err _ _ |- _ =>
           let H' := fresh in
           rename H into H';
           epose proof (named_list_lookup_none _ _ H') as H;
           clear H';
           exfalso; eapply H;
           eapply in_map_flip;
           now eauto
         end.
  
  basic_goal_prep;basic_utils_crush.
Qed.


Lemma underscore_rename_inverse_spec2 l n
  : Is_true (no_dupb (map snd l)
             && forallb no_underscore (map snd l)
             && all_freshb l) ->
    underscore_rename l (underscore_rename_inverse l n) = n.
Proof.
  intro Hdup.
  basic_utils_crush.
  eapply use_no_dupb in H1; try typeclasses eauto.
  eapply use_compute_all_fresh in H0; eauto.
  unfold underscore_rename_inverse, underscore_rename.
  (*issue: doesn't hit innermost match*)
  intros.
  repeat (case_match'; subst; eauto).
  all: repeat lazymatch goal with
         | H : Some _ = named_list_lookup_err _ _ |- _ =>
             eapply named_list_lookup_err_in in H
         | H : In (_, String "_" _) ?l,
             Hall : all _ (map snd ?l) |- _ =>
             eapply pair_snd_in in H;
             eapply in_all in H; eauto;
             cbn in H;
             tauto
         | H : In (_, "__" ++ _)%string ?l,
             Hall : all _ (map snd ?l) |- _ =>
             eapply pair_snd_in in H;
             eapply in_all in H; eauto;
             cbn in H;
             tauto
         end.
  all: rewrite ?in_map_flip in *.
  all: eauto using In_nodup_codomain_same.
  all: try congruence.
  all: eauto using in_all_fresh_same.   
  all: autorewrite with bool utils in *.
  all: basic_goal_prep; subst.
  all: try now (exfalso; eauto using pair_snd_in).
  all: try lazymatch goal with 
       | H : None = named_list_lookup_err _ _ |- _ =>
           let H' := fresh in
           rename H into H';
           epose proof (named_list_lookup_none _ _ H') as H;
           clear H';
           exfalso; eapply H;
           eapply in_map_flip;
           now eauto
         end.
  {
    TODO: this doesn't seem like a provable case;
    where did it come from?
    lazymatch goal with 
       | H : None = named_list_lookup_err _ _ |- _ =>
           let H' := fresh in
           rename H into H';
           epose proof (named_list_lookup_none _ _ H') as H;
           clear H';
           exfalso; eapply H;
           eapply in_map_flip
         end.
    TODO: need all_fresh
    
  all: try now (symmetry; eauto using In_nodup_codomain_same).
  
  basic_goal_prep;basic_utils_crush.
Qed.

(*TODO: careful; parameterize doesn't check freshness*)
Definition elt_cartesian_rename (n : string) : string :=
  match n with
  | "unit" => "elt"
  | "u" => "v"
  (* for injectivity *)
  | "elt" => "_elt"
  | "v" => "_v"
  (* TODO: prefix matching notation *)
  | String "_" s => "__" ++ s
  (* end injectivity *)
  | _ => n
  end.

(*TODO: I think this exists in coqutil*)
Ltac simple_case_match :=
  match goal with
  | |- context [ match ?e with
                 | _ => _
                 end ] => destruct e
  end.

Ltac prove_injective :=
  lazymatch goal with
  | |- Injective ?f =>
      unfold f
  end;
  intros ? ?;
    repeat (simple_case_match; subst; cbn; try congruence).


(*TODO: move to right place*)
Existing Class Injective.
#[export] Instance elt_cartesian_rename_injective : Injective elt_cartesian_rename.
Proof. prove_injective. Qed.
  

#[local] Definition elt_cartesian_in := (rename_lang elt_cartesian_rename
            (unit_cartesian ++ unit_action ++ obj_consumer)).
#[local] Definition elt_cartesian_ps := (elab_param "A" elt_cartesian_in
                           [("ext", Some 0); ("elt",Some 0)]).



Lemma simple_sort_wf {V} `{Eqb V} (n : V)
  : wf_lang_ext [] [(n,sort_rule [] [])].
Proof.
  constructor;
    basic_core_crush.
Qed.
#[export] Hint Resolve simple_sort_wf : elab_pfs.

(* TODO: beyond this point there are some category-theoretic
   names that could be used but which I would get wrong in choosing.
 *)
(*Define the unevaluated one locally for proof convenience*)
#[local] Definition typed_consumer' : lang _ :=
  (parameterize_lang "A" {{s #"ty"}}
     elt_cartesian_ps
     (rename_lang elt_cartesian_rename (obj_consumer))).
Definition typed_consumer : lang _ :=
  Eval compute in typed_consumer'.


Definition ty_sort_singleton : lang string := [("ty",sort_rule [] [])].

  Ltac prove_from_known_elabs' :=
  rewrite <- ?as_nth_tail;
   repeat
    lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ [] => apply wf_lang_nil
    | |- wf_lang_ext _ (rename_lang _ _) => apply rename_lang_mono
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => compute_all_fresh
    | |- incl _ _ => compute_incl
    end.

  (*TODO: move to Renaming.v*)

  Definition finite_injective_inverse A B `{Eqb B} `{WithDefault A} (f: A -> B) l :=
    let nlf x := (f x, x) in
    let nl := map nlf l in
    fun y => match named_list_lookup_err nl y with
             | Some x => x
             | None => default
             end.

  Lemma finite_injective_inverse_spec1 A `{WithDefault A} B `{Eqb_ok B} (f : A -> B) l
    : Injective f -> forall x, In x l -> finite_injective_inverse f l (f x) = x.
  Proof.
    unfold finite_injective_inverse.
    intro HInj.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    (*TODO: eqb_case on recurrences*)
    pose proof (eqb_spec (f x) (f a)); destruct (eqb (f x) (f a)).
    {
      eapply HInj; eauto.
    }
    {
      eapply IHl; eauto.
    }
  Qed.
  

  Lemma finite_injective_inverse_spec2 A `{WithDefault A} B `{Eqb_ok B} (f : A -> B) l
    : Injective f -> forall x, In x (map f l) -> f (finite_injective_inverse f l x) = x.
  Proof.
    unfold finite_injective_inverse.
    intro HInj.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
    (*TODO: eqb_case on recurrences*)
    pose proof (eqb_spec x (f a)); destruct (eqb x (f a));
      try congruence.
    eapply IHl; eauto.
  Qed.

  Lemma map_identity A f (l1 : list A)
    : map f l1 = l1 <-> (forall x, In x l1 -> f x = x).
  Proof.
    induction l1; 
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma sublist_map_identity C g (l1 l2 : list C)
    : sublist l1 l2 -> map g l2 = l2 -> map g l1 = l1.
  Proof.
    rewrite !map_identity.
    intro Hsub; eapply sublist_incl in Hsub; unfold incl in Hsub.
    intuition eauto.
  Qed.    
  
  Section RenameInverse.

    Context A `{Eqb_ok A} `{WithDefault A} B `{Eqb_ok B} (f : A -> B).
    Context (HInj :  Injective f).

    Section Varlist.
      Context (varlist : list A).
      
      Let f' := finite_injective_inverse f varlist.

      Section __.
        Context (l : lang A).

        Context (Hlincl : incl (map fst l) varlist).
        
        
        Lemma rename_inverse1
          : (forall c t, wf_sort l c t ->
                         incl (map fst c) varlist ->
                         rename_sort f' (rename_sort f t) = t)
            /\ (forall c (e : term A) t,
                   wf_term l c e t ->
                   incl (map fst c) varlist ->
                   rename f' (rename f e) = e)
            /\ (forall c s c0,
                   wf_args (Model:=core_model l) c s c0 ->
                   incl (map fst c) varlist ->
                   map (rename f') (map (rename f) s) = s).
        Proof.
          subst f'.
          eapply wf_judge_ind;
            basic_goal_prep;
            basic_utils_crush.
          
          all: rewrite finite_injective_inverse_spec1; eauto; try congruence.
          all: basic_utils_crush.
        Qed.      
        
        Lemma rename_inverse_ctx1 c
          : incl (map fst c) varlist ->
            wf_ctx (Model:=core_model l) c ->
            rename_ctx f' (rename_ctx f c) = c.
        Proof.
          induction c;
            basic_goal_prep;
            basic_core_crush.
          {
            subst f'; cbn.
            rewrite finite_injective_inverse_spec1; eauto; try congruence.
          }
          {
            eapply rename_inverse1; eauto.
          }
        Qed.

        
        Lemma rename_inverse_rule1 r
          : wf_rule l r ->
            incl (map fst (get_ctx r)) varlist ->
            rename_rule f' (rename_rule f r) = r.
        Proof.
          destruct r;
            basic_goal_prep;
            basic_utils_crush.
          all: f_equal.
          all: try first [ eapply rename_inverse_ctx1 | eapply rename_inverse1 ];
            basic_core_crush.
          all: rewrite map_map.
          all: eapply rename_inverse_ctx1 in H5; eauto.
          all: unfold rename_ctx in H5.
          all: eapply sublist_map_identity; eauto.
          all: apply f_equal with (f:= map fst) in H5.
          all: rewrite !map_map in *.
          all: cbn in *.
          all: eauto.
        Qed.

      End __.
        

      Lemma rename_inverse_lang1' l
        : wf_lang l ->
          incl (map fst l) varlist ->
          all (fun '(_, r) => incl (map fst (get_ctx r)) varlist) l ->
          rename_lang f' (rename_lang f l) = l.
      Proof.
        induction 1;
          basic_goal_prep;
          basic_utils_crush.
        {
          subst f'; cbn.
          rewrite finite_injective_inverse_spec1; eauto; try congruence.
        }
        { eapply rename_inverse_rule1; eauto. }
      Qed.

      
      Section __.
        Context (l : lang B).

        Context (Hlincl : incl (map fst l) (map f varlist)).
        
        
        Lemma rename_inverse2
          : (forall c t, wf_sort l c t ->
                         incl (map fst c) (map f varlist) ->
                         rename_sort f (rename_sort f' t) = t)
            /\ (forall c (e : term B) t,
                   wf_term l c e t ->
                   incl (map fst c) (map f varlist) ->
                   rename f (rename f' e) = e)
            /\ (forall c s c0,
                   wf_args (Model:=core_model l) c s c0 ->
                   incl (map fst c) (map f varlist) ->
                   map (rename f) (map (rename f') s) = s).
        Proof.
          subst f'.
          eapply wf_judge_ind;
            basic_goal_prep;
            basic_utils_crush.
          
          all: rewrite finite_injective_inverse_spec2; eauto; try congruence.
          all: basic_utils_crush.
        Qed.      
        
        Lemma rename_inverse_ctx2 c
          : incl (map fst c) (map f varlist) ->
            wf_ctx (Model:=core_model l) c ->
            rename_ctx f (rename_ctx f' c) = c.
        Proof.
          induction c;
            basic_goal_prep;
            basic_core_crush.
          {
            subst f'; cbn.
            rewrite finite_injective_inverse_spec2; eauto; try congruence.
          }
          {
            eapply rename_inverse2; eauto.
          }
        Qed.

        
        Lemma rename_inverse_rule2 r
          : wf_rule l r ->
            incl (map fst (get_ctx r)) (map f varlist) ->
            rename_rule f (rename_rule f' r) = r.
        Proof.
          destruct r;
            basic_goal_prep;
            basic_utils_crush.
          all: f_equal.
          all: try first [ eapply rename_inverse_ctx2 | eapply rename_inverse2 ];
            basic_core_crush.
          all: rewrite map_map.
          all: eapply rename_inverse_ctx2 in H5; eauto.
          all: unfold rename_ctx in H5.
          all: eapply sublist_map_identity; eauto.
          all: apply f_equal with (f:= map fst) in H5.
          all: rewrite !map_map in *.
          all: cbn in *.
          all: eauto.
        Qed.

      End __.
        

      Lemma rename_inverse_lang2' l
        : wf_lang l ->
          incl (map fst l) (map f varlist) ->
          all (fun '(_, r) => incl (map fst (get_ctx r)) (map f varlist)) l ->
          rename_lang f (rename_lang f' l) = l.
      Proof.
        induction 1;
          basic_goal_prep;
          basic_utils_crush.
        {
          subst f'; cbn.
          rewrite finite_injective_inverse_spec2; eauto; try congruence.
        }
        { eapply rename_inverse_rule2; eauto. }
      Qed.

      
    End Varlist.

    
    Lemma rename_inverse_lang1 l
      : wf_lang l ->
        let varlist := (flat_map (fun '(_, r) => map fst (get_ctx r)) l ++ map fst l) in
        rename_lang (finite_injective_inverse f varlist) (rename_lang f l) = l.
    Proof.
      intros.
      subst varlist.
      eapply rename_inverse_lang1'; eauto.
      1:basic_utils_crush.
      lazymatch goal with
        |- all ?P ?l =>
          enough (forall l', incl l' l -> all P l')
          by (basic_goal_prep;
              basic_utils_crush)
      end.
      induction l';
        basic_goal_prep;
        basic_utils_crush.
      eapply incl_appl.
      change (map fst (get_ctx r))
        with ((fun '(_, r0) => map fst (get_ctx r0)) (a,r)).
      eapply incl_flat_map; eauto.
    Qed.

    (*TODO: need inverse of varlist*)    
    Lemma rename_inverse_lang2 (l : lang B)
      : wf_lang l ->
        let varlist := map f (flat_map (fun '(_, r) => map fst (get_ctx r)) l ++ map fst l) in
        rename_lang f (rename_lang (finite_injective_inverse f varlist) l) = l.
    Proof.
      intros.
      subst varlist.
      eapply rename_inverse_lang2'; eauto.
      1:basic_utils_crush.
      lazymatch goal with
        |- all ?P ?l =>
          enough (forall l', incl l' l -> all P l')
          by (basic_goal_prep;
              basic_utils_crush)
      end.
      induction l';
        basic_goal_prep;
        basic_utils_crush.
      eapply incl_appl.
      change (map fst (get_ctx r))
        with ((fun '(_, r0) => map fst (get_ctx r0)) (a,r)).
      eapply incl_flat_map; eauto.
    Qed.

  End RenameInverse.
  
Lemma typed_consumer_wf
  : wf_lang_ext (cat++ty_sort_singleton) typed_consumer.
Proof.
  change (wf_lang_ext (cat++ty_sort_singleton) typed_consumer').
  replace cat with (parameterize_lang "A" {{s #"ty"}} elt_cartesian_ps cat).
  {
    eapply parameterize_lang_preserving_ext;
    try typeclasses eauto;
    basic_core_crush.
    all: prove_from_known_elabs.
    erewrite <- rename_inverse_lang with (l:=cat) (f:=elt_cartesian_rename);
      eauto;
      try typeclasses eauto.
    2: prove_from_known_elabs.
    TODO: inverse is the wrong direction!
    TODO: injective inverse?
    apply rename_lang_mono_ext; try typeclasses eauto.
  {
    TODO: need rename_lang_mono _ext.
    rename ty_sort_singleton as a base for obj_consumer
                                  obj_consumer_wf
    
    TODO: make renames injective, automate injectivity proofs
  TODO: obj_consumer depends on obj
  2:  prove_from_known_elabs.
  
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
                       ++ty_sort_singleton++cat)
                    typed_consumer.

Definition elt_action_def :=
  Eval compute in Rule.hide_lang_implicits
                    (elt_action++typed_consumer
                       ++ty_sort_singleton++cat)
                    elt_action.

Definition elt_cartesian_def :=
  Eval compute in Rule.hide_lang_implicits
                    (elt_cartesian++elt_action++typed_consumer
                       ++ty_sort_singleton++cat)
                    elt_cartesian.


TODO: from here. prove w/out auto_elab

Lemma typed_consumer_wf
  : elab_lang_ext (ty_sort_singleton++cat)
      typed_consumer_def typed_consumer.
Proof. auto_elab. Qed.
#[export] Hint Resolve typed_consumer_wf : elab_pfs.

Lemma elt_action_wf
  : elab_lang_ext (typed_consumer++ty_sort_singleton++cat)
      elt_action_def elt_action.
Proof. auto_elab. Qed.
#[export] Hint Resolve elt_action_wf : elab_pfs.

Lemma elt_cartesian_wf
  : elab_lang_ext (elt_action++typed_consumer++ty_sort_singleton++cat)
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

(* TODO: prove this w/out re-elabbing*)
Lemma ty_subst_wf
  : elab_lang_ext [] ty_subst_def ty_subst_lang.
Proof. auto_elab. Qed.
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
                    (val_subst++ty_sort_singleton)
                    val_subst.

Lemma val_subst_wf
  : elab_lang_ext ty_sort_singleton val_subst_def val_subst.
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
                    (exp_subst_base ++ val_subst++ty_sort_singleton)
                    exp_subst_base.

Lemma exp_subst_base_wf
  : elab_lang_ext (val_subst++ty_sort_singleton)
      exp_subst_base_def exp_subst_base.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_subst_base_wf : elab_pfs.



Definition exp_ret_def : lang _ :=
  {[l/subst [(exp_subst_base++val_subst++ty_sort_singleton)]
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
    ] ]}.

Derive exp_ret
  SuchThat (elab_lang_ext (exp_subst_base++val_subst++ty_sort_singleton)
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
  (*Eval compute in*)
    let ps := (elab_param "D" (exp_ret ++ exp_subst_base
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base ++ val_subst).

(*
Definition exp_and_val_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (exp_and_val_parameterized
                       ++ty_subst_lang)
                    exp_and_val_parameterized.*)

(*this is instant. What's the problem?*)

Let pl :=
      Eval compute in
      (elab_param "D"
          (exp_ret ++
           exp_subst_base ++
           val_subst ++ [[s| 
                             -----------------------------------------------
                             #"ty" srt
                         ]%rule])
          [("sub", Some 2); ("ty", Some 0); ("env", Some 0); ("val", Some 2); ("exp", Some 2)]).

Let l :=
      Eval compute in (exp_ret ++ exp_subst_base ++ val_subst).

Let fl := Eval compute in (frontier l).

Let fl1 := Eval compute in (dep_trans_step fl).

Let fl2 := Eval compute in (named_map (dedup (eqb (A:=_))) fl1).

Definition compute_dependencies' :=
fun (V : Type) (V_Eqb : Eqb V) (l : lang V) =>
  let init := frontier l in fixpoint (Basics.compose (named_map (dedup (eqb (A:=_))))
                                        (dep_trans_step (V:=V))) 10 init.
(*
TODO: is the issue a lack of deduping? that would explain everything
        secondary issue: is fixpoint short-circuit dependant on dedup order?
 *)
Compute ty_subst_lang.

Lemma ty_sort_singleton_wf : wf_lang ty_sort_singleton.
Proof.
  repeat constructor.
  t'.
Qed.
#[export] Hint Resolve ty_sort_singleton_wf : elab_pfs.

Lemma exp_and_val_parameterized_wf
  : wf_lang_ext ty_subst_lang exp_and_val_parameterized.
Proof.
  eapply parameterize_lang_preserving.
  Compute ty_subst_lang.
  TODO: need to split  ty_subst_lang into old and new parts.
  Specifically, need to separate ty and up from ty_env part
  5:{ 
    prove_from_known_elabs.
  }
  TODO: to generalize: wf_lang l. Needs an add'l wf_lang_ext l_pre l
  4:{
  Compute ty_subst_lang.
  TODO: why goal 4? answer: using ty_subst_lang as l_base.
  base/l too restrictive?
    eauto; try typeclasses eauto.
  {
    repeat t'.
    constructor (*TODO: add to t'*).
  }
  { TODO: where is ty_sort_singleton?
    prove_from_known_elabs.
    val_subst_wf
    Compute val_subst.
    Note: val_subst depends on "ty"
    prove_from_known_elabs.
    Note: ty_subst irrelevant here.
    TODO: ty_subst has an argument to ty; why no D here? what ty is it looking for?
    prove_ident_from_known_elabs.
    
     lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ [] => apply wf_lang_nil
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => compute_all_fresh
    | |- incl _ _ => compute_incl
     end.
     1:
     lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ [] => apply wf_lang_nil
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => compute_all_fresh
    | |- incl _ _ => compute_incl
    end.
     1:{ TODO: this is false!/not what I should have to prove. Where is the rule for ty?
       eapply lang_ext_monotonicity.
   [ typeclasses eauto with auto_elab elab_pfs | auto with utils | compute_all_fresh ]
       prove_ident_from_known_elabs.
     lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ [] => apply wf_lang_nil
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => compute_all_fresh
    | |- incl _ _ => compute_incl
    end.
    prove_from_known_elabs.
    TODO: seems to be dropping ty rule?
    all:shelve (*TODO: what are these incls?*).
  }
  {
    prove_from_known_elabs.
    all:shelve (*TODO: what are these incls?*).
  }
  { vm_compute. exact I. }
Qed.
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

Derive exp_ty_subst
  SuchThat (elab_lang_ext (env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
      exp_ty_subst_def
      exp_ty_subst)
       As exp_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ty_subst_wf : elab_pfs. 


Definition exp_and_val_param_substs_def :=
  eqn_rules type_subst_mode (exp_ty_subst++env_ty_subst++exp_and_val_parameterized ++ty_subst_lang)
    exp_and_val_parameterized_def.
             
Derive exp_and_val_param_substs
  SuchThat (elab_lang_ext (exp_ty_subst
                             ++env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
              exp_and_val_param_substs_def
              exp_and_val_param_substs)
  As exp_and_val_param_substs_wf.
Proof.
  setup_elab_lang.
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  - break_elab_rule.
    all: unfold Model.eq_term.
    all: compute_eq_compilation.
    all: try apply eq_term_refl.
    all: try  cleanup_auto_elab.
    (* Note: wkn's argument can't be inferred here*)
    instantiate (1:= {{e #"ty_subst" "D'" "D" "d" "A"}}).
    by_reduction.
  - break_elab_rule.
    all: unfold Model.eq_term.
    all: compute_eq_compilation.
    all: try apply eq_term_refl.
    all: try  cleanup_auto_elab.
    instantiate (1:= {{e #"env_ty_subst" "D'" "D" "d" "G"}}).
    by_reduction.
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
     cleanup_auto_elab ]).
   Unshelve.
   all: cleanup_auto_elab.
Qed.
#[export] Hint Resolve exp_and_val_param_substs_wf : elab_pfs.

Local Open Scope lang_scope.
Definition poly_def : lang _ :=
  {[l (*l/subst TODO: psubst*)
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
    ]
    (* TODO: autogenerate G substs w/ ambient D *)
    
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

#[export] Hint Resolve (inst_for_db "ty_id") : injective_con.
#[export] Hint Resolve (inst_for_db "ty_emp") : injective_con.
#[export] Hint Resolve (inst_for_db "ty_forget") : injective_con.
#[export] Hint Resolve (inst_for_db "ty_ext") : injective_con.
#[export] Hint Resolve (inst_for_db "ty_snoc") : injective_con.
#[export] Hint Resolve (inst_for_db "ty_wkn") : injective_con.
#[export] Hint Resolve (inst_for_db "ty_hd") : injective_con.
#[export] Hint Resolve (inst_for_db "id") : injective_con.
#[export] Hint Resolve (inst_for_db "emp") : injective_con.
#[export] Hint Resolve (inst_for_db "forget") : injective_con.
#[export] Hint Resolve (inst_for_db "ext") : injective_con.
#[export] Hint Resolve (inst_for_db "snoc") : injective_con.
#[export] Hint Resolve (inst_for_db "wkn") : injective_con.
#[export] Hint Resolve (inst_for_db "hd") : injective_con.
#[export] Hint Resolve (inst_for_db "ret") : injective_con.
#[export] Hint Resolve (inst_for_db "All") : injective_con.

Derive poly
  SuchThat (elab_lang_ext (exp_and_val_param_substs
                             ++ exp_ty_subst
                             ++env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
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
    ( unit_action++obj_consumer).


Definition block_subst_def :=
  Eval compute in Rule.hide_lang_implicits
                    (block_subst ++ val_subst ++ty_sort_singleton)
                    block_subst.

Lemma block_subst_wf
  : elab_lang_ext (val_subst ++ty_sort_singleton)
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


Lemma env_ty_subst_wf'
  : elab_lang_ext (block_and_val_parameterized++ty_subst_lang)
      env_ty_subst_def
      (env_ty_subst).
Proof. auto_elab. Qed.
#[export] Hint Resolve env_ty_subst_wf' : elab_pfs.


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
                             ++block_and_val_parameterized
                             ++ty_subst_lang)
      block_ty_subst_def
      block_ty_subst)
       As block_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve block_ty_subst_wf : elab_pfs. 



Definition block_and_val_param_substs_def :=
  eqn_rules type_subst_mode (block_ty_subst++env_ty_subst++block_and_val_parameterized ++ty_subst_lang)
    block_and_val_parameterized_def.
             
Derive block_and_val_param_substs
  SuchThat (elab_lang_ext (block_ty_subst
                             ++env_ty_subst
                             ++block_and_val_parameterized
                             ++ty_subst_lang)
              block_and_val_param_substs_def
              block_and_val_param_substs)
  As block_and_val_param_substs_wf.
Proof.
  setup_elab_lang.
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
  - break_elab_rule.
    all: unfold Model.eq_term.
    all: compute_eq_compilation.
    all: try apply eq_term_refl.
    all: try  cleanup_auto_elab.
    (* Note: wkn's argument can't be inferred here*)
    instantiate (1:= {{e #"ty_subst" "D'" "D" "d" "A"}}).
    by_reduction.
  - break_elab_rule.
    all: unfold Model.eq_term.
    all: compute_eq_compilation.
    all: try apply eq_term_refl.
    all: try  cleanup_auto_elab.
    instantiate (1:= {{e #"env_ty_subst" "D'" "D" "d" "G"}}).
    by_reduction.
  -(first
   [ unshelve (solve [ break_elab_rule; apply eq_term_refl; cleanup_auto_elab ]); try apply eq_term_refl;
      cleanup_auto_elab ]).
   Unshelve.
   all: cleanup_auto_elab.
Qed.
#[export] Hint Resolve block_and_val_param_substs_wf : elab_pfs.
