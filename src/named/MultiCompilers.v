Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core AllConstructors.
Import Core.Notations.
(*TODO: rename this to compiler proofs and have a separate export-only file?*)
Require Export MultiCompilerDefs.


Lemma flat_map_all_empty {A B} (f : A -> list B) l
  : (forall x, f x = []) ->
    flat_map f l = [].
Proof.
  induction l; basic_goal_prep; basic_utils_firstorder_crush.
  rewrite H, H0.
  reflexivity.
Qed.

(*
Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) l
  : map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Admitted.


Lemma named_map_fst_eq {A B}
  : forall (f : A -> B) (l1 : named_list A), map fst (named_map f l1) = map fst l1.
Admitted.


Lemma flat_map_ext {A B} (f g : A -> list B) l
  : (forall x, f x = g x) -> (flat_map f l) = flat_map g l.
Admitted.

Lemma flat_map_f_cons {A B} f (g : A -> list B) l x b
  : In x l -> b = f x -> In b (flat_map (fun x => (f x)::(g x)) l).
Admitted.




Lemma fresh_compile_ctx_cons cname x l0 n l s c 
  : fresh (cname :: x) (compile_ctx (l0, n) ((l, s) :: c)) <->
      (fresh (cname :: x) (map (fun '(n', t) => (cname :: n', compile_sort (l0, n) cname t)) c)
      /\ fresh (cname :: x) (compile_ctx (l0, n) c)).
Admitted.
Hint Rewrite fresh_compile_ctx_cons : lang_core.

Lemma fresh_compile_ctx x cmp c cname
  : In cname (fst cmp) ->
    fresh (cname::x) (compile_ctx cmp c) <-> fresh x c.
Proof.
  induction c; basic_goal_prep;
    basic_core_firstorder_crush.
  {
    apply H0.
    rewrite map_map.
    erewrite map_ext.
    2:{
      instantiate (1:= fun p => cname::(fst p)).
      intros; destruct a; reflexivity.
    }
    simpl.
      auto. (*
      intro a.
      inst
      destruct a.
      
      reflexivity.
      simpl. reflexivity.
    simpl.
    rewrite map_flat_map.
    erewrite flat_map_ext.
    2: intros; apply map_map.
    simpl.
    eapply flat_map_f_cons; eauto.
  }
      let __ := match constr:(Set) with _ =>
          syntactic_unify_deltavar x y end in
  {
    apply fresh_compile_ctx_cons_tl in H0.
    auto.
  }
  {
    
    rewrite fresh_cons in H0.
    basic_core_crush.
    destruct H0. basic_core_crush.
    apply H1.

    }
    
    cbv [compile_ctx fst named_map].
    simpl.
    unfold In.*)
Admitted.*)
(*
Hint Rewrite fresh_compile_ctx : lang_core.*)

(*

Lemma all_fresh_compile_ctx cmp c
  : all_fresh (compile_ctx cmp c) <-> all_fresh c.
Proof.
  induction c; basic_goal_prep;
    basic_core_crush.
Qed.
Hint Rewrite all_fresh_compile_ctx : lang_core.

*)

Lemma fresh_lang_fresh_cmp cmp_pre lt cmp l n
  : preserving_compiler_ext cmp_pre lt cmp l ->
    fresh n l -> fresh n cmp.
Proof.
  induction 1; basic_goal_prep;
    basic_core_crush.
Qed.
Hint Resolve fresh_lang_fresh_cmp : lang_core.


Lemma all_fresh_compiler lt names cmp l
  : preserving_compiler_ext (names,[]) lt cmp l ->
    all_fresh l ->
    all_fresh cmp.
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
Qed.
Hint Resolve all_fresh_compiler : lang_core.

(*TODO: move to source*)
Arguments eqb {A}%type_scope {Eqb} !_ !_ /.

(*TODO: move to utils*)
Lemma flat_map_funext {A B} (f g : A ->  list B) l
  : (forall x, In x l -> f x = g x) ->
    flat_map f l = flat_map g l.
Proof.
  intros; induction l; basic_goal_prep; basic_utils_crush.
  rewrite H, IHl; auto.
Qed.

Lemma compile_strengthen_term cnames ccs n cc e cname
  : fresh n ccs ->
    all_fresh ccs ->
    all_constructors (fun n => In n (map fst ccs)) e ->
    compile (cnames,(n,cc)::ccs) cname e = compile (cnames,ccs) cname e.
Proof.
  revert cname.
  induction e; basic_goal_prep; basic_core_crush.
  my_case Heq (eqb n0 n); basic_goal_prep;
    basic_core_crush.
  case_match; basic_goal_prep;
      basic_core_crush.
  case_match; basic_goal_prep;
    basic_core_crush.
  f_equal.
  f_equal.
  apply flat_map_funext; intros.
  apply map_ext_in; intros.
  eapply in_all in H; eauto.
  eapply in_all in H4; eauto.
Qed.
Hint Rewrite compile_strengthen_term : lang_core.


Lemma compile_args_cons_eq l n1 n2 a e
  : (forall cname, In cname l -> compile (l, n1) cname a = compile (l, n2) cname a) ->
    compile_args (l, n1) e = compile_args (l, n2) e ->
    compile_args (l, n1) (a :: e) = compile_args (l, n2) (a :: e).
Proof.
  simpl.
  intros Ha ->.
  f_equal.
  eauto using map_ext_in.
Qed.

Lemma compile_strengthen_args cnames ccs n cc e
  : fresh n ccs ->
    all_fresh ccs ->
    all (all_constructors (fun n => In n (map fst ccs))) e ->
    compile_args (cnames, (n,cc)::ccs) e = compile_args (cnames, ccs) e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  apply compile_args_cons_eq;
    basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite compile_strengthen_args : lang_core.

Lemma compile_strengthen_sort cnames ccs n cc e cname
  : fresh n ccs ->
    all_fresh ccs ->
    all_constructors_sort (fun n => In n (map fst ccs)) e ->
    compile_sort (cnames,(n,cc)::ccs) cname e = compile_sort (cnames, ccs) cname e.
Proof.
  destruct e; basic_goal_prep; basic_core_crush.
  my_case Heq (eqb l n); basic_goal_prep;
    basic_core_crush.
Qed.
Hint Rewrite compile_strengthen_sort : lang_core.


Lemma compile_strengthen_ctx cnames ccs n cc c
  : fresh n ccs ->
    all_fresh ccs ->
    all (fun '(_,t) => all_constructors_sort (fun n => In n (map fst ccs)) t) c ->
    compile_ctx (cnames,(n,cc)::ccs) c = compile_ctx (cnames, ccs) c.
Proof.
  induction c; basic_goal_prep; f_equal; basic_core_crush.
  apply map_ext_in; intros; f_equal.
  basic_core_crush.
Qed.
Hint Rewrite compile_strengthen_ctx : lang_core.


Lemma sort_name_in_cmp cmp_pre tgt ccs src c' args n
  : preserving_compiler_ext cmp_pre tgt ccs src ->
    In (n, sort_rule c' args) src ->
    In n (map fst ccs).
Proof.
  induction 1;basic_goal_prep;
    with_rule_in_wf_crush.
  all: try typeclasses eauto. (*TODO: put in with_rule_if_wf_crush*)
Qed.
Local Hint Resolve sort_name_in_cmp : lang_core.

Lemma term_name_in_cmp cmp_pre tgt cmp src c' args t n
  : preserving_compiler_ext cmp_pre tgt cmp src ->
    In (n, term_rule c' args t) src ->
    In n (map fst cmp).
Proof.
  induction 1;basic_goal_prep;
    with_rule_in_wf_crush.
  all: try typeclasses eauto. (*TODO: put in with_rule_if_wf_crush*)
Qed.
Local Hint Resolve term_name_in_cmp : lang_core.
                   
Local Lemma all_constructors_from_wf cnames tgt cmp src
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    (forall c t,
        wf_sort src c t ->
        all_constructors_sort (fun n0 => In n0 (map fst cmp)) t)
    /\ (forall c e t,
           wf_term src c e t ->
           all_constructors (fun n0 => In n0 (map fst cmp)) e)
    /\ (forall c s c',
           wf_args src c s c' ->
           all (all_constructors (fun n0 => In n0 (map fst cmp))) s).
Proof using.
  intros; apply wf_judge_ind; basic_goal_prep;
    with_rule_in_wf_crush.
  all: try typeclasses eauto. (*TODO: put in with_rule_if_wf_crush*)
Qed.

Definition all_constructors_sort_from_wf cnames tgt cmp src (pr : preserving_compiler_ext (cnames,[]) tgt cmp src)
  := proj1 (all_constructors_from_wf pr).
Hint Resolve all_constructors_sort_from_wf : lang_core.

Definition all_constructors_term_from_wf cnames tgt cmp src (pr : preserving_compiler_ext (cnames,[]) tgt cmp src)
  := proj1 (proj2 (all_constructors_from_wf pr)).
Hint Resolve all_constructors_term_from_wf : lang_core.

Definition all_constructors_args_from_wf cnames tgt cmp src (pr : preserving_compiler_ext (cnames,[]) tgt cmp src)
  := proj2 (proj2 (all_constructors_from_wf pr)).
Hint Resolve all_constructors_args_from_wf : lang_core.

Lemma all_constructors_ctx_from_wf cnames tgt cmp src c
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    wf_ctx src c ->
    all_constructors_ctx (fun n0 => In n0 (map fst cmp)) c.
Proof.
  induction 2; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Hint Resolve all_constructors_ctx_from_wf : lang_core.


  (*TODO: lift*)
Ltac use_in_all :=
  repeat lazymatch goal with
  | [H : all _ _|-_] =>
      simple eapply in_all in H; [|eassumption]
  end.

(*TODO: think about whether this should be generalized*)
Lemma inductive_implies_semantic_sort_axiom cnames ls lt cmp name c t1 t2 cname
  : wf_lang lt -> preserving_compiler_ext (cnames,[]) lt cmp ls -> wf_lang ls ->
    In cname cnames ->
    In (name, sort_eq_rule c t1 t2) ls ->
    eq_sort lt (compile_ctx (cnames,cmp) c) (compile_sort (cnames,cmp) cname t1) (compile_sort (cnames,cmp) cname t2).
Proof.
  induction 2;
    basic_goal_prep; try use_rule_in_wf; use_in_all;
      basic_core_firstorder_crush.
  (*TODO: why is this needed? should be automated*)  
  all: use_rule_in_wf;autorewrite with lang_core utils in *;
    intuition eauto with lang_core.
Qed.


Lemma inductive_implies_semantic_term_axiom cnames ls lt cmp name c e1 e2 t cname
  : wf_lang lt -> preserving_compiler_ext (cnames,[]) lt cmp ls -> wf_lang ls ->
    In cname cnames ->
    In (name, term_eq_rule c e1 e2 t) ls ->
    eq_term lt (compile_ctx (cnames,cmp) c) (compile_sort (cnames,cmp) cname t)
            (compile (cnames,cmp) cname e1) (compile (cnames,cmp) cname e2).
Proof.
  induction 2;
    basic_goal_prep;
    try use_rule_in_wf;
    use_in_all;
    basic_core_firstorder_crush.
  (*TODO: why is this needed? should be automated*)
  all: use_rule_in_wf;autorewrite with lang_core utils in *;
    intuition eauto with lang_core.
Qed.

(*TODO: generalize
Lemma with_names_from_compile_ctx (A:Type) cmp c (s : list A)
  : with_names_from (compile_ctx cmp c) s
    = with_names_from c s.
Proof.
  revert s; induction c;
    destruct s; break; basic_core_crush.
  cbn.
  f_equal; basic_core_crush.
Qed.
  *)


(* TODO: generalize*)
(*Lemma compile_id_args A cmp (c : named_list A)
  : map (compile mp) (id_args c) = id_args c.
Proof.
  unfold id_args.
  induction c; 
    basic_goal_prep;
    basic_core_crush.
Qed.
Hint Rewrite compile_id_args : lang_core.
*)

Lemma fst_equal_id_args_equal A B (c1 : named_list A) (c2 : named_list B)
  : map fst c1 = map fst c2 -> id_args c1 = id_args c2.
Proof.
  unfold id_args; basic_core_crush.
Qed.

(*TODO: generalize*)
(*
Lemma compile_ctx_fst_equal cmp c
  : map fst (compile_ctx cmp c) = map fst c.
Proof.
  induction c; break; simpl; f_equal; auto.
Qed.
*)

(*TODO: should be in Utils.v*)
Lemma named_list_lookup_err_is_Some {A} d l n (v:A)  
  : Some v = named_list_lookup_err l n ->
    named_list_lookup d l n = v.
Proof.
  induction l; basic_goal_prep.
  basic_utils_crush.
  my_case Heq (eqb n s).
  inversion H; tauto.
  basic_utils_crush.
Qed.


Lemma combine_app_same_len {A B} (a1 b1 : list A) (a2 b2 : list B)
  : length a1 = length a2 ->
    combine (a1++b1) (a2++b2) = (combine a1 a2) ++ (combine b1 b2).
Proof.
  revert a2; induction a1; destruct a2; basic_goal_prep;
    basic_utils_crush.
Qed.
(*Note: not completely safe, but usually useful *)
Hint Rewrite @combine_app_same_len : utils.

Lemma id_args_app (a b : ctx)
  : id_args (a++b) = id_args a ++ id_args b.
Proof.
  induction a; basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite id_args_app : utils.

Lemma with_names_from_app_same_len {A B} (a1 b1 : named_list A) (a2 b2 : list B)
  : length a1 = length a2 ->
    with_names_from (a1++b1) (a2++b2) = (with_names_from a1 a2) ++ (with_names_from b1 b2).
Proof.
  revert a2; induction a1; destruct a2; basic_goal_prep;
    basic_utils_crush.
Qed.
(*Note: not completely safe, but usually useful *)
Hint Rewrite @with_names_from_app_same_len : utils.


(*TODO: get rid of with_names_from, or define in terms of combine? *)

(*cmp1,2 an artifact of env_args taking a full compiler*)
Lemma compile_id_subst cnames cmp1 cmp2 c
  : combine (env_args (cnames, cmp1) (map fst c))
            (compile_args (cnames, cmp2) (id_args c))
    = id_subst (compile_ctx (cnames, cmp2) c).
Proof.
  induction c; basic_goal_prep; basic_core_crush.
  f_equal; eauto.
  rewrite <- combine_map_fst_is_with_names_from.
  f_equal;
    unfold id_args;
    rewrite !map_map;
    apply map_ext;
    basic_goal_prep; basic_core_crush.
  all: constructor. (*TODO: where does this come from?*)
Qed.


Lemma P_of_named_list_lookup_from_all {A B P} `{Eqb A} (l1 : list A) (l2:list B) n d
  : all P l2 ->
    In n l1 ->
    length l2 = length l1 ->
    P (named_list_lookup d (combine l1 l2) n).
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep; basic_utils_crush.
  my_case Heqb (eqb n a);
    basic_goal_prep; basic_utils_crush.
Qed.

Lemma P_of_named_list_lookup_from_all_combined {A B P} `{Eqb A} (l1 : list A) (l2:list B) n d
  : all P (combine l1 l2) ->
    In n l1 ->
    length l2 = length l1 ->
    P (n, (named_list_lookup d (combine l1 l2) n)).
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep; basic_utils_crush.
  my_case Heqb (eqb n a);
    basic_goal_prep; basic_utils_crush.
Qed.

(*TODO: move to utils*)
Hint Resolve incl_nil_l : utils.
Hint Resolve incl_tl : utils.

Lemma map_snd_combine_incl {A B} (a : list A) (b : list B)
  : incl (map snd (combine a b)) b.
Proof.
  revert b; induction a; destruct b;
    basic_goal_prep; basic_utils_crush.
Qed.  

Lemma all_weaken_incl {A P} (a b : list A)
  : incl a b -> all P b -> all P a.
Proof.
  revert b; induction a;
    basic_goal_prep; basic_utils_crush.
  eapply in_all; eauto.
Qed.



Lemma lang_compiler_sort_case_args_eq cmp_pre lt cmp ls n c args args' e
  : preserving_compiler_ext cmp_pre lt cmp ls ->
    all_fresh ls ->
    In (n, sort_rule c args) ls ->
    In (n, sort_case args' e) cmp ->
    args' = map fst c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  match goal with
    [Hp : preserving_compiler_ext _ _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  basic_core_crush.
Qed.
Hint Resolve lang_compiler_sort_case_args_eq : lang_core.

Lemma lang_compiler_term_case_args_eq cmp_pre lt cmp ls n c args args' e t
  : preserving_compiler_ext cmp_pre lt cmp ls ->
    all_fresh ls ->
    In (n, term_rule c args t) ls ->
    In (n, term_case args' e) cmp ->
    args' = map fst c.
Proof.
  (*TODO: takes a long time*)
  induction 1; basic_goal_prep; basic_core_firstorder_crush.
  match goal with
    [Hp : preserving_compiler_ext _ _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  basic_core_crush.
Qed.
Hint Resolve lang_compiler_term_case_args_eq : lang_core.

Lemma inductive_implies_semantic_sort_rule_id cnames ls lt cmp name c args cname
  : wf_lang lt -> preserving_compiler_ext (cnames,[]) lt cmp ls -> wf_lang ls ->
    In (name, sort_rule c args) ls ->
    In cname cnames ->
    wf_sort lt (compile_ctx (cnames,cmp) c) (compile_sort (cnames,cmp) cname (scon name (id_args c))).
Proof.
  intros wfl pr wfl';
    revert wfl'; induction pr;
    basic_goal_prep;
    use_in_all;
      with_rule_in_wf_crush.
  all: try typeclasses eauto.
  (*TODO: no longer does anything*)
  all: try eapply all_constructors_ctx_from_wf; eauto with lang_core.
3:{
  with_rule_in_wf_crush.
}
4:{
  with_rule_in_wf_crush.
}
{
  rewrite compile_id_subst.
  rewrite subst_id.
  simple eapply P_of_named_list_lookup_from_all; eassumption.
}
{
      with_rule_in_wf_crush.
    my_case Hname (eqb name n);[|case_match]; basic_core_firstorder_crush.
}
{
  my_case Hname (eqb name n);[|case_match]; basic_core_crush.
}
Qed.



Lemma inductive_implies_semantic_term_rule_id cnames ls lt cmp name c args t cname
  : wf_lang lt -> preserving_compiler_ext (cnames,[]) lt cmp ls -> wf_lang ls ->
    In (name, term_rule c args t) ls ->
    In cname cnames ->
    wf_term lt (compile_ctx (cnames,cmp) c)
            (compile (cnames,cmp) cname (con name (id_args c)))
            (compile_sort (cnames,cmp) cname t).
Proof.
  intros wfl pr wfl';
    revert wfl'; induction pr;
    basic_goal_prep;
    use_in_all;
      try use_rule_in_wf;
      basic_core_firstorder_crush.
  all: try solve [use_rule_in_wf; basic_core_crush].
  2:{
    change (flat_map
           (fun x : term =>
            map
              (fun cname0 : string =>
                 compile (cnames, ?cmp) cname0 x) cnames))
    with (compile_args (cnames, cmp)).
    rewrite compile_id_subst.
    rewrite subst_id.
    lazymatch goal with
      H : all ?P (combine _ _) |- _ =>        
        eapply (P_of_named_list_lookup_from_all_combined _ _ _ _ H)
    end; auto.
  }
  {
    my_case Hname (eqb name n);[|case_match]; basic_core_crush.
    revert H7; case_match; auto.
    change (flat_map
           (fun x : term =>
            map
              (fun cname0 : string =>
                 compile (cnames, ?cmp) cname0 x) cnames))
      with (compile_args (cnames, cmp)).
    replace args1 with (map fst c).
    rewrite !compile_id_subst.
    rewrite !subst_id.
    auto.
    symmetry.
    eapply lang_compiler_term_case_args_eq; try eassumption.
    basic_core_crush.
  }
  {
    my_case Hname (eqb name n);[|case_match]; basic_core_firstorder_crush.
    revert H8; case_match; auto.
    pose proof (lang_compiler_term_case_args_eq _ _ _ _ _ _ pr ltac:(basic_core_crush) H3 HeqH9).
    subst.
    all:change (flat_map
           (fun x : term =>
            map
              (fun cname0 : string =>
                 compile (cnames, ?cmp) cname0 x) cnames))
      with (compile_args (cnames, cmp)).
    rewrite !compile_id_subst.
    rewrite !subst_id.
    auto.
  }
Qed.



Lemma lookup_in_dom s n
  : In n (map fst s) -> In (subst_lookup s n) (map snd s).
Proof.
  induction s;
    basic_goal_prep;
    basic_core_crush.
  case_match; basic_core_crush.
Qed.

(*
Lemma wf_con_id_args_subst' A (c : named_list A) s
  : forall n e, In n (map fst c) ->
                In n (map fst s) ->
                In e (id_args c)[/s/] -> In e (map snd s).
Proof.
  induction c;
    basic_goal_prep;
    basic_core_crush.
  (apply lookup_in_dom; assumption).
  
  
  rewrite IHc.
  unfold args_subst.
*)

(*TODO: put in utils*)
Lemma named_list_lookup_notin_app {A B} `{Eqb A} (n : A) l1 l2 (d : B)
  : ~ In n (map fst l1) ->
    named_list_lookup d (l1++l2) n = named_list_lookup d l2 n.
Proof.
  induction l1;
    basic_goal_prep;
    basic_utils_crush.
  case_match; basic_utils_crush.
Qed.

(*TODO: put in utils*)
Lemma named_list_lookup_in_app {A B} `{Eqb A} (n : A) l1 l2 (d : B)
  : In n (map fst l1) ->
    named_list_lookup d (l1++l2) n = named_list_lookup d l1 n.
Proof.
  induction l1;
    basic_goal_prep;
    basic_utils_crush.
  case_match; basic_utils_crush.
Qed.

(*TODO: put in utils *)
Lemma all2_refl {A} `{Eqb A} (l : list A) : all2 eqb l l = true.
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Rewrite all2_refl : utils.

(*TODO: put in utils *)
Lemma and_true_l b : (true && b = b)%bool.
Proof.
  basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Rewrite and_true_l : utils.

(*TODO: put in utils *)
Lemma and_true_r b : (b && true = b)%bool.
Proof.
  destruct b;
  basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Rewrite and_true_r : utils.

Lemma compile_subst_lookup cmp s n cname
  : In cname (fst cmp) ->
    compile cmp cname (subst_lookup s n)
  = subst_lookup (compile_subst cmp s) (cname::n).
Proof.
  induction s;
    basic_goal_prep;
    basic_core_crush.
  case_match; basic_core_crush.
  2:{
    unfold subst_lookup in *.
    rewrite H0.
    rewrite named_list_lookup_notin_app; auto.
    assert (l<> n) by basic_utils_crush.
    rewrite map_map.
    simpl.
    revert H1; clear.
    induction l0;
      basic_goal_prep;
      basic_utils_crush.
  }
  {
    unfold subst_lookup in *.
    rewrite named_list_lookup_in_app; simpl; auto.
    2:{
      rewrite map_map; simpl.
      revert H; clear.
      induction l0;
      basic_goal_prep;
      basic_utils_crush.
    }
    
    revert H; clear.
    generalize (compile (l0,n0)) as cf; intro.
    induction l0;
      basic_goal_prep;
      basic_utils_crush.
    case_match;
      basic_goal_prep;
      basic_utils_crush.
  }
Qed.
Hint Rewrite compile_subst_lookup : lang_core.


Lemma combine_subst args l s
  : (combine args l)[/s/] = combine args l[/s/].
Proof.
  revert args.
  induction l;
    destruct args;
    basic_goal_prep;
    basic_core_crush.
Qed.

(*TODO: move to utils*)
Hint Rewrite map_map : utils.
Hint Rewrite map_app : utils.

Lemma env_args_as_fst_ctx cmp1 cmp2 c
  : fst cmp1 = fst cmp2 ->
    (env_args cmp1 (map fst c))
    = (map fst (compile_ctx cmp2 c)).
Proof.
  induction c; basic_goal_prep; basic_core_firstorder_crush.
Qed.

Lemma all_impl {A} {P Q : _ -> Prop} (l : list A)
  : (forall a, In a l -> P a -> Q a) -> all P l -> all Q l.
Proof.
  intro; induction l; basic_goal_prep; basic_utils_crush.
Qed.

Lemma sort_case_in_preserving_well_scoped cmp_pre tgt cmp src n args t
  : preserving_compiler_ext cmp_pre tgt cmp src ->
    ws_lang tgt ->
    In (n, sort_case args t) cmp ->
    all (well_scoped (env_args cmp_pre args)) t.
Proof.
  induction 1; basic_goal_prep; basic_core_firstorder_crush.
  erewrite env_args_as_fst_ctx.
  eapply all_impl; [|eassumption].
  basic_goal_prep; basic_core_firstorder_crush.
  destruct cmp_pre; reflexivity.
Qed.
Hint Resolve sort_case_in_preserving_well_scoped : lang_core.

(*TODO: move to utils*)
Tactic Notation "open_generalize" uconstr(c) :=
  let a' := fresh "v" in
  let a := fresh "v" in
  set c as a; generalize a as a'; clear a.

Lemma term_case_in_preserving_well_scoped cmp_pre tgt cmp src n args t
  : preserving_compiler_ext cmp_pre tgt cmp src ->
    ws_lang tgt ->
    In (n, term_case args t) cmp ->
    well_scoped (env_args cmp_pre args) t.
Proof.
  induction 1; basic_goal_prep; basic_core_firstorder_crush.
  assert (all (fun p => well_scoped (env_args cmp_pre (map fst c)) (snd p))
              (combine (fst cmp_pre) t)).
  {
    erewrite env_args_as_fst_ctx.
    eapply all_impl; [|eassumption].
    basic_goal_prep.
    basic_core_firstorder_crush.
    destruct cmp_pre; reflexivity.
  }
  destruct cmp_pre; simpl in *;
    revert H4 H1; clear.
  open_generalize (env_args _ _); intro args.
  revert l0; induction t; destruct l0; 
    basic_goal_prep;
    basic_core_firstorder_crush.
Qed.
Hint Resolve term_case_in_preserving_well_scoped : lang_core.


(*cmp1,2 an artifact of env_args taking a full compiler*)
Lemma compile_args_to_subst {B} cnames cmp1 cmp2 c (l : list B)
  : combine (env_args (cnames, cmp1) (map fst c)) l
    = with_names_from (compile_ctx (cnames, cmp2) c) l.
Proof.
  induction c; basic_goal_prep; basic_core_crush.
  rewrite <- combine_map_fst_is_with_names_from.
  basic_core_crush.
  f_equal.
  f_equal.
  apply env_args_as_fst_ctx; auto.
Qed.


Lemma sort_case_length_in_preserving cnames cmp_pre tgt cmp src n args t
  : preserving_compiler_ext (cnames, cmp_pre) tgt cmp src ->
    In (n, sort_case args t) cmp ->
    length t = length cnames.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.


Lemma term_case_length_in_preserving cnames cmp_pre tgt cmp src n args t
  : preserving_compiler_ext (cnames, cmp_pre) tgt cmp src ->
    In (n, term_case args t) cmp ->
    length t = length cnames.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.




Require Import Lia.
(*TODO: move to utils*)
Hint Rewrite app_length : utils.
Lemma flat_map_const_len {A B} (f : A -> list B) len l
  : (forall a, length (f a) = len) ->
    length (flat_map f l) = len * length l.
Proof.
  intros; induction l;
    basic_goal_prep;
    basic_utils_crush.
  simpl.
  specialize (H a).
  lia.
Qed.

Local Lemma distribute_compile_subst cnames tgt cmp src s
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    (forall c t,
        wf_sort src c t ->
        map fst c = map fst s ->
        forall cname, 
          In cname cnames ->
        compile_sort (cnames,cmp) cname t[/s/]
        = (compile_sort (cnames,cmp) cname t)[/compile_subst (cnames,cmp) s/])
    /\ (forall c e t,
           wf_term src c e t ->
           map fst c = map fst s ->
        forall cname, 
          In cname cnames ->
           compile (cnames,cmp) cname e[/s/]
           = (compile (cnames,cmp) cname e)[/compile_subst (cnames,cmp) s/])
    /\ (forall c s' c',
           wf_args src c s' c' ->
           map fst c = map fst s ->
           compile_args (cnames,cmp) s'[/s/]
           = (compile_args (cnames,cmp) s')[/compile_subst (cnames,cmp) s/]).
Proof using.
  intros; apply wf_judge_ind; 
    basic_goal_prep;
    basic_core_firstorder_crush.
  {
    case_match; basic_core_crush.
    case_match; auto.
    replace args0 with (map fst c').
    unfold env_args.
    pose proof @compile_args_to_subst.
    unfold env_args in H8; erewrite !H8.
    clear H8.
    rewrite subst_assoc.
    fold_Substable.
    rewrite <- with_names_from_args_subst.
    rewrite H7.
    reflexivity.
    rewrite map_fst_with_names_from.
    pose proof (sort_case_in_preserving_well_scoped _ _ _ H ltac:(basic_core_crush) HeqH8).
    pose proof (lang_compiler_sort_case_args_eq _ _ _ _ _ H H0 H2 HeqH8).
    subst.
    enough (all (fun p => well_scoped (env_args (cnames,[]) (map fst c')) (snd p))
                (combine cnames tl)).
    {
      eapply P_of_named_list_lookup_from_all_combined in H9.
      erewrite <- env_args_as_fst_ctx; try reflexivity.
      exact H9.
      auto.
      eapply sort_case_length_in_preserving; eauto.
    }
    {
      revert H8.
      pose proof (sort_case_length_in_preserving _ _ _ H HeqH8) as H8; revert H8.
      clear.
      open_generalize (env_args _ _); intro args.
      revert tl; induction cnames;
        destruct tl;
        basic_goal_prep;
        basic_core_firstorder_crush.
    }
    {
      unfold compile_ctx, compile_args;
      erewrite !flat_map_const_len.
      f_equal.
      basic_core_crush.
      all: intros; simpl; try case_match; rewrite ?map_length; reflexivity.
    }
    {
      symmetry; eapply lang_compiler_sort_case_args_eq; eauto.
    }
  }
  {
    case_match; basic_core_crush.
    case_match; auto.
    replace args0 with (map fst c').
    unfold env_args.
    pose proof @compile_args_to_subst.
    unfold env_args in H8; erewrite !H8.
    clear H8.
    rewrite subst_assoc.
    fold_Substable.
    rewrite <- with_names_from_args_subst.
    all:change (flat_map
           (fun x : term =>
            map
              (fun cname0 : string =>
                 compile (?cnames, ?cmp) cname0 x) ?cnames))
      with (compile_args (cnames, cmp)).
    rewrite !H7.
    reflexivity.
    rewrite map_fst_with_names_from.
    pose proof (term_case_in_preserving_well_scoped _ _ _ H ltac:(basic_core_crush) HeqH8).
    pose proof (lang_compiler_term_case_args_eq _ _ _ _ _ _ H H0 H2 HeqH8).
    subst.
    enough (all (fun p => well_scoped (env_args (cnames,[]) (map fst c')) (snd p))
                (combine cnames el)).
    {
      eapply P_of_named_list_lookup_from_all_combined in H9.
      erewrite <- env_args_as_fst_ctx; try reflexivity.
      exact H9.
      auto.
      eapply term_case_length_in_preserving; eauto.
    }
    {
      revert H8.
      pose proof (term_case_length_in_preserving _ _ _ H HeqH8) as H8; revert H8.
      clear.
      open_generalize (env_args _ _); intro args.
      revert el; induction cnames;
        destruct el;
        basic_goal_prep;
        basic_core_firstorder_crush.
    }
    {
      unfold compile_ctx, compile_args;
      erewrite !flat_map_const_len.
      f_equal.
      basic_core_crush.
      all: intros; simpl; try case_match; rewrite ?map_length; reflexivity.
    }
    {
      symmetry; eapply lang_compiler_term_case_args_eq; eauto.
    }
  }
  {
    unfold apply_subst,substable_args, substable_term, args_subst.
    basic_utils_crush.
    unfold apply_subst,substable_args, substable_term, args_subst; simpl.
    fold_Substable.
    f_equal.
    {
      apply map_ext_in; 
        basic_goal_prep;
        basic_core_firstorder_crush.
    }
    {
      change (map (term_subst ?s) ?l) with (l[/s/]).
      assumption.
    }
  }
Qed.

Lemma compile_term_subst tgt cmp src s c e t cnames cname
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    wf_term src c e t ->
    map fst c = map fst s ->
    In cname cnames ->
    compile (cnames,cmp) cname e[/s/]
    = (compile (cnames,cmp) cname e)[/compile_subst (cnames,cmp) s/].
Proof.
  intros; eapply distribute_compile_subst; eassumption.
Qed.
Hint Rewrite compile_term_subst : lang_core.


Lemma compile_sort_subst tgt cmp src s c t cnames cname
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    wf_sort src c t ->
    map fst c = map fst s ->
    In cname cnames ->
    compile_sort (cnames,cmp) cname t[/s/]
    = (compile_sort (cnames,cmp) cname t)[/compile_subst (cnames,cmp) s/].
Proof.
  intros; eapply distribute_compile_subst; eassumption.
Qed.
Hint Rewrite compile_sort_subst : lang_core.


Lemma compile_args_subst tgt cmp src s c s' c' cnames
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    wf_args src c s' c' ->
    map fst c = map fst s ->
    compile_args (cnames,cmp) s'[/s/]
    = (compile_args (cnames,cmp) s')[/compile_subst (cnames,cmp) s/].
Proof.
  intros; eapply distribute_compile_subst; eassumption.
Qed.
Hint Rewrite compile_args_subst : lang_core.

(*
Lemma compile_subst_with_names_from A cmp (c':named_list A) s
  : (compile_subst cmp (with_names_from c' s)) = with_names_from c' (map (compile cmp) s).
Proof.
  unfold compile_subst.
  rewrite <- with_names_from_map_is_named_map.
  reflexivity.
Qed.
*)

Existing Instance sort_default.


(* TODO: move generalization to utils*)

Lemma named_list_lookup_none {A}
      (l : named_list A) (s:list string) (a:A)
  : None = Utils.named_list_lookup_err l s ->
    ~ In (s, a) l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
  my_case Hs (eqb s l0); basic_goal_prep; basic_utils_crush.
Qed.

Lemma compile_scon cmp args s name t cname cnames
  : all_fresh cmp ->
    In (name, sort_case args t) cmp ->
    In cname cnames ->
    length cnames = length t ->
    (compile_sort (cnames,cmp) cname (scon name s))
    = (named_list_lookup default (combine cnames t) cname)
        [/(combine (env_args (cnames, cmp) args) (compile_args (cnames,cmp) s))/].
Proof.
  basic_goal_prep; repeat case_match; basic_core_crush.
  {
    (*TODO: should be automated; how best to do so?*)
    pose proof (in_all_fresh_same _ _ _ _ H H0 HeqH3).
    basic_core_crush.
  }
  {
    (*TODO: should be automated; how best to do so?*)
    pose proof (in_all_fresh_same _ _ _ _ H H0 HeqH3).
    basic_core_crush.
  }
  {
    exfalso.
    (*TODO: why isn't this automated already?*)
    eapply named_list_lookup_none; eauto.
  }
Qed.
  
Lemma lang_compiler_conflict_sort_term cmp_pre lt cmp ls n c args args' e
  : preserving_compiler_ext cmp_pre lt cmp ls ->
    all_fresh ls ->
    In (n, sort_rule c args) ls ->
    In (n, term_case args' e) cmp ->
    False.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  match goal with
    [Hp : preserving_compiler_ext _ _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  basic_core_crush.
Qed.
Hint Resolve lang_compiler_conflict_sort_term : lang_core.

  
Lemma lang_compiler_conflict_term_sort cmp_pre lt cmp ls n c args args' e t
  : preserving_compiler_ext cmp_pre lt cmp ls ->
    all_fresh ls ->
    In (n, term_rule c args t) ls ->
    In (n, sort_case args' e) cmp ->
    False.
Proof.
  induction 1; basic_goal_prep; basic_core_firstorder_crush.
  match goal with
    [Hp : preserving_compiler_ext _ _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  eauto with utils.
Qed.
Hint Resolve lang_compiler_conflict_term_sort : lang_core.


Lemma combine_map {A B C D} (f : A -> C) (g : B -> D) l1 l2 
  : combine (map f l1) (map g l2)
    = map (fun '(a,b) => (f a,g b)) (combine l1 l2).
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
Qed.


Lemma map_combine_XX {A B} (f : A * A -> B) x
  : map f (combine x x) = map (fun a => f(a,a)) x.
Proof.
  induction x; 
    basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma compile_subst_with_names_from cnames cmp c' s
  : length c' = length s ->
    (compile_subst (cnames, cmp) (with_names_from c' s))
    = with_names_from (compile_ctx (cnames, cmp) c')
                      (compile_args (cnames, cmp) s).
Proof.
  revert s; induction c';
    destruct s;
    basic_goal_prep;
    basic_core_crush.
  rewrite IHc'; auto.
  f_equal.
  rewrite <- !combine_map_fst_is_with_names_from.
  rewrite map_map.
  simpl.
  rewrite combine_map.
  rewrite map_combine_XX.
  simpl.
  reflexivity.
Qed.


Lemma compiled_args_len cnames cname cmp c s c' lt
  : In cname cnames ->
    wf_args lt (compile_ctx (cnames, cmp) c) (compile_args (cnames, cmp) s) (compile_ctx (cnames, cmp) c') ->
    Datatypes.length c' = Datatypes.length s.
Proof.
  intros inc wfa;
    apply wf_args_length_eq in wfa;
    unfold compile_args, compile_ctx in *.
  enough (length cnames * length c' = length cnames * length s).
  {
    revert inc H.
    clear.
    intro inc.
    assert (length cnames > 0) by (destruct cnames; basic_goal_prep; basic_utils_crush; lia).
    rewrite PeanoNat.Nat.mul_cancel_l; auto; lia.
  }
  erewrite !flat_map_const_len in wfa.
  eassumption.
  all: intros; simpl; break;
    rewrite map_length; reflexivity.
Qed.
Local Hint Resolve compiled_args_len : core.

(*TODO: do the same thing for terms*)
Lemma inductive_implies_semantic_sort_rule
      ls lt cmp name c c' args s
      cnames cname
  : wf_lang lt ->
    preserving_compiler_ext (cnames,[]) lt cmp ls ->
    wf_lang ls ->
    In (name, sort_rule c' args) ls ->
    In cname cnames ->
    wf_ctx lt (compile_ctx (cnames,cmp) c') ->
    wf_args lt (compile_ctx (cnames,cmp) c)
            (compile_args (cnames,cmp) s)
            (compile_ctx (cnames,cmp) c') ->
    wf_sort lt (compile_ctx (cnames,cmp) c)
            (compile_sort (cnames,cmp) cname (scon name s)).
Proof.
  intros.
  replace (scon name s) with (scon name (id_args c'))[/(with_names_from c' s)/].
  erewrite compile_sort_subst; try eassumption; eauto with lang_core.
  2:{
    econstructor; [eassumption |].
    basic_core_crush.
  }
  eapply wf_sort_subst_monotonicity; auto.
  {
    eapply inductive_implies_semantic_sort_rule_id; eauto.
  }
  all: basic_core_firstorder_crush.
  {
    rewrite compile_subst_with_names_from.
    eapply wf_subst_from_wf_args; basic_core_crush.
    eapply compiled_args_len; eauto.
  }
  {
    simpl; f_equal.
    rewrite wf_con_id_args_subst; basic_core_firstorder_crush.
    use_rule_in_wf.
    inversion H6.
    basic_core_crush.
  }
Qed.

Lemma inductive_implies_semantic_term_rule cnames ls lt cmp name c c' args t s cname
  : wf_lang lt ->
    preserving_compiler_ext (cnames,[]) lt cmp ls ->
    wf_lang ls ->
    In (name, term_rule c' args t) ls ->
    In cname cnames ->
    wf_ctx lt (compile_ctx (cnames,cmp) c') ->
    wf_args lt (compile_ctx (cnames,cmp) c) (compile_args (cnames,cmp) s) (compile_ctx (cnames,cmp) c') ->
    wf_term lt (compile_ctx (cnames,cmp) c)
            (compile (cnames,cmp) cname (con name s))
            (compile_sort (cnames,cmp) cname t)[/compile_subst (cnames,cmp) (with_names_from c' s)/].
Proof.
  intros.
  replace (con name s) with (con name (id_args c'))[/(with_names_from c' s)/].
  erewrite compile_term_subst; try eassumption; eauto with lang_core.
  2:{
    econstructor; [eassumption |].
    basic_core_crush.
  }
  eapply wf_term_subst_monotonicity; auto.
  {
    eapply inductive_implies_semantic_term_rule_id; eauto.
  }
  all: basic_core_firstorder_crush.
  {
    rewrite compile_subst_with_names_from.
    eapply wf_subst_from_wf_args; basic_core_crush.
    eapply compiled_args_len; eauto.
  }
  {
    simpl; f_equal.
    fold_Substable.
    rewrite wf_con_id_args_subst; basic_core_firstorder_crush.
    use_rule_in_wf.
    inversion H6.
    basic_core_crush.
  }
Qed.


(*TODO: maybe not necessary with better strengthening lemma?
  See what happens when I use the better one
*)
Variant rule_compiles_with {lt cmp} : rule -> Prop :=
| sort_rule_compiles_with c args
  : wf_ctx lt (compile_ctx cmp c) -> rule_compiles_with (sort_rule c args)
| term_rule_compiles_with c args t
  : wf_ctx lt (compile_ctx cmp c) ->
    (forall cname, In cname (fst cmp) -> wf_sort lt (compile_ctx cmp c) (compile_sort cmp cname t)) ->
    rule_compiles_with (term_rule c args t)
(*Similar properties are not necessary for eq rules*)
| sort_eq_rule_compiles_with c t1 t2 : rule_compiles_with (sort_eq_rule c t1 t2)
| term_eq_rule_compiles_with c e1 e2 t : rule_compiles_with (term_eq_rule c e1 e2 t).
Arguments rule_compiles_with : clear implicits.
                       
Definition lang_compiles_with lt cmp : lang -> Prop :=
  all (fun p => rule_compiles_with lt cmp (snd p)).


Lemma lang_compiles_with_sort_ctx_in lt cmp ls n c' args
  : lang_compiles_with lt cmp ls ->
    In (n, sort_rule c' args) ls ->
    wf_ctx lt (compile_ctx cmp c').
Proof.
  induction ls; 
    basic_goal_prep;
    basic_core_firstorder_crush.
  (*TODO: This could be automated w/ an inversion lemma*)
  match goal with
    [H : rule_compiles_with _ _ _ |-_]=>
    inversion H; basic_core_crush
  end.
Qed.
Local Hint Resolve lang_compiles_with_sort_ctx_in : lang_core.

Lemma lang_compiles_with_term_ctx_in lt cmp ls n c' args t
  : lang_compiles_with lt cmp ls ->
    In (n, term_rule c' args t) ls ->
    wf_ctx lt (compile_ctx cmp c').
Proof.
  induction ls; 
    basic_goal_prep;
    basic_core_firstorder_crush.
  (*TODO: This could be automated w/ an inversion lemma*)
  match goal with
    [H : rule_compiles_with _ _ _ |-_]=>
    inversion H; basic_core_crush
  end.
Qed.
Local Hint Resolve lang_compiles_with_term_ctx_in : lang_core.


Lemma lang_compiles_with_term_sort_in lt cmp ls n c' args t cname
  : lang_compiles_with lt cmp ls ->
    In (n, term_rule c' args t) ls ->
    In cname (fst cmp) ->
    wf_sort lt (compile_ctx cmp c') (compile_sort cmp cname t).
Proof.
  induction ls; 
    basic_goal_prep;
    basic_core_firstorder_crush.
  (*TODO: This could be automated w/ an inversion lemma*)
  match goal with
    [H : rule_compiles_with _ _ _ |-_]=>
    inversion H; basic_core_crush
  end.
Qed.
Local Hint Resolve lang_compiles_with_term_sort_in : lang_core.



Lemma in_flat_map {A B} x (f : A -> list B) l a
  : In x l -> In a (f x) -> In a (flat_map f l).
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_firstorder_crush.
Qed.

Lemma extend_ctx_with_map
  : forall {A} (l:lang) (lst : list A) c,
    wf_lang l->
    wf_ctx l c ->
    forall f,
      (forall x, In x lst -> wf_sort l c (snd (f x))) ->
      all_fresh ((map f lst) ++ c) ->
      wf_ctx l (map f lst ++ c).
Proof.
  intros A l lst c wfl wfc f.
  induction lst; basic_goal_prep; basic_utils_crush.
  remember H as H'.
  clear HeqH'.
  specialize (H' a ltac:(intuition)).
  revert H' H0; generalize (f a); basic_goal_prep.
  constructor; auto.
  (*TODO: hack to get around missing lemma*)
  revert wfl H'.
  clear.
  generalize (map f lst).
  induction l0; basic_goal_prep; basic_core_firstorder_crush.
Qed.

Lemma preserving_implies_unique_names cnames cmp_pre lt cmp ls
  : preserving_compiler_ext (cnames,cmp_pre) lt cmp ls ->
    all_unique cnames.
Proof.
  induction 1; eauto.
Qed.


Lemma in_namespaced a name cnames l
  : In (a :: l) (map (fun x : string => x :: name) cnames) <->
      (l = name /\ In a cnames).
Proof.
  induction cnames;
    basic_goal_prep; basic_utils_crush.
Qed.

(*TODO: replace all_fresh entirely?*)
Lemma all_fresh_as_all_unique {V A} (l : @Utils.named_list V A)
  : all_fresh l <-> all_unique (map fst l).
Proof.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
Qed.


Lemma map_flat_map  {A B C} (f : B -> C) (g : A -> list B) l
  : map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof.
  induction l; 
    basic_goal_prep;
    basic_utils_crush.
Qed.


Lemma all_unique_flat_map_inj {A B} (f : A -> list B) l
  : (forall x y z, In z (f x) -> In z (f y) -> x = y) ->
    all_unique l ->
    all_unique (flat_map f l).
Proof.
  intro.
  induction l;
    basic_goal_prep;
    basic_utils_crush.
  specialize (H a).
  assert (forall b z, In b l -> In z (f a) -> ~ In z (f b)) by admit.
  revert H3.
  generalize (f a) as l'; induction l';
    basic_goal_prep;
    basic_utils_crush.
Admitted.

(*TODO: move to core*)
Lemma eq_subst_ctx_monotonicity_app
     : forall (V : Type) (V_Eqb : Eqb V) (l : Rule.lang V) c_ext (t' : Term.sort V),
       wf_lang l ->
       forall (c c' : Term.ctx V) (s1 s2 : Term.subst V),
       eq_subst l c c' s1 s2 -> eq_subst l (c_ext ++ c) c' s1 s2.
Proof.
  intros; induction c_ext;
    basic_goal_prep;
    basic_core_crush.
Qed.

Local Lemma inductive_implies_semantic' cnames lt cmp ls
  : wf_lang ls ->
    wf_lang lt ->
    (* TODO: need cnames unique
    all_fresh cnames ->*)
    preserving_compiler_ext (cnames,[]) lt cmp ls ->
    lang_compiles_with lt (cnames,cmp) ls ->
    semantics_preserving lt (cnames,cmp) ls.
Proof.
  intros; apply judge_ind; 
    basic_goal_prep;
    basic_core_firstorder_crush.
  {
    eapply inductive_implies_semantic_sort_axiom; eassumption.
  }
  {
    erewrite !compile_sort_subst.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_firstorder_crush.
  }
  {
    erewrite !compile_sort_subst.
    erewrite !compile_term_subst.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_firstorder_crush.
  }
  {
    eapply inductive_implies_semantic_term_axiom; eassumption.
  }
  {
    revert H4.
    assert (incl cnames cnames) by basic_utils_crush.
    revert H4.
    enough (forall cnames', incl cnames' cnames ->
  (forall cname : string,
   In cname cnames' ->
   eq_term lt (compile_ctx (cnames, cmp) c) (compile_sort (cnames, cmp) cname t [/s2 /])
     (compile (cnames, cmp) cname e1) (compile (cnames, cmp) cname e2)) ->
  eq_subst lt (compile_ctx (cnames, cmp) c)
    (map (fun cname : string => (cname :: name, compile_sort (cnames, cmp) cname t)) cnames' ++
     compile_ctx (cnames, cmp) c')
    (map (fun cname : string => (cname :: name, compile (cnames, cmp) cname e1)) cnames' ++
     compile_subst (cnames, cmp) s1)
    (map (fun cname : string => (cname :: name, compile (cnames, cmp) cname e2)) cnames' ++
     compile_subst (cnames, cmp) s2)) by eauto.
    induction cnames'; basic_goal_prep;
      basic_core_firstorder_crush.
    constructor; eauto.
    clear H13.
    assert ((compile_sort (cnames, cmp) a t)
    [/map (fun cname : string => (cname :: name, compile (cnames, cmp) cname e2)) cnames' ++
      compile_subst (cnames, cmp) s2 /]
            = (compile_sort (cnames, cmp) a t)[/compile_subst (cnames, cmp) s2 /]) by admit.
    rewrite H13.
    erewrite <- compile_sort_subst; basic_core_firstorder_crush.
    symmetry; eapply eq_subst_dom_eq_r; eauto.
  } 
  {
    eapply inductive_implies_semantic_sort_rule; try eassumption.
    all: try use_rule_in_wf; basic_core_firstorder_crush.
  }
  {
    erewrite compile_sort_subst; eauto.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_firstorder_crush.
    assert (wf_ctx ls c') by (use_rule_in_wf; basic_core_crush).
    eapply inductive_implies_semantic_term_rule; try (auto;eassumption).
    all: try use_rule_in_wf; basic_core_firstorder_crush.
  }
  {
    constructor.
    unfold compile_ctx.
    eapply in_flat_map; eauto.
    simpl.
    rewrite in_map_iff; eauto.
  }
  {
    admit (*wf_args app*).
  }
  {
    eapply extend_ctx_with_map; eauto.
    apply wf_ctx_all_fresh in H5.
    pose proof (preserving_implies_unique_names H1) as H7.
    {
      rewrite all_fresh_as_all_unique in *.
      rewrite map_app.
      erewrite <- env_args_as_fst_ctx in * by reflexivity.
      rewrite map_map.
      simpl.
      unfold env_args in *.
      simpl.
      change
        (all_unique
           (flat_map (fun x : list string => map (fun c0 : string => c0 :: x) cnames) (name ::map fst c))).
      Lemma all_unique_flat_map_inj
        : (forall x y, f x = f y -> x = y) ->
          all_unique l ->
          all_unique (flat_map f l).
      rewrite map_flat_map.
      erewrite flat_map_funext.
      2:{
        basic_goal_prep.
        rewrite map_map.
        simpl.
        instantiate
          (1:= fun p => map (fun x : string => x :: fst p) cnames).
        reflexivity.
      }
      simpl.
      
      
    revert H7 H5 H3; clear; intros.
    basic_utils_crush.
    simpl in *.
    revert H7.
    induction cnames;
      basic_goal_prep;
      basic_utils_crush.
    { rewrite in_namespaced in *; intuition. }
    {
      revert H3 H2; clear.
      unfold compile_ctx.
      rewrite map_flat_map.
      erewrite flat_map_funext.
      2:{
        basic_goal_prep.
        rewrite map_map.
        simpl.
        instantiate
          (1:= fun p => (a :: (fst p)) :: map (fun x : string => x :: (fst p)) cnames).
        reflexivity.
      }
      {
        induction c;
        basic_goal_prep;
        basic_utils_crush.
        rewrite in_namespaced in *; intuition.
      }
    }
    erewrite <- env_args_as_fst_ctx in * by reflexivity.(*
    TODO: need all_unique reordering! a better way?
        rewrite 
          apply H.
    
    TODO: cname freshness reasoning*)
  }
  }
Admitted.

Local Lemma inductive_implies_semantic_ctx' lt cmp ls cnames
  : wf_lang ls ->
    wf_lang lt ->
    preserving_compiler_ext (cnames,[]) lt cmp ls ->
    lang_compiles_with lt (cnames,cmp) ls ->
    forall c : ctx, wf_ctx ls c -> wf_ctx lt (compile_ctx (cnames,cmp) c).
Proof.
  intros wfs wft pc lcw.
  apply inductive_implies_semantic'; eauto.
Qed.
Local Hint Resolve inductive_implies_semantic_ctx' : lang_core.


Local Hint Constructors rule_compiles_with : lang_core.

Local Lemma rule_compiles_extend_fresh lt cmp r n cc cnames
  : rule_compiles_with lt (cnames,cmp) r ->
    all_constructors_rule (fun n0 => In n0 (map fst cmp)) r ->
    fresh n cmp ->
    all_fresh cmp ->
    rule_compiles_with lt (cnames,(n,cc)::cmp) r.
Proof.
  inversion 1; basic_goal_prep; with_rule_in_wf_crush.
  all: constructor.
  all: try erewrite compile_strengthen_ctx; eauto.
  {
    intros.
    erewrite compile_strengthen_sort;eauto.
  }    
Qed. 
  
Local Lemma lang_compiles_extend_fresh lt cmp ls n cc cnames
  : lang_compiles_with lt (cnames,cmp) ls ->
    all (fun '(_,r) => all_constructors_rule (fun n0 => In n0 (map fst cmp)) r) ls ->
    fresh n cmp ->
    all_fresh cmp ->
    lang_compiles_with lt (cnames,(n,cc)::cmp) ls.
Proof.
  unfold lang_compiles_with.
  induction ls; basic_goal_prep; with_rule_in_wf_crush.
  eapply rule_compiles_extend_fresh; eauto.
Qed.  

(*TODO: move to core with like lemmas above*)
Lemma all_constructors_rule_from_wf tgt cmp src r cnames
  : preserving_compiler_ext (cnames,[]) tgt cmp src ->
    wf_rule src r ->
    all_constructors_rule (fun n0 => In n0 (map fst cmp)) r.
Proof.
  inversion 2; basic_goal_prep;
    with_rule_in_wf_crush.
  (*TODO: automation; need to restrict simplify?*)
  all: eapply all_constructors_ctx_from_wf; eauto.
Qed.
Hint Resolve all_constructors_rule_from_wf : lang_core.


Lemma wf_lang_implies_all_constructors lt l
  : wf_lang l ->
    forall cnames cmp,
    preserving_compiler_ext (cnames,[]) lt cmp l ->
    all (fun '(_,r) => all_constructors_rule (fun n0 => In n0 (map fst cmp)) r) l.
Proof.
  induction 1; basic_goal_prep;
    with_rule_in_wf_crush.
  (*TODO: break down cmp*)
  inversion H2; subst.
  1,2:specialize (IHwf_lang_ext cnames cmp0).
  3,4:specialize (IHwf_lang_ext cnames cmp).
  all:eapply all_constructors_lang_weaken.
  all: try apply IHwf_lang_ext; auto.
  all:basic_goal_prep; basic_core_firstorder_crush.
Qed.


Local Lemma preserving_compiler_to_lang_compiles_with lt ls
  : wf_lang ls ->
    wf_lang lt ->
    forall cnames cmp,
    preserving_compiler_ext (cnames,[]) lt cmp ls ->
    lang_compiles_with lt (cnames,cmp) ls.
Proof.
  induction 1; inversion 2; basic_goal_prep; try use_rule_in_wf; basic_core_firstorder_crush.
  all: try constructor.
  all: try rewrite compile_strengthen_ctx; eauto.
  all: try (intros; rewrite compile_strengthen_sort; eauto).
  all: try apply lang_compiles_extend_fresh; eauto with lang_core.
  all: try eapply wf_lang_implies_all_constructors; eauto.
  {
    simpl in *.
     (*TODO: hack for missing lemma*)
    eapply eq_term_wf_sort; auto;
      [basic_core_firstorder_crush
      | eapply eq_term_refl; auto].
    unshelve(eapply P_of_named_list_lookup_from_all_combined in H9); eauto; exact (con [] []).
  }
Qed.


Theorem inductive_implies_semantic lt cmp ls cnames
  : wf_lang ls ->
    wf_lang lt ->
    preserving_compiler_ext (cnames,[]) lt cmp ls ->
    semantics_preserving lt (cnames,cmp) ls.
Proof.
  intros; apply inductive_implies_semantic';
    eauto using preserving_compiler_to_lang_compiles_with.
Qed.


#[export] Hint Rewrite fresh_compile_ctx : lang_core.
#[export] Hint Rewrite all_fresh_compile_ctx : lang_core.
#[export] Hint Resolve fresh_lang_fresh_cmp : lang_core.
#[export] Hint Resolve all_fresh_compiler : lang_core.

#[export] Hint Rewrite compile_strengthen_term : lang_core.
#[export] Hint Rewrite compile_strengthen_args : lang_core.
#[export] Hint Rewrite compile_strengthen_sort : lang_core.
#[export] Hint Rewrite compile_strengthen_ctx : lang_core.


#[export] Hint Resolve all_constructors_sort_from_wf : lang_core.
#[export] Hint Resolve all_constructors_term_from_wf : lang_core.
#[export] Hint Resolve all_constructors_args_from_wf : lang_core.
#[export] Hint Resolve all_constructors_ctx_from_wf : lang_core.
#[export] Hint Rewrite compile_id_args : lang_core.
#[export] Hint Rewrite compile_subst_lookup : lang_core.

#[export] Hint Resolve lang_compiler_sort_case_args_eq : lang_core.
#[export] Hint Resolve lang_compiler_term_case_args_eq : lang_core.
#[export] Hint Resolve sort_case_in_preserving_well_scoped : lang_core.
#[export] Hint Resolve term_case_in_preserving_well_scoped : lang_core.

#[export] Hint Rewrite compile_term_subst : lang_core.
#[export] Hint Rewrite compile_sort_subst : lang_core.
#[export] Hint Rewrite compile_args_subst : lang_core.

#[export] Hint Resolve lang_compiler_conflict_sort_term : lang_core.
#[export] Hint Resolve lang_compiler_conflict_term_sort : lang_core.


#[export] Hint Resolve all_constructors_rule_from_wf : lang_core.
