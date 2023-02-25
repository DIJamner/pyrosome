Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Import Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Infinite Monad.
From Pyrosome Require Import Theory.Core Theory.Renaming Compilers.CompilerDefs.
Import Core.Notations.

(*TODO: move to Utils.v*)
Definition unique_proofs P := forall (a b : P), a = b.

Lemma is_true_unique : forall b, unique_proofs (Is_true b).
Proof.
  destruct b; intros a b;
    destruct a; destruct b;
    auto.
Qed.


Notation "'{B' x & c }" :=
  (sigT (fun x => Is_true c))
    (x binder, format "'[' '{B'  x  &  c } ']'").


Lemma is_true_subset_eq {A} f (a b : {B x : A & f x})
  : a = b <-> projT1 a = projT1 b.
Proof.
  destruct a; destruct b; simpl;
    intuition try congruence; subst.
  f_equal.
  apply is_true_unique.
Qed.


(*TODO: make Injective a typeclass?*)
Lemma is_true_subset_proj_Injective {A} (f : A -> _)
  : Injective (projT1 (P:= fun x => Is_true (f x))).
Proof.
  intros a b; apply is_true_subset_eq.
Qed.
#[export] Hint Resolve is_true_subset_proj_Injective : utils.

(*TODO: split proofs out/split Eqb?*)
#[export] Instance is_true_subset_Eqb A f `{Eqb A} : Eqb {B x : A & f x} :=
  fun a b => eqb (projT1 a) (projT1 b).

#[export] Instance is_true_subset_Eqb_ok A f `{Eqb_ok A}
  : Eqb_ok (is_true_subset_Eqb f).
Proof.
  intros a b.
  unfold eqb, is_true_subset_Eqb.
  destruct a, b; simpl;
    case_match;
    basic_utils_crush.
  {
    f_equal; 
    apply is_true_unique.
  }
  {
    safe_invert H1.
    auto.
  }
Qed.

(*TODO: move to Monad.v *)
Definition named_list_Mmap {M V A B} `{Monad M} (f : A -> M B)
  : @named_list V A -> M (@named_list V B) :=
  list_Mmap (fun '(x,a) => @! let b <- f a in ret (x,b)).

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}
  (*{V_inf : Infinite V}*).
  

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  Section WithParameter.

    (*TODO: how to handle p_name freshness?
      idea: non-identity injective endofunction
      - skip p_name in cod
      - preserve lang vars (w/out proof they are in the lang)
     *)
    Context (p_name : V)
      (p_sort : sort).

      Section WithInjection.
        Context
          (V' : Type)
          (* assume a renaming where p_name isn't in the codomain *)
          (f : V' -> V)
            (*TODO: make Injective a typeclass?*)
            {f_inj : Injective f}
            {p_name_fresh : forall x, f x <> p_name}.

        (* the names of the rules in the language prefix *)
        (*TODO: also record the name here, gen a fresh one when processing rule*)
    Context (parameterize_list : named_list nat).
    
    Fixpoint parameterize_term (e : term) : term :=
      match e with
      | var x => var x
      | con n s =>
          let s' := map parameterize_term s in
          con n
            match named_list_lookup_err parameterize_list n with
            | None => s'
            | Some n => (firstn n s') ++ (var p_name)::(skipn n s')
            end
      end.
    
    Definition parameterize_sort (e : sort) : sort :=
      match e with
      | scon n s =>
          let s' := map parameterize_term s in
          scon n
               (*Note: this is a shortcut for using the base lang and finding the ctx*)
            match named_list_lookup_err parameterize_list n with
            | None => s'
            | Some n => (firstn n s') ++ (var p_name)::(skipn n s')
            end
      end.
    
    (*TODO: double-check when delta should be added.
          E.G. sort w/ parametric arg must be parameterized
          simple sort should not
          Should be like above, insert on first use
     *)

    
    Fixpoint insert_parameter (c : ctx) : option ctx :=
      match c with
      | [] => None
      | (x,t)::c' =>
          match insert_parameter c' with
          | Some c'' => Some ((x, t)::c'')
          | None =>
              if eqb t (parameterize_sort t)
              then None
              else Some ((x,t)::(p_name, p_sort)::c')
          end
      end.
    
    Definition parameterize_ctx c :=
      match insert_parameter c with
      | Some c' => named_map parameterize_sort c'
      | None => c
      end.
    
    Definition parameterize_ctx_always c :=
      match insert_parameter c with
      | Some c' => named_map parameterize_sort c'
      | None => (p_name, p_sort)::c
      end.

    (*
    Fixpoint insert_parameter_sub (c : ctx) : option ctx :=
      match c with
      | [] => None
      | (x,t)::c' =>
          match insert_parameter c' with
          | Some c'' => Some ((x, t)::c'')
          | None =>
              if uses_parameter_sort t
              then Some ((x,t)::(p_name, p_sort)::c')
              else None
          end
      end.

    Definition parameterize_sub s :=
      (named_map parameterize_term s)++[(p_name, var p_name)].
    
    Definition parameterize_args s :=
      (map parameterize_term s)++[var p_name].
     *)

    Definition parameterize_rule (r : rule) : rule :=
      match r with
      | sort_rule c args =>
          (*TODO: making p implicit in terms but not args is heuristic.
                Give the user more control.
                TODO: make sure p goes at the right places
           *)
          sort_rule (parameterize_ctx_always c) (args++[p_name])
      | term_rule c args t =>
          term_rule (parameterize_ctx_always c) args (parameterize_sort t)
      | sort_eq_rule c t1 t2 =>
          sort_eq_rule (parameterize_ctx c)
            (parameterize_sort t1)
            (parameterize_sort t2)
      | term_eq_rule c e1 e2 t =>
          term_eq_rule (parameterize_ctx c)
            (parameterize_term e1)
            (parameterize_term e2)
            (parameterize_sort t)
      end.

    
    Definition parameterize_ccase (c : compiler_case V) : compiler_case V :=
      match c with
      | sort_case args t =>
          sort_case (args++[p_name]) (parameterize_sort t)
      | term_case args e =>
          term_case (args++[p_name]) (parameterize_term e)
      end.

    Definition parameterize_compiler : _ -> compiler V :=
      named_map parameterize_ccase.

    Notation parameterize_lang := (named_map parameterize_rule).

    
    Lemma parameterize_subst_lookup s n e
      : n <> p_name ->
        parameterize_term (subst_lookup s n) =
          subst_lookup (named_map parameterize_term s ++ [(p_name, e)]) n.
    Proof.
      intro.
      induction s;
        basic_goal_prep;
        basic_term_crush.
      case_match; basic_utils_crush.
    Qed.

    (*
    Lemma subst_lookup_p_name s
      : fresh p_name s ->
        subst_lookup (parameterize_sub s) p_name = var p_name.
    Proof.
      induction s;
        basic_goal_prep;
        basic_term_crush.
    Qed.

    
    Lemma p_name_not_in_map l
      :  ~ In p_name (map f l).
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.        
      
    Lemma p_name_fresh_in_subst s
      : fresh p_name (rename_subst f s).
    Proof.
      unfold rename_subst, fresh.
      rewrite map_map; simpl.
      rewrite <- map_map.
      apply p_name_not_in_map.
    Qed.

    Lemma p_name_fresh_in_ctx s
      : fresh p_name (rename_ctx f s).
    Proof.
      unfold rename_ctx, fresh.
      rewrite map_map; simpl.
      rewrite <- map_map.
      apply p_name_not_in_map.
    Qed.
     *)

    (*
    
    Lemma parameterize_term_subst e s
      : parameterize_term (rename f e) [/rename_subst f s /]
        = (parameterize_term (rename f e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
      {
        unfold parameterize_sub.
        apply parameterize_subst_lookup; auto.
        firstorder.
      }
      {
        rewrite !map_app, !map_map;
          simpl.
        f_equal.
        {
          revert H.
          induction l;
            basic_goal_prep;
            basic_term_crush.
        }
        {
          f_equal.
          case_match; simpl; auto.
          rewrite subst_lookup_p_name; auto.
          apply p_name_fresh_in_subst.
        }
      }
    Qed.

    
    Lemma map_parameterize_term_subst e s
      : map parameterize_term (map (rename f) e) [/rename_subst f s /]
        = (map parameterize_term (map (rename f) e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
     
      {
        cbn.
        fold_Substable.
        f_equal; auto.
        rewrite !parameterize_term_subst; eauto.
      }
    Qed.
    
    Lemma parameterize_args_subst e s
      : parameterize_args (map (rename f) e) [/rename_subst f s /]
        = (parameterize_args (map (rename f) e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
      {
        cbn; f_equal.
        rewrite subst_lookup_p_name; auto.
        apply p_name_fresh_in_subst.
      }
      {
        cbn.
        unfold parameterize_args in *.
        fold_Substable.
        f_equal; auto.
        rewrite !parameterize_term_subst; eauto.
      }
    Qed.

    (*TODO: move to Term.v*)
    Lemma subst_app_args (l1 l2 : list term) s
      : (l1 ++ l2)[/s/] = l1[/s/] ++ l2[/s/].
    Proof.
      unfold apply_subst, substable_args, args_subst.
      rewrite map_app.
      reflexivity.
    Qed.
    
    Lemma parameterize_sort_subst e s
      : parameterize_sort (rename_sort f e) [/rename_subst f s /]
        = (parameterize_sort (rename_sort f e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      destruct e;
        basic_goal_prep;
        basic_term_crush.
      case_match; basic_utils_crush.
      {
        apply map_parameterize_term_subst.
      }
      {
        apply parameterize_args_subst.
      }
    Qed.

      End WithInjection.

      
      Section WithInjection.
        Context
          (* assume a renaming where p_name isn't in the codomain *)
          (f : V -> V)
            (*TODO: make Injective a typeclass?*)
            {f_inj : Injective f}
            {p_name_fresh : forall x, f x <> p_name}.

    Lemma p_name_freshb x : Is_true (negb (eqb (f x) p_name)).
    Proof.
      apply negb_prop_intro.
      intro H.
      apply p_name_fresh with (x:=x).
      revert H; unfold Is_true; case_match;
        basic_utils_crush.
    Qed.

    (*TODO: move to Renaming?*)
    Local Notation V' := {B x & negb (eqb x p_name)}.
    Definition f' x : V' :=
      existT _ (f x) (p_name_freshb x).
    
    Notation term' := (@Term.term V').
    Notation ctx' := (@Term.ctx V').
    Notation sort' := (@Term.sort V').
    Notation subst' := (@Term.subst V').
    Notation rule' := (@Rule.rule V').
    Notation lang' := (@Rule.lang V').

    Lemma V'_proj_not_p_name : forall x : V', projT1 x <> p_name.
    Proof.
      destruct x; simpl;
        basic_utils_crush.
    Qed.
      
     *)
    
      End WithInjection.
      
  End WithParameter.
  (*TODO: should be option?*)
  Fixpoint idx_of {A} `{Eqb A} (a:A) l : nat :=
    match l with
    | [] => 0 (*should never happen, but out of bounds if it does*)
    | a'::l =>
        if eqb a a' then 0 else S (idx_of a l)
    end.
         
  Context (p_name : V)
            (p_sort : sort).
    Fixpoint parameterize_lang' l parameterize_list :=
      match l with
      | [] => (parameterize_list, [])
      | (n,r)::l =>
          let (pl',l') := parameterize_lang' l parameterize_list in
          let r' := parameterize_rule p_name p_sort pl' r in
          let pl'' :=
          (*TODO: do this in a more idiomatic way?*)
            if eqb r r'
            then pl'
            else (n,idx_of p_name (map fst (get_ctx r)))::pl' in
          (pl'', (n,r')::l')
      end.
    Definition parameterize_lang l := snd (parameterize_lang' l []).
(*    Notation parameterize_lang :=
      (named_map (parameterize_rule (map f untouched_constructors))).
    Notation parameterize_sort :=
      (parameterize_sort (map f untouched_constructors)).
    Notation parameterize_term :=
      (parameterize_term (map f untouched_constructors)).
    Notation parameterize_ctx :=
      (parameterize_ctx (map f untouched_constructors)).
    Notation parameterize_sub :=
      (parameterize_sub (map f untouched_constructors)).
    Notation parameterize_args :=
      (parameterize_args (map f untouched_constructors)).
*)
    (*
    Lemma parameterization_monotonicity'
      (P := fun x => Is_true (negb (eqb (Impl := V_Eqb) x p_name)))
      (l : lang') lp
      (l':= (parameterize_lang (rename_lang (@projT1 V P) l))++lp)
      : all_fresh l' ->
     (*   untouched_constructors = (map fst lp) ->*)
        (forall c t1 t2,
            (*TODO: rename lp*)
            eq_sort (V:=V') (l ++ lp) c t1 t2 ->
            eq_sort l' (parameterize_ctx (rename_ctx (@projT1 V P) c))
              (parameterize_sort (rename_sort (@projT1 V P) t1))
              (parameterize_sort (rename_sort (@projT1 V P) t2)))
        /\ (forall c t e1 e2,
               eq_term (l ++ lp) c t e1 e2 ->
               eq_term l' (parameterize_ctx (rename_ctx (@projT1 V P) c))
                 (parameterize_sort (rename_sort (@projT1 V P) t))
                 (parameterize_term (rename (@projT1 V P) e1))
                 (parameterize_term (rename (@projT1 V P) e2)))
        /\ (forall c c' s1 s2,
               eq_subst (l ++ lp) c c' s1 s2 ->
               eq_subst l' (parameterize_ctx (rename_ctx (@projT1 V P) c))
                 (parameterize_ctx (rename_ctx (@projT1 V P) c'))
                 (parameterize_sub (rename_subst (@projT1 V P) s1))
                 (parameterize_sub (rename_subst (@projT1 V P) s2)))
        /\ (forall c t,
               wf_sort (l ++ lp) c t ->
               wf_sort l' (parameterize_ctx (rename_ctx (@projT1 V P) c))
                 (parameterize_sort (rename_sort (@projT1 V P) t)))
        /\ (forall c e t,
               wf_term (l ++ lp) c e t ->
               wf_term l' (parameterize_ctx (rename_ctx (@projT1 V P) c))
                 (parameterize_term (rename (@projT1 V P) e))
                 (parameterize_sort (rename_sort (@projT1 V P) t)))
        /\ (forall c s c',
               wf_args (l ++ lp) c s c' ->
               wf_args l' (parameterize_ctx (rename_ctx (@projT1 V P) c))
                 (parameterize_args (map (rename (@projT1 V P)) s))
                 (parameterize_ctx (rename_ctx (@projT1 V P) c)))
        /\ (forall c,
               wf_ctx (l ++ lp) c ->
               wf_ctx l' (parameterize_ctx (rename_ctx (@projT1 V P) c))).
Proof using.
  intros all_fresh.
  apply judge_ind; basic_goal_prep.
  all: try solve [constructor; eauto].
  all: erewrite ?rename_sort_distr_subst, ?rename_distr_subst in *
    by apply is_true_subset_proj_Injective.
  all:rewrite ?parameterize_term_subst, ?parameterize_sort_subst with (f:= projT1 (P:=P)) in *
    by apply V'_proj_not_p_name.
  {
    subst l'.
    eapply eq_sort_by.
    eapply in_or_app; left.
    unfold parameterize_lang, rename_lang.
    rewrite map_map; simpl.
    eapply in_map in H; exact H.
  }
  1:solve[basic_core_crush].
  1:solve[basic_core_crush].
  1:solve [basic_core_crush].
  {
    subst l'.
    eapply eq_term_by.
    eapply in_or_app; left.
    unfold parameterize_lang, rename_lang.
    rewrite map_map; simpl.
    eapply in_map in H; exact H.
  }  
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  {
    cbn.
    repeat constructor.
    unfold parameterize_ctx.
    basic_utils_crush.
    right.
    simpl.
    left.
    f_equal.
    admit (*TODO: find lemma*).
  }
  {
    cbn.
    constructor; basic_core_crush.
  }
  {
    TODO: should have n in l', not l?
    subst l'.
    case_match.
    eapply wf_sort_by.
    {
      eapply in_or_app; left.
    unfold parameterize_lang, rename_lang.
    rewrite map_map; simpl.
    eapply in_map in H; exact H.
    }  
    {
      TODO: 
        case_match;
      basic_core_crush.
    1:unfold parameterize_ctx.
    TODO: false; ctx always extended, but args not always extended
    TODO: important case; when we do/don't have D appended
    TODO: need wf
    eapply sort_con_congruence.
  }
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  {
    basic_core_crush.
    TODO: why are s1, s2 not renamed?
    rewrite <- !rename_sort_distr_subst.
     all: rewrite <- ?parameterize_term_subst, <- ?parameterize_sort_subst.
 
    Idea: rename via V -> V' renaming, using a subset type

    all: rewrite ?parameterize_term_subst, ?parameterize_sort_subst.
    TODO: how to rename? generalize mutual inductive to include list of reserved names?
      - relies on V being infinite
    eapply eq_sort_subst; cycle 1; eauto. }
  {
    TODO: what to do about ctxs in eq_sort_subst? alpha-rename? cut elim?
    alpha:                                                          
    pair of lemmas for renaming a ctx
  }
  constructor. eauto].
    eauto.
    rewrite parameterize_sort_subst; eauto.
      TODO: commute w/ subst
Qed.
     *)


End WithVar.

From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC.

(*Notation parameterize_lang p_name p_sort l_ext := (named_map (parameterize_rule p_name p_sort (map fst l_ext))).*)
Compute (parameterize_lang' "D" {{s #"ty_env"}}
           (value_subst)  []   ).
TODO: adding to whitelist isn't working
TODO: whitelisting future rules is awkward
Compute (insert_parameter "D" {{s #"ty_env"}} [] [("G" ,{{s #"env"}})]).
           (snd(     [s|"G" : #"env", "G'" : #"env"
           -----------------------------------------------
           #"sub" "G" "G'" srt
             ]%rule))).
idea: pass sublist of names
Q: take the closure before/manually or in parameterization?                                 
                      
TODO: D still always at the front
        TODO: emp incorrectly given D


Require Import Pyrosome.Elab.Elab.
Require Import Pyrosome.Tools.Matches.
(*TODO: use elab_lang notation?*)
Goal
  let l := (parameterize_lang "D" {{s #"ty_env"}} value_subst
              ++ [("ty_env",sort_rule [] [])]) in
  (elab_lang_ext [] (hide_lang_implicits [] l) l
              ).
Proof. auto_elab Qed.
#[export] Hint Resolve value_subst_wf : elab_pfs.

*)
