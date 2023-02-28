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

  
  (*TODO: should be option?*)
  Fixpoint idx_of {A} `{Eqb A} (a:A) l : nat :=
    match l with
    | [] => 0 (*should never happen, but out of bounds if it does*)
    | a'::l =>
        if eqb a a' then 0 else S (idx_of a l)
    end.

  Section WithParameter.

    (*TODO: how to handle p_name freshness?
      idea: non-identity injective endofunction
      - skip p_name in cod
      - preserve lang vars (w/out proof they are in the lang)
     *)
    Context (p_name : V)
      (p_sort : sort).


    (*c idx * is_explicit*)
    Definition param_spec := named_list (nat * bool).

    

    Definition get_args (r : rule) :=
      match r with
        sort_rule _ args
      | term_rule _ args _ => args 
      | sort_eq_rule c _ _ 
      | term_eq_rule c _ _ _ => map fst c
      end.

    Section PairMap.
      Context {A1 A2 B1 B2}
        (f : A1 -> A2)
        (g : B1 -> B2).
    (* TODO: move to utils*)
      Definition pairmap p := (f (fst p), g (snd p)).
    End PairMap.

    Fixpoint get_rule_indices n args (c : ctx) :=
      match n, args, c with
      | S n', x'::args', (xc,_)::c' =>
          if eqb x' xc
          then pairmap S S (get_rule_indices n' args' c')
          else pairmap S id (get_rule_indices n' args c')
      | _, _, _ => (0,0)
      end.
    
    Definition elab_param_rule r args :=
      let args' := get_args r in
      let c := get_ctx r in
      get_rule_indices args args' c.


      Section WithInjection.
        Context
          (V' : Type)
          (* assume a renaming where p_name isn't in the codomain *)
          (f : V' -> V)
            (*TODO: make Injective a typeclass?*)
            {f_inj : Injective f}
            {p_name_fresh : forall x, f x <> p_name}.

        (* the context indices of the rules
           that have been parameterized so far *)
        (*TODO: also record the name here?,
          can gen a fresh one when processing rule*)
        Context (parameterize_list : param_spec).

        (*TODO: move to List.v*)
        Definition insert {A} n (a : A) l :=
          (firstn n l) ++ a :: (skipn n l).
    
    Fixpoint parameterize_term (e : term) : term :=
      match e with
      | var x => var x
      | con n s =>
          let s' := map parameterize_term s in
          con n
            match named_list_lookup_err parameterize_list n with
            | None => s'
            | Some n => insert (fst n) (var p_name) s'
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
            | Some n => insert (fst n) (var p_name) s'
            end
      end.
    
    (*TODO: double-check when delta should be added.
          E.G. sort w/ parametric arg must be parameterized
          simple sort should not
          Should be like above, insert on first use
     *)

    (*
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
      end.*)
    
    Definition parameterize_ctx (mn : option (_*bool)) c :=
      let c' := named_map parameterize_sort c in
        match mn with
        | Some n => insert (fst n) (p_name, p_sort) c'
        | None => c'
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

    Fixpoint parameterize_args' n (c : ctx) args :=
      match n, c, args with
      | 0, _, _ => p_name::args
      | S n, (x,_)::c, [] =>
          parameterize_args' n c []
      | S n, (x,_)::c, x'::args' =>
          if eqb x x'
          then x'::parameterize_args' n c args'
          else parameterize_args' n c args
      (* should never hit this case *)
      | S _, [] , _ => args
      end.

    Definition parameterize_args (mn : option (_*bool)) :=
      match mn with
      | Some n => if (snd n) then parameterize_args' (fst n) else fun _ => id
      | None => fun _ => id
      end.

    Definition parameterize_rule '(n,r) : rule :=
      let mn := named_list_lookup_err parameterize_list  n in
      match r with
      | sort_rule c args =>
          (*TODO: making p implicit in terms but not args is heuristic.
                Give the user more control.
                TODO: make sure p goes at the right places
           *)
          sort_rule (parameterize_ctx mn c)
            (parameterize_args mn c args)
      | term_rule c args t =>
          term_rule (parameterize_ctx mn c) 
            (parameterize_args mn c args)
            (parameterize_sort t)
      | sort_eq_rule c t1 t2 =>
          sort_eq_rule (parameterize_ctx mn c)
            (parameterize_sort t1)
            (parameterize_sort t2)
      | term_eq_rule c e1 e2 t =>
          term_eq_rule (parameterize_ctx mn c)
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

         
  Context (p_name : V)
    (p_sort : sort).

  Definition parameterize_lang (pl : param_spec) : lang -> lang :=
    map (fun p => (fst p, parameterize_rule p_name p_sort pl p)).

  
    (*args idx*)
  Definition param_generator := named_list (option nat).

  Fixpoint calc_param_pos ps (c : ctx) : option nat :=
    match c with
    | [] => None
    | (_,t)::c =>
        match calc_param_pos ps c with
        | Some n => Some (S n)
        | None =>
            if eqb t (parameterize_sort p_name ps t)
            then None
            else Some 1
        end
    end.

  Fixpoint arg_n_to_ctx_n n args (c : ctx) :=
    match n, args, c with
    | 0, _, _ => 0
    | S n', x::args', (xc,_)::c' =>
        S (if eqb x xc
           then arg_n_to_ctx_n n' args' c'
           else arg_n_to_ctx_n n args c')
    (*should never happen*)
    | _, _, _ => 0
    end.

  Definition no_param_needed (ps : param_spec) r : bool :=
    match r with
    | sort_rule _ _ => true
    | term_rule _ _ t => eqb t (parameterize_sort p_name ps t)
    | sort_eq_rule c t1 t2 =>
        andb (eqb t1 (parameterize_sort p_name ps t1))
         (eqb t2 (parameterize_sort p_name ps t2))
    | term_eq_rule c e1 e2 t =>
        andb (eqb e1 (parameterize_term p_name ps e1))
        (andb (eqb e2 (parameterize_term p_name ps e2))
         (eqb t (parameterize_sort p_name ps t)))
    end.
      
  
  Fixpoint elab_param (l : lang) (pa : param_generator) : param_spec :=
      match l with
      | [] => []
      | (x,r)::l =>
          let ps := elab_param l pa in
          let c := get_ctx r in
          let args := get_args r in
          match named_list_lookup_err pa x with
          | Some (Some n) => (x,(arg_n_to_ctx_n n args c, true))::ps
          | Some None =>
              match calc_param_pos ps c with
              | Some n => (x,(n, false))::ps
              (*TODO: check this case*)
              | None => (x,(0,false))::ps
              end
          | None =>
              match calc_param_pos ps c with
              | Some n => (x,(n, false))::ps
              | None =>
                  (* Account for cases where ctx doesn't need param
                     but sort or terms do
                     TODO: broken; debug & fix
                   *)
                  if no_param_needed ps r
                  then ps
                  else (x,(0, false))::ps
              end
          end
      end.
(*

    
    Definition parameterize_rule_if_in_list '(n,r) :=
      if inb n (map fst parameterize_list)
    
    Fixpoint parameterize_lang l :=
      match l with
      | [] => []
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

    Fixpoint auto_param_ctx (s : param_spec) (c : ctx) :=
      
    Fixpoint auto_param_ctx (s : param_spec) (c : ctx) :=
*)
(*
    Fixpoint elab_param_spec l (g : param_generator) : param_spec :=
      match l, g with
      | (n,r)::l', (n', args)::g' =>
          if eqb n n'
           then (n, elab_param_rule r args):: (elab_param_spec l' g')
          else
            let s := (elab_param_spec l' g) in
            
            algorithm:
          if r needs to be parameterized (should we just assume this? sufficient, but less convenient), determine how
            (elab_param_spec l' g)            
      | _, _ => []
      end.
*)
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



From Pyrosome Require Import Tools.Matches Elab.Elab.

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


(*TODO: careful; parameterize doesn't check freshness*)
Definition elt_cartesian_rename (n : string) : string :=
  match n with
  | "unit" => "elt"
  | "u" => "v"
  | _ => n
  end.


Let elt_cartesian_in := (rename_lang elt_cartesian_rename
            (unit_cartesian ++ unit_action ++ obj_consumer)).
Let elt_cartesian_ps := (elab_param "A" elt_cartesian_in
                           [("ext", Some 0); ("elt",Some 0)]).


(* TODO: beyond this point there are some category-theoretic
   names that could be used but which I would get wrong in choosing.
 *)
Definition typed_consumer : lang _ :=
  Eval compute in
  (parameterize_lang "A" {{s #"ty"}}
     elt_cartesian_ps
     (rename_lang elt_cartesian_rename (obj_consumer))).

  
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
                       ++[("ty",sort_rule [] [])]++cat)
                    typed_consumer.

Definition elt_action_def :=
  Eval compute in Rule.hide_lang_implicits
                    (elt_action++typed_consumer
                       ++[("ty",sort_rule [] [])]++cat)
                    elt_action.

Definition elt_cartesian_def :=
  Eval compute in Rule.hide_lang_implicits
                    (elt_cartesian++elt_action++typed_consumer
                       ++[("ty",sort_rule [] [])]++cat)
                    elt_cartesian.

Lemma simple_sort_wf {V} `{Eqb V} (n : V)
  : wf_lang_ext [] [(n,sort_rule [] [])].
Proof.
  constructor;
    basic_core_crush.
Qed.
#[export] Hint Resolve simple_sort_wf : elab_pfs.

Lemma typed_consumer_wf
  : elab_lang_ext ([("ty",sort_rule [] [])]++cat)
      typed_consumer_def typed_consumer.
Proof. auto_elab. Qed.
#[export] Hint Resolve typed_consumer_wf : elab_pfs.

Lemma elt_action_wf
  : elab_lang_ext (typed_consumer++[("ty",sort_rule [] [])]++cat)
      elt_action_def elt_action.
Proof. auto_elab. Qed.
#[export] Hint Resolve elt_action_wf : elab_pfs.

Lemma elt_cartesian_wf
  : elab_lang_ext (elt_action++typed_consumer++[("ty",sort_rule [] [])]++cat)
      elt_cartesian_def elt_cartesian.
Proof. auto_elab. Qed.
#[export] Hint Resolve elt_cartesian_wf : elab_pfs.


Require Import Pyrosome.Theory.Renaming Ascii.

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


Lemma ty_subst_wf
  : wf_lang ty_subst_lang.
Proof.
apply Renaming.rename_lang_mono.
2:now prove_from_known_elabs.
(*TODO: injectivity machinery*)
Admitted.
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

Lemma val_subst_wf
  : wf_lang_ext [("ty",sort_rule [] [])] val_subst.
Proof.
  (*TODO: generalize to lang_ext
eapply Renaming.rename_lang_mono.
2:now prove_from_known_elabs.
(*TODO: injectivity machinery*)*)
Admitted.
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

Lemma exp_subst_base_wf
  : wf_lang_ext (val_subst++[("ty",sort_rule [] [])]) exp_subst_base.
Proof.
  (*TODO: generalize to lang_ext
eapply Renaming.rename_lang_mono.
2:now prove_from_known_elabs.
(*TODO: injectivity machinery*)*)
Admitted.
#[export] Hint Resolve exp_subst_base_wf : elab_pfs.

Require Import Pyrosome.Lang.SimpleVSubst.

Definition exp_ret_def : lang :=
  {[l/subst
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
    ] ]}.



Derive exp_ret
  SuchThat (elab_lang_ext (exp_subst_base++val_subst++[("ty",sort_rule [] [])])
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
  Eval compute in
    let ps := (elab_param "D" (exp_ret ++ exp_subst_base
                                 ++ val_subst++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2);
                ("exp",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_ret ++ exp_subst_base ++ val_subst).


Definition exp_and_val_parameterized_def :=
  Eval compute in Rule.hide_lang_implicits
                    (exp_and_val_parameterized
                       ++ty_subst_lang)
                    exp_and_val_parameterized.

Lemma exp_and_val_parameterized_wf
  : elab_lang_ext ty_subst_lang
      exp_and_val_parameterized_def
      exp_and_val_parameterized.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_and_val_parameterized_wf : elab_pfs.

Compute ty_subst_lang.

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


(*TODO: add & generate coherence rules*)
Definition exp_ty_subst_def : lang :=
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
       ]
      ]}.


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


Derive exp_ty_subst
  SuchThat (elab_lang_ext (env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
      exp_ty_subst_def
      exp_ty_subst)
       As exp_ty_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ty_subst_wf : elab_pfs. 

Definition poly_def : lang :=
  {[l/subst
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
  ]
  ]}.


Derive poly
  SuchThat (elab_lang_ext (exp_ty_subst
                             ++env_ty_subst
                             ++exp_and_val_parameterized
                             ++ty_subst_lang)
              poly_def poly)
       As poly_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve exp_ty_subst_wf : elab_pfs. 

Steps:
  -prove one more base lang wf
  -prove poly def wf
  -autogenerate subst coherence rules for all substs
  -parameterize compilers (better elab?)
  -re-prove (parameterized) compilers
  -fix up combined thm
  -add to paper
  -discuss DimSum in related work

Definition exptysubst_rename :=
    (fun n =>
       match n with
       | "obj" => "ty_env"
       | "arr" => "ty_subst"
       | "unit" => "ty"
       | "v" =>
       | "A" =>
       | "g"
       | "f"
       | "h" => n 
       | String "G"%char s => String "D" s
       (*needed for injectivity*)
       | "env" => "_env"
       | "subst" => "_subst"
       (**)
       | _ => ("ty_"++ n)%string
       end).
Definition ty_action :=
  Eval compute in
  let ps := (elab_param "D" (exp_subst ++ val_subst'++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2)]) in
  (parameterize_lang "D" {{s #"ty_env"}}
     ???
     (rename_lang exptysubst_rename (elt_action))).

Compute  exp_subst_base.
TODO: how best to add more substs to existing sorts? e.g. exp_ty_subst
  want ext_subst_base w/out exp sort built-in
  Add wrinkle: extra arguments/parameters
  Easiest to define a template for 3-parameter substs?

Lemma exp_subst_wf
  : wf_lang_ext (val_subst++[("ty",sort_rule [] [])]) val_subst_lang.
Proof.
  (*TODO: generalize to lang_ext
eapply Renaming.rename_lang_mono.
2:now prove_from_known_elabs.
(*TODO: injectivity machinery*)*)
Admitted.

Definition exp_core_def : lang _ :=
      [s| "G" : #"env", "A" : #"ty"
          -----------------------------------------------
          #"exp" "G" "A" srt
      ];
  
  [:| "G" : #"env", "A" : #"ty", "v" : #"val" "G" "A"
       -----------------------------------------------
       #"ret" "v" : #"exp" "G" "A"
  ];

TODO: need an arrow groupoid action
TODO: re-separate elt_cartesian, rename non-sub portion for exps?


Exp next


Definition val_subst' :=
  Eval compute in
  let ps := (elab_param "A" pre_val_subst
               [("ext", Some 0); ("val",Some 0)]) in
  (parameterize_lang "A" {{s #"ty"}}
     ps pre_val_subst).



(*TODO: prove wf (need unelab_lang)*)

Definition val_subst_ty_param :=
  Eval compute in
  let ps := (elab_param "D" (exp_subst ++ val_subst'++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_subst ++val_subst').

Derive obj_subst
       SuchThat (elab_lang_ext [] obj_subst_def obj_subst)
       As obj_subst_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve obj_subst_wf : elab_pfs.

Definition ty_subst :=
  Eval compute in
  (rename_lang
    (fun s =>
       match s with
       | "obj" => "ty"
       | String "G"%char s => String "D"%char s
       | String "A"%char s => String "A"%char s
       | "f" =>"f"
       | "g" =>"g"
       | "h" =>"h"
       | s => ("ty_" ++ s)%string
       end)
    obj_subst).


Definition pre_val_subst :=
  Eval compute in
  (rename_lang
    (fun s =>
       match s with
       | "obj" => "val"
       | "env" => "env"
       | "sub" => "sub"
       | "ext" => "ext"
       | "cmp" => "cmp"
       | "snoc" => "snoc"
       | "wkn" => "wkn"
       | "hd" => "hd"
       | "emp" => "emp"
       | "id" => "id"
       | String "G"%char s => String "G"%char s
       | String "A"%char s => String "v"%char s
       | String "g"%char s => String "g"%char s
       | String "f"%char s => String "f"%char s
       | String "h"%char s => String "h"%char s
       | s => ("val_" ++ s)%string
       end)
    obj_subst).

(*TODO: how to generate exp?
  Need to separate 2 things: subst calc for things in subst
  and subst calc extension to other input
 *)

Require Import Pyrosome.Lang.SimpleVSubst.


Definition val_subst' :=
  Eval compute in
  let ps := (elab_param "A" pre_val_subst
               [("ext", Some 0); ("val",Some 0)]) in
  (parameterize_lang "A" {{s #"ty"}}
     ps pre_val_subst).



(*TODO: prove wf (need unelab_lang)*)

Definition val_subst_ty_param :=
  Eval compute in
  let ps := (elab_param "D" (exp_subst ++ val_subst'++[("ty",sort_rule[][])])
               [("sub", Some 2);
                ("ty", Some 0);
                ("env", Some 0);
                ("val",Some 2)]) in
  parameterize_lang "D" {{s #"ty_env"}}
    ps (exp_subst ++val_subst').

Definition poly_val_subst :=
  val_subst_ty_param ++ ty_subst.

Definition poly_subst_def :=
  Eval compute in Rule.hide_lang_implicits poly_val_subst poly_val_subst.

Lemma poly_subst_wf : elab_lang_ext [] poly_subst_def poly_val_subst.
Proof.
  auto_elab. Qed.
#[export] Hint Resolve poly_subst_wf : elab_pfs.

Compute (map fst (poly_subst_def)).


Section gen_ty_subst_rules.

  
(*TODO: duplicated*)
Definition ty_under s :=
  {{e #"ty_snoc" (#"ty_cmp" #"ty_wkn" {s}) #"ty_hd"}}.

Definition get_subst_constr s :=
  match s with
  | "exp" => Some "exp_ty_subst"
  | "val" => Some "val_ty_subst"
  | "env" => Some "env_ty_subst"
  | "sub" => Some "sub_ty_subst"
  | _ => None
  end.

Section GenRHSSubterms.
  Context (G : string)
          (g : string).

  (*TODO: careful! _ in patterns does bad things (treated as a var)
   document &/or fix *)
  Fixpoint gen_arg_subst s :=
    match s with
    | {{e#"ty_emp"}} => {{e#"ty_forget"}}
    | var G' => if G =? G' then var g else {{e#"ERR1"}}
    | {{e#"ty_ext" {s'} }} => under (gen_arg_subst s')
    | _ => {{e#"ERR2" {s} }}
    end.
  
  Fixpoint gen_rhs_subterms c args {struct c} :=
    match c, args with
    | (n1,t)::c', n2::args' =>
      if n1 =? n2
      then
        match t with
        | scon name [G']
        | scon name [_;G'] =>
          match get_subst_constr name with
          | Some subst_constr =>
            let s := gen_arg_subst G' in
            let e := {{e #subst_constr {s} n1 }} in
            e::(gen_rhs_subterms c' args')
          | _ => (var n1)::(gen_rhs_subterms c' args')
          end
        | _ => (var n1)::(gen_rhs_subterms c' args')
        end
      else gen_rhs_subterms c' args
    | _, _ => []
    end.
End GenRHSSubterms.

Definition substable_constr name c args t : option lang :=
  match t with
  (*TODO: assumes arbitrary G below the line. Is that the behavior I want or can I generalize?*)
  | scon s [A; var G] =>
    match get_subst_constr s with
    | Some subst_constr =>      
      let constr_rule := term_rule c args t in
      let G' := choose_fresh "D'" c in
      let g := choose_fresh "d" c in
      let c' := (g,{{s#"ty_sub" G' G }})
                  ::(G', {{s#"ty_env"}})
                  ::c in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr g {blank_term} }} in
      let rhs := con name (gen_rhs_subterms G g c args) in
      let t' := scon s [A; var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-ty_subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  (*TODO: duplicated work for blocks since there is no A*)
  | scon s [var G] =>
    match get_subst_constr s with
    | Some subst_constr =>      
      let constr_rule := term_rule c args t in
      let G' := choose_fresh "D'" c in
      let g := choose_fresh "d" c in
      let c' := (g,{{s#"ty_sub" G' G }})
                  ::(G', {{s#"ty_env"}})
                  ::c in
      let blank_term := con name (map var args) in
      let lhs := {{e #subst_constr g {blank_term} }} in
      let rhs := con name (gen_rhs_subterms G g c args) in
      let t' := scon s [var G'] in
      let subst_rule :=
          term_eq_rule c' lhs rhs t' in
      Some [(append name "-ty_subst",subst_rule);(name, constr_rule)]
    | None => None
    end
  | _ => None
  end.

Definition sc '(n,r) :=
  match r with
  |term_rule c args t =>
   match substable_constr n c args t with
   | Some l => l
   | None => [(n,r)]
   end
  | r => [(n,r)]
  end.



Definition poly_subst'_def :=
  Eval compute in
    List.flat_map sc
      (Rule.hide_lang_implicits
      poly_val_subst
      (val_subst_ty_param)).

TODO: generated subst rules don't traverse different sorts? e.g. ret

Lemma poly_subst_wf : elab_lang_ext [] poly_subst_def poly_val_subst.
Proof.
  auto_elab. Qed.
#[export] Hint Resolve poly_subst_wf : elab_pfs.

Compute (map fst (poly_subst_def)).



(*TODO: generate fully-typed rules *)
List.flat_map sc 

(*TODO: autogenerate ty_subst rules that apply to all existing rules*)

(*usage pattern: only bring 1 into (local) scope as an instance at a time*)
Class subst_renaming V : Type :=
  {
    env : V;
    sub : V;
    id : V;
    cmp : V;
    obj : V;
    subst : V;
    emp : V;
    forget : V;
    ext : V;
    snoc : V;
    wkn : V;
    hd : V;
  }.

Definition renaming_of_fn { B : Type} (f : string -> B) : subst_renaming B :=
  {|
    env := f "env";
    sub := f "sub";
    id := f "id";
    cmp := f "cmp";
    obj := f "obj";
    subst := f "subst";
    emp := f "emp";
    forget := f "forget";
    ext := f "ext";
    snoc := f "snoc";
    wkn := f "wkn";
    hd := f "hd";
  |}.

Section gen_subst_rules.
  
