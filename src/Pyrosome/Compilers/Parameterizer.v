Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Infinite Monad.
From Pyrosome Require Import Theory.Core Theory.Renaming
  Compilers.SemanticsPreservingDef Compilers.CompilerDefs.
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

    Definition parameterize_subst (mn : option (_*bool)) s :=
      let s' := named_map parameterize_term s in
        match mn with
        | Some n => insert (fst n) (p_name, var p_name) s'
        | None => s'
        end.
    
    Definition parameterize_args (mn : option (_*bool)) s :=
      let s' := map parameterize_term s in
        match mn with
        | Some n => insert (fst n) (var p_name) s'
        | None => s'
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

    Definition parameterize_elab_args (mn : option (_*bool)) :=
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
            (parameterize_elab_args mn c args)
      | term_rule c args t =>
          term_rule (parameterize_ctx mn c) 
            (parameterize_elab_args mn c args)
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

    Section Compilers.
      Context (src_parameterize_list : param_spec).
    (*TODO: also need to parameterize the source language*)
      Definition parameterize_ccase '(n,c) : compiler_case V :=
        let p_args args :=
          match named_list_lookup_err src_parameterize_list n with
          | None => args
          | Some n => insert (fst n) p_name args
          end in
        match c with
        | sort_case args t =>
            sort_case (p_args args) (parameterize_sort t)
        | term_case args e =>
            term_case (p_args args) (parameterize_term e)
        end.

      
      Definition parameterize_compiler : compiler _ -> compiler _ :=
        map (fun p => (fst p, parameterize_ccase p)).

    End Compilers.
    
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


    Lemma lookup_app_r n s1 s2
      : fresh n s1 -> subst_lookup (s1++s2) n = subst_lookup s2 n.
    Proof.
      induction s1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Lemma named_list_lookup_app_r A n s1 s2 (v : A)
      : fresh n s1 -> named_list_lookup v (s1++s2) n = named_list_lookup v s2 n.
    Proof.
      induction s1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    (*TODO: move to Utils*)
    Lemma fresh_firstn A n i (l : named_list A)
      : fresh n l -> fresh n (firstn i l).
    Proof.
      revert l; induction i;
        destruct l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve fresh_firstn : utils.
    
    (*TODO: move to Utils*)
    Lemma fresh_skipn A n i (l : named_list A)
      : fresh n l -> fresh n (skipn i l).
    Proof.
      revert l; induction i;
        destruct l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve fresh_skipn : utils.
    
    Lemma lookup_insert i (s : subst) v
      : fresh p_name s ->
        subst_lookup (insert i (p_name, v) s) p_name = v.
    Proof.
      unfold insert.
      intros.
      rewrite lookup_app_r by basic_utils_crush.
      cbn.
      basic_utils_crush.
    Qed.

    (* TODO: move to Utils *)
    Lemma fresh_named_map A B n (g : A -> B) s
      : fresh n s <-> fresh n (named_map g s).
    Proof.
      induction s;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite <- fresh_named_map : utils.
    Hint Resolve -> fresh_named_map : utils.
    
    Lemma subst_lookup_fresh n s
      : fresh n s ->
        subst_lookup s n = var n.
    Proof.
      induction s;
        basic_goal_prep;
        basic_term_crush.
    Qed.
    
    Lemma subst_lookup_p_name mn s
      : fresh p_name s ->
        subst_lookup (parameterize_subst mn s) p_name = var p_name.
    Proof.
      unfold parameterize_subst.
      destruct mn.
      2:{
        induction s;
        basic_goal_prep;
        basic_term_crush.
      }
      {
        intros.
        apply lookup_insert; basic_utils_crush.
      }
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
    
    Lemma lookup_app_l n s1 s2
      : fresh n s2 -> subst_lookup (s1++s2) n = subst_lookup s1 n.
    Proof.
      induction s1;
        basic_goal_prep;
        basic_utils_crush.
      { eapply subst_lookup_fresh; eauto. }
      { eqb_case n v; eauto. }
    Qed.

    (* TODO: move to coqutil *)
    Lemma In_skipn_to_In
      : forall (A : Type) (n : nat) (a : A) (l : list A), In a (skipn n l) -> In a l.
    Proof.
      induction n; destruct l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve In_skipn_to_In : utils.
    
    Hint Resolve In_firstn_to_In : utils.


    Lemma named_list_lookup_default A d (s : named_list A) n
      : fresh n s -> named_list_lookup d s n = d.
    Proof.
      induction s;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    (* TODO: move to term, replacing (?) cons version *)
    Lemma subst_ext (a : term) args s s'
      : (forall x, In x args -> subst_lookup s x = subst_lookup s' x) ->
        well_scoped args a -> a [/s/] = a [/s' /].
    Proof.
      induction a;
        basic_goal_prep;
        basic_utils_crush.
      f_equal.
      revert dependent l.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma lookup_insert_neq i s v x n
      : fresh n s -> x <> n -> subst_lookup (insert i (n, v) s) x = subst_lookup s x.
    Proof.
      unfold insert.
      unfold subst_lookup.
      intros.
      assert (fresh n (firstn i s)) by basic_utils_crush.
      assert (fresh n (skipn i s)) by basic_utils_crush.
      revert H1 H2.
      rewrite <- firstn_skipn with (l:=s) (n:=i) at 5.
      generalize (skipn i s).
      generalize (firstn i s).
      revert H0.
      clear s H.
      induction l;
        basic_goal_prep;
        basic_utils_crush.        
      eqb_case x v0; eauto.
    Qed.

    Lemma strengthen_subst_insert
      s n v e (a : term)
      : fresh v s ->
        well_scoped (map fst s) a -> a [/insert n (v,e) s/] = a [/s /].
    Proof.
      intros; eapply subst_ext; eauto; intros.
      eapply lookup_insert_neq; eauto.
      basic_utils_crush.
    Qed.

    
    Lemma lookup_insert' i s x n
      : fresh n s -> subst_lookup (insert i (n, var n) s) x = subst_lookup s x.
    Proof.
      unfold insert.
      unfold subst_lookup.
      intros.
      assert (fresh n (firstn i s)) by basic_utils_crush.
      assert (fresh n (skipn i s)) by basic_utils_crush.
      revert H0 H1.
      rewrite <- firstn_skipn with (l:=s) (n:=i) at 5.
      generalize (skipn i s).
      generalize (firstn i s).
      clear s H.
      induction l;
        basic_goal_prep;
        basic_utils_crush.        
      {
        eqb_case x n; eauto.
        rewrite named_list_lookup_default; eauto.
      }
      {
        eqb_case x v; eauto.
      }
    Qed.
    
    Lemma strengthen_subst_insert'
      : forall (s : named_list term) (n : nat) (v : V) (a : term),
        fresh v s -> a [/insert n (v, var v) s /] = a [/s /].
    Proof.
      induction a; basic_goal_prep;
        basic_term_crush.
      { eapply lookup_insert'; eauto. }
      {
        revert H; induction l;
          basic_goal_prep;
          basic_term_crush.
      }
    Qed.

    
    Lemma strengthen_list_subst_insert'
      : forall (s : named_list term) (n : nat) (v : V) (a : list term),
        fresh v s -> a [/insert n (v, var v) s /] = a [/s /].
    Proof.
      induction a; basic_goal_prep;
        basic_term_crush.
      apply strengthen_subst_insert'; eauto.
    Qed.

    (*TODO move to utils*)    
    Lemma map_fst_named_map A B (g : A -> B) s
      : (map fst (named_map g s)) = map fst s.
    Proof.
      induction s; basic_goal_prep; basic_utils_crush.
    Qed.
    Hint Rewrite map_fst_named_map  : utils.

    Lemma parameterize_term_subst' e s
      : parameterize_term (rename f e) [/rename_subst f s /] =
          (parameterize_term (rename f e)) [/named_map parameterize_term (rename_subst f s) /].
    Proof.
      induction e;
          basic_goal_prep;
          basic_term_crush.
        {
          erewrite parameterize_subst_lookup; eauto.
          rewrite lookup_app_l;
            basic_goal_prep; basic_utils_crush.
        }
        {
          case_match; basic_goal_prep.
          {
            unfold insert.
            rewrite map_app. (*TODO: add to utils rw?*)
            rewrite !firstn_map, !skipn_map.
            rewrite map_cons.
            rewrite !map_map.
            f_equal.
            {
              apply map_ext_in; intros; eauto.
              eapply in_all with (a:=a) in H; basic_utils_crush.
            }
            f_equal.
            2:{
              apply map_ext_in; intros; eauto.
              eapply in_all with (a:=a) in H; basic_utils_crush.
            }
            {
              cbn.
              unfold term_subst_lookup.
              rewrite named_list_lookup_default; auto.
              basic_utils_crush.
              apply p_name_fresh_in_subst.
            }
          }
          {
            rewrite !map_map.
            apply map_ext_in; intros; eauto.
            eapply in_all with (a:=a) in H; basic_utils_crush.
          }
        }
        Unshelve.
        exact default. (*TODO: where is this coming from?*)
    Qed.

                                               
    Lemma parameterize_term_subst mn e s
      : parameterize_term (rename f e) [/rename_subst f s /]
        = (parameterize_term (rename f e)) [/parameterize_subst mn (rename_subst f s) /].
    Proof.
      unfold parameterize_subst;
        destruct mn;
        rewrite ?strengthen_subst_insert'; eauto using parameterize_term_subst'.
      {
        unfold rename_subst.
        unfold fresh.
        basic_term_crush.
        rewrite map_map in *; cbn in *.
        enough (all (fun x => ~ x = p_name) (map (fun x : V' * Term.term V' => f (fst x)) s)).
        {
          eapply in_all in H0; eauto.
        }
        revert p_name_fresh; clear; induction s; basic_goal_prep; basic_utils_crush.
      }
    Qed.

    
    Lemma map_parameterize_term_subst e s
      : map parameterize_term (map (rename f) e) [/rename_subst f s /]
        = (map parameterize_term (map (rename f) e))
            [/named_map parameterize_term (rename_subst f s)/].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
     
      {
        cbn.
        fold_Substable.
        f_equal; auto.
        erewrite !parameterize_term_subst; eauto.
        change (named_map parameterize_term (rename_subst f s))
          with (parameterize_subst None (rename_subst f s)).
        eauto.
      }
    Qed.

    
    Lemma subst_app (l1 l2 : list term) s
      : (l1 ++ l2)[/s/] = l1[/s/] ++ l2[/s/].
    Proof.
      induction l1;
        basic_goal_prep;
        basic_term_crush.
    Qed.
    Hint Rewrite subst_app : term.

    Lemma firstn_subst n (e : list term) s
      : firstn n e [/s/]
        = (firstn n e) [/ s /].
    Proof.
      revert e; induction n; destruct e;
        basic_goal_prep;
        basic_term_crush.
    Qed.
    Hint Rewrite <- firstn_subst : term.
    
    Lemma skipn_subst n (e : list term) s
      : skipn n e [/s/]
        = (skipn n e) [/ s /].
    Proof.
      revert e; induction n; destruct e;
        basic_goal_prep;
        basic_term_crush.
    Qed.
    Hint Rewrite <- skipn_subst : term.

    Lemma subst_cons (a : term) l s : (a::l)[/s/] = a[/s/] :: l[/s/].
    Proof. reflexivity. Qed.
    Hint Rewrite subst_cons : term.
      
    Lemma insert_p_name_subst n e s
      : {{e p_name }}[/s/] = {{e p_name }} ->
        insert n {{e p_name }} e [/s/]
        = (insert n {{e p_name }} e) [/ s /].
    Proof.
      intros.
      unfold insert;
        basic_goal_prep;
        basic_term_crush.
    Qed.          

    Hint Immediate p_name_fresh_in_subst : term.
      
    (* TODO: same mn or different? *)
    Lemma parameterize_args_subst mn e s
      : parameterize_args mn (map (rename f) e) [/rename_subst f s /]
        = (parameterize_args mn (map (rename f) e)) [/parameterize_subst mn (rename_subst f s) /].
    Proof.
      unfold parameterize_args, parameterize_subst;
      destruct mn.
      2: apply map_parameterize_term_subst.
      destruct p.
      cbn [fst].
      rewrite strengthen_list_subst_insert';
        basic_term_crush.
      rewrite <- insert_p_name_subst.
      2:{
        cbn; basic_term_crush.
        rewrite subst_lookup_fresh; eauto.
        basic_term_crush.
      }
      f_equal.
      apply map_parameterize_term_subst.
    Qed.
    
    Lemma parameterize_sort_subst mn e s
      : parameterize_sort (rename_sort f e) [/rename_subst f s /]
        = (parameterize_sort (rename_sort f e)) [/parameterize_subst mn (rename_subst f s) /].
    Proof.
      destruct mn; cbn.
      2:{
        destruct e;
        basic_goal_prep;
        basic_term_crush.
        case_match; basic_utils_crush.
        2: apply map_parameterize_term_subst.
        cbn [fst].
        rewrite <- insert_p_name_subst.
        {
          rewrite map_parameterize_term_subst; eauto.
        }
        {
          cbn.
          basic_term_crush.
          apply subst_lookup_fresh.
          basic_term_crush.
        }
      }
      {
        destruct e;
        basic_goal_prep;
        basic_term_crush.
        case_match; basic_utils_crush.
        all: cbn [fst].
        1:rewrite <- insert_p_name_subst.
        2:{
          cbn.
          basic_term_crush.
          apply lookup_insert.
          basic_term_crush.
        }
        all:rewrite ?strengthen_list_subst_insert';
          try rewrite map_parameterize_term_subst;
          basic_term_crush.
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
      
     
      End WithInjection.
      
  End WithParameter.

         
  Context (p_name : V)
    (p_sort : sort).

  
  Section WithSpec.
    Context (pl : param_spec).

    Notation pctx := (parameterize_ctx p_name p_sort pl).
    Notation psort := (parameterize_sort p_name pl).
    Notation pterm := (parameterize_term p_name pl).
  
  Definition parameterize_lang : lang -> lang :=
    map (fun p => (fst p, parameterize_rule p_name p_sort pl p)).

  (*TODO: use cut-free induction here? yes or no?
    Probably no since I acutally need all the judgments.
   *)

  Notation semantics_preserving l :=
    (semantics_preserving
       (V_Eqb := V_Eqb)
       (tgt_Model := core_model (parameterize_lang l))
       (parameterize_term p_name pl)
       (parameterize_sort p_name pl)
       (parameterize_ctx p_name p_sort pl _(*TODO:what goes here again?*))
       (parameterize_args p_name pl _(*TODO:what goes here again?*))
       (parameterize_subst p_name pl _(*TODO:what goes here again?*))
       l).

  (* TODO: should really generalize semantics_preserving, which should take a fn as input
     rather than a compiler.
   *)
  Lemma parameterize_term l c t e1 e2 is_param
    : eq_term l c t e1 e2 ->
      wf_ctx l c ->
      eq_term (parameterize_lang l)
        (pctx is_param c) (psort t)
        (pterm e1) (pterm e2).
  Proof.
    induction 1. (*TODO: use cut_ind*)
    {
      intros.
      (*TODO: commute w/ substitution...*)
  Abort.
    

  End WithSpec.
  
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

  (*TODO: propositional characterization of a valid param_spec.
  Question: can I use a boolean validity check on param_specs? (implicit args behavior is more limited)
   *)
  
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

