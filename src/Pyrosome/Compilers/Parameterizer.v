Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Infinite Monad.
From Pyrosome Require Import Theory.Core Theory.Renaming Theory.CutFreeInd
  Tools.ConstructorsOf
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
    
    Lemma strengthen_sort_subst_insert'
      : forall (s : named_list term) (n : nat) (v : V) (a : sort),
        fresh v s -> a [/insert n (v, var v) s /] = a [/s /].
    Proof.
      induction a; basic_goal_prep;
        basic_term_crush.
      apply strengthen_list_subst_insert'; eauto.
    Qed.

    (*TODO move to utils*)    
    Lemma map_fst_named_map A B (g : A -> B) s
      : (map fst (named_map g s)) = map fst s.
    Proof.
      induction s; basic_goal_prep; basic_utils_crush.
    Qed.
    Hint Rewrite map_fst_named_map  : utils.

    (*TODO: move to Utils*)
    Lemma all_firstn {A} P n (l : list A)
      :  all P l -> all P (firstn n l).
    Proof.
      revert l; induction n;
        destruct l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    
    Lemma all_skipn {A} P n (l : list A)
      :  all P l -> all P (skipn n l).
    Proof.
      revert l; induction n;
        destruct l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma parameterize_term_subst' e s
      : fresh p_name s ->
        well_scoped (map fst s) e ->
        parameterize_term e [/ s /]
        = (parameterize_term e) [/named_map parameterize_term s /].
    Proof.
      induction e;
          basic_goal_prep;
          basic_term_crush.
        {
          erewrite parameterize_subst_lookup; basic_utils_crush.
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
              eapply H3; eauto.
              eapply in_all; basic_utils_crush.
            }
            f_equal.
            2:{
              apply map_ext_in; intros; eauto.
              eapply in_all with (a:=a) in H; basic_utils_crush.
              eapply H3; eauto.
              eapply in_all; basic_utils_crush.
            }
            {
              cbn.
              unfold term_subst_lookup.
              rewrite named_list_lookup_default; auto.
              basic_term_crush.
            }
          }
          {
            rewrite !map_map.
            apply map_ext_in; intros; eauto.
            eapply in_all with (a:=a) in H; basic_utils_crush.
            eapply H3; eauto.
            eapply in_all; basic_utils_crush.
          }
        }
        Unshelve.
        exact default. (*TODO: where is this coming from?*)
    Qed.

                                               
    Lemma parameterize_term_subst mn e s
      : fresh p_name s ->
        well_scoped (map fst s) e ->
        parameterize_term e [/ s /]
        = (parameterize_term e) [/parameterize_subst mn s /].
    Proof.
      intros.
      unfold parameterize_subst;
        destruct mn;
        rewrite ?strengthen_subst_insert'; eauto using parameterize_term_subst'.
      basic_utils_crush.
    Qed.

    
    Lemma map_parameterize_term_subst e s
      : fresh p_name s ->
        well_scoped (map fst s) e ->
        map parameterize_term e [/s /]
        = (map parameterize_term e)
            [/named_map parameterize_term s/].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
     
      {
        cbn.
        fold_Substable.
        f_equal; auto.
        erewrite !parameterize_term_subst; eauto.
        change (named_map parameterize_term s)
          with (parameterize_subst None s).
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
      : fresh p_name s ->
        well_scoped (map fst s) e ->
        parameterize_args mn e [/s /]
        = (parameterize_args mn e) [/parameterize_subst mn s /].
    Proof.
      intros.
      unfold parameterize_args, parameterize_subst;
      destruct mn.
      2: apply map_parameterize_term_subst; basic_utils_crush.
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
      apply map_parameterize_term_subst;
        basic_utils_crush.
    Qed.
    
    Lemma parameterize_sort_subst mn e s
      : fresh p_name s ->
        well_scoped (map fst s) e ->
        parameterize_sort e [/s /]
        = (parameterize_sort e) [/parameterize_subst mn s /].
    Proof.
      intros.
      destruct mn; cbn.
      2:{
        destruct e;
        basic_goal_prep;
        basic_term_crush.
        case_match; basic_utils_crush.
        2: apply map_parameterize_term_subst;
        basic_utils_crush.
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


  
  Lemma in_insert A (a a' : A) n l
    : In a (insert n a' l) <-> a = a' \/ In a l.
  Proof.
    unfold insert.
    basic_utils_crush;
      basic_goal_prep;
      intuition eauto using In_firstn_to_In, In_skipn_to_In.
    rewrite <- firstn_skipn with (n:=n) (l:=l) in H0.
    basic_utils_crush.
  Qed.
  Hint Rewrite in_insert : utils.

  
  (*TODO: move to utils*)
  Hint Rewrite skipn_nil : utils.
  Hint Rewrite firstn_nil : utils.
    
  Lemma in_parameterize_ctx n t mn c
    : In (n, t) c -> In (n, psort t) (pctx mn c).
  Proof.
    unfold parameterize_ctx.
    case_match; basic_utils_crush.
  Qed.
  #[local] Hint Resolve in_parameterize_ctx : term.

  (*TODO:move to Utils*)
  Definition Is_Some {A} (x : option A) := if x then True else False.

  (*TODO: imposes constraints on mn
  Lemma in_p_name_pctx mn c
    : In (p_name, p_sort) (pctx mn c).
  Proof.
    destruct mn; cbn.*)
 
  Notation semantics_preserving l mn :=
    (semantics_preserving
       (V_Eqb := V_Eqb)
       (tgt_Model := core_model (parameterize_lang l))
       (parameterize_term p_name pl)
       (parameterize_sort p_name pl)
       (parameterize_ctx p_name p_sort pl mn(*TODO:what goes here again?*))
       (parameterize_args p_name pl mn(*TODO:what goes here again?*))
       (parameterize_subst p_name pl mn(*TODO:what goes here again?*))
       l).

  Section __.
    Context (l : lang).
    Definition tgt_model := (core_model (parameterize_lang l)).
    Existing Instance tgt_model.

    Context (wfl : wf_lang l).
    Context (IH_l : wf_lang (parameterize_lang l)).
    Context (H_p_name_l : all (fun p => fresh p_name (get_ctx (snd p))) l).    
    
    Definition direct_dependency n n' :=
      match named_list_lookup_err l n with
      | Some r => In n' (constructors_of_rule r)
      | None => False
      end.

    
    (*TODO: move to Term.v*)    
    Definition sort_name : sort -> V := fun '(scon n _ ) => n.

    Inductive dependency : _ -> _ -> Prop :=
    (*| dep_refl n : dependency n n*)
    | dep_trans n n1 n2 : dependency n n1 -> dependency n1 n2 -> dependency n n2
    | dep_direct n n1 : direct_dependency n n1 -> dependency n n1
    | dep_eqn n c e1 e2 t : In (n, term_eq_rule c e1 e2 t) l -> dependency (sort_name t) n
    | dep_con n c args t : In (n, term_rule c args t) l -> dependency (sort_name t) n.

    Definition pl_is_ordered :=
      all (fun '(n,_) => forall n', dependency n n' ->
                                    (Is_Some (named_list_lookup_err pl n') ->
                                     Is_Some (named_list_lookup_err pl n))
                                    /\ (fresh n pl ->
                                        fresh n' pl)) l.
    
    Context (H_pl : pl_is_ordered).
    (*
    TODO: what to do about mn for c?.
    It doesn't make sense to connect it to any name.
    It can be None
    It can be some (but maybe always (0,true)?)
     *)


    
    (*TODO: move to Rule*)
    Definition is_sort_eqn (r : rule) :=
      match r with
      | sort_eq_rule _ _ _ => true
      | _ => false
      end.
    Definition no_sort_eqns : lang -> _ := forallb (fun p => negb (is_sort_eqn (snd p))).

    Context (H_no_sort_eqns : Is_true (no_sort_eqns l)).

    
    Lemma sort_name_subst t s : sort_name t [/s/] = sort_name t.
    Proof.
      destruct t; reflexivity.
    Qed.
    Hint Rewrite sort_name_subst : term.

    
    
    Lemma eq_fresh_iff_sort_fresh c' e1 e2 t name
      : In (name, term_eq_rule c' e1 e2 t) l ->
        fresh name pl <->
        fresh (sort_name t) pl.
    Proof.
      unfold pl_is_ordered in H_pl.
      intros.
      assert (dependency name (sort_name t)).
      {
        eapply dep_direct.
        unfold direct_dependency.
        case_match.
        2:{
          apply named_list_lookup_none_iff in HeqH0; eauto.
          eapply fresh_notin; eauto.
        }
        apply named_list_lookup_err_in in HeqH0.
        eapply in_all_fresh_same in HeqH0; [| basic_core_crush | clear HeqH0; eassumption].
        subst.
        destruct t; cbn.
        basic_utils_crush.
      }
      assert (dependency (sort_name t) name).
      {
        eapply dep_eqn; eauto.
      }
      
      pose proof H as H_copy.
      eapply in_all in H; eauto.
      cbn in *.
      eapply H in H0.
      intuition eauto.
      use_rule_in_wf; autorewrite with lang_core utils in *; break.
      destruct H7.
      eapply in_all in H7; eauto.
      eapply H7 in H1.
      intuition eauto.
    Qed.

       
    Lemma con_fresh_iff_sort_fresh c' args t name
      : In (name, term_rule c' args t) l ->
        fresh name pl <->
        fresh (sort_name t) pl.
    Proof.
      unfold pl_is_ordered in H_pl.
      intros.
      pose proof H as H_copy.
      eapply in_all in H; eauto.
      cbn in *.
      assert (dependency name (sort_name t)).
      {
        eapply dep_direct.
        unfold direct_dependency.
        case_match.
        2:{
          apply named_list_lookup_none_iff in HeqH0; eauto.
          eapply fresh_notin; eauto.
        }
        apply named_list_lookup_err_in in HeqH0.
        eapply in_all_fresh_same in HeqH0; [| basic_core_crush | clear HeqH0; eassumption].
        subst.
        destruct t; cbn.
        basic_utils_crush.
      }
      assert (dependency (sort_name t) name).
      {
        eapply dep_con; eauto.
      }
      
      eapply H in H0.
      intuition eauto.
      use_rule_in_wf; autorewrite with lang_core utils in *; break.
      destruct H6.
      eapply in_all in H6; eauto.
      eapply H6 in H1.
      intuition eauto.
    Qed.

    (*TODO: move to utils*)
    Lemma all_in A (P : A -> Prop) lst : (forall (a : A), In a lst -> P a) -> all P lst.
    Proof.
      induction lst;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Lemma ctx_fresh_if_sort_fresh r name
      : In (name, r) l ->
        fresh name pl ->
        (all (fun n : V => fresh n pl) (constructors_of_ctx (get_ctx r))).
    Proof.
      unfold pl_is_ordered in H_pl.
      intros.
      pose proof H as H_copy.
      eapply in_all in H; eauto.
      cbn in *.
      apply all_in; intros.
      eapply H; eauto.
      eapply dep_direct.
      unfold direct_dependency.
      case_match.
      2:{
        apply named_list_lookup_none_iff in HeqH2; eauto.
        eapply fresh_notin; eauto.
      }
      apply named_list_lookup_err_in in HeqH2.
      eapply in_all_fresh_same in HeqH2; [| basic_core_crush | clear HeqH2; eassumption].
      subst.
      destruct r0; cbn;
        basic_utils_crush.
    Qed.

    (*TODO: move to utils*)
    Lemma with_named_from_named_map A B C (f : A -> B) c' (s : list C)
      : with_names_from (named_map f c') s
        = with_names_from c' s.
    Proof.
      revert s; induction c';
        destruct s;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite  with_named_from_named_map : utils.

    
    (*TODO: move to utils*)
    Lemma all_app A (P : A -> Prop) l1 l2 : all P (l1++l2) <-> all P l1 /\ all P l2.
    Proof.
      induction l1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite all_app : utils.

    
    Lemma named_map_with_names_from A B C (f : A -> B) (c' : named_list C) s
      : named_map f (with_names_from c' s) = with_names_from c' (map f s).
    Proof.
      revert s; induction c'; destruct s;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Rewrite  named_map_with_names_from : utils.

    
  (*TODO: move to utils*)  
  Lemma incl_insert A (a:A) n lst
    : incl lst (insert n a lst).
  Proof.
    enough (incl (firstn n lst ++ skipn n lst) (insert n a lst)).
    { rewrite firstn_skipn in *; auto. }
    unfold insert.
    basic_utils_crush.
  Qed.
  Hint Immediate incl_insert : utils.

  (*TODO: move to core *)
  Lemma eq_args_ctx_monotonicity l' c1 c' s1 s2
    : wf_lang l' ->
      eq_args l' c1 c' s1 s2 -> forall c0 : list (V * Term.sort V), incl c1 c0 -> eq_args l' c0 c' s1 s2.
  Proof.
    induction 2;
      basic_goal_prep;
      basic_core_crush.
    eapply eq_term_ctx_monotonicity; eauto.
  Qed.

  
  Lemma insert_0 A (a : A) lst : insert 0 a lst = a::lst.
  Proof. reflexivity. Qed.
  Hint Rewrite insert_0 : utils.

  
  Lemma insert_S A n (a : A) a' lst : insert (S n) a (a'::lst) = a'::(insert n a lst).
  Proof. reflexivity. Qed.
  Hint Rewrite insert_S : utils.

  Context (H_p_sort_closed: well_scoped [] p_sort).

  
  Definition pl_indices_sound :=
    forall n p r, In (n,p) pl ->
                In (n,r) l ->
                all (fun n0 : V => fresh n0 pl) (constructors_of_ctx (skipn (fst p) (get_ctx r))).

  Context (H_pl_indices_sound : pl_indices_sound).


  Lemma firstn_with_names_from A B  n (l1 : named_list A) (l2 : list B)
    : firstn n (with_names_from l1 l2)
      = with_names_from (firstn n l1) (firstn n l2).
  Proof.
    revert l1 l2; induction n;
      destruct l1,l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite firstn_with_names_from : utils.

  (*TODO: move to term.v*)
  Lemma closed_term_subst (e:term) s
    : well_scoped [] e ->
      e [/s/] = e.
  Proof.
    induction e;
      basic_goal_prep;
      basic_term_crush.
    revert dependent l0.
    induction l0;
      basic_goal_prep;
      basic_term_crush.
  Qed.
  
  Lemma closed_args_subst (e:list term) s
    : well_scoped [] e ->
      e [/s/] = e.
  Proof.
    induction e;
      basic_goal_prep;
      basic_term_crush.
    eapply closed_term_subst; eauto.
  Qed.
    
  Lemma closed_sort_subst (e:sort) s
    : well_scoped [] e ->
      e [/s/] = e.
  Proof.
    destruct e; basic_goal_prep.
    f_equal; eapply closed_args_subst.
    auto.
  Qed.
  

  Lemma skipn_with_names_from A B  n (l1 : named_list A) (l2 : list B)
    : skipn n (with_names_from l1 l2)
      = with_names_from (skipn n l1) (skipn n l2).
  Proof.
    revert l1 l2; induction n;
      destruct l1,l2;
      basic_goal_prep;
      basic_utils_crush.
    destruct (skipn n l1); try reflexivity.
    cbv.
    destruct p.
    reflexivity.
  Qed.
  Hint Rewrite skipn_with_names_from : utils.

  
  Lemma with_names_from_app A B (l11 l12 : named_list A) (l21 l22 : list B)
    : length l11 = length l21 ->
      with_names_from (l11++l12) (l21++l22)
      = (with_names_from l11 l21) ++ (with_names_from l12 l22).
  Proof.
    revert l21; induction l11;
      destruct l21;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma with_names_from_insert A B (a:A) (b:B) n l1 l2 (name:V)
    : length l1 = length l2 ->
      insert n (name,a) (with_names_from l1 l2)
      = with_names_from (insert n (name,b) l1) (insert n a l2).
  Proof.
    intros.
    unfold insert.
    basic_utils_crush.
    rewrite with_names_from_app; eauto.
    rewrite !firstn_length; Lia.lia.
  Qed.

  Section WithCtx.

     Context (c : ctx).
    Context (wfc : wf_ctx l c).

    Context (H_p_name_c : fresh p_name c).
    
    Lemma sort_names_equal t1 t2
      : eq_sort l c t1 t2 -> sort_name t1 = sort_name t2.
    Proof.
      (*TODO: sort-only cut-free induction*)
      enough ((forall t t0 : Term.sort V, eq_sort l c t t0 -> sort_name t = sort_name t0) /\
       (forall (s : Term.sort V) (t t0 : Term.term V), eq_term l c s t t0 -> True) /\
       (forall (c0 : Term.ctx V) (s s0 : Term.subst V), eq_subst l c c0 s s0 -> True) /\
                (forall (c0 : Term.ctx V) (s s0 : list (Term.term V)), eq_args l c c0 s s0 -> True))
        by firstorder.
      eapply cut_ind;
        try typeclasses eauto; intuition (eauto; try congruence).
      {
        my_case H' (no_sort_eqns l).
        2: simpl in *; tauto.
        unfold no_sort_eqns in *.
        rewrite forallb_forall in H'.
        apply H' in H.
        cbn in *.
        congruence.
      }
    Qed.

    
    Lemma wf_sort_name_in t
      : wf_sort l c t -> exists r, In (sort_name t, r) l.
    Proof.
      destruct 1.
      eexists; eauto.
    Qed.
   
                               
  Lemma parameterize_preserving'_None
    : (forall (t1 t2 : sort),
          eq_sort l c t1 t2 -> wf_ctx l c ->
          fresh (sort_name t1) pl ->
            Model.eq_sort (pctx None c) (psort t1) (psort t2)) /\
  (forall (t : sort) (e1 e2 : term),
   eq_term l c t e1 e2 -> wf_ctx l c ->
   fresh (sort_name t) pl ->
   Model.eq_term (pctx None c) (psort t) (pterm e1) (pterm e2)) /\
  (forall (c' : named_list sort) (s1 s2 : named_list term),
   eq_subst l c c' s1 s2 ->
   wf_ctx l c ->
   wf_ctx l c' ->
   fresh p_name c' ->
   all (fun n => fresh n pl) (constructors_of_ctx c') ->
     eq_subst (parameterize_lang l) (pctx None c) (pctx None c') (parameterize_subst p_name pl None s1)
     (parameterize_subst p_name pl None s2)) /\
  (forall (c' : named_list sort) (s1 s2 : list term),
   eq_args l c c' s1 s2 ->
   wf_ctx l c ->
   wf_ctx l c' ->
   fresh p_name c' ->
   all (fun n => fresh n pl) (constructors_of_ctx c') ->
   eq_args (parameterize_lang l) (pctx None c) (pctx None c') (parameterize_args p_name pl None s1)
     (parameterize_args p_name pl None s2)).
  Proof.
    apply cut_ind;
      eauto;
      try typeclasses eauto;
      basic_goal_prep.
    {
      my_case H' (no_sort_eqns l).
      2: simpl in *; tauto.
      unfold no_sort_eqns in *.
      rewrite forallb_forall in H'.
      apply H' in H.
      cbn in *.
      congruence.
    }
    {
      use_rule_in_wf; autorewrite with utils lang_core in *; break.
      assert (all (fun n : V => fresh n pl) (constructors_of_ctx c')).
      {
        change c' with (get_ctx ( sort_rule c' args)).
        eapply ctx_fresh_if_sort_fresh; eauto.
      }
      eapply in_all in H_p_name_l; eauto;
        cbn in *.
      eapply in_map with
        (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
        in H.
      eapply sort_con_congruence; eauto.
      apply named_list_lookup_none_iff in H3; rewrite <- H3.
      eauto.
    }
    {
      apply sort_names_equal in H, H1.
      rewrite H in *; rewrite H1 in *.
      eauto using eq_sort_trans.
    }
    {
      apply sort_names_equal in H.
      rewrite H in *.
      eauto using eq_sort_sym.
    }
    {
      eapply in_all in H_p_name_l; eauto;
      cbn in *.
      use_rule_in_wf.
      autorewrite with lang_core utils term in *.
      break.
      assert (named_list_lookup_err pl name = None).
      {
        symmetry.
        apply named_list_lookup_none_iff.
        eapply eq_fresh_iff_sort_fresh; eauto.
      }      
      assert (all (fun n : V => fresh n pl) (constructors_of_ctx c')).
      {
        change c' with (get_ctx (term_eq_rule c' e1 e2 t)).
        eapply ctx_fresh_if_sort_fresh; eauto.
        apply named_list_lookup_none_iff; eauto.        
      }
      eapply in_map with
        (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
        in H.
      cbn in H.
      use_rule_in_wf; autorewrite with utils lang_core in *; break.

      erewrite !parameterize_sort_subst with (mn:=None).
      2:{
        eapply eq_subst_name_fresh_r_from_ctx; eauto.
      }
      2: basic_core_crush.
      erewrite !parameterize_term_subst with (mn:=None).
      2:{
        eapply eq_subst_name_fresh_r_from_ctx; eauto.
      }      
      3:{
        eapply eq_subst_name_fresh_l_from_ctx; eauto.
      }
      2,3:basic_core_crush.
      rewrite H8 in *.
      eapply eq_term_subst; [| eapply H1; eauto| eauto].
      eapply eq_term_by; eauto.
    }
    {
      
      assert (named_list_lookup_err pl name = None).
      {
        autorewrite with term in H3.
        eapply con_fresh_iff_sort_fresh in H.
        symmetry.
        apply named_list_lookup_none_iff.
        intuition auto.
      }
      assert (all (fun n : V => fresh n pl) (constructors_of_ctx c')).
      {
        change c' with (get_ctx (term_rule c' args t)).
        eapply ctx_fresh_if_sort_fresh; eauto.
        apply named_list_lookup_none_iff; eauto.        
      }
      use_rule_in_wf; autorewrite with utils lang_core in *; break.
      rewrite H4 in *.
       eapply in_all in H_p_name_l; eauto;
         cbn in *.
       eapply in_map with
         (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
         in H.
       eapply term_con_congruence; eauto.
       2:{
         rewrite H4.
         apply H1; eauto.
       }
       {
         right.
         rewrite H4.
         cbn.
         rewrite with_names_from_map_is_named_map.
         rewrite  with_named_from_named_map.
         erewrite !parameterize_sort_subst with (mn:=None); auto;
           autorewrite with utils model term lang_core;
           eauto with utils model term lang_core.
         2:{
           eapply @eq_args_length_eq_r with (Model:=core_model l).
           eapply H0.
         }
         rewrite CutElim.fresh_with_names_from; eauto.
         
         eapply @eq_args_length_eq_r with (Model:=core_model l).
         eapply H0.
       }
     }
     {
       basic_core_crush.
     }
     {
       eauto using eq_term_trans.
     }
     {
       eauto using eq_term_sym.
     }
     {
       eapply eq_term_conv; eauto.
       {
         eapply H2; eauto.
         apply sort_names_equal in H.
         congruence.
       }
       {
         eapply H0; eauto.
         apply sort_names_equal in H.
         congruence.
       }
     }
     {
       basic_core_crush.
     }
     {
       unfold constructors_of_ctx in *.
       basic_goal_prep.
       autorewrite with utils lang_core term model in *; break.
       constructor; eauto.
       unfold Model.eq_term, core_model.
       erewrite !parameterize_sort_subst with (mn:=None) in H2.
       2:{
         eapply eq_subst_name_fresh_r_from_ctx; eauto.
       }      
       2:basic_core_crush.
       eapply H2; eauto.
       destruct t;
         basic_goal_prep.
       intuition eauto.
     }
     {
       basic_core_crush.
     }
     {
       unfold constructors_of_ctx in *.
       basic_goal_prep.
       autorewrite with utils lang_core term model in *; break.
       constructor; eauto.
       unfold Model.eq_term, core_model.
       erewrite !parameterize_sort_subst with (mn:=None) in H2.
       2:{
         rewrite CutElim.fresh_with_names_from; eauto.
         eapply @eq_args_length_eq_r with (Model:=core_model l);
           eauto.
       }      
       2:{
         autorewrite with term model utils lang_core.
         2:eapply @eq_args_length_eq_r with (Model:=core_model l);
         eauto.
         basic_core_crush.
       }      
       cbn in *.
       autorewrite with term model utils in *.
       eapply H2; eauto.
       destruct t; cbn in *.
       intuition.
     }
  Qed.
  
  Lemma parameterize_preserving'_Some
    : (forall (t1 t2 : sort),
          eq_sort l c t1 t2 -> wf_ctx l c ->
          (*fresh (sort_name t1) pl ->*)
          forall p,
            Model.eq_sort (pctx (Some p) c) (psort t1) (psort t2)) /\
  (forall (t : sort) (e1 e2 : term),
   eq_term l c t e1 e2 -> wf_ctx l c ->
   (*fresh (sort_name t) pl ->*)
   forall p,
   Model.eq_term (pctx (Some p) c) (psort t) (pterm e1) (pterm e2)) /\
  (forall (c' : named_list sort) (s1 s2 : named_list term),
   eq_subst l c c' s1 s2 ->
   wf_ctx l c ->
   wf_ctx l c' ->
   fresh p_name c' ->
   forall p p',
     all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p') c'))->
     eq_subst (parameterize_lang l) (pctx (Some p) c) (pctx (Some p') c')
       (parameterize_subst p_name pl (Some p') s1)
       (parameterize_subst p_name pl (Some p') s2)) /\
  (forall (c' : named_list sort) (s1 s2 : list term),
      eq_args l c c' s1 s2 ->
      wf_ctx l c ->
      wf_ctx l c' ->
      fresh p_name c' ->
      forall p p',
        all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p') c'))->
        eq_args (parameterize_lang l) (pctx (Some p) c) (pctx (Some p') c')
          (parameterize_args p_name pl (Some p') s1)
          (parameterize_args p_name pl (Some p') s2)).
  Proof.
    apply cut_ind;
      eauto;
      try typeclasses eauto;
      basic_goal_prep.
    {
      my_case H' (no_sort_eqns l).
      2: simpl in *; tauto.
      unfold no_sort_eqns in *.
      rewrite forallb_forall in H'.
      apply H' in H.
      cbn in *.
      congruence.
    }
    {
      use_rule_in_wf; autorewrite with utils lang_core in *; break.
      case_match.
      2:{
        eapply eq_sort_ctx_monotonicity; eauto.
        {
          eapply sort_con_congruence; eauto.
          2:{
            eapply parameterize_preserving'_None; eauto.
            
            {
              eapply in_all in H_p_name_l; eauto;
                cbn in *.
              eapply in_map with
                (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
                in H.
              eauto.
            }
            {
              change c' with (get_ctx ( sort_rule c' args)).
              eapply ctx_fresh_if_sort_fresh; eauto.
              apply named_list_lookup_none_iff; eauto.
            }
          }
          eapply in_map with (f:=(fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p))) in H.
          unfold parameterize_lang.
          cbn in H.
          rewrite <- HeqH5 in *.
          eapply H.
        }
        {
          cbn.
          basic_utils_crush.
        }
      }
      {
        eapply sort_con_congruence; eauto.
        {
          eapply in_map with (f:=(fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p))) in H.
          unfold parameterize_lang.
          cbn in H.
          rewrite <- HeqH5 in *.
          eapply H.
        }
        cbn.
        specialize H1 with (p:= (n,b)).
        eapply H1; eauto.
        {
          eapply in_all in H_p_name_l; eauto;
            cbn in *.
          eapply in_map with
            (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
            in H.
          eauto.
        }
        change c' with (get_ctx (sort_rule c' args)).
        eapply  H_pl_indices_sound; eauto.
        basic_utils_crush.
      }
    }
    {
      specialize H0 with (p:=(n,b)).
      specialize H2 with (p:=(n,b)).
      basic_goal_prep.
      eauto using eq_sort_trans.
    }
    {
      specialize H0 with (p:=(n,b)).
      basic_goal_prep.
      eauto using eq_sort_sym.
    }
    {
      erewrite !parameterize_term_subst with (mn:=(named_list_lookup_err pl name)),
          !parameterize_sort_subst with (mn:=(named_list_lookup_err pl name)).
      
      3,5,7: use_rule_in_wf; basic_core_crush.
      2,3,4:enough (fresh p_name c'); 
      try (unfold fresh in *;
           (erewrite !eq_subst_dom_eq_l
            +erewrite !eq_subst_dom_eq_r); now eauto).
      2,3,4: eapply in_all in H_p_name_l; eauto;
      cbn in *;
      eapply in_map with
          (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
          in H;
        now eauto.
      eapply eq_term_subst.
      {
        eapply eq_term_by.
        eapply in_map with
          (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
          in H.
        eauto.
      }
      {
        my_case Hmn (named_list_lookup_err pl name).
        2:{
          cbn.
          eapply eq_subst_ctx_monotonicity; eauto.
          {
            eapply parameterize_preserving'_None; eauto.
            1: use_rule_in_wf; basic_core_crush.
            {
              eapply in_all in H_p_name_l; eauto;
                cbn in *;
                eapply in_map with
                (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
                in H;
                now eauto.
            }
            change c' with (get_ctx (term_eq_rule c' e1 e2 t)).
            eapply ctx_fresh_if_sort_fresh; eauto.
            apply named_list_lookup_none_iff; congruence.
          }
          {
            cbn; basic_utils_crush.
          }
        }
        {
          cbn.
          specialize H1 with (p:=(n,b)).
          eapply H1; eauto.
          { use_rule_in_wf; basic_core_crush. }
          {
            eapply in_all in H_p_name_l; eauto;
              cbn in *;
              eapply in_map with
              (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
              in H;
              now eauto.
          }
        change c' with (get_ctx (term_eq_rule c' e1 e2 t)).
        eapply  H_pl_indices_sound; eauto.
        basic_utils_crush.
        }
      }
      {
        eapply in_map with
          (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
          in H.
        cbn in H.
        use_rule_in_wf.
        basic_core_crush.
      }
    }
    {
      eapply term_con_congruence.
      {
        eapply in_map with
          (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
          in H.
        eauto.
      }
      {
        right.
        erewrite parameterize_sort_subst with (mn:=(named_list_lookup_err pl name)).
        2:{
          rewrite CutElim.fresh_with_names_from.
          {
            eapply in_all in H_p_name_l; eauto.
            eauto.
          }
          {
            eapply @eq_args_length_eq_r with (Model:=core_model l); eauto.
          }
        }
        2:{
          basic_utils_crush.
          2: eapply @eq_args_length_eq_r with (Model:=core_model l); eauto.
          use_rule_in_wf; basic_core_crush.
        }
        1:case_match; cbn;eauto.
        {
          rewrite named_map_with_names_from.
          erewrite <- with_named_from_named_map.
          erewrite with_names_from_insert; eauto.
          basic_utils_crush.
           eapply @eq_args_length_eq_r with (Model:=core_model l); eauto.
        }
        {
          rewrite named_map_with_names_from.
          erewrite <- with_named_from_named_map.
          reflexivity.
        }
      }
      {
        eauto.
      }
      {
        specialize H1 with (p:=(n,b)).
        case_match; cbn;eauto.
        2:{
          cbn.
          eapply eq_args_ctx_monotonicity; eauto.
          {
            eapply parameterize_preserving'_None; eauto.
            { use_rule_in_wf; basic_core_crush. }
            {
              eapply in_all in H_p_name_l; eauto;
                cbn in *;
                eapply in_map with
                (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
                in H;
                now eauto.
            }
            {
              change c' with (get_ctx (term_rule c' args t)).
              eapply ctx_fresh_if_sort_fresh; eauto.
              apply named_list_lookup_none_iff; eauto.
            }
          }
          {
            cbn; basic_utils_crush.
          }
        }
        {
          cbn in *.
          eapply H1; eauto.
          { use_rule_in_wf; basic_core_crush. }
          {
            eapply in_all in H_p_name_l; eauto;
              cbn in *;
              eapply in_map with
              (f:= (fun p : V * rule => (fst p, parameterize_rule p_name p_sort pl p)))
              in H;
              now eauto.
          }
          {
            change c' with (get_ctx (term_rule c' args t)).
            eapply H_pl_indices_sound; eauto.
            basic_utils_crush.
          }
        }
      }
    }
    {
      basic_core_crush.
    }
    {
      specialize H0 with (p:=(n,b)).
      specialize H2 with (p:=(n,b)).
      eapply eq_term_trans; eauto.
    }
    {
      specialize H0 with (p:=(n,b)).
      eapply eq_term_sym; eauto.
    }
    {
      specialize H0 with (p:=(n,b)).
      specialize H2 with (p:=(n,b)).
      eapply eq_term_conv; eauto.
    }
    {
      unfold insert.
      basic_utils_crush.
      cbn.
      constructor; constructor.
      eapply wf_term_var.
      replace  p_sort [/[] /] with p_sort;
        basic_core_crush.
      symmetry.
      apply sort_subst_nil.
    }
    {
      specialize H0 with (p:=(n0,b0)).
      cbn -[insert] in *.
      destruct n; basic_utils_crush.
      {
        constructor.
        {
          eapply eq_subst_ctx_monotonicity; eauto.
          {
            eapply (proj1 (proj2 (proj2 parameterize_preserving'_None)))
              with (c':=(name,t)::c')
                   (s1:=(name,e1)::s1)
                   (s2:=(name,e2)::s2); eauto.
            1: basic_core_crush.
            basic_utils_crush.
          }
          {
            cbn; basic_utils_crush.
          }
        }
        {
          eapply eq_term_refl.
          replace  p_sort [/(name, pterm e2) :: named_map pterm s2 /]
            with p_sort.
          {
            eapply wf_term_var.
            basic_utils_crush.
          }
          rewrite closed_sort_subst; eauto.
        }
      }
      {
        constructor.
        {
          specialize H7 with (p':=(n,b)).
          eapply H7; eauto.
          basic_core_crush.
        }
        replace ((psort t) [/insert n (p_name, {{e p_name}}) (named_map pterm s2) /])
          with  (psort t [/s2 /]).
        (*rewrite strengthen_sort_subst_insert'.*)
        {
          specialize H0 with (p:=(n0,b0)); cbn -[insert] in*.
          eapply H0.
        }
        {
          rewrite parameterize_sort_subst with (mn:=Some (n,b)); eauto.
          {
            unfold fresh in *.
            erewrite eq_subst_dom_eq_r; eauto.
          }
          {
            erewrite eq_subst_dom_eq_r; eauto.
            basic_core_crush.
          }
        }
      }
    }
    {
      unfold insert.
      basic_utils_crush.
      cbn.
      constructor; constructor.
      eapply wf_term_var.
      replace  p_sort [/with_names_from [] [] /] with p_sort;
        basic_core_crush.
      symmetry.
      apply sort_subst_nil.
    }
    {
      specialize H0 with (p:=(n0,b0)).
      cbn -[insert] in *.
      destruct n; basic_utils_crush.
      {
        constructor.
        {
          eapply eq_args_ctx_monotonicity; eauto.
          {
            eapply (proj2 (proj2 (proj2 parameterize_preserving'_None)))
              with (c':=(name,t)::c')
                   (s1:=e1::s1)
                   (s2:=e2::s2); eauto.
            1: basic_core_crush.
            basic_utils_crush.
          }
          {
            cbn; basic_utils_crush.
          }
        }
        {
          eapply eq_term_refl.
          replace p_sort [/with_names_from ((name, psort t) :: named_map psort c') (pterm e2 :: map pterm s2) /]
            with p_sort.
          {
            eapply wf_term_var.
            basic_utils_crush.
          }
          rewrite closed_sort_subst; eauto.
        }
      }
      {
        constructor.
        {
          specialize H7 with (p':=(n,b)).
          eapply H7; eauto.
          basic_core_crush.
        }
        replace ((psort t)  [/with_names_from (insert n (p_name, p_sort) (named_map psort c')) (insert n {{e p_name}} (map pterm s2)) /])
          with  (psort t [/with_names_from c' s2 /]).
        (*rewrite strengthen_sort_subst_insert'.*)
        {
          specialize H0 with (p:=(n0,b0)); cbn -[insert] in*.
          eapply H0.
        }
        {
          rewrite parameterize_sort_subst with (mn:=Some (n,b)); eauto.
          2:{
            rewrite CutElim.fresh_with_names_from; basic_utils_crush.
            eapply @eq_args_length_eq_r with (Model:=core_model l); eauto.
          }
          2:{
            autorewrite with utils term model lang_core in *; intuition eauto with lang_core.
            eapply @eq_args_length_eq_r with (Model:=core_model l); eauto.
          }
          rewrite <- with_names_from_insert, ?with_named_from_named_map,
            <-named_map_with_names_from; eauto.
          basic_utils_crush.
          eapply @eq_args_length_eq_r with (Model:=core_model l); eauto.
        }
      }
    }
  Qed.

  Lemma parameterize_preserving'
    : (forall (t1 t2 : sort),
          eq_sort l c t1 t2 -> wf_ctx l c ->
          forall (mn : option _),
            (if mn then True else fresh (sort_name t1) pl) ->
            Model.eq_sort (pctx mn c) (psort t1) (psort t2)) /\
        (forall (t : sort) (e1 e2 : term),
            eq_term l c t e1 e2 -> wf_ctx l c ->
            forall (mn : option _),
              (if mn then True else fresh (sort_name t) pl) ->
              Model.eq_term (pctx mn c) (psort t) (pterm e1) (pterm e2)) /\
        (forall (c' : named_list sort) (s1 s2 : named_list term),
            eq_subst l c c' s1 s2 ->
            wf_ctx l c ->
            wf_ctx l c' ->
            fresh p_name c' ->
            forall (mn mn' : option _),
              (if mn then match mn' with
                          | Some p' => all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p') c'))
                          | None => all (fun n => fresh n pl) (constructors_of_ctx c')
                          end
               else ~ Is_Some mn' /\ all (fun n => fresh n pl) (constructors_of_ctx c')) ->
              eq_subst (parameterize_lang l) (pctx mn c) (pctx mn' c')
                     (parameterize_subst p_name pl mn' s1)
                     (parameterize_subst p_name pl mn' s2)) /\
        (forall (c' : named_list sort) (s1 s2 : list term),
            eq_args l c c' s1 s2 ->
            wf_ctx l c ->
            wf_ctx l c' ->
            fresh p_name c' ->
            forall (mn mn' : option _),
              (if mn then match mn' with
                          | Some p' => all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p') c'))
                          | None => all (fun n => fresh n pl) (constructors_of_ctx c')
                          end
               else ~ Is_Some mn' /\ all (fun n => fresh n pl) (constructors_of_ctx c')) ->
                   eq_args (parameterize_lang l) (pctx mn c) (pctx mn' c')
                     (parameterize_args p_name pl mn' s1)
                     (parameterize_args p_name pl mn' s2)).
  Proof.
    repeat split; destruct mn; try destruct mn';
      intros.
    all: cbn in *; intuition eauto.
    all: try now (apply parameterize_preserving'_None; cbn in *; intuition eauto).
    all: try now (apply parameterize_preserving'_Some; cbn in *; intuition; eauto).
    {
      eapply eq_subst_ctx_monotonicity; eauto.
      { apply parameterize_preserving'_None; intuition eauto. }
      {
        cbn; apply incl_insert; eauto.
      }
    }
    {
      eapply eq_args_ctx_monotonicity; eauto.
      { apply parameterize_preserving'_None; intuition eauto. }
      {
        cbn; apply incl_insert; eauto.
      }
    }
  Qed.

  End WithCtx.


  (*
    sort_eq_preserving_sem (tgt_Model := core_model (parameterize_lang l))
        psort (pctx mn) l /\
        term_eq_preserving_sem (tgt_Model := core_model (parameterize_lang l))
          pterm psort (pctx mn) l /\
        subst_eq_preserving_sem (tgt_Model := core_model (parameterize_lang l))
          (pctx mn) (parameterize_subst p_name pl mn) l /\
        args_eq_preserving_sem (tgt_Model := core_model (parameterize_lang l))
          (pctx mn) (parameterize_args p_name pl mn) l.
  Proof.
    unfold sort_eq_preserving_sem,
      term_eq_preserving_sem,
      subst_eq_preserving_sem,
       args_eq_preserving_sem.
    apply cut_ind with (l:=l).
*)
    
  Lemma parameterize_preserving mn
    : semantics_preserving l mn.
  Proof.
    unfold semantics_preserving.
    (*
  sort_wf_preserving_sem psort (pctx mn) l /\
  term_wf_preserving_sem pterm psort (pctx mn) l /\
  args_wf_preserving_sem (pctx mn) (parameterize_args p_name pl mn) l /\ ctx_wf_preserving_sem (pctx mn) l

    cut_ind
    eapply judge_ind.
    {
      unfold Model.eq_sort, core_model.
      intros.
      admit (* TODO: use same induction as in cut-free?*).
    }
    {
      intros.
      TODO: use cut_free_ind?
      TODO: push mn inside the quantification?
     *)
  Abort.


  End __.
    

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

