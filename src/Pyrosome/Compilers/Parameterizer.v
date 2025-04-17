Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Require Import Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Infinite Monad.
From Pyrosome Require Import Theory.Core Theory.Renaming Theory.CutFreeInd
  Theory.ModelImpls
  Tools.ConstructorsOf.
From Pyrosome.Compilers Require Import SemanticsPreservingDef Compilers CompilerFacts.
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
              eapply in_all; eauto.
              basic_utils_crush.
            }
            f_equal.
            2:{
              apply map_ext_in; intros; eauto.
              eapply in_all with (a:=a) in H; basic_utils_crush.
              eapply H3; eauto.
              eapply in_all; eauto; basic_utils_crush.
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
            (*TODO: why is this much slower w/out the eauto?*)
            eapply in_all; eauto; basic_utils_crush.
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
    Notation prule := (parameterize_rule p_name p_sort pl).
  
  Definition parameterize_lang : lang -> lang :=
    map (fun p => (fst p, prule p)).


  
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

  Context (l_base : lang).
  

  Context (H_p_sort_closed: wf_sort l_base [] p_sort).

  
  Notation semantics_preserving l mn :=
    (semantics_preserving
       (V_Eqb := V_Eqb)
       (tgt_Model := core_model (parameterize_lang l ++ l_base))
       (parameterize_term p_name pl)
       (parameterize_sort p_name pl)
       (parameterize_ctx p_name p_sort pl mn(*TODO:what goes here again?*))
       (parameterize_args p_name pl mn(*TODO:what goes here again?*))
       (parameterize_subst p_name pl mn(*TODO:what goes here again?*))
       l).

  Section __.
    Context (l : lang).
    
    Let l_plus := (parameterize_lang l ++ l_base).
    Definition tgt_model := (core_model l_plus).
    Existing Instance tgt_model.

    Context (wfl : wf_lang l).
    Context (IH_l : wf_lang l_plus).
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
          symmetry in case_match_eqn.
          apply named_list_lookup_none_iff in case_match_eqn; eauto.
          eapply fresh_notin; eauto.
        }
        symmetry in case_match_eqn.
        apply named_list_lookup_err_in in case_match_eqn.
        eapply in_all_fresh_same in case_match_eqn;
          [| basic_core_crush | clear case_match_eqn; eassumption].
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
          symmetry in case_match_eqn.
          apply named_list_lookup_none_iff in case_match_eqn; eauto.
          eapply fresh_notin; eauto.
        }
        symmetry in case_match_eqn.
        apply named_list_lookup_err_in in case_match_eqn.
        eapply in_all_fresh_same in case_match_eqn;
          [| basic_core_crush | clear case_match_eqn; eassumption].
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
      case_match;
        symmetry in case_match_eqn.
      2:{        
        apply named_list_lookup_none_iff in case_match_eqn; eauto.
        eapply fresh_notin; eauto.
      }
      apply named_list_lookup_err_in in case_match_eqn.
      eapply in_all_fresh_same in case_match_eqn;
        [| basic_core_crush | clear case_match_eqn; eassumption].
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
            eq_sort l_plus (pctx None c) (psort t1) (psort t2)) /\
  (forall (t : sort) (e1 e2 : term),
   eq_term l c t e1 e2 -> wf_ctx l c ->
   fresh (sort_name t) pl ->
   eq_term l_plus (pctx None c) (psort t) (pterm e1) (pterm e2)) /\
  (forall (c' : named_list sort) (s1 s2 : named_list term),
   eq_subst l c c' s1 s2 ->
   wf_ctx l c ->
   wf_ctx l c' ->
   fresh p_name c' ->
   all (fun n => fresh n pl) (constructors_of_ctx c') ->
     eq_subst l_plus (pctx None c) (pctx None c') (parameterize_subst p_name pl None s1)
     (parameterize_subst p_name pl None s2)) /\
  (forall (c' : named_list sort) (s1 s2 : list term),
   eq_args l c c' s1 s2 ->
   wf_ctx l c ->
   wf_ctx l c' ->
   fresh p_name c' ->
   all (fun n => fresh n pl) (constructors_of_ctx c') ->
   eq_args l_plus (pctx None c) (pctx None c') (parameterize_args p_name pl None s1)
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
      eapply sort_con_congruence; subst l_plus; basic_utils_crush.
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
      epose proof (in_or_app _ l_base _ (or_introl H)).
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
      subst l_plus.
      eapply eq_term_by; basic_utils_crush.
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
       subst l_plus.
       eapply term_con_congruence; basic_utils_crush.
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
       autorewrite with rw_prop inversion utils lang_core term model in *; break.
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
          forall p, eq_sort l_plus (pctx (Some p) c) (psort t1) (psort t2)) /\
  (forall (t : sort) (e1 e2 : term),
   eq_term l c t e1 e2 -> wf_ctx l c ->
   forall p, eq_term l_plus (pctx (Some p) c) (psort t) (pterm e1) (pterm e2)) /\
  (forall (c' : named_list sort) (s1 s2 : named_list term),
   eq_subst l c c' s1 s2 ->
   wf_ctx l c ->
   wf_ctx l c' ->
   fresh p_name c' ->
   forall p p',
     all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p') c'))->
     eq_subst l_plus (pctx (Some p) c) (pctx (Some p') c')
       (parameterize_subst p_name pl (Some p') s1)
       (parameterize_subst p_name pl (Some p') s2)) /\
  (forall (c' : named_list sort) (s1 s2 : list term),
      eq_args l c c' s1 s2 ->
      wf_ctx l c ->
      wf_ctx l c' ->
      fresh p_name c' ->
      forall p p',
        all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p') c'))->
        eq_args l_plus (pctx (Some p) c) (pctx (Some p') c')
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
          rewrite case_match_eqn in *.
          subst l_plus; basic_utils_crush.
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
          rewrite case_match_eqn in *.
          subst l_plus; basic_utils_crush.
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
        subst l_plus; basic_utils_crush.
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
        subst l_plus.
        epose proof (in_or_app _ l_base _ (or_introl H)).
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
        subst l_plus; basic_utils_crush.
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
          rewrite closed_sort_subst; basic_core_crush.
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
          rewrite closed_sort_subst; basic_core_crush.
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
            eq_sort l_plus  (pctx mn c) (psort t1) (psort t2)) /\
        (forall (t : sort) (e1 e2 : term),
            eq_term l c t e1 e2 -> wf_ctx l c ->
            forall (mn : option _),
              (if mn then True else fresh (sort_name t) pl) ->
              eq_term l_plus  (pctx mn c) (psort t) (pterm e1) (pterm e2)) /\
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
              eq_subst l_plus (pctx mn c) (pctx mn' c')
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
                   eq_args l_plus (pctx mn c) (pctx mn' c')
                     (parameterize_args p_name pl mn' s1)
                     (parameterize_args p_name pl mn' s2)).
  Proof.
    repeat split; destruct mn; try destruct mn';
      intros.
    all: break.
    all: try now (cbn in *; intuition eauto).
    all: try now (apply parameterize_preserving'_None; cbn in *; intuition eauto).
    all: try now (apply parameterize_preserving'_Some; cbn in *; intuition eauto).
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

  
  Lemma insert_nil A n (a : A) : insert n a [] = [a].
  Proof.
    unfold insert; basic_utils_crush.
  Qed.
  Hint Rewrite insert_nil : utils.

  (*TODO: move tp utils*)
  Hint Immediate incl_nil_l : utils.

  
  Lemma fresh_insert name A n (p : V * A) lst
    : fresh name (insert n p lst) <-> name <> (fst p) /\ fresh name lst.
  Proof.
    unfold insert; basic_goal_prep.
    rewrite <- firstn_skipn with (n:=n) (l:=lst) at 3.
    basic_utils_crush.
  Qed.
  Hint Rewrite fresh_insert : utils.

  Lemma parameterize_ctx_preserving' c mn
    : wf_ctx l c ->
      fresh p_name c ->
      match mn with
      | Some p => all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p) c))
      | None => all (fun n => fresh n pl) (constructors_of_ctx c)
      end ->
      wf_ctx l_plus (pctx mn c).
  Proof.
    intro Hwf.
    revert mn.
    induction Hwf;
      destruct mn;
      basic_goal_prep;
      basic_core_crush.
    {
      unfold Model.wf_sort, core_model.
      subst l_plus.
      eapply wf_sort_lang_monotonicity; eauto; basic_utils_crush.
    }
    2:{
      specialize (IHHwf None).
      eapply IHHwf; unfold constructors_of_ctx in *;
        basic_goal_prep;
        basic_utils_crush.
    }
    2:{
      unfold Model.wf_sort, core_model.
      eapply eq_sort_wf_l; eauto.
      {
        specialize (IHHwf None).
        eapply IHHwf; unfold constructors_of_ctx in *;
          basic_goal_prep;
          basic_utils_crush.
      }
      eapply (proj1 (parameterize_preserving' _)) with (mn:=None);
        unfold constructors_of_ctx in *;
        basic_goal_prep; basic_core_crush.
      destruct v; 
        basic_goal_prep; basic_core_crush.
    }
    {
      destruct n; basic_utils_crush;
        autorewrite with model utils.
      all: intuition eauto.
      {
        specialize (IHHwf None).
        eapply IHHwf; unfold constructors_of_ctx in *;
          basic_goal_prep;
          basic_utils_crush.
      }
      {
        unfold Model.wf_sort, core_model.
        eapply eq_sort_wf_l; eauto.
        {
          specialize (IHHwf None).
          eapply IHHwf; unfold constructors_of_ctx in *;
            basic_goal_prep;
            basic_utils_crush.
        }
        eapply (proj1 (parameterize_preserving' _)) with (mn:=None);
          unfold constructors_of_ctx in *;
          basic_goal_prep; basic_core_crush.
        destruct v; 
          basic_goal_prep; basic_core_crush.
      }
      {
        subst l_plus.
        eapply wf_sort_ctx_monotonicity; auto.
        1: eapply wf_sort_lang_monotonicity; auto.
        2:eauto.
        all: basic_utils_crush.
      }
      {
        specialize (IHHwf (Some (n,b))).
        eapply IHHwf; unfold constructors_of_ctx in *;
            basic_goal_prep;
            basic_utils_crush.
      }      
      {
        unfold Model.wf_sort, core_model.
        eapply eq_sort_wf_l; eauto.
        {
          specialize (IHHwf (Some (n,b))).
          eapply IHHwf; unfold constructors_of_ctx in *;
            basic_goal_prep;
            basic_utils_crush.
        }
        eapply (proj1 (parameterize_preserving' _)) with (mn:=Some(n,b));
          unfold constructors_of_ctx in *;
          basic_goal_prep; basic_core_crush.
      }
    }
    Unshelve.
    all: eauto.
  Qed.

  Definition fresh_sort r :=
    match r with
    | sort_rule x x0 => True
    | term_rule x x0 x1 => fresh (sort_name x1) pl
    | sort_eq_rule x x0 x1 => False
    | term_eq_rule x x0 x1 x2 => fresh (sort_name x2) pl
    end.


  
  Definition elab_args_sublist p r : Prop :=
    match r with
    | sort_rule c args
    | term_rule c args _ =>
        sublist (parameterize_elab_args p_name (Some p) c args) (map fst (pctx (Some p) c))
    | sort_eq_rule _ _ _
    | term_eq_rule _ _ _ _ => True
    end.
  
  Definition rule_checked '(name,r) :=
    fresh p_name (get_ctx r)
    /\ match named_list_lookup_err pl name with
       | Some p => all (fun n => fresh n pl) (constructors_of_ctx (skipn (fst p) (get_ctx r)))
                   (*TODO: this fact is decidable so we shortcut by leaving it assumed,
                     but it should be provable universally.
                    *)
                   /\ elab_args_sublist p r
      | None => all (fun n => fresh n pl) (constructors_of_ctx (get_ctx r)) /\ fresh_sort r
       end.

  
  (*TODO: add to utils*)
  Hint Rewrite map_fst_named_map : utils.
  Hint Rewrite map_app firstn_map @skipn_map : utils.

  
  Lemma map_insert A B (f : A -> B) n a lst
    : map f (insert n a lst) = insert n (f a ) (map f lst).
  Proof.
    unfold insert; basic_utils_crush.
  Qed.
  Hint Rewrite map_insert : utils.

  
  Lemma sublist_app_r A (l1' : list A) l2 l2'
    : sublist l2 l2' -> sublist l2 (l1' ++ l2').
  Proof.
    induction l1';
      basic_goal_prep;
      basic_utils_crush.
    destruct l2; intuition eauto.
  Qed.
  Hint Resolve sublist_app_r : utils.

  Lemma sublist_split A a (l2 l' : list A)
    : sublist (a::l2) l' -> exists l1' l2', l'=l1'++a::l2' /\ sublist l2 l2'.
  Proof.
    induction l'.
    {
      cbn; basic_utils_crush.
    }
    cbn.
    intuition subst.
    {
      exists [], l'.
      basic_utils_crush.
    }
    {
      basic_goal_prep.
      subst.
      exists (a0::x), x0.
      cbn.
      basic_utils_crush.
    }
  Qed.
    
    (*
  Lemma sublist_app A (l1 l1' l2 l2' : list A)
    : sublist l1 l1' -> sublist l2 l2' -> sublist (l1++l2) (l1'++l2').
  Proof.
    revert l1';
      induction l1;
      basic_goal_prep;
      basic_utils_crush.
    {
      apply sublist_split in H.
      break.
      subst.
      apply IHl1 in H1; eauto.
      replace ((x ++ a :: x0) ++ l2') with ((x++[a])++(x0++l2')).
  Admitted.
  Hint Resolve sublist_app : utils.
*)

  (*
  Lemma sublist_insert A n (a:A) lst
    : sublist lst (insert n a lst).
  Proof.
    rewrite <- firstn_skipn with (n:=n) (l:=lst) at 1.
    unfold insert.
    basic_utils_crush.
  Qed.
  (*Hint Immediate sublist_insert : utils.*)
*)

(*
  Lemma sublist_trans A (l1 l2 l3 : list A)
    : sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
  Proof.
    revert l2 l3.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
    destruct l2; basic_goal_prep; [tauto|].
    destruct l3; basic_goal_prep;[tauto|].
    intuition subst.
    { basic_utils_crush. }
    {
      right.
      apply sublist_split in H1.
      break.
      subst.
      change (a0 :: l1) with ([a0]++l1).
      replace (x ++ a0 :: x0)
        with ((x ++ [a0]) ++ x0).
      {
        eapply sublist_app; eauto.
        eapply sublist_app_r.
        cbn; intuition eauto.
      }
      rewrite <- app_assoc.
      reflexivity.
    }
    {
      right.
      apply sublist_split in H1.
      break.
      subst.
      replace (x ++ a :: x0)
        with ((x ++ [a]) ++ x0) in H2.
      {
        (*
        apply sublist_split in H2.
        eapply sublist_app; eauto.
        eapply sublist_app_r.
        cbn; intuition eauto.
      }
      rewrite <- app_assoc.
      reflexivity.
    }
      
    }*)
  Admitted.
*)

  (*
  Lemma sublist_insert' A n (a:A) l1 l2
    : sublist l1 l2 -> sublist l1 (insert n a l2).
  Proof.
    intros.
    eapply sublist_trans; eauto.
    apply sublist_insert.
  Qed.
  Hint Resolve sublist_insert' : utils.
*)

  (* TODO: restrict to lhs by restricting n0 to len c?*)
  Lemma parameterize_args'_empty n0 c
    : parameterize_args' p_name n0 c [] = [p_name]
      \/ parameterize_args' p_name n0 c [] = [].
  Proof.
    revert c.
    induction n0;
      destruct c;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma sublist_singleton_insert A n lst (p:A)
    : sublist [p] (insert n p lst).
  Proof.
    unfold insert;
    revert lst; induction n;
      destruct lst;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Immediate sublist_singleton_insert : utils.

  (*
  Lemma sublist_parameterize_args' n n0 l0
    : sublist l0 (map fst n) ->
      sublist (parameterize_args' p_name n0 n l0) (insert n0 p_name (map fst n)).
  Proof.
    revert n l0;
      induction n0;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct l0; intuition eauto.
      destruct (parameterize_args'_empty n0 []) as [H' | H']; rewrite H'.
      all:basic_utils_crush.
    }
    {
      destruct l0; intuition eauto.
      {
        destruct (parameterize_args'_empty n0 ((v, s) :: n)) as [H' | H']; rewrite H';
        basic_utils_crush.
      }
      {
        subst.
        change (v :: map fst n) with (map fst ((v,s)::n)).
        eapply IHn.
      }
      {

      }
    }
      cbn.
      case_match; eauto.
      right.
      TODO: need IH
  Qed.
   *)
                 
  Lemma parameterize_rule_preserving' p
    : wf_rule l (snd p) ->
      rule_checked p ->
      wf_rule l_plus (prule p).
  Proof.
    repeat basic_goal_prep.
    destruct r; autorewrite with utils model lang_core in *;
      intuition subst.
    all: try eapply eq_sort_wf_r; eauto; try eapply eq_term_wf_r; eauto.
    all: try eapply parameterize_preserving'; eauto.
    all: try apply eq_sort_refl; eauto.
    all: try apply eq_term_refl; eauto.
    all: try eapply parameterize_ctx_preserving'; eauto.
    all: my_case H_lookup (named_list_lookup_err pl v); try solve [basic_goal_prep; basic_utils_crush].
  Qed.

  End __.

  Lemma dependency_weakening l l' n0 n'
    : all_fresh l' -> incl l l' -> dependency l n0 n' -> dependency l' n0 n'.
  Proof.
    induction 3;
      basic_goal_prep; eauto using dep_trans, dep_direct, dep_eqn, dep_con.
    eapply dep_direct.
    revert H1;
      unfold direct_dependency;
      case_match;
      basic_utils_crush.
    symmetry in case_match_eqn.
    apply named_list_lookup_err_in in case_match_eqn.
    case_match;
      symmetry in case_match_eqn0;
      basic_utils_crush.
    2:{
      eapply named_list_lookup_none in case_match_eqn0.
      apply case_match_eqn0.
      apply H0.
      eauto.
    }
    {
      apply named_list_lookup_err_in in case_match_eqn0.
      apply H0 in case_match_eqn.
      eapply in_all_fresh_same in case_match_eqn; eauto.
      congruence.
    }
  Qed.
  
    Lemma pl_is_ordered_incl l l'
      : all_fresh l' ->
        pl_is_ordered l' ->
        incl l l' ->
        pl_is_ordered l.
    Proof.
      unfold pl_is_ordered; cbn; intuition eauto.
      apply all_in.
      repeat basic_goal_prep.
      eapply in_all with (a:=(v,r)) in H0.
      2:basic_utils_crush.
      eapply dependency_weakening in H3; eauto.
    Qed.

    (* TODO: move to utils*)
    Lemma all_fresh_app_l A (l1 l2 : named_list A)
      : all_fresh (l1 ++l2) -> all_fresh l1.
    Proof.
      induction l1;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve all_fresh_app_l : utils.

    
    Lemma pl_indices_sound_incl l l'
      : pl_indices_sound l' ->
        incl l l' ->
        pl_indices_sound l.
    Proof.
      unfold pl_indices_sound; cbn; intuition eauto.
    Qed.
    
  Lemma parameterize_lang_preserving' l
    : wf_lang l ->
      wf_lang l_base ->
      all (fun p : V * rule => fresh p_name (get_ctx (snd p))) l ->
      Is_true (no_sort_eqns l) ->
      all rule_checked l ->
      all_fresh (l++l_base) ->
      pl_is_ordered l ->
      pl_indices_sound l ->
      wf_lang_ext l_base (parameterize_lang l).
  Proof.
    unfold parameterize_lang, no_sort_eqns in *.
    induction 1; cbn [map fst all_fresh all forallb].
    1:constructor.
    intros.
    assert (pl_is_ordered l).
    {
      eapply pl_is_ordered_incl; [| eauto|];
        basic_utils_crush.
    }
    assert (pl_indices_sound l).
    {
      eapply pl_indices_sound_incl;
        basic_utils_crush.
    }
    constructor.
    {
      unfold parameterize_lang, fresh;
        basic_goal_prep;
        basic_utils_crush.
      match goal with H : In _ _ |- _ => revert H end.
      rewrite map_app.
      rewrite map_map.
      basic_goal_prep;
        basic_utils_crush.
    }
    {
      cbn in *; basic_utils_crush.      
    }
    {
      eapply parameterize_rule_preserving';
        try now basic_utils_crush.
      {
        apply wf_lang_concat; eauto.
        apply IHwf_lang_ext; basic_goal_prep; basic_utils_crush.
      }
      unfold parameterize_lang, no_sort_eqns in *.
      basic_utils_crush.
    }      
  Qed.
  
  (*TODO: next: write a boolean expression for all of the assumptions,
    use in final thm.
    TODO: do the same for compilers.
   *)

  Definition elab_args_sublistb p r : bool :=
    match r with
    | sort_rule c args
    | term_rule c args _ =>
        sublistb (parameterize_elab_args p_name (Some p) c args)
                             (map fst (pctx (Some p) c))
    | _ => true
    end.

  Definition fresh_sortb r :=
    match r with
    | sort_rule _ _ => true
    | term_rule _ _ x1 => freshb (sort_name x1) pl
    | sort_eq_rule _ _ _ => false
    | term_eq_rule _ _ _ x2 => freshb (sort_name x2) pl
    end.

  Definition rule_checkedb namer : bool :=
    freshb p_name (get_ctx (snd namer)) &&
      match named_list_lookup_err pl (fst namer) with
      | Some p =>
          forallb (fun n : V => freshb n pl)
            (constructors_of_ctx (skipn (fst p) (get_ctx (snd namer))))
            && elab_args_sublistb p (snd namer)
      | None =>
          forallb (fun n : V => freshb n pl) (constructors_of_ctx (get_ctx (snd namer)))
          && fresh_sortb (snd namer)
      end.

  Definition pl_indices_soundb : lang -> bool :=
    forallb (fun nr =>
               match named_list_lookup_err pl (fst nr) with
               | Some p => forallb (fun n0 : V => freshb n0 pl)
                             (constructors_of_ctx (skipn (fst p)
                                                     (get_ctx (snd nr))))
               | None => true
               end).

  (*TODO: remove hint if possible*)
  (*Hint Rewrite Is_true_forallb : utils.*)

  
  Lemma compute_elab_args_sublist n b r
    : Is_true (elab_args_sublistb (n, b) r) -> elab_args_sublist (n, b) r.
  Proof.
    destruct r;
      basic_goal_prep;
      basic_utils_crush.
    all: apply use_sublistb; eauto.
  Qed.

  
  Lemma compute_fresh_sort r
    :  Is_true (fresh_sortb r) -> fresh_sort r.
  Proof.
    destruct r;
      basic_goal_prep;
      basic_utils_crush;
      cbn; eauto using use_compute_fresh.
  Qed.

  Lemma compute_pl_indices_sound l
    : Is_true (all_freshb pl) ->
      Is_true (pl_indices_soundb l) -> pl_indices_sound l.
  Proof.
    unfold pl_indices_sound, pl_indices_soundb.
    basic_goal_prep;
      basic_utils_crush.
    eapply all_in; intros; eapply in_all in H0;
      cbn; eauto using use_compute_fresh.
    apply <- all_fresh_named_list_lookup_err_in in H1;
      eauto using use_compute_all_fresh.
    cbn in *.
    rewrite <- H1 in H0.
    basic_utils_crush.
    apply use_compute_fresh.
    eapply in_all in H0; eauto.
  Qed.

  
  Definition syntactic_parameterization_conditions' l :=
    (forallb (fun p : V * rule => freshb p_name (get_ctx (snd p))) l)
    && (no_sort_eqns l)
    && (forallb rule_checkedb l)
    && (all_freshb (l++l_base))
    && (all_freshb pl)
    && (pl_indices_soundb l).

  Lemma parameterize_lang_preserving''
     : forall l : lang,
       wf_lang l ->
       wf_lang l_base ->
       Is_true (syntactic_parameterization_conditions' l) ->
       pl_is_ordered l ->
       wf_lang_ext l_base (parameterize_lang l).
  Proof.
    unfold syntactic_parameterization_conditions',
      rule_checkedb.
    intros.
    basic_utils_crush.
    eapply parameterize_lang_preserving';
        eauto using use_compute_all_fresh.
    {
      eapply all_in; intros; eapply in_all in H3;
        cbn; eauto using use_compute_fresh.
    }
    {
      unfold rule_checked.
      eapply all_in; intros; eapply in_all in H7;
        cbn; eauto.
      basic_goal_prep;
        basic_utils_crush;
        eauto using use_compute_fresh.
      case_match;
      basic_goal_prep;
        basic_utils_crush;
        eauto using compute_elab_args_sublist.
      {
        eapply all_in; intros; eapply in_all in H7;
          cbn; eauto using use_compute_fresh.
      }
      {
        eapply all_in; intros; eapply in_all in H7;
          cbn; eauto using use_compute_fresh.
      }
      {
        eapply compute_fresh_sort; eauto.
      }
    }
    {
      eapply compute_pl_indices_sound;
        basic_utils_crush.
    }
  Qed.

  End WithSpec.

  Local Notation preserving_compiler_ext tgt cmp_pre cmp src :=
    (preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src).
  Local Notation compiler := (@compiler V term sort).

  (*TODO: move to a better location*)
  Definition id_compiler : lang -> compiler :=
    flat_map (fun '(name,r) =>
                match r with
                | sort_rule c _ => [(name,sort_case (map fst c) (scon name (map var (map fst c))))]
                | term_rule c _ _ => [(name,term_case (map fst c) (con name (map var (map fst c))))]
                | _ => []
                end).

  
  Lemma term_rule_not_fresh_in_id_compiler n c' args t l
    :  In (n, term_rule c' args t) l -> ~ fresh n (id_compiler l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma term_rule_in_id_compiler n c' args t l
    :  In (n, term_rule c' args t) l ->
       In (n,term_case (map fst c') (con n (map var (map fst c'))))
          (id_compiler l).
  Proof.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma id_compiler_fresh n l
    : fresh n l -> fresh n (id_compiler l).
  Proof.
    induction l;
      basic_goal_prep;
      try destruct r;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Resolve id_compiler_fresh : utils.
  
  Lemma id_compiler_all_fresh l
    : all_fresh l -> all_fresh (id_compiler l).
  Proof.
    induction l;
      basic_goal_prep;
      try destruct r;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Resolve id_compiler_all_fresh : utils.


  
  (*TODO: move somewhere better*)
  Lemma named_list_lookup_in A (a:A) n v s'
    : all_fresh s' -> In (n,v) s' -> named_list_lookup a s' n = v.
  Proof with (basic_goal_prep; basic_term_crush).
    induction s'...     
    eqb_case n v0...
  Qed.      
      
  Lemma var_args_helper' s s'
    : all_fresh s' ->
      incl s s' ->
      (map var (map fst s)) [/s'/] = map snd s.
  Proof.
    induction s;
      basic_goal_prep;
      basic_term_crush.
    apply named_list_lookup_in; eauto.
  Qed.

  
  Lemma map_snd_with_names_from A B (s : list A) (c' : named_list B)
    : Datatypes.length s = Datatypes.length c' ->
      map snd (with_names_from c' s) = s.
  Proof.
    revert s;
      induction c';
      destruct s;
      basic_goal_prep;
      basic_term_crush.
  Qed.
  Hint Rewrite map_snd_with_names_from : utils.


  Lemma fresh_with_names_from n A B (s : list A) (c' : named_list B)
    : fresh n c' ->
      fresh n (with_names_from c' s).
  Proof.
    revert s;
      induction c';
      destruct s;
      basic_goal_prep;
      basic_term_crush.
  Qed.
  Hint Resolve fresh_with_names_from : utils.
  
  Lemma all_fresh_with_names_from A B (s : list A) (c' : named_list B)
    : all_fresh c' ->
      all_fresh (with_names_from c' s).
  Proof.
    revert s;
      induction c';
      destruct s;
      basic_goal_prep;
      basic_term_crush.
  Qed.
  Hint Resolve all_fresh_with_names_from : utils.
    
  Lemma var_args_helper s (c' : ctx)
    : all_fresh c' ->
      length s = length c' ->
      (map var (map fst c')) [/combine_r_padded (map fst c') s /] = s.
  Proof.
    intros H H'.
    rewrite combine_r_padded_eq_len by basic_utils_crush.
    replace (map fst c') with
      (map fst (combine (map fst c') s)) at 2
      by basic_utils_crush.
    rewrite var_args_helper';
      basic_utils_crush.
  Qed.

  
  Lemma map_flat_map A B C (f : B -> C) (g : A -> list B) l
    : map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
    rewrite !map_app.
    congruence.
  Qed.

  
  Lemma incl_flat_map A B (f : A -> list B) x l
    : In x l -> incl (f x) (flat_map f l).
  Proof.
    induction l; basic_goal_prep; basic_utils_crush.
  Qed.
    
  
  Lemma id_compiler_identity l
    : wf_lang l ->
      (forall c t, wf_sort l c t ->
                     compile_sort (id_compiler l) t = t)
      /\ (forall c e t, wf_term l c e t ->
                     compile (id_compiler l) e = e)
      /\ (forall c s c', wf_args l c s c'->
                     compile_args (id_compiler l) s = s).
  Proof.
    intro.
    apply wf_judge_ind;
      basic_goal_prep;
      basic_core_crush.
    all: case_match; symmetry in case_match_eqn; [| exfalso].
    4:eapply term_rule_not_fresh_in_id_compiler; eauto;
    eapply named_list_lookup_none_iff; eauto.
    all: use_rule_in_wf.
    all: set (f:=fun '(name,r) =>
                match r with
                | sort_rule c _ => [(name:V,sort_case (map fst c) (scon name (map var (map fst c))))]
                | term_rule c _ _ => [(name,term_case (map fst c) (con name (map var (map fst c))))]
                | _ => []
                end).
    all: apply incl_flat_map with (f:=f) in H0;
      cbn in H0.
    2:{
      eapply named_list_lookup_none_iff in case_match_eqn.
      eapply case_match_eqn.
      unfold id_compiler.
      rewrite map_flat_map.
      basic_utils_crush.
    }
    {
      eapply named_list_lookup_err_in in case_match_eqn.
      basic_utils_crush.
      eapply in_all_fresh_same in case_match_eqn; eauto;
        subst;
        basic_core_crush.
      change (scon ?n ?s) [/?s'/] with (scon n s[/s'/]).
      f_equal.
      unfold compile_args in *.
      erewrite H2.
      apply var_args_helper;
        basic_core_crush.
      symmetry; eapply wf_args_length_eq; eauto.
    }
    {
      eapply named_list_lookup_err_in in case_match_eqn.
      basic_utils_crush.
      eapply in_all_fresh_same in case_match_eqn; eauto;
        subst;
        basic_core_crush.
      change (con ?n ?s) [/?s'/] with (con n s[/s'/]).
      f_equal.
      unfold compile_args in *.
      erewrite H2.
      apply var_args_helper;
        basic_core_crush.
      symmetry; eapply wf_args_length_eq; eauto.
    }
  Qed.
    
  Lemma id_compiler_identity_ctx l c
    : wf_lang l ->
      wf_ctx l c ->
      compile_ctx (id_compiler l) c = c.
  Proof.
    intro.
    induction 1;
      basic_goal_prep; eauto.
    f_equal; eauto.
    f_equal; eauto.
    eapply id_compiler_identity; eauto.
  Qed.
    
  Lemma id_compiler_preserving' l l'
    : wf_lang l -> incl l l' -> preserving_compiler_ext l' [] (id_compiler l) l.
  Proof.
    induction l;
      basic_goal_prep;
      basic_core_crush.
    destruct r;
      basic_goal_prep;
      constructor;
      basic_utils_crush.
    all: try use_rule_in_wf.
    all: rewrite id_compiler_identity_ctx; 
      basic_core_crush.
    { eapply wf_sort_by; basic_core_crush. }
    {
      replace (compile_sort (id_compiler l) s)
        with s[/with_names_from n (map var (map fst n))/].
      { eapply wf_term_by; basic_core_crush. }
      {
        etransitivity.
        { apply sort_subst_id; eauto. }
        {
          symmetry.
          eapply id_compiler_identity; eauto.
        }
      }
    }
    {
      erewrite !(proj1 (id_compiler_identity H0)); eauto.
      eapply eq_sort_by; eauto.
    }
    {
      erewrite !(proj1 (id_compiler_identity H0)); eauto.
      erewrite !(proj1 (proj2 (id_compiler_identity H0))); eauto.
      eapply eq_term_by; eauto.
    }
  Qed.

  Lemma id_compiler_preserving l
    : wf_lang l -> preserving_compiler_ext l [] (id_compiler l) l.
  Proof.
    intros; apply id_compiler_preserving'; basic_utils_crush.
  Qed.

  Context (tgt : lang).

  Context (l_base : lang).
  Context (src_spec tgt_spec : param_spec).

  
  Lemma lookup_Some_to_pcmp cmp n c
    : let pcmp := (parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base) in
      named_list_lookup_err cmp n = Some c ->
      named_list_lookup_err pcmp n
      = Some (parameterize_ccase p_name tgt_spec src_spec (n,c)).
  Proof.
    induction cmp;
      basic_goal_prep;
      subst;
      basic_goal_prep;
      basic_utils_crush.
    eqb_case n v;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  
  Hint Rewrite map_insert : utils.
  
  Lemma named_map_combine A B (f : A -> B) l1 l2
    : named_map f (combine l1 l2) = combine l1 (map f l2).
  Proof.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite named_map_combine : utils.

  Hint Rewrite skipn_nil firstn_nil combine_nil : utils.

  Lemma combine_skipn A B (l : list A) (l' : list B) (n : nat)
    : skipn n (combine l l') = combine (skipn n l) (skipn n l').
  Proof.
    revert l' n;
      induction l;
      destruct l';
      destruct n;
      basic_goal_prep;
      basic_utils_crush.
  Qed.          
  
  Hint Rewrite firstn_length combine_firstn combine_skipn : utils.
  
  Lemma combine_insert A B n (a:A) (b:B) l1 l2
    : length l1 = length l2 ->
      combine (insert n a l1) (insert n b l2)
      = insert n (a,b) (combine l1 l2).
  Proof.
    unfold insert.
    intros.
    rewrite combine_app by basic_utils_crush.
    basic_goal_prep;
      basic_utils_crush.
  Qed.

  (*TODO: edited from Compilers.v *_plus inductive*)
  

  Lemma fresh_lang_fresh_cmp tgt' cmp_pre cmp l n
    : preserving_compiler_ext tgt' cmp_pre cmp l ->
      fresh n l -> fresh n cmp.
  Proof.
    induction 1; basic_goal_prep;
      basic_core_crush.
  Qed.
  Hint Resolve fresh_lang_fresh_cmp : lang_core.

    Lemma preserving_contradiction tgt' cmp_pre cmp l n r
      : preserving_compiler_ext tgt' cmp_pre cmp l ->
        all_fresh l ->        
        In (n,r) l ->
        match r, named_list_lookup_err cmp n with
        | term_rule _ _ _, Some (term_case _ _)
        | sort_rule _ _, Some (sort_case _ _) => True
        | term_rule _ _ _, None
        | sort_rule _ _, None => False
        | _, Some _ => False
        | _, None => True
        end.
    Proof.
      induction 1;
        basic_goal_prep;
        repeat case_match;
        subst;
        autorewrite with utils in *;
        try tauto;
        intuition (subst;try congruence; eauto with lang_core).
      all: my_case H' (named_list_lookup_err cmp n); cbn in *; try tauto.
      all: autorewrite with utils in *.
      all: try congruence.
      all: try match goal with
           | H : _ = Some _ |- _ =>
               symmetry in H;
               eapply named_list_lookup_err_in in H
             end.
      all: repeat match goal with
             | H : context [ match _ with _ => _ end ] |- _ =>
                 revert H; case_match; eauto; try congruence
             end.
      all: basic_goal_prep; basic_utils_crush.
      all: assert (fresh n cmp) by eauto with lang_core;
                basic_utils_crush.      
    Qed.

    Lemma preserving_args_length tgt' cmp_pre cmp l n r
      : preserving_compiler_ext tgt' cmp_pre cmp l ->
        all_fresh l ->        
        In (n,r) l ->
        match named_list_lookup_err cmp n with
        | Some (term_case args _)
        | Some (sort_case args _) => length args = length (get_ctx r)
        | None => True
        end.
    Proof.
      induction 1;
        basic_goal_prep;
        repeat case_match;
        subst;
        autorewrite with utils in *;
        try tauto;
        intuition (subst;try congruence; eauto with lang_core).
      all: my_case H' (named_list_lookup_err cmp n); cbn in *; try tauto.
      all: autorewrite with utils in *.
      all: try congruence.
      all: try match goal with
           | H : _ = Some _ |- _ =>
               symmetry in H;
               eapply named_list_lookup_err_in in H
             end.
      all: repeat match goal with
             | H : context [ match _ with _ => _ end ] |- _ =>
                 revert H; case_match; eauto; try congruence
             end.
      all: basic_goal_prep; basic_core_crush.
      all: exfalso; eapply fresh_lang_fresh_cmp; eauto.
      all:eapply in_map in H'; eauto; exact H'.
    Qed.

    Definition p_name_fresh_in_cmp : compiler -> Prop :=
      all (fun p => match snd p with
                    | term_case args _
                    | sort_case args _ => ~In p_name args
                    end).

    
    Lemma fresh_combine_r_padded A B (n:A) l (l' : list B) `{WithDefault B}
      : ~In n l -> fresh n (combine_r_padded l l').
    Proof.
      revert l';
        induction l;
        destruct l';
        basic_goal_prep;
        basic_utils_crush.
    Qed.
    Hint Resolve fresh_combine_r_padded : utils.

    Lemma not_in_p_name_cmp_term cmp args e n
      : p_name_fresh_in_cmp cmp ->
        In (n, term_case args e) cmp ->
        ~In p_name args.
    Proof.
      unfold p_name_fresh_in_cmp.
      intros.
      eapply in_all in H; eauto.
      cbn in *.
      auto.
    Qed.
    Hint Resolve not_in_p_name_cmp_term : core.

    
    Lemma not_in_p_name_cmp_sort cmp args e n
      : p_name_fresh_in_cmp cmp ->
        In (n, sort_case args e) cmp ->
        ~In p_name args.
    Proof.
      unfold p_name_fresh_in_cmp.
      intros.
      eapply in_all in H; eauto.
      cbn in *.
      auto.
    Qed.
    Hint Resolve not_in_p_name_cmp_term : core.

    Hint Rewrite @map_fst_combine_r_padded : utils.

    Lemma preserving_compiler_ws tgt' cmp_pre cmp l
      : wf_lang tgt' ->
        preserving_compiler_ext tgt' cmp_pre cmp l ->
        ws_compiler (tgt_Model:=core_model tgt') cmp.
    Proof.
      induction 2; basic_goal_prep; intuition auto.
      {
        eapply well_scoped_change_args;
          try typeclasses eauto.
        {
          change  (@substable_sort V V_Eqb) with  (sort_substable).
          change  (@syntax_model V V_Eqb) with (@premodel V term sort (core_model tgt')) in *.
          eapply Model.wf_sort_implies_ws; eauto.
        }
        {
          unfold compile_ctx.
          rewrite named_map_fst_eq.
          reflexivity.
        }
      }
      {
        eapply well_scoped_change_args.
        - typeclasses eauto.
        - 
          change  (@substable_term V V_Eqb) with  (term_substable).
          change  (@substable_sort V V_Eqb) with  (sort_substable).
          change  (@syntax_model V V_Eqb) with (@premodel V term sort (core_model tgt')) in *.
          eapply Model.wf_term_implies_ws; eauto.
        - unfold compile_ctx.
          rewrite named_map_fst_eq.
          reflexivity.
      }
      Unshelve.
      all: eapply core_model_ok; eauto.
    Qed.
    Hint Resolve preserving_compiler_ws : lang_core.

    Hint Rewrite app_length skipn_length : utils.
    
    Lemma length_insert A n (a:A) l
      : length (insert n a l) = S (length l).
    Proof.
      unfold insert; basic_utils_crush.
      cbn.
      basic_utils_crush.
      Lia.lia.
    Qed.
    Hint Rewrite length_insert : utils.
     
  Lemma compile_parameterize_commute src cmp
    : all_fresh src ->
      wf_lang tgt ->
      p_name_fresh_in_cmp cmp ->
      preserving_compiler_ext tgt [] cmp src ->
      let pcmp := (parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base) in
    (forall c t,
        wf_sort src c t ->
        compile_sort pcmp (parameterize_sort p_name src_spec t)
        = parameterize_sort p_name tgt_spec (compile_sort cmp t))
    /\ (forall c e t, wf_term src c e t ->
        compile pcmp (parameterize_term p_name src_spec e)
        = parameterize_term p_name tgt_spec (compile cmp e))
    /\ (forall c s c',
           Model.wf_args (Model:=core_model src) c s c' ->
           forall mn,
             compile_args pcmp (parameterize_args p_name src_spec mn s)
             = parameterize_args p_name tgt_spec mn (compile_args cmp s)).
  Proof.
    intros.
    apply wf_judge_ind;
      intros.
    {
      cbn.
      my_case H_lookup (named_list_lookup_err cmp n).
      2:{
        eapply preserving_contradiction in H;
        basic_utils_crush.
        all:cbn in *.
        exfalso.
        rewrite H_lookup in H; tauto.
      }
      subst pcmp.
      erewrite lookup_Some_to_pcmp; eauto.
      destruct c0.
      {
        eapply preserving_contradiction in H;
        basic_utils_crush.
        all:cbn in *.
        exfalso.
        rewrite H_lookup in H; tauto.
      }
      cbn.
      rewrite parameterize_sort_subst with (mn:=named_list_lookup_err src_spec n); eauto.
      2:{
        symmetry in H_lookup; apply named_list_lookup_err_in in H_lookup.
        apply fresh_combine_r_padded.
        eapply not_in_p_name_cmp_sort; eauto.
      }
      2:{
        basic_utils_crush.
        assert (ws_compiler (tgt_Model:=core_model tgt) cmp)
          by basic_core_crush.
        symmetry in H_lookup; apply named_list_lookup_err_in in H_lookup.
        eapply in_all in H6; eauto.
        cbn in *; eauto.
      }
      f_equal.
      rewrite !combine_r_padded_eq_len.
      2:{
        eapply preserving_args_length in H3; eauto.
        rewrite H_lookup in H3.
        basic_goal_prep;
          basic_core_crush.
        erewrite <- wf_args_length_eq; eauto.
      }
      2:{
        eapply preserving_args_length in H3; eauto.
        rewrite H_lookup in H3.
        case_match;
          basic_goal_prep;
          basic_core_crush.
        all:erewrite <- wf_args_length_eq; eauto.
      }
      case_match;
        basic_goal_prep;
        basic_utils_crush.
      2:{
        f_equal.
        specialize (H5 None).
        apply H5.
      }
      {
        rewrite combine_insert.
        2: basic_utils_crush.
        2:{
          eapply preserving_args_length in H3; eauto.
          rewrite H_lookup in H3.
          basic_goal_prep;
            basic_core_crush.
          erewrite <- wf_args_length_eq; eauto.
        }
        f_equal; try reflexivity.
        f_equal.
        specialize (H5 None).
        apply H5.
      }
    }
    {
      cbn.
      my_case H_lookup (named_list_lookup_err cmp n).
      2:{
        eapply preserving_contradiction in H;
        basic_utils_crush.
        all:cbn in *.
        exfalso.
        rewrite H_lookup in H; tauto.
      }
      subst pcmp.
      erewrite lookup_Some_to_pcmp; eauto.
      destruct c0.
      2:{
        eapply preserving_contradiction in H;
        basic_utils_crush.
        all:cbn in *.
        exfalso.
        rewrite H_lookup in H; tauto.
      }
      cbn.
      rewrite parameterize_term_subst with (mn:=named_list_lookup_err src_spec n); eauto.
      2:{
        symmetry in H_lookup; apply named_list_lookup_err_in in H_lookup.
        apply fresh_combine_r_padded.
        eapply not_in_p_name_cmp_term; eauto.
      }
      2:{
        basic_utils_crush.
        assert (ws_compiler (tgt_Model:=core_model tgt) cmp)
          by basic_core_crush.
        symmetry in H_lookup; apply named_list_lookup_err_in in H_lookup.
        eapply in_all in H6; eauto.
        cbn in *; eauto.
      }
      f_equal.
      rewrite !combine_r_padded_eq_len.
      2:{
        eapply preserving_args_length in H3; eauto.
        rewrite H_lookup in H3.
        basic_goal_prep;
          basic_core_crush.
        erewrite <- wf_args_length_eq; eauto.
      }
      2:{
        eapply preserving_args_length in H3; eauto.
        rewrite H_lookup in H3.
        case_match;
          basic_goal_prep;
          basic_core_crush.
        all:erewrite <- wf_args_length_eq; eauto.
      }
      case_match;
        basic_goal_prep;
        basic_utils_crush.
      2:{
        f_equal.
        specialize (H5 None).
        apply H5.
      }
      {
        rewrite combine_insert.
        2: basic_utils_crush.
      2:{
        eapply preserving_args_length in H3; eauto.
        rewrite H_lookup in H3.
        basic_goal_prep;
          basic_core_crush.
        erewrite <- wf_args_length_eq; eauto.
      }
        f_equal; try reflexivity.
        f_equal.
        specialize (H5 None).
        apply H5.        
      }
    }
    all: eauto.
    {
      destruct mn; cbn;
        basic_utils_crush.
      unfold compile_args.
      cbn.
      basic_utils_crush.
    }
    {
      unfold compile_args in *.
      destruct mn; cbn;
        basic_utils_crush.
      2:{
        specialize (H6 None).
        basic_utils_crush.
      }
      {
        specialize (H6 None).
        cbn -[insert].
        basic_utils_crush.
      }
    }
  Qed.

  Hint Rewrite insert_nil : utils.

  
  Context (Hwfl_base: wf_lang l_base).
  Context (Hwf_p_sort : wf_sort l_base {{c }} p_sort).

  
  (*TODO: move to utils.*)
  Lemma fresh_incl A B n (a : named_list A) (b : named_list B)
    : incl (map fst b) (map fst a) -> fresh n a -> fresh n b.
  Proof.
    unfold fresh, incl.
    generalize (map fst a) (map fst b).
    clear a b.
    basic_goal_prep;
      basic_utils_crush.
  Qed.

  Lemma sublist_incl A (l1 l2 : list A)
    : sublist l1 l2 -> incl l1 l2.
  Proof.
    revert l1;
      induction l2;
      destruct l1; 
      basic_goal_prep;
      basic_utils_crush.
  Qed.
    
  Lemma all_fresh_sublist A B (a : named_list A) (b : named_list B)
    : sublist (map fst b) (map fst a) -> all_fresh a -> all_fresh b.
  Proof.
    revert b;
      induction a;
      destruct b;
      basic_goal_prep;
      basic_utils_crush.

    {
      eapply fresh_incl; eauto using sublist_incl.
    }
    {
      specialize (IHa ((v,b0)::b)).
      eapply IHa in H0; eauto.
      cbn in *.
      intuition subst.
    }
  Qed.
  
  Lemma sublist_app_hom A (l1 l1' l2 l2' : list A)
    : sublist l1 l1' ->
      sublist l2 l2' ->
      sublist (l1++l2) (l1'++l2').
  Proof.
    revert l1;
      induction l1';
      destruct l1;
      basic_goal_prep;
      basic_utils_crush.
    {
      destruct l2; eauto.
      right.
      eauto using sublist_app_r.
    }
    {
      right.
      change (a0 :: l1 ++ l2)
        with ((a0 :: l1) ++ l2).
      eapply IHl1'; eauto.
    }
  Qed.
  
  Lemma preserving_compiler_sublist tgt' cmp_pre cmp src
    : preserving_compiler_ext tgt' cmp_pre cmp src ->
      sublist (map fst cmp) (map fst src).
  Proof.
    induction 1;
      basic_goal_prep;
      basic_utils_crush.
    all: destruct cmp; cbn; eauto.
  Qed.

  (*TODO: move somewhere*)
  Hint Resolve core_model_ok id_compiler_preserving : lang_core.
    
  Lemma compile_p_sort cmp src
    : all_fresh (src ++ l_base) ->
      p_name_fresh_in_cmp cmp ->
      preserving_compiler_ext tgt [] cmp src ->
      let pcmp := (parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base) in
      compile_sort pcmp p_sort = p_sort.
  Proof.
    intros.
    replace (compile_sort pcmp p_sort) with (compile_sort (id_compiler l_base) p_sort).
    {
      eapply id_compiler_identity; eauto.
    }
    {
      subst pcmp.
      symmetry.
      change (@syntax_model V V_Eqb) with (@premodel V _ _ (core_model l_base)).
      eapply strengthening_sort; eauto.
      {
        eapply strengthen_preserving_compiler; eauto;
          basic_core_crush.
      }
      {
        unfold parameterize_compiler.
        basic_utils_crush.
        eapply all_fresh_sublist; try eassumption.
        rewrite !map_app.
        eapply sublist_app_hom; eauto.
        2:{
          eapply preserving_compiler_sublist.
          eapply id_compiler_preserving.
          auto.
        }
        rewrite map_map.
        cbn.
        eapply preserving_compiler_sublist; eauto.
      }
    }
  Qed.

  
  Lemma named_map_insert A B (f : A -> B) n a lst
    : named_map f (insert n a lst) = insert n (fst a, f (snd a)) (named_map f lst).
  Proof.
    unfold named_map.
    rewrite map_insert.
    unfold pair_map_snd.
    break; reflexivity.
  Qed.
  Hint Rewrite named_map_insert : utils.
  
  Lemma compile_parameterize_commute_ctx src cmp
    : all_fresh (src++l_base) ->
      wf_lang tgt ->
      p_name_fresh_in_cmp cmp ->
      preserving_compiler_ext tgt [] cmp src ->
      let pcmp := (parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base) in
      forall c,
        wf_ctx src c ->
        forall mn,
        compile_ctx pcmp (parameterize_ctx p_name p_sort src_spec mn c)
        = parameterize_ctx p_name p_sort tgt_spec mn (compile_ctx cmp c).
  Proof.
    intros until c.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    {
      destruct mn; cbn; eauto.
      basic_utils_crush.
      cbn.
      subst pcmp. erewrite compile_p_sort; eauto.
    }
    {
      unfold parameterize_ctx.
      case_match.
      2:{
        cbn in *.
        specialize (IHwf_ctx None).
        f_equal; eauto.
        f_equal.
        eapply compile_parameterize_commute.
        5:eauto.
        all: eauto.
        basic_utils_crush.
        eapply all_fresh_app_l; eauto.
      }
      {
        subst.
        unfold compile_ctx in *.
        basic_utils_crush.
        cbn -[insert]  in*.
        destruct a.
        {
          cbn.
          subst pcmp.
          erewrite !compile_p_sort; eauto.
          f_equal.
          f_equal.
          {
            f_equal.
            eapply compile_parameterize_commute.
            5:eauto.
            all: eauto.
            basic_utils_crush.
            eapply all_fresh_app_l; eauto.
          }
          {
            specialize (IHwf_ctx None); eauto.
          }
        }
        {
          rewrite !insert_S.
          subst pcmp.
          erewrite !compile_p_sort; eauto.
          f_equal.
          {
            f_equal.
            eapply compile_parameterize_commute.
            5:eauto.
            all: eauto.
            basic_utils_crush.
            eapply all_fresh_app_l; eauto.
          }
          {
            specialize (IHwf_ctx (Some (a,b))).
            cbn -[insert] in *.
            basic_utils_crush.
            cbn -[insert] in *.
            erewrite !compile_p_sort in *; eauto.
          }
        }
      }
    }
  Qed.
        
  Fixpoint constructors_containing_vars vars e :=
    match e with
    | var _ => []
    | con n s =>
        if existsb (fun x => inb x vars) (fv_args s)
        then let cs := flat_map (constructors_containing_vars vars) s in
             n::cs
        else []
    end.

  Definition sort_constructors_containing_vars vars e :=
    match e with
    | scon n s =>
        if existsb (fun x => inb x vars) (fv_args s)
        then let cs := flat_map (constructors_containing_vars vars) s in
             n::cs
        else []
    end.
        
  
  Definition specs_compatibleb : compiler -> bool :=
    forallb (fun '(name, cc) =>
               match cc with
               | sort_case args t => 
                   match named_list_lookup_err src_spec name with
                   | Some n0 =>
                       true (*forallb (fun n => inb n (map fst tgt_spec))
                         (sort_constructors_containing_vars (firstn (fst n0) args) t)*)
                   | None => forallb (fun n => freshb n tgt_spec) (constructors_of_sort t)
                   end
               | term_case args e =>
                   match named_list_lookup_err src_spec name with
                   | Some n0 =>
                       true
                       (*forallb (fun n => inb n (map fst tgt_spec))
                         (constructors_containing_vars (firstn (fst n0) args) e)*)
                   | None => forallb (fun n => freshb n tgt_spec) (constructors_of e)
                   end
               end).


  Hint Rewrite Is_true_forallb:utils.

  
  Definition compiler_respects_parameterization l cmp :=
    forall n num x r,
      In (n, r) l ->
      (In (n,(num,x)) src_spec
       \/ (num = 0 /\ fresh n src_spec)) ->
      all (fun n0 : V => fresh n0 tgt_spec)
        (constructors_of_ctx (skipn num (compile_ctx cmp (get_ctx r)))).

  Definition compiler_respects_parameterizationb l cmp : bool :=
    let P '(n,r) :=
      let num_skip :=
        match named_list_lookup_err src_spec n with
        | Some p => fst p
        | None => 0
        end in
      forallb (fun n0 : V => freshb n0 tgt_spec)
        (constructors_of_ctx (skipn num_skip (compile_ctx cmp (get_ctx r))))
    in
    forallb P l.
  

  (* TODO: move to Utils *)
  Hint Rewrite Is_true_true : utils.

  Lemma all_impl A (P Q : A -> Prop) l
    : (forall a, P a -> Q a) -> all P l -> all Q l.
  Proof.
    intro Hpq.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.


  Lemma Is_true_freshb A x (l : named_list A)
    : Is_true (freshb x l) <-> fresh x l.
  Proof.
    unfold fresh, freshb.
    induction l;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite Is_true_freshb : utils.

  Context (H_src_fresh : all_fresh src_spec).
  
  Lemma compiler_respects_parameterizationb_spec l cmp
    : all_fresh l ->
      Is_true (compiler_respects_parameterizationb l cmp)
      <-> compiler_respects_parameterization l cmp.
  Proof.
    intro Hfresh.
    unfold compiler_respects_parameterizationb, compiler_respects_parameterization.
    autorewrite with utils.
    split.
    {
      intros.
      eapply in_all in H; eauto.
      basic_goal_prep.

      destruct H1; basic_goal_prep;
        autorewrite with utils in *;
        eauto.
      {
        replace (named_list_lookup_err src_spec n)
          with (Some (num,x)) in H.
        1:eapply all_impl; eauto; basic_goal_prep;
        basic_utils_crush.
        clear H.
        apply all_fresh_named_list_lookup_err_in; eauto.
      }
      {
        subst.
        replace (named_list_lookup_err src_spec n)
          with (@None (nat * bool)) in H.
        1:eapply all_impl; eauto; basic_goal_prep;
        basic_utils_crush.
        clear H.
        apply named_list_lookup_none_iff; eauto.
      }
    }
    {
      intros.
      eapply all_in;
        basic_goal_prep.
      autorewrite with utils in *;
        eauto.
      case_match;
        symmetry in case_match_eqn;
        basic_goal_prep.
      1: apply named_list_lookup_err_in in case_match_eqn.
      2: apply named_list_lookup_none_iff in case_match_eqn.
      all: eapply H in H0; intuition eauto.
      all:eapply all_impl; eauto; basic_goal_prep;
        basic_utils_crush.      
    }
    Unshelve.
    (*TODO: where is this from?*)
    constructor.
  Qed.
      
  Lemma parameterize_compiler_preserving' cmp src (H_ordered_src: pl_is_ordered src_spec src)
    : wf_lang tgt ->
      Is_true (syntactic_parameterization_conditions' tgt_spec l_base tgt) ->
      Is_true (compiler_respects_parameterizationb src cmp) ->
      pl_is_ordered tgt_spec tgt ->
      preserving_compiler_ext tgt [] cmp src ->
      wf_lang src ->
      p_name_fresh_in_cmp cmp ->
      all_fresh (src++l_base) ->
      Is_true (specs_compatibleb cmp) ->
      preserving_compiler_ext (parameterize_lang tgt_spec tgt ++ l_base)
        (id_compiler l_base)
        (parameterize_compiler p_name tgt_spec src_spec cmp)
        (parameterize_lang src_spec src).
  Proof.
    intros wft H_b H_respectsb H_ord H H0.
    rewrite compiler_respects_parameterizationb_spec in *;[|basic_core_crush].
    unfold compiler_respects_parameterization in *.
    intros H1 H2 H3.
    assert(
        exists (*spec'*) src' cmp',
        (forall (n : V) (num : nat) (x : bool) (r : rule),
                In (n, r) src' ->
                In (n, (num, x)) src_spec \/
                num = 0 /\ fresh n src_spec ->
                all (fun n0 : V => fresh n0 tgt_spec)
                  (constructors_of_ctx (skipn num (compile_ctx cmp' (get_ctx r)))))
        /\ Is_true (specs_compatibleb cmp')
        /\ wf_lang src'
        /\ preserving_compiler_ext tgt [] cmp' src'
        /\ incl src src'
        (*/\ incl src_spec spec'*)
        /\ incl cmp cmp'
        /\ all_fresh cmp'
        /\ pl_is_ordered src_spec src'
      ).
    {
      exists (*src_spec,*) src, cmp.
      intuition eauto using incl_refl.
      eapply strengthen_preserving_compiler in H; auto; basic_core_crush.
    }
    revert H1 H2 H3.
(*    assert (exists spec' src' cmp',
                (forall (n : V) (p : nat * bool) (r : rule),
                In (n, p) spec' ->
                In (n, r) src' ->
                all (fun n0 : V => fresh n0 tgt_spec)
                  (constructors_of_ctx
                     (skipn (fst p) (compile_ctx cmp' (get_ctx r)))))
                /\ incl src src'
                /\ incl src_spec spec'
                /\ incl cmp cmp'
                /\ all_fresh cmp').
    {
      exists src_spec, src.
      eauto using incl_refl.
    }*)
    clear H_respectsb H_ordered_src.
    break.
    rename H1 into H_respectsb.
    (*rename H3 into Hincl_spec.*)
    rename H2 into Hincl_src.
    rename H3 into Hincl_cmp.
    rename H4 into Hfresh_cmp.
    rename H8 into H_ordered_src.
    revert H H0 (*Hincl_spec*) Hincl_src Hincl_cmp.
    unfold parameterize_lang, parameterize_compiler.


(*

 V : Type
  V_Eqb : Eqb V
  V_Eqb_ok : Eqb_ok V_Eqb
  V_default : WithDefault V
  p_name : V
  p_sort : sort
  tgt, l_base : lang
  src_spec, tgt_spec : param_spec
  Hwfl_base : wf_lang l_base
  Hwf_p_sort : wf_sort l_base {{c }} p_sort
  H_src_fresh : all_fresh src_spec
  cmp : compiler
  src : lang
  wft : wf_lang tgt
  H_b : Is_true (syntactic_parameterization_conditions' tgt_spec l_base tgt)
  H_ord : pl_is_ordered tgt_spec tgt
  x : list (V * rule)
  x0 : compiler
  H_respectsb : forall (n : V) (num : nat) (x1 : bool) (r : rule),
                In (n, r) x ->
                In (n, (num, x1)) src_spec \/ num = 0 /\ fresh n src_spec ->
                all (fun n0 : V => fresh n0 tgt_spec)
                  (constructors_of_ctx (skipn num (compile_ctx x0 (get_ctx r))))
  Hfresh_cmp : preserving_compiler_ext tgt [] x0 x
  H5 : incl src x
  H6 : incl cmp x0
  H7 : all_fresh x0
  H_ordered_src : pl_is_ordered src_spec x
  ============================
  preserving_compiler_ext tgt [] cmp src ->
  wf_lang src ->
  Is_true (specs_compatibleb x0) ->
  wf_lang x ->
  p_name_fresh_in_cmp cmp ->
  all_fresh (src ++ l_base) ->
  Is_true (specs_compatibleb cmp) ->
  preserving_compiler_ext
    (map (fun p : V * rule => (fst p, parameterize_rule p_name p_sort tgt_spec p)) tgt ++
     l_base) (id_compiler l_base)
    (map
       (fun p : V * compiler_case V => (fst p, parameterize_ccase p_name tgt_spec src_spec p))
       cmp) (map (fun p : V * rule => (fst p, parameterize_rule p_name p_sort src_spec p)) src)



*)


    
    
    induction 1; intros; cbn [map fst] in *.
    { constructor. }
    {
      cbn -[parameterize_ctx parameterize_compiler].
      replace (match named_list_lookup_err src_spec n with
               | Some n0 => insert (fst n0) p_name (map fst c)
               | None => map fst c
               end)
        with (map fst (parameterize_ctx p_name p_sort src_spec (named_list_lookup_err src_spec n) c)).
      {
        eapply CompilerDefs.preserving_compiler_sort; eauto.
        {
          eapply IHpreserving_compiler_ext; eauto.
          all: basic_goal_prep; basic_core_crush.
        }
        cbn -[parameterize_ctx parameterize_compiler].
        pose proof H as Hpres.
        eapply compile_parameterize_commute_ctx in H;
          [| basic_goal_prep; basic_utils_crush..].
        {
          unfold parameterize_lang, parameterize_compiler in H.
          erewrite H; eauto.
          eapply eq_sort_wf_r; eauto.
          {
            eapply wf_lang_concat; eauto.
            eapply parameterize_lang_preserving''; eauto.
          }
          {
            eapply parameterize_ctx_preserving'; eauto.
            {
              eapply wf_lang_concat; eauto.
              eapply parameterize_lang_preserving''; eauto.
            }
            {
              unfold syntactic_parameterization_conditions' in *;
                basic_utils_crush.
              match goal with
              | [H : all ?P ?l |- all _ ?l] =>
                  match P with context[freshb] => idtac end;
                  eapply all_in; try eapply H; intros
              end.
              eapply in_all in H6; eauto.
              eapply use_compute_fresh; eauto.
            }
            {
              unfold syntactic_parameterization_conditions' in *;
                basic_utils_crush.
            }
            
            {
              unfold syntactic_parameterization_conditions' in *;
                basic_utils_crush.
              eapply compute_pl_indices_sound;
                basic_utils_crush.
            }
            {
              
              eapply inductive_implies_semantic; cycle 6;
                eauto;
                basic_core_crush.
            }
            {
              revert H2; clear.
              cbn.
              intros; basic_goal_prep;
                unfold compile_ctx;
                basic_core_crush.
            }
            case_match.
            {
              break.
              cbn in *.
              break.
              
              replace (compile_ctx cmp c) with (compile_ctx x0 c).
              {
                break.
                eapply H_respectsb with (r:=sort_rule c args);
                  cbn;eauto.
                1: basic_utils_crush.
                left.
                apply named_list_lookup_err_in; eauto.
              }
              {
                autorewrite with utils lang_core in *.
                break.
                eapply strengthening_ctx; eauto.
              }
            }
            {
              replace (compile_ctx cmp c)
                with (skipn 0 (compile_ctx cmp c)).
              {
                change c with (get_ctx (sort_rule c args)).
                erewrite <- strengthening_ctx;
                  try eassumption.
                {
                  eapply H_respectsb.
                  1: basic_utils_crush.
                  right; intuition eauto.
                  apply named_list_lookup_none_iff; eauto.
                }
                all: cbn; basic_core_crush.
              }
              {
                autorewrite with utils lang_core in *.
                break.                
                basic_utils_crush.
              }
            }
          }
          {
            eapply parameterize_preserving'; eauto.
            {
              apply wf_lang_concat; eauto.
              eapply parameterize_lang_preserving''; eauto.
            }
            5:{ eapply eq_sort_refl; basic_core_crush. }
            all: break; cbn in *.
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              eapply all_impl; eauto.
              basic_goal_prep;
                basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              apply compute_pl_indices_sound;
                basic_utils_crush.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2;
              eauto with lang_core.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2;
              eauto with lang_core.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              case_match; basic_utils_crush.
              destruct t; cbn in*.
              basic_utils_crush.
            }
          }
        }
        {
          basic_core_crush.
        }
      }
      {
        case_match; basic_goal_prep;
          basic_utils_crush.
        all: cbn.
        all: rewrite map_fst_named_map;
          reflexivity.
      }
    }
    {
      cbn -[parameterize_ctx parameterize_compiler].
      replace (match named_list_lookup_err src_spec n with
               | Some n0 => insert (fst n0) p_name (map fst c)
               | None => map fst c
               end)
        with (map fst (parameterize_ctx p_name p_sort src_spec (named_list_lookup_err src_spec n) c)).
      {
        eapply CompilerDefs.preserving_compiler_term; eauto.
        {
          eapply IHpreserving_compiler_ext; eauto.
          all: basic_goal_prep; basic_core_crush.
        }
        cbn -[parameterize_ctx parameterize_compiler].
        pose proof H as Hpres.
        eapply  compile_parameterize_commute_ctx in H;
          [| basic_goal_prep; basic_utils_crush..].
        {
          unfold parameterize_lang, parameterize_compiler in H.
          erewrite H; eauto.
          eapply eq_term_wf_r; eauto.
          {
            eapply wf_lang_concat; eauto.
            eapply parameterize_lang_preserving''; eauto.
          }
          {
            eapply parameterize_ctx_preserving'; eauto.
            {
              eapply wf_lang_concat; eauto.
              eapply parameterize_lang_preserving''; eauto.
            }
            {
              unfold syntactic_parameterization_conditions' in *;
                basic_utils_crush.
              eapply all_in; intros.
              eapply in_all in H6; eauto.
              eapply use_compute_fresh; eauto.
            }
            {
              unfold syntactic_parameterization_conditions' in *;
                basic_utils_crush.
            }
            
            {
              unfold syntactic_parameterization_conditions' in *;
                basic_utils_crush.
              eapply compute_pl_indices_sound;
                basic_utils_crush.
            }
            {
              
              eapply inductive_implies_semantic; cycle 6;
                eauto;
                basic_core_crush.
            }
            {
              revert H2; clear.
              cbn.
              intros; basic_goal_prep;
                unfold compile_ctx;
                basic_core_crush.
            }
            case_match.
            {
              break.
              cbn in *.
              break.
              
              replace (compile_ctx cmp c) with (compile_ctx x0 c).
              {
                break.
                eapply H_respectsb with (r:=term_rule c args t);
                  cbn;eauto.
                1: basic_utils_crush.
                left.
                apply named_list_lookup_err_in; eauto.
              }
              {
                autorewrite with utils lang_core in *.
                break.
                eapply strengthening_ctx; eauto.
              }
            }
            {
              replace (compile_ctx cmp c)
                with (skipn 0 (compile_ctx cmp c)).
              {
                change c with (get_ctx (term_rule c args t)).
                erewrite <- strengthening_ctx;
                  try eassumption.
                {
                  eapply H_respectsb.
                  1: basic_utils_crush.
                  right; intuition eauto.
                  apply named_list_lookup_none_iff; eauto.
                }
                all: cbn; basic_core_crush.
              }
              {
                autorewrite with utils lang_core in *.
                break.                
                basic_utils_crush.
              }
            }
          }
          {
            change (compile_sort (map (fun p : V * compiler_case V => (fst p, parameterize_ccase p_name tgt_spec src_spec p)) cmp ++ id_compiler l_base)
                        (parameterize_sort p_name src_spec t))
              with (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                    in compile_sort pcmp (parameterize_sort p_name src_spec t)).
            replace  (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                      in compile_sort pcmp (parameterize_sort p_name src_spec t))
              with (parameterize_sort p_name tgt_spec (compile_sort cmp t)).
            2:{
              symmetry.
              basic_core_crush.
              cbn in *.
              eapply compile_parameterize_commute; eauto.
              1:basic_core_crush.
              {
                unfold syntactic_parameterization_conditions' in *;
                  basic_utils_crush.
              }
            }
            eapply parameterize_preserving'; eauto.
            {
              apply wf_lang_concat; eauto.
              eauto using parameterize_lang_preserving''.
            }
            5:{ eapply eq_term_refl; basic_core_crush. }
            all: break; cbn in *.
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              eapply all_impl; eauto.
              basic_goal_prep;
                basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              apply compute_pl_indices_sound;
                basic_utils_crush.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2; eauto with lang_core.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2; eauto with lang_core.
            }
            {
              replace (compile_sort cmp t)
                with (compile_sort x0 t).
              {
                unfold syntactic_parameterization_conditions' in *.
                basic_utils_crush.
                case_match; basic_utils_crush.
                use_rule_in_wf.
                autorewrite with lang_core model term utils in H2.
                break.
                inversion H23; subst.
                (*TODO: names off by 1*)
                unfold specs_compatibleb in Hincl_src.
                autorewrite with lang_core model term utils in Hincl_src.
                eapply sort_case_in_cmp in H24; eauto.
                break.
                eapply in_all in Hincl_src; eauto.
                cbn in *.
                eapply all_fresh_named_list_lookup_err_in in H24;
                  eauto.
                rewrite <- H24.
                destruct x2; cbn.
                revert Hincl_src; case_match;
                  basic_goal_prep.
                2:{
                  basic_utils_crush.
                } 
                enough (fresh n0 src_spec).
                {
                  symmetry in case_match_eqn0.
                  eapply all_fresh_named_list_lookup_err_in in case_match_eqn0; eauto.
                  eapply pair_fst_in in case_match_eqn0.
                  unfold fresh in *; eauto.
                }
                
                assert (dependency x n n0) as Hdep.
                {
                  eapply dep_direct.
                  unfold direct_dependency.
                  eapply all_fresh_named_list_lookup_err_in in H12; eauto.
                  2: basic_core_crush.
                  rewrite <- H12.
                  cbn.
                  clear.
                  basic_utils_crush.
                }
                unfold pl_is_ordered in H_ordered_src.
                eapply in_all in H_ordered_src; eauto.
                cbn in *.
                eapply H_ordered_src in Hdep.
                eapply Hdep.
                symmetry in case_match_eqn.
                eapply named_list_lookup_none_iff in case_match_eqn; eauto.
              }
              {
                autorewrite with lang_core utils term in *.
                symmetry.
                eapply compile_strengthen_sort_incl; intuition eauto.
                all: eauto with lang_core term model utils.
                {
                  eapply all_fresh_compiler.
                  {
                    eapply strengthen_preserving_compiler; cycle 6; eauto with lang_core.
                  }
                  basic_core_crush.
                }
                {
                  eapply all_constructors_sort_from_wf; eauto.
                  eapply strengthen_preserving_compiler; cycle 6; eauto with lang_core.
                }
              }
            }
          }
        }
        {
          basic_core_crush.
        }
      }
      {
        case_match; basic_goal_prep;
          basic_utils_crush.
        all: cbn.
        all: rewrite map_fst_named_map;
          reflexivity.
      }
    }
    {
      cbn -[parameterize_ctx parameterize_compiler].
      eapply CompilerDefs.preserving_compiler_sort_eq; eauto.
      {
        eapply IHpreserving_compiler_ext; eauto.
        all: basic_goal_prep; basic_core_crush.
      }
      cbn -[parameterize_ctx parameterize_compiler].
      pose proof H as Hpres.
      eapply  compile_parameterize_commute_ctx in H;
          [| basic_goal_prep; basic_utils_crush..].
        {
          unfold parameterize_lang, parameterize_compiler in H.
          erewrite H; eauto.


          change (compile_sort (map (fun p : V * compiler_case V =>
                                       (fst p, parameterize_ccase p_name tgt_spec src_spec p)) cmp ++ id_compiler l_base)
                        (parameterize_sort p_name src_spec ?t))
            with (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                  in compile_sort pcmp (parameterize_sort p_name src_spec t)).
          replace  (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                    in compile_sort pcmp (parameterize_sort p_name src_spec t1))
            with (parameterize_sort p_name tgt_spec (compile_sort cmp t1)).
          2:{
            symmetry.
            basic_core_crush.
            cbn in *.
            eapply compile_parameterize_commute; eauto.
            1:basic_core_crush.
          }
          replace  (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                    in compile_sort pcmp (parameterize_sort p_name src_spec t2))
            with (parameterize_sort p_name tgt_spec (compile_sort cmp t2)).
          2:{
            symmetry.
            basic_core_crush.
            cbn in *.
            eapply compile_parameterize_commute; eauto.
            1:basic_core_crush.
          }
          eapply parameterize_preserving'; auto.
            {
              apply wf_lang_concat; eauto.
              eapply parameterize_lang_preserving''; eauto.
            }
            5:{ basic_core_crush. }
            all: break; cbn in *.
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              eapply all_impl; eauto.
              basic_goal_prep;
                basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              apply compute_pl_indices_sound;
                basic_utils_crush.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2;
              eauto with lang_core.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic;auto; cycle 2;
              eauto with lang_core.
            }
            {
              replace (compile_sort cmp t1)
                with (compile_sort x0 t1).
              {
                unfold syntactic_parameterization_conditions' in *.
                basic_utils_crush.
                case_match; basic_utils_crush.
                use_rule_in_wf.
                autorewrite with lang_core model term utils in H8.
                break.
                inversion H19; subst.
                (*TODO: names off by 1*)
                unfold specs_compatibleb in Hincl_src.
                autorewrite with lang_core model term utils in Hincl_src.
                eapply sort_case_in_cmp in H21; eauto.
                break.
                eapply in_all in Hincl_src; eauto.
                cbn in *.
                eapply all_fresh_named_list_lookup_err_in in H21;
                  eauto.
                rewrite <- H21.
                destruct x2; cbn.
                revert Hincl_src; case_match;
                  basic_goal_prep.
                2:{
                  basic_utils_crush.
                }
                enough (fresh n0 src_spec).
                {
                  symmetry in case_match_eqn0.
                  eapply all_fresh_named_list_lookup_err_in in case_match_eqn0; eauto.
                  eapply pair_fst_in in case_match_eqn0.
                  unfold fresh in *; eauto.
                }
                
                assert (dependency x n n0) as Hdep.
                {
                  eapply dep_direct.
                  unfold direct_dependency.
                  eapply all_fresh_named_list_lookup_err_in in H11; eauto.
                  2: basic_core_crush.
                  rewrite <- H11.
                  cbn.
                  clear.
                  basic_utils_crush.
                }
                unfold pl_is_ordered in H_ordered_src.
                eapply in_all in H_ordered_src; eauto.
                cbn in *.
                eapply H_ordered_src in Hdep.
                eapply Hdep.
                symmetry in case_match_eqn.
                eapply named_list_lookup_none_iff in case_match_eqn; eauto.
              }
              {
                autorewrite with lang_core utils term in *.
                symmetry.
                eapply compile_strengthen_sort_incl; intuition eauto.
                all: eauto with lang_core term model utils.
                {
                  eapply all_fresh_compiler.
                  {
                    eapply strengthen_preserving_compiler; cycle 6; eauto with lang_core.
                  }
                  basic_core_crush.
                }
                {
                  eapply all_constructors_sort_from_wf; eauto.
                  eapply strengthen_preserving_compiler; cycle 6; eauto with lang_core.
                }
              }
            }
          }
        {
          basic_core_crush.
        }
    }
    {
      cbn -[parameterize_ctx parameterize_compiler].
      eapply CompilerDefs.preserving_compiler_term_eq; eauto.
      {
        eapply IHpreserving_compiler_ext; eauto.
        all: basic_goal_prep; basic_core_crush.
      }
      cbn -[parameterize_ctx parameterize_compiler].
      pose proof H as Hpres.
      eapply  compile_parameterize_commute_ctx in H;
          [| basic_goal_prep; basic_utils_crush..].
        {
          unfold parameterize_lang, parameterize_compiler in H.
          erewrite H; eauto.


          change (compile_sort (map (fun p : V * compiler_case V =>
                                       (fst p, parameterize_ccase p_name tgt_spec src_spec p)) cmp ++ id_compiler l_base)
                        (parameterize_sort p_name src_spec ?t))
            with (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                  in compile_sort pcmp (parameterize_sort p_name src_spec t)).
          replace  (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                    in compile_sort pcmp (parameterize_sort p_name src_spec t))
            with (parameterize_sort p_name tgt_spec (compile_sort cmp t)).
          2:{
            symmetry.
            basic_core_crush.
            cbn in *.
            eapply compile_parameterize_commute; eauto.
            1:basic_core_crush.
          }
          replace  (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                    in compile pcmp (parameterize_term p_name src_spec e1))
            with (parameterize_term p_name tgt_spec (compile cmp e1)).
          2:{
            symmetry.
            basic_core_crush.
            cbn in *.
            eapply compile_parameterize_commute; eauto.
            1:basic_core_crush.
          }
          replace  (let pcmp := parameterize_compiler p_name tgt_spec src_spec cmp ++ id_compiler l_base
                    in compile pcmp (parameterize_term p_name src_spec e2))
            with (parameterize_term p_name tgt_spec (compile cmp e2)).
          2:{
            symmetry.
            basic_core_crush.
            cbn in *.
            eapply compile_parameterize_commute; eauto.
            1:basic_core_crush.
          }
          eapply parameterize_preserving'; auto.
            {
              apply wf_lang_concat; eauto.
              eapply parameterize_lang_preserving''; eauto.
            }
            5:{ basic_core_crush. }
            all: break; cbn in *.
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              eapply all_impl; eauto.
              basic_goal_prep;
                basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
            }
            {
              unfold syntactic_parameterization_conditions' in *.
              basic_utils_crush.
              apply compute_pl_indices_sound;
                basic_utils_crush.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2;
              eauto with lang_core.
            }
            {
              autorewrite with lang_core model utils in *.
              break.
              eapply inductive_implies_semantic; auto; cycle 2;
                eauto with lang_core.
            }
            {
              replace (compile_sort cmp t)
                with (compile_sort x0 t).
              {
                unfold syntactic_parameterization_conditions' in *.
                basic_utils_crush.
                case_match; basic_utils_crush.
                use_rule_in_wf.
                autorewrite with lang_core model term utils in H8.
                break.
                inversion H21; subst.
                (*TODO: names off by 1*)
                unfold specs_compatibleb in Hincl_src.
                autorewrite with lang_core model term utils in Hincl_src.
                eapply sort_case_in_cmp in H22; eauto.
                break.
                eapply in_all in Hincl_src; eauto.
                cbn in *.
                eapply all_fresh_named_list_lookup_err_in in H22;
                  eauto.
                rewrite <- H22.
                destruct x2; cbn.
                revert Hincl_src; case_match;
                  basic_goal_prep.
                2:{
                  basic_utils_crush.
                }  
                enough (fresh n0 src_spec).
                {
                  symmetry in case_match_eqn0.
                  eapply all_fresh_named_list_lookup_err_in in case_match_eqn0; eauto.
                  eapply pair_fst_in in case_match_eqn0.
                  unfold fresh in *; eauto.
                }
                
                assert (dependency x n n0) as Hdep.
                {
                  eapply dep_direct.
                  unfold direct_dependency.
                  eapply all_fresh_named_list_lookup_err_in in H11; eauto.
                  2: basic_core_crush.
                  rewrite <- H11.
                  cbn.
                  clear.
                  basic_utils_crush.
                }
                unfold pl_is_ordered in H_ordered_src.
                eapply in_all in H_ordered_src; eauto.
                cbn in *.
                eapply H_ordered_src in Hdep.
                eapply Hdep.
                symmetry in case_match_eqn.
                eapply named_list_lookup_none_iff in case_match_eqn; eauto.
              }
              {
                autorewrite with lang_core utils term in *.
                symmetry.
                eapply compile_strengthen_sort_incl; intuition eauto.
                all: eauto with lang_core term model utils.
                {
                  eapply all_fresh_compiler.
                  {
                    eapply strengthen_preserving_compiler; cycle 6; eauto with lang_core.
                  }
                  basic_core_crush.
                }
                {
                  eapply all_constructors_sort_from_wf; eauto.
                  eapply strengthen_preserving_compiler; cycle 6; eauto with lang_core.
                }
              }
            }
          }
        {
          basic_core_crush.
        }
    }
    Unshelve.
    all:constructor.
  Qed.



      Definition sort_elem_constructors (l : lang) sname :=
      flat_map (fun '(n,r) =>
                    match r with
                    | term_eq_rule _ _ _ t
                    | term_rule _ _ t =>
                        if eqb (sort_name t) sname then [n] else []
                    | _ => []
                    end) l.
    

    Definition compute_direct_dependencies (l : lang) n :=
      match named_list_lookup_err l n with
      | Some r => (ConstructorsOf.constructors_of_rule r)
      | None => []
      end.
                                               
    Definition frontier l :=
      let f n := n::sort_elem_constructors l n ++ compute_direct_dependencies l n in
      map (fun n => (n,f n)) (map fst l).

    
    (*TODO: move to utils*)
    Section Fixpoints.
      Context {A} `{Eqb_ok A} (f: A -> A).
      Fixpoint fixpoint fuel a :=
        match fuel with
        | 0 => a
        | S n =>
            let a' := f a in
            if eqb a a' then a else fixpoint n a'
        end.
        
    Definition fixed_point p := eqb (f p) p.

    
    Lemma fixpoint_fixed (a:A) n
      : a = f a -> fixpoint n a = a.
    Proof.
      induction n;
        basic_goal_prep; eauto.
      rewrite <- H1.
      basic_utils_crush.
    Qed.        
    
    Lemma fixpoint_inside_out (a:A) n
      : (fixpoint n (f a)) = f (fixpoint n a).
    Proof.
      revert a.
      induction n;
        basic_goal_prep;
        auto.
      
      rewrite IHn.
      pose proof (eqb_spec a (f a)).
      destruct (eqb a (f a)).
      {
        rewrite <- !H1.
        basic_utils_crush.
      }
      {
        pose proof (eqb_spec (f a) (f (f a))).
        destruct (eqb (f a) (f (f a))); eauto.
        revert H2.
        clear H1 IHn.
        generalize (f a).
        clear a; intro a; intros.
        rewrite fixpoint_fixed; eauto.
      }
    Qed.

    Context (P : A -> Prop)
      (P_invariant : forall a, P a -> P (f a)).

    Lemma fixpoint_invariant a n
      : P a -> P (fixpoint n a).
    Proof.
      intro P_initial.
      induction n;
        basic_goal_prep;
        basic_utils_crush.
      pose proof (eqb_spec a (f a)).
      destruct (eqb a (f a)); eauto.
      rewrite fixpoint_inside_out.
      eauto.
    Qed.

    End Fixpoints.


    Definition dep_trans_step out :=
      named_map (Basics.compose (dedup (eqb (A:=_))) (flat_map (named_list_lookup [] out))) out.
    
    Definition compute_dependencies l : named_list (list V) :=
      let init := frontier l in
      fixpoint dep_trans_step 10 (*fuel: TODO: does it short circuit ever?*) init.

    
    Lemma incl_flat_map_elt A B (f:A -> list B) x l l'
      : In x l' -> incl l (f x) -> incl l (flat_map f l').
    Proof.
      induction l';
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    Definition deps_extends (s1 s2 : named_list (list V)) :=
      all2 (fun '(n1,l1) '(n2,l2) => n1 = n2 /\ incl l1 l2) s1 s2.
    
    Lemma deps_extends_refl s : deps_extends s s.
    Proof.
      induction s;
        basic_goal_prep; eauto.
      basic_utils_crush.
    Qed.
    Local Hint Resolve deps_extends_refl : utils.

    Definition dep_reflexive (s : named_list (list V)) :=
      forall n l, In (n,l) s -> In n l.
    
    Lemma dep_trans_step_mono s
      : all_fresh s ->
        dep_reflexive s ->
        deps_extends s (dep_trans_step s).
    Proof.
      unfold deps_extends, dep_trans_step, dep_reflexive.
      enough (forall s',
                 all_fresh s' ->
                 (forall (n : V) (l : list V), In (n, l) s -> In n l) ->
                 incl s s' ->
                 all2 (fun '(n1, l1) '(n2, l2) => n1 = n2 /\ incl l1 l2) s
                   (named_map (Basics.compose (dedup (eqb (A:=V)))
                                 (flat_map (named_list_lookup [] s'))) s)).
      {
        intros.
        eapply H; basic_utils_crush.
      }
      intros s' Hfresh.
      induction s;
        basic_goal_prep;
        basic_utils_crush.
      {
        cbv [Basics.compose].
        intros a H'; rewrite <- dedup_preserves_In.
        revert a H'.
        apply incl_flat_map_elt with (x:=v).
        { eapply H; left; eauto. }
        {
          erewrite named_list_lookup_in; eauto.
          eapply incl_refl.
        }
      }
    Qed.

    Lemma frontier_reflexive l
      : dep_reflexive (frontier l).
    Proof.
      unfold frontier, dep_reflexive.
      intros.
      rewrite map_map in *.
      cbn in *.
      rewrite in_map_iff in *.
      break.
      basic_utils_crush.
    Qed.

    (*TODO: move to Utils*)
    Lemma in_named_map A B (f : A -> B) l n x
      : In (n, x) (named_map f l) -> exists y, In (n, y) l /\ x = f y.
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.
      
    Lemma dep_trans_step_reflexive l
      : all_fresh l ->
        dep_reflexive l -> dep_reflexive (dep_trans_step l).
    Proof.
      unfold dep_trans_step, dep_reflexive.
      intuition subst.
      apply in_named_map in H1.
      break.
      subst.
      cbv [Basics.compose].
      rewrite <- dedup_preserves_In.
      apply in_flat_map.
      exists n.
      firstorder.
      erewrite named_list_lookup_in; eauto.
    Qed.
    
    Lemma frontier_map_fst l
      : map fst l = map fst (frontier l).
    Proof.
      unfold frontier.
      rewrite !map_map.
      cbn.
      reflexivity.
    Qed.
      
    Lemma frontier_all_fresh l
      : all_fresh l -> all_fresh (frontier l).
    Proof.
      apply all_fresh_sublist.
      rewrite frontier_map_fst.
      apply sublist_refl.
    Qed.


    Lemma deps_extends_trans a b c
      : deps_extends a b -> deps_extends b c -> deps_extends a c.
    Proof.
      unfold deps_extends.
      intro H; revert b H c.
      induction a;
        destruct b,c;
        basic_goal_prep;
        basic_utils_crush.
      revert H4 H5; clear.
      unfold incl; firstorder.
    Qed.

    
    Lemma deps_extends_step_map_fst a b
      : deps_extends a b -> map fst a = map fst b.
    Proof.
      revert b;
        induction a; destruct b;
        basic_goal_prep;
        basic_utils_crush.
    Qed.

    
    Lemma map_fst_compute_deps n l
          : map fst (fixpoint dep_trans_step n l)
            = map fst l.
    Proof.
      apply fixpoint_invariant; eauto.
      intros.
      unfold dep_trans_step.
      rewrite map_fst_named_map.
      auto.
    Qed.

    

    Lemma compute_dependencies_reflexive l
      : all_fresh l ->
        dep_reflexive (compute_dependencies l).
    Proof.
      unfold compute_dependencies.
      intro Hfresh.
      enough (dep_reflexive (fixpoint dep_trans_step 10 (frontier l))
              /\ all_fresh (fixpoint dep_trans_step 10 (frontier l))) by intuition eauto.
      simple apply fixpoint_invariant;
        basic_goal_prep;
        intuition eauto using dep_trans_step_reflexive,
        frontier_all_fresh,
        frontier_reflexive.
      eapply all_fresh_sublist; eauto.
      unfold dep_trans_step.
      rewrite map_fst_named_map.
      eapply sublist_refl.
    Qed.
      
    Lemma dependencies_contain_frontier l
      : all_fresh l ->
         deps_extends (frontier l) (compute_dependencies l).
    Proof.
      unfold compute_dependencies.
      intro Hfresh.
      generalize 10 as n.
      induction n; basic_goal_prep;
        basic_utils_crush.
      case_match; basic_goal_prep;
        basic_utils_crush.
      rewrite fixpoint_inside_out.
      eapply deps_extends_trans; eauto.
      apply dep_trans_step_mono.
      {
        
        eapply all_fresh_sublist; eauto.
        rewrite map_fst_compute_deps.
        rewrite <- frontier_map_fst.
        eapply sublist_refl.
      }
      {
        enough (dep_reflexive (fixpoint dep_trans_step n (frontier l))
                /\ all_fresh (fixpoint dep_trans_step n (frontier l))) by intuition eauto.
        simple apply fixpoint_invariant;
          basic_goal_prep;
          intuition eauto using dep_trans_step_reflexive,
          frontier_all_fresh,
          frontier_reflexive.
        eapply all_fresh_sublist; eauto.
        unfold dep_trans_step.
        rewrite map_fst_named_map.
        eapply sublist_refl.
      }
    Qed.

    Lemma frontier_direct_dep_complete l n n'
      : all_fresh l ->
        direct_dependency l n n' ->
        let deps := (frontier l) in
        match named_list_lookup_err deps n with
        | Some l => In n' l
        | None => False
        end.
    Proof.
      unfold direct_dependency.
      intros.
      revert H0; case_match;
        basic_goal_prep; try tauto.
      pose proof case_match_eqn as H'.
      symmetry in case_match_eqn.
      eapply named_list_lookup_err_in in case_match_eqn.
      case_match; symmetry in case_match_eqn0.
      {
        eapply named_list_lookup_err_in in case_match_eqn0.
        unfold frontier in *.
        rewrite map_map in *.
        lazymatch goal with
        | H : In _ (map ?f' ?l), H' : In _ ?l |- _ =>
            eapply in_map with (f:=f') in H';
            cbn in *;
            eapply in_all_fresh_same in H'; eauto
        end.
        2:{
          eapply all_fresh_sublist; eauto.
          lazymatch goal with
          | |- sublist ?l1 ?l2 =>
              replace l1 with l2;
              eauto using sublist_refl
          end.
          rewrite map_map in *.
          cbn.
          reflexivity.
        }
        subst.
        cbn.
        right.
        basic_utils_crush.
        right.
        unfold compute_direct_dependencies.
        rewrite H'.
        eauto.
      }
      {
        symmetry in H'.
        eapply named_list_lookup_err_in in H'.
        eapply named_list_lookup_none_iff in case_match_eqn0.
        unfold frontier in *.
        unfold fresh in *.
        rewrite !map_map in *.
        eapply case_match_eqn0.
        lazymatch goal with
        | H' : In _ ?l |- In _ (map ?f' ?l) =>
            eapply in_map with (f:=f') in H';
            cbn in *;
            eauto
        end.
      }
    Qed.
    
    Lemma deps_extends_lookup l1 l2 l1' n
      : deps_extends l1 l2 -> Some l1' = named_list_lookup_err l1 n ->
        exists l2', Some l2' = named_list_lookup_err l2 n /\ incl l1' l2'.
    Proof.
      unfold deps_extends.
      revert l2; induction l1;
        destruct l2;
        basic_goal_prep;
        basic_utils_crush.
      eqb_case n v; basic_utils_crush.
    Qed.

    (*TODO: move to utils*)
    Lemma named_list_lookup_to_err A (l:named_list A) x d
      : named_list_lookup d l x
        = @unwrap_with_default A d (named_list_lookup_err l x).
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
      eqb_case x v;
        basic_utils_crush.
    Qed.

    Lemma in_named_map'
     : forall (A B : Type) (f : A -> B) (l : named_list A) (n : V) (x : B),
        In (n, x) (named_map f l) <-> exists y : A, In (n, y) l /\ x = f y.
    Proof.
      intuition eauto using in_named_map.
      break.
      subst.
      unfold named_map.
      basic_utils_crush.
    Qed.

    Lemma fixed_point_named_map_inv A `{Eqb_ok A} (f : A -> A) m n l
      : Is_true (fixed_point (named_map f) m) ->
        In (n,l) m ->
        Is_true (fixed_point f l).
    Proof.
      unfold fixed_point.
      induction m;
        basic_goal_prep;
        basic_utils_crush;
        unfold named_list in H1;
        basic_utils_crush.
    Qed.            
    
    Lemma fixed_point_deps_helper deps n l
      : Is_true (fixed_point dep_trans_step deps) ->
        In (n,l) deps ->
        Basics.compose (dedup (@eqb _ _)) (flat_map (named_list_lookup [] deps)) l = l.
    Proof.
      unfold dep_trans_step.
      intros.
      eapply fixed_point_named_map_inv in H; eauto;
        try typeclasses eauto.
      unfold fixed_point in *.
      cbv [Basics.compose] in *.
      basic_utils_crush.
    Qed.
    
    Lemma fixed_point_deps_closed deps n l n' l'
      : all_fresh deps ->
        Is_true (fixed_point dep_trans_step deps) ->
        In (n,l) deps ->
        In n' l ->
        In (n',l') deps ->
        incl l' l.
    Proof.
      intros; intros n'' Hin.

      pose proof H1 as H1';
        pose proof H3 as H3'.
      eapply fixed_point_deps_helper in H1, H3; eauto.
      rewrite <- H1.
      cbv [Basics.compose] in *.
      rewrite <- !dedup_preserves_In.
      apply in_flat_map.
      exists n'; intuition eauto.
      erewrite named_list_lookup_in; eauto.
    Qed.
    
    Lemma all_fresh_deps l
      : all_fresh l -> all_fresh (compute_dependencies l).
    Proof.
      unfold compute_dependencies, dep_trans_step.
      intros.
      eapply fixpoint_invariant;
        eauto using frontier_all_fresh.
      intros.
      eapply all_fresh_sublist; eauto.
      rewrite map_fst_named_map.
      basic_utils_crush.
    Qed.
    
    Lemma compute_dependencies_complete l n n'
      : wf_lang l ->
        dependency l n n' ->
        let deps := (compute_dependencies l) in
        Is_true (fixed_point dep_trans_step deps) ->
        match named_list_lookup_err deps n with
        | Some l => In n' l
        | None => False
        end.
    Proof.
      intro Hwf.
      assert (all_fresh l) as Hfresh by basic_core_crush.
      induction 1;
        basic_goal_prep; subst deps;
        intuition subst;
        basic_utils_crush.
      {
        case_match; try tauto.
        revert H3; case_match; intros; try tauto.
        symmetry in case_match_eqn, case_match_eqn0.
        eapply named_list_lookup_err_in in case_match_eqn, case_match_eqn0.
        eapply fixed_point_deps_closed; eauto using all_fresh_deps.
      }
      {
        unfold fixed_point.
        eapply frontier_direct_dep_complete in H; eauto.
        revert H; case_match; intros; try tauto.
        pose proof (dependencies_contain_frontier l ltac:(auto)) as Hext.
        eapply deps_extends_lookup in Hext; eauto.
        break.
        rewrite <- H1.
        eapply H2; eauto.
      }
      {
        pose proof (dependencies_contain_frontier ltac:(auto)) as Hext.
        use_rule_in_wf.
        basic_core_crush.
        safe_invert H6.
        case_match; symmetry in case_match_eqn.
        2:{
          eapply named_list_lookup_none_iff in case_match_eqn.
          unfold fresh in *.
          eapply case_match_eqn.
          unfold compute_dependencies.
          rewrite map_fst_compute_deps.
          rewrite <- frontier_map_fst.
          eauto using pair_fst_in.
        }
        {
          assert (exists x, Some x = named_list_lookup_err (frontier l) n0).
          {
            my_case Hfrontier (named_list_lookup_err (frontier l) n0).
            { exists l1; eauto. }
            exfalso.
            symmetry in Hfrontier.
            eapply named_list_lookup_none_iff in Hfrontier.
            unfold fresh in Hfrontier.
            rewrite <- frontier_map_fst in Hfrontier.
            apply pair_fst_in in H5.
            eauto.
          }
          break.

          pose proof H6.
          
          eapply deps_extends_lookup in H6; eauto.
          break.
          basic_goal_prep.
          replace l0 with x0 in * by congruence; clear l0 H6.

          eapply H9.
          eapply named_list_lookup_err_in in H8.

          unfold frontier in H8.
          apply in_map_iff in H8.
          break.
          basic_utils_crush.
          basic_goal_prep.
          right.
          basic_utils_crush.
          left.
          unfold sort_elem_constructors.
          eapply in_flat_map.
          exists (n, term_eq_rule c e1 e2 (scon n0 s));
            intuition eauto.
          cbn.
          basic_utils_crush.
        }
      }
      {
        pose proof (dependencies_contain_frontier ltac:(auto)) as Hext.
        use_rule_in_wf.
        basic_core_crush.
        safe_invert H5.
        case_match; symmetry in case_match_eqn.
        2:{
          eapply named_list_lookup_none_iff in case_match_eqn.
          unfold fresh in *.
          eapply case_match_eqn.
          unfold compute_dependencies.
          rewrite map_fst_compute_deps.
          rewrite <- frontier_map_fst.
          eauto using pair_fst_in.
        }
        {
          assert (exists x, Some x = named_list_lookup_err (frontier l) n0).
          {
            my_case Hfrontier (named_list_lookup_err (frontier l) n0).
            { exists l1; eauto. }
            exfalso.
            symmetry in Hfrontier.
            eapply named_list_lookup_none_iff in Hfrontier.
            unfold fresh in Hfrontier.
            rewrite <- frontier_map_fst in Hfrontier.
            apply pair_fst_in in H4.
            eauto.
          }
          break.

          pose proof H5.
          
          eapply deps_extends_lookup in H5; eauto.
          break.
          basic_goal_prep.
          replace l0 with x0 in * by congruence; clear l0 H5.

          eapply H8.
          eapply named_list_lookup_err_in in H7.

          unfold frontier in H7.
          apply in_map_iff in H7.
          break.
          basic_utils_crush.
          basic_goal_prep.
          right.
          basic_utils_crush.
          left.
          unfold sort_elem_constructors.
          eapply in_flat_map.
          exists (n, term_rule c args (scon n0 s));
            intuition eauto.
          cbn.
          basic_utils_crush.
        }
      }
    Qed.

    Definition pl_is_orderedb (pl : param_spec) (l : lang) :=
      let deps := (compute_dependencies l) in
      (* fails if not a fixed point to make sure it's sound.
           To fix this failure, just up the fuel enough.
       *)
      (fixed_point dep_trans_step deps) &&
        let Q n n' :=
          (implb (inb n' (map fst pl)) (inb n (map fst pl)))
          && (implb (freshb n pl) (freshb n' pl))
        in
        let P '(n,_) :=
          match named_list_lookup_err deps n with
          | Some l => forallb (Q n) l
          | None => false
          end               
        in
        forallb P l.

    (*TODO: move to Utils*)
    Lemma Is_true_implb a b : Is_true (implb a b) <-> (Is_true a -> Is_true b).
    Proof. destruct a, b; cbn in *; intuition eauto. Qed.
    Hint Rewrite Is_true_implb : utils.
    
    Lemma pl_is_orderedb_sound pl l
      : wf_lang l ->
        Is_true (pl_is_orderedb pl l) ->
        pl_is_ordered pl l.
    Proof.
      unfold pl_is_orderedb, pl_is_ordered.
      basic_utils_crush.
      eapply all_impl; eauto.
      clear H2.
      basic_goal_prep.
      revert H0; case_match;
        basic_goal_prep;
        try tauto.
      eapply compute_dependencies_complete in H2;
        eauto.
      rewrite case_match_eqn in H2.
      autorewrite with utils in H0.
      assert (In v l0).
      {
        eapply compute_dependencies_reflexive;
          eauto using named_list_lookup_err_in.
        basic_core_crush.
      }
      eapply in_all in H2, H3; eauto.
      basic_utils_crush.
      revert H4.
      unfold Is_Some.
      repeat case_match;
        basic_utils_crush.
      symmetry in case_match_eqn1.
      apply named_list_lookup_none_iff in case_match_eqn1.
      symmetry in case_match_eqn0.
      eapply named_list_lookup_err_in in case_match_eqn0.
      eapply pair_fst_in in case_match_eqn0.
      intuition eauto.
    Qed.

    Local Hint Resolve pl_is_orderedb_sound : lang_core.
    
    Lemma parameterize_lang_preserving
      : forall l : lang,
        wf_lang l ->
        wf_lang l_base ->
        Is_true (syntactic_parameterization_conditions' src_spec l_base l
                 && pl_is_orderedb src_spec l) ->
        wf_lang_ext l_base (parameterize_lang src_spec l).
    Proof.
      intros.
      eapply parameterize_lang_preserving''; eauto;
        basic_core_crush.
    Qed.
    
    Lemma parameterize_lang_preserving_ext
      : forall l l_pre : lang,
        wf_lang l_pre ->
        wf_lang_ext l_pre l ->
        wf_lang l_base ->
        Is_true (syntactic_parameterization_conditions' src_spec l_base (l++l_pre)
                 && pl_is_orderedb src_spec (l++l_pre)) ->
        wf_lang_ext (parameterize_lang src_spec l_pre ++ l_base) (parameterize_lang src_spec l).
    Proof.
      intros.
      apply wf_lang_concat_iff.
      unfold parameterize_lang.
      rewrite app_assoc.
      rewrite <- map_app.
      apply wf_lang_concat_iff.
      split; auto.
      apply parameterize_lang_preserving; eauto.
      apply wf_lang_concat_iff; intuition eauto.
    Qed.

    Definition p_name_fresh_in_cmpb : compiler -> bool :=
      forallb (fun p =>
                 match snd p with
                 | term_case args _ | sort_case args _ => negb (inb p_name args)
                 end).
    
    Lemma p_name_fresh_in_cmpbsound cmp
      : Is_true (p_name_fresh_in_cmpb cmp) ->
        p_name_fresh_in_cmp cmp.
    Proof.
      unfold p_name_fresh_in_cmp, p_name_fresh_in_cmpb.
      basic_utils_crush.
      eapply all_impl; eauto; clear H.
      basic_goal_prep;
        case_match;
        basic_utils_crush.
    Qed.

    (*TODO: rename one above; really should merge them/refactor*)
    Definition syntactic_parameterization_conditions tgt_spec l_base tgt src cmp :=
      syntactic_parameterization_conditions' tgt_spec l_base tgt
      && compiler_respects_parameterizationb src cmp
      && pl_is_orderedb tgt_spec tgt
      && pl_is_orderedb src_spec src
      && all_freshb (src++l_base)
      && specs_compatibleb cmp
      && p_name_fresh_in_cmpb cmp.
      
    (*TODO: rename one above; really should merge them/refactor*)
    Lemma parameterize_compiler_preserving cmp src
      : (* Assumed invariants*)
      wf_lang tgt ->
      preserving_compiler_ext tgt [] cmp src ->
      wf_lang src ->
      (* computable invariants*)
      Is_true (syntactic_parameterization_conditions tgt_spec l_base tgt src cmp) ->
      preserving_compiler_ext (parameterize_lang tgt_spec tgt ++ l_base)
        (id_compiler l_base)
        (parameterize_compiler p_name tgt_spec src_spec cmp)
        (parameterize_lang src_spec src).
    Proof.
      unfold syntactic_parameterization_conditions.
      intros; eapply parameterize_compiler_preserving'; eauto;
        basic_goal_prep;
        basic_utils_crush.
      all: eauto using p_name_fresh_in_cmpbsound, pl_is_orderedb_sound, use_compute_all_fresh.
    Qed.
    
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

End WithVar.

