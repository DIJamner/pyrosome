Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Pf.

Require Import String.


Create HintDb pfcore discriminated.



(*TODO: put in utils*)
Lemma in_all_fresh_same {A:eqType} (a b : A) l s
  : all_fresh l -> (s,a) \in l -> (s,b) \in l -> a = b.
Proof.
  induction l; simpl; intros; break;
    repeat match goal with
           | [H : is_true (_\in [::])|- _] =>
             solve[ inversion H]
           | [H : is_true (_\in _::_)|- _] =>
             rewrite in_cons in H;
               move: H => /orP []; intros; break
           | [H : is_true ((_,_) == (_,_))|- _] =>
             move: H => /eqP []; intros; subst
           end; simpl in *; auto.
  eapply fresh_neq_in in H2; eauto;
  exfalso;  move: H2 => /eqP; auto.
  eapply fresh_neq_in in H2; eauto;
  exfalso;  move: H2 => /eqP; auto.
Qed.


Lemma eq_sym {A :eqType} (a b :A) : (a == b) = (b == a).
Proof.
  case ab: (a==b);
    move: ab => /eqP ab; subst;
    [ by rewrite eq_refl
    | case ba: (b==a);
      move: ba => /eqP ba; auto].
Qed.          
  
(*TODO: move to utils *)
Lemma named_list_lookup_err_none {A} (l : named_list A) n
  : n \notin (map fst l) ->
    named_list_lookup_err l n = None.
Proof.
  elim: l; simpl; auto.
  intros; break; simpl.
  rewrite in_cons in H0.
  move: H0 => /norP []; simpl; intros.
  apply negbTE in a0;
    change (n =? s = false)%string in a0;
    rewrite a0.
  auto.
Qed.
  
Lemma named_list_lookup_err_inb {A : eqType} l x (v:A)
  : all_fresh l ->
    named_list_lookup_err l x == Some v = ((x,v) \in l).
Proof.
  induction l; break; [by compute | simpl]; intros; break.
  case_match.
  {
    match goal with
      [H : true = (?a =? ?b)%string |-_]=>
      symmetry in H; change (is_true (a == b)) in H;
        move: H => /eqP H; subst
    end.
    case veqs0: (s0 == v).
    {
      move:veqs0 => /eqP veqs0; subst.
      rewrite in_cons.
      rewrite !eq_refl.
      by compute.
    }
    {
      rewrite in_cons.
      cbn.
      rewrite veqs0 eqb_refl.
      rewrite eq_sym in veqs0.
      rewrite veqs0.
      simpl.
      simpl in IHl.
      rewrite <- IHl; auto.
      rewrite named_list_lookup_err_none; auto.
    }
  }
  {
      rewrite in_cons.
      cbn.
      rewrite <- HeqH1.
      cbn.
      auto.
  }
Qed.

Lemma named_list_lookup_none {A:eqType} l s (a:A)
  : None = named_list_lookup_err l s ->
    (s, a) \notin l.
Proof.
  induction l; break; simpl in *; auto.
  case seqs0: (s=?s0)%string.
  {
    intro fls; inversion fls.
  }
  {
    intros; rewrite in_cons; apply /orP.
    intro c; destruct c.
    {
      cbn in *.
      rewrite seqs0 in H0; move: H0 => /andP [] //.
    }
    {
      apply IHl in H.
      rewrite H0 in H.
      inversion H.
    }
  }
Qed.
  
Section TermsAndRules.
  Context (l : pf_lang).

  Inductive is_dom : pf -> pf -> Prop :=
  | dom_var x : is_dom (pvar x) (pvar x)
  | dom_con n pl pl_l
    : List.Forall2 is_dom pl pl_l ->
      is_dom (pcon n pl) (pcon n pl_l)
  | dom_ax_sort n pl pl_l c p' p_r
    : List.Forall2 is_dom pl pl_l ->
      (n, sort_le_pf c p' p_r) \in l ->
      is_dom (ax n pl) (pf_subst (with_names_from c pl_l) p')
  | dom_ax_term n pl pl_l c p' p_r t
    : List.Forall2 is_dom pl pl_l ->
      (n, term_le_pf c p' p_r t) \in l ->
      is_dom (ax n pl) (pf_subst (with_names_from c pl_l) p')
  | dom_sym p p_r
    : is_codom p p_r ->
      is_dom (sym p) p_r
  | dom_trans p1 p2 p1_l
    : is_dom p1 p1_l ->
      is_dom (trans p1 p2) p1_l
  | dom_conv pt p p_l
    : is_dom p p_l ->
      is_dom (conv pt p) (conv pt p_l)
  with is_codom : pf -> pf -> Prop :=
  | codom_var x : is_codom (pvar x) (pvar x)
  | codom_con n pl pl_r
    : List.Forall2 is_codom pl pl_r ->
      is_codom (pcon n pl) (pcon n pl_r)
  | codom_ax_sort n pl pl_r c p' p_l
    : List.Forall2 is_dom pl pl_r ->
      (n, sort_le_pf c p_l p') \in l ->
      is_codom (ax n pl) (pf_subst (with_names_from c pl_r) p')
  | codom_ax_term n pl pl_r c p' p_l t
    : List.Forall2 is_dom pl pl_r ->
      (n, term_le_pf c p_l p' t) \in l ->
      is_codom (ax n pl) (pf_subst (with_names_from c pl_r) p')
  | codom_sym p p_r
    : is_dom p p_r ->
      is_codom (sym p) p_r
  | codom_trans p1 p2 p2_r
    : is_codom p2 p2_r ->
      is_codom (trans p1 p2) p2_r
  | codom_conv pt p p_r
    : is_codom p p_r ->
      is_codom (conv pt p) (conv pt p_r).

  (* assumes ok inputs
    equivalent to exists p', is_codom p1 p' /\ is_dom p2 p'; TODO: prove 
    Note that this judgment is wrt the left-to-right orientation
    of equivalences
   TODO: sym is tricky; better to just use dom/codom?
  Inductive can_compose : pf -> pf -> Prop :=
  | can_compose_var x : can_compose (pvar x) (pvar x)
  | can_compose_con n pl pl_l
    : List.Forall2 can_compose pl pl_l ->
      can_compose (pcon n pl) (pcon n pl_l)
  | can_compose_ax_sort_l n pl c p p' p_r
    : (n, sort_le_pf c p p') \in l ->
      can_compose (pf_subst (with_names_from c pl) p') p_r ->
      can_compose (ax n pl) p_r
  | can_compose_ax_sort_r n pl c p p' p_l
    : (n, sort_le_pf c p p') \in l ->
      can_compose p_l (pf_subst (with_names_from c pl) p) ->
      can_compose p_l (ax n pl)
  | can_compose_ax_term_l n pl c p p' p_r t
    : (n, term_le_pf c p p' t) \in l ->
      can_compose (pf_subst (with_names_from c pl) p') p_r ->
      can_compose (ax n pl) p_r
  | can_compose_ax_term_r n pl c p p' p_l t
    : (n, term_le_pf c p p' t) \in l ->
      can_compose p_l (pf_subst (with_names_from c pl) p) ->
      can_compose p_l (ax n pl)
  | can_compose_sym_l p p'
    : can_compose p' p ->
      can_compose (sym p) p'
  | can_compose_trans p1 p2 p1_l
    : can_compose p1 p1_l ->
      can_compose (trans p1 p2) p1_l
  | can_compose_conv pt p p_l
    : can_compose p p_l ->
      can_compose (conv pt p) (conv pt p_l).
   *)

  (*TODO: move to OptionMonad *)
  Import OptionMonad.
  Fixpoint Mmap {A B} (f : A -> option B) (l_a : list A) : option (list B) :=
    match l_a with
    | [::] => do ret [::]
    | a::l_a' =>
      do l_b' <- Mmap f l_a';
         b <- f a;
         ret (b::l_b')
    end.              

  Section DomInnerLoop.
    (*For some reason I need two copies of Mmap
      for the mutual recursion to go through below.
     *)
    Context (dom : pf -> option pf)
            (codom : pf -> option pf).
    Fixpoint dom_args (pl : list pf) :=
      match pl with
      | [::] => do ret [::]
      | a::pl' =>
        do pl'_dom <- dom_args pl';
           b <- dom a;
           ret (b::pl'_dom)
      end.

    Fixpoint codom_args (pl : list pf) :=
         match pl with
         | [::] => do ret [::]
         | a::pl' =>
           do pl'_codom <- codom_args pl';
              b <- codom a;
              ret (b::pl'_codom)
         end.
  End DomInnerLoop.
    
  (*Pressupposition: p is ok *)
  Fixpoint dom (p:pf) :=
    match p with
    | pvar x => do ret (pvar x)
    | pcon name pl => omap (pcon name) (dom_args dom pl)
    | ax name pl =>
      match named_list_lookup_err l name with
      | Some (sort_le_pf c p' _)
      | Some (term_le_pf c p' _ _) =>
        do pl' <- dom_args dom pl;
        ret pf_subst (with_names_from c pl') p'
      | _ => None
      end
    | sym p => codom p
    | trans p1 p2 => dom p1
    | conv pt p' => omap (conv pt) (dom p')
    end               
 (*Pressupposition: p is ok *)
  with codom (p:pf) :=
    match p with
    | pvar x => do ret (pvar x)
    | pcon name pl => omap (pcon name) (codom_args codom pl)
    | ax name pl =>
      match named_list_lookup_err l name with
      | Some (sort_le_pf c _ p')
      | Some (term_le_pf c _ p' _) =>
        do pl' <- codom_args codom pl;
        ret pf_subst (with_names_from c pl') p'
      | _ => None
      end
    | sym p => dom p
    | trans p1 p2 => codom p2
    | conv pt p' => omap (conv pt) (codom p')
    end.

  Lemma is_domP p p' : reflect (is_dom p p') (dom p == Some p')
  with is_codomP p p' : reflect (is_dom p p') (codom p == Some p').
  Proof.
    all: destruct p; destruct p'; cbn;
      repeat match goal with
             | [H : true = false |- _] => inversion H
             | [H : context [(?s =? ?s)%string] |- _] =>
               rewrite eqb_refl in H
            | [|- ~ _] => let fls := fresh "fls" in intro fls; inversion fls; subst; clear fls
            | [|- is_dom _ _] => constructor
            | [|- reflect _ true] => constructor
            | [|- reflect _ false] => constructor
            | [|- reflect _ (?a =? ?b)%string] =>
              let Heq := fresh "Heq" in
              my_case Heq (a =? b)%string;
                [change (is_true (a == b)) in Heq;
                 move: Heq => /eqP ->|]
             end.
    Admitted.
      
                      
  (*TODO: relate dom to is_dom on ok terms
    TODO: should dom be partial?
    prob. want Inhabited typeclass first,
    maybe this one too:
    Class SyntaxWithPredicate t :=
    {
      inhabited :> Inhabited t;
      is_ok : t -> Prop
    }
   *)

  (* Strips components of the proof that we consider
     irrelevant for the purpose of equality.
     TODO: generalize this, e.g. (sym (sym x)) ~ x.
     Probably not necessary as long as this is only
     used on projections
   *)
  
  (*
    Judgments for checking proofs of relations between programs.
    Can check wfness of a program by identifying it with its
    identity relation.

    All assume lang_ok.
    All ctxs (other than in ctx_ok) are assumed to satisfy ctx_ok.
    Judgments whose assumptions take ctxs must ensure they are ok.
    Sorts are not assumed to be ok; the term judgments should guarantee
    that their sorts are ok and is_exp.
   *)
  
  Inductive sort_ok : pf_ctx -> pf -> Prop :=
  | sort_ok_ax : forall c c' name t1 t2 s,
      (name, sort_le_pf c' t1 t2) \in l ->
      args_ok c s c' ->
      sort_ok c (ax name s)
  | sort_ok_con : forall c name c' args s,
      (name, (sort_rule_pf c' args)) \in l ->
      args_ok c s c' ->
      sort_ok c (pcon name s)
  | sort_ok_trans : forall c t1 t t2,
      sort_ok c t1 ->
      sort_ok c t2 ->
      is_codom t1 t ->
      is_dom t2 t ->
      sort_ok c (trans t1 t2)
  | sort_ok_sym : forall c t, sort_ok c t -> sort_ok c (sym t)
  with term_ok : pf_ctx -> pf -> pf -> Prop :=
  | term_ok_ax : forall c c' name e1 e2 t s t',
      (name, term_le_pf c' e1 e2 t) \in l ->
      args_ok c s c' ->
      (*non-obvious fact: the sort may not be a wfness proof if we don't project;
        may be a non-identity relation due to s
       *)
      is_dom (pf_subst (with_names_from c' s) t) t' ->
      term_ok c (ax name s) t'
  | term_ok_con : forall c name c' args t t' s,
      (name, (term_rule_pf c' args t)) \in l ->
      args_ok c s c' ->
      is_dom (pf_subst (with_names_from c' s) t) t' ->
      (* same as above *)
      term_ok c (pcon name s) t'
  | term_ok_trans : forall c e1 e e2 t,
      term_ok c e1 t ->
      term_ok c e2 t ->
      is_codom e1 e ->
      is_dom e2 e ->
      term_ok c (trans e1 e2) t
  | term_ok_sym : forall c e t, term_ok c e t -> term_ok c (sym e) t
  | term_ok_var : forall c x t,
      (x,t) \in c ->
      term_ok c (pvar x) t
  (* Conversion:

c |- e1 = e2 : t = t'
                 ||
c |- e1 = e2 : t' = t''

TODO: this rule is no good; 
want to have output type (proj_r? t'), not trans.
(note that this interferes w/ removing symmetry if I aim to do that later.)
The theoretically proper thing to do is to give computation rules to trans, sym,
e.g.: sym (trans a b) = trans (sym b) (sym a), sym (var x) = var x
   *)
  | term_ok_conv : forall c e t tp t',
      sort_ok c tp ->
      term_ok c e t ->
      is_dom tp t ->
      is_codom tp t' ->
      term_ok c (conv tp e) t'
  with args_ok : pf_ctx -> list pf -> pf_ctx -> Prop :=
  | args_ok_nil : forall c, args_ok c [::] [::]
  | args_ok_cons : forall c s c' name e t,
      args_ok c s c' ->
      (* assumed because the output ctx is wf: fresh name c' ->*)
      term_ok c e (pf_subst (with_names_from c' s) t) ->
      args_ok c (e::s) ((name, t)::c').
  
  Inductive subst_ok : pf_ctx -> named_list pf -> pf_ctx -> Prop :=
  | subst_ok_nil : forall c, subst_ok c [::] [::]
  | subst_ok_cons : forall c s c' name e t,
      subst_ok c s c' ->
      (* assumed because the output ctx is wf: fresh name c' ->*)
      term_ok c e (pf_subst s t) ->
      subst_ok c ((name,e)::s) ((name, t)::c').

  Inductive ctx_ok : pf_ctx -> Prop :=
  | ctx_ok_nil : ctx_ok [::]
  | ctx_ok_cons : forall name c v,
      fresh name c ->
      ctx_ok c ->
      sort_ok c v ->
      ctx_ok ((name,v)::c).

  (* Denotes when a proof represents
     an expression (as opposed to a relation
     between 2 expressions)
   *)
  Inductive is_exp : pf -> Prop :=
  | var_is_exp x : is_exp (pvar x)
  | con_is_exp name s
    : List.Forall is_exp s ->
      is_exp (pcon name s)
  | conv_is_exp pt p
    : is_exp p ->
      is_exp (conv pt p).

  Fixpoint check_is_exp e : bool :=
    match e with
    | pvar _ => true
    | pcon _ s => List.forallb check_is_exp s
    | conv _ p => check_is_exp p
    | _ => false
    end.

  Lemma check_is_expP e : reflect (is_exp e) (check_is_exp e).
  Proof using.
    induction e; simpl; repeat constructor;
    try match goal with
        [|- ~_] => let H := fresh in intro H; inversion H; clear H; subst
        end.
    {
      suff: (reflect (List.Forall is_exp l0) (List.forallb check_is_exp l0)).
      {
        intro lfr.
        match goal with
           |- reflect _ ?b =>
           case alll0: b
        end; repeat constructor.
        { apply /lfr; assumption. }
        {
          intro H; inversion H; subst; clear H.
          move: H1 => /lfr.
          rewrite alll0 => //.
        }
      }
      {
        revert X; induction l0; simpl; [repeat constructor|].
        intro; break.
        solve_reflect_norec;
          [match goal with
             |- reflect _ ?b =>
             case alll0: b
           end|]; repeat constructor.
        { apply /r; auto. }
        { apply /IHl0; auto. }
        {
          intro H; inversion H; subst; clear H.
          move: H3 => /IHl0.
          rewrite alll0 => //.
          auto.
        }
        {
          intro H; inversion H; subst; clear H.
          move: H2 => /r //.
        }
      }
    }
    {
      revert IHe2.
      case ce2: (check_is_exp e2); intro r; constructor; inversion r.
      constructor; auto.
      intro H'; inversion H'; auto.
    }
  Qed.  

  (*TODO: for le's, how to make this
    correspond to existing fwk; should I?
    existing defs allow for higher rels in an unfortunate way.
    e.g:
    
    ...
    --------------------------------------------------
    stlc_beta G A A' e e' = ... : (G |- A) = (G' |- B)
    
    where l[stlc_beta] = ...|- \e e' = e[/e'/]
   *)
  Variant rule_ok : rule_pf -> Prop :=
  | sort_rule_ok : forall c args,
      ctx_ok c ->
      subseq args (map fst c) ->
      rule_ok (sort_rule_pf c args)
  | term_rule_ok : forall c args t,
      ctx_ok c ->
      sort_ok c t ->
      subseq args (map fst c) ->
      rule_ok (term_rule_pf c args t)
  | sort_le_ok : forall c t1 t2,
      ctx_ok c ->
      is_exp t1 ->
      is_exp t2 ->
      sort_ok c t1 ->
      sort_ok c t2 ->
      rule_ok (sort_le_pf c t1 t2)
  | term_le_ok : forall c e1 e2 t,
      ctx_ok c ->
      is_exp e1 ->
      is_exp e2 ->
      is_exp t ->
      sort_ok c t ->
      term_ok c e1 t ->
      term_ok c e2 t ->
      rule_ok (term_le_pf c e1 e2 t).

  Hint Constructors sort_ok term_ok subst_ok args_ok ctx_ok rule_ok : pfcore.
  
  Section InnerLoop.
    Context (check_term_ok : pf -> pf -> bool).
    Context (lfresh : all_fresh l).
    Context c (check_term_okP : forall e t, reflect (term_ok c e t) (check_term_ok e t)).

    Fixpoint check_args_ok' (pl : list pf) (c' : pf_ctx) {struct pl} : bool :=
      match pl, c' with
      | [::], [::] => true
      | p::pl', (_,t)::c'' =>
        (check_term_ok p (pf_subst (with_names_from c'' pl') t)) &&
        (check_args_ok' pl' c'')
      |_,_=> false
    end.

    Fixpoint check_sort_ok' (pt : pf) : bool :=
      match pt with
      | pcon name pl =>
        match named_list_lookup_err l name with
        | Some (sort_rule_pf c' _) => check_args_ok' pl c'
        | _ => false
        end
      | ax name pl =>
        match named_list_lookup_err l name with
        | Some (sort_le_pf c' _ _) => check_args_ok' pl c'
        | _ => false
        end
      | sym p => check_sort_ok' p
      | trans p1 p2 =>
        (check_sort_ok' p1) &&
        (check_sort_ok' p2) &&
        (*TODO: will need to show that they are not none when the sorts are okay
          because I am using the ==, but it reads more nicely this way
         *)
        (codom p1 == dom p2) 
      | conv _ _ => false
      | pvar _ => false
      end.

    Hint Constructors reflect : pfcore.
         
  End InnerLoop.

  (*computes the sort of the term for any ok term *)
  (*TODO: unnecessary*)
  (*Fixpoint sort_of_term (c : pf_ctx) (e : pf) : pf :=
    let default := ax "ERR" [::] in
    match e with
    | pvar x =>
      match named_list_lookup_err c x with
      | Some t => t
      | None => default
      end
    | pcon name pl =>
      match named_list_lookup_err l name with
      | Some (term_rule_pf c' _ t') => pf_subst (with_names_from c' pl) t'
      | _ => default
      end
    | ax name pl =>
      match named_list_lookup_err l name with
      | Some (term_rule_pf c' _ t') => pf_subst (with_names_from c' pl) t'
      | _ => default
      end
    | sym p => sort_of_term c p
    (*TODO: needs normalization here to be consistent in the right way;
      otherwise weakens some syntactic identities to semantic ones.
      Is this a problem?
      TODO: figure out whether this matters when all ok terms have is_exp sorts
     *)
    | trans p1 p2 => sort_of_term c p2
    | conv pt p' => dom pt
    end. *)
  
  Fixpoint synth_term_ok (c : pf_ctx) e {struct e} : option pf :=
    let check_term_ok e t := synth_term_ok c e == Some t in 
    match e with
    | pvar x => named_list_lookup_err c x
    | pcon name pl =>
      do (term_rule_pf c' _ t') <- named_list_lookup_err l name;
         ! check_args_ok' check_term_ok pl c';
         d <-(codom (pf_subst (with_names_from c' pl) t'));
         ret d
    | ax name pl =>
      do (term_le_pf c' _ _ t') <- named_list_lookup_err l name;
         ! check_args_ok' check_term_ok pl c';
         d <-(codom (pf_subst (with_names_from c' pl) t'));
         ret d
    | sym p => synth_term_ok c p
    | trans p1 p2 =>
      do t1 <- synth_term_ok c p1;
         t2 <- synth_term_ok c p2;
         ! codom p1 == dom p2;
         ! t1 == t2;
         ret t2
    | conv pt p' =>
      do t1 <- synth_term_ok c p';
         ! check_sort_ok' check_term_ok pt;
         d <- dom pt;
         ! t1 == d;
         cd <- codom pt;
         ret cd
  end.

  Definition check_term_ok c e t := synth_term_ok c e == Some t.
  Definition check_sort_ok c p := check_sort_ok' (check_term_ok c) p.
  Definition check_args_ok c pl c' := check_args_ok' (check_term_ok c) pl c'.

  
  (*TODO: build right induction*)
  Lemma check_term_okP c e t
    : all_fresh l ->
      all_fresh c ->
      reflect (term_ok c e t) (check_term_ok c e t)
  with check_args_okP c pl c'
       : all_fresh l ->
         all_fresh c ->
         reflect (args_ok c pl c') (check_args_ok c pl c')
  with check_sort_okP c t
      : all_fresh l ->
        all_fresh c ->
        reflect (sort_ok c t) (check_sort_ok c t).
  Proof using.
    (* TODO: may need updates for == vs eq_pf_irr and dom/codom
    all: unfold check_sort_ok in *; unfold check_args_ok in *; unfold check_term_ok in *.
    all: intros frl frc.
    all: match goal with
    | [|- reflect (term_ok _ ?e _) _]=> destruct e
    | [|- reflect (sort_ok _ ?t) _]=> destruct t
    | [|- reflect (args_ok _ ?s _) _]=> destruct s
    end; intros; repeat (break; simpl in *; try case_match);
      repeat lazymatch goal with
    | [|- args_ok _ [::] [::]] => by constructor
    | [|- args_ok _ (_::_) (_::_)] => constructor
    | [|- sort_ok _ (sym _)] => apply sort_ok_sym
    | [|- sort_ok _ (trans _ _)] => apply sort_ok_trans
     (*Recursive cases; proceed w/ caution*)
    | [H : is_true(synth_term_ok _ ?e == Some ?t) |- term_ok _ ?e ?t]=>
      apply /check_term_okP; auto
    | [H : is_true(check_args_ok' _ ?e ?t) |- args_ok _ ?e ?t]=>
      apply /check_args_okP; auto
    | [H : is_true(check_sort_ok' _ ?t) |- sort_ok _ ?t]=>
      apply /check_sort_okP; auto
    (* end of recursive cases *)
    | [ H: ?P |- ?P] => exact H
    | [ H: ?P, Hf : ~?P |- _] => exfalso; exact (Hf H)
    | [|- is_true(?a == ?a)]=> apply /eqP
    | [H : ~(is_true(?a == ?a)) |-_]=>
      exfalso; exact (H (eq_refl a))
    | [|- ?a = ?a]=> reflexivity
    | [H : term_le_pf _ _ _ _ = _ |-_]=> inversion H; subst; clear H
    | [H : sort_le_pf _ _ _ = _ |-_]=> inversion H; subst; clear H
    | [H : sort_rule_pf _ _ = _ |-_]=> inversion H; subst; clear H
    | [H : term_rule_pf _ _ _ = _ |-_]=> inversion H; subst; clear H
    | [H : true = true |-_]=> clear H
    | [H : true = ?a |-_]=> symmetry in H
    | [H : (?a)=true |-_]=> change (is_true a) in H
    | [H : false = false |-_]=> clear H
    | [H : false = ?a |-_]=> symmetry in H
    | [H : None = Some _ |-_]=> inversion H
    | [H : Some _ = Some _ |-_]=> inversion H; subst; clear H
    | [H : is_true(_&&_) |-_]=> break
    | [|-is_true(_&&_)]=> break_goal
    | [H : is_true(_==_) |-_]=> move: H => /eqP H; subst
    | [H : (?e==?e)=false |-_]=> rewrite eq_refl in H; inversion H
    | [H : ?a = false, H': is_true ?a |-_]=> rewrite H in H'; inversion H'
    | [|- reflect _ true]=> constructor
    | [|- reflect _ false]=> constructor
    | [|- reflect _ ?p]=>
      let H := fresh in my_case H p
    | [|- ~_]=> let H:= fresh in intro H; inversion H; subst; clear H; auto
    |[_:~_, _:~_|-_] => idtac "two possible negations"
    |[H:~_|-False] => apply H 
    | [H : (do ret ?t) = synth_term_ok ?c ?e|- _] => symmetry in H
    | [H : synth_term_ok ?c ?e = (do ret _)|- term_ok ?c ?e _] =>
      move: H => /eqP /check_term_okP; auto
    | [|- rule_ok _]=> constructor; auto
    | [|- term_ok _ (trans _ _) _]=> eapply term_ok_trans
    | [|- term_ok _ _ _]=> constructor
    | [|- ctx_ok _]=> apply /check_ctx_okP; auto
    | [H : ~(is_true(check_args_ok' _ ?e ?t)), H' : args_ok _ ?e ?t|- _]=>
      move: H => /negP /check_args_okP H;
      exfalso; apply H; auto
    | [H : ~(is_true(check_term_ok _ ?e ?t)), H' : term_ok _ ?e ?t|- _]=>
      move: H => /negP /check_term_okP H;
      exfalso; apply H; auto
    | [H : ~(is_true(check_sort_ok' _ ?t)), H' : sort_ok _ ?t|- _]=>
      move: H => /negP /check_sort_okP H;
      exfalso; apply H; auto
    | [H : (synth_term_ok _ ?e == Some ?t) = false, H' : term_ok _ ?e ?t|- _]=>
      move: H' => /check_term_okP; rewrite H; auto
    | [H : check_args_ok' _ ?e ?t = false, H' : args_ok _ ?e ?t|- _]=>
      move: H' => /check_args_okP; rewrite H; auto
    | [H : check_sort_ok' _ ?t = false, H' : sort_ok _ ?t|- _]=>
      move: H' => /check_sort_okP; rewrite H; auto
    | [H : check_is_exp ?e = false, H' : is_exp ?e|- _]=>
      move: H' => /check_is_expP; rewrite H; auto
    | [|- is_exp _]=> apply /check_is_expP; auto
    | [|- is_true (_\in_)]=> by apply named_list_lookup_err_in
    | [H: Some _ = named_list_lookup_err _ _|- _]=>
      apply named_list_lookup_err_in in H
    | [H1 : is_true((?n,?a)\in ?l),
       H2 : is_true((?n,?b)\in ?l),
       Hfr : is_true(all_notin (map fst ?l))
                       |- _]=>
      let H' := fresh in
      pose proof (in_all_fresh_same Hfr H1 H2) as H';
        clear H2;
        move: H' => /eqP H'; subst
    | [H: None = named_list_lookup_err _ ?n,
       H' : is_true((?n,_)\in _) |- _]=>
      eapply named_list_lookup_none in H;
      erewrite H' in H; simpl in H; inversion H
    | [H: ~(is_true(_&&_)) |-_]=>
       move: H => /negP /nandP [] H
    | [H: (_&&_)=false |-_]=>
       move: H => /nandP [] H
    |[H:is_true(~~_)|-_] => move: H => /negP H
    |[H :context [(named_list_lookup_err _ _ == (do ret _))] |- _] =>
     rewrite named_list_lookup_err_inb in H
             end.
    { (*TODO: automate*)
      eapply term_ok_con.
      apply named_list_lookup_err_in; eauto.
      apply /check_args_okP; auto.
    }
    { (*TODO: automate*)
      eapply term_ok_ax.
      apply named_list_lookup_err_in; eauto.
      apply /check_args_okP; auto.
    }
    admit (*TODO: need to fix t in theorem for induction*).
    admit (*TODO: need to fix t in theorem for induction*).
    {
      rewrite HeqH0 in H.
      move: H => /check_term_okP H; apply H; auto.
    }
    
    (* TODO: finish (might still have bugs)
    eapply term_ok_trans.
    constructor.
    TODO: false case for term_ok
    { (*TODO: automate*)
      move: H => /eqP H.
      eapply sort_ok_con; eauto.
      apply /check_args_ok'P; auto.
    }
    { (*TODO: automate*)
      eapply sort_ok_ax; eauto.
      apply /check_args_ok'P; auto.
    }*)
   (* TODO: break 2 directions up to make the fixpoint go through?
                reflection harder to reason about wrt termination
      prob not necessary w/ right recursion*)
    (*Guarded.*)*)
  Admitted.

  Fixpoint check_ctx_ok c :=
    match c with
    | [::] => true
    | (name,t)::c' =>
      (fresh name c') &&
      (check_sort_ok c' t) &&
      (check_ctx_ok c')
    end.

  
  Lemma ctx_ok_all_fresh c
    : ctx_ok c -> all_fresh c.
  Proof using.
    induction c; intro cok; inversion cok; subst; clear cok; break; simpl in *;
      break_goal; auto.
  Qed.
  Hint Resolve ctx_ok_all_fresh : pfcore.

  Lemma check_ctx_okP c : all_fresh l -> reflect (ctx_ok c) (check_ctx_ok c).
  Proof using.
    intro frl.
    induction c; intros; break; simpl; repeat constructor.
    repeat lazymatch goal with
           | [|- reflect _ (_&&_)]=>
             (destruct_reflect_andb_l; simpl)
           end.
    lazymatch goal with
    | [|- reflect _ ?p]=>
      let H := fresh in my_case H p
    end.
    all: constructor.
    {
      constructor;
      inversion IHc; auto.
      apply /check_sort_okP; auto using ctx_ok_all_fresh.
    }
    all: intro cok; inversion cok; subst; clear cok.
      match goal with
        [ H : reflect _ false |-_]=> inversion H
      end; auto using ctx_ok_all_fresh.
      match goal with
        [ frl : is_true(all_fresh l),
          H : false = check_sort_ok ?c ?p,
          H' : sort_ok ?c ?p |-_]=>
        move: H' => /(check_sort_okP); intro H';
        rewrite <-H in H'; auto using ctx_ok_all_fresh
      end.
      simpl in H2.
      rewrite <-Heqb in H2; inversion H2.
  Qed.
    
  Definition check_rule_ok r :=
    match r with
    | sort_rule_pf c args =>
      (check_ctx_ok c) && (subseq args (map fst c))
    | term_rule_pf c args t =>
      (check_ctx_ok c) &&
      (subseq args (map fst c)) &&
      (check_sort_ok c t)
    | sort_le_pf c t1 t2 =>
      (check_ctx_ok c) &&
      (check_is_exp t1) &&
      (check_is_exp t2) &&
      (check_sort_ok c t1) &&
      (check_sort_ok c t2)
    | term_le_pf c e1 e2 t =>
      (check_ctx_ok c) &&
      (check_is_exp e1) &&
      (check_is_exp e2) &&
      (check_is_exp t) &&
      (check_term_ok c e1 t) &&
      (check_term_ok c e2 t) &&
      (check_sort_ok c t)
    end.

  Lemma check_rule_okP r : all_fresh l -> reflect (rule_ok r) (check_rule_ok r).
  Proof using.
    intro frl.
    pose proof ctx_ok_all_fresh.
    destruct r; intros; break; simpl; repeat constructor;
    solve_reflect_norec;
    repeat lazymatch goal with
    | [H : true = true |-_]=> clear H
    | [H : true = ?a |-_]=> symmetry in H
    | [H : ?a=true |-_]=> change (is_true a) in H
    | [H : false = false |-_]=> clear H
    | [H : false = ?a |-_]=> symmetry in H
    | [H : ?a = false, H': is_true ?a |-_]=> rewrite H in H'; inversion H'
    | [|- reflect _ true]=> constructor
    | [|- reflect _ false]=> constructor
    | [|- reflect _ ?p]=>
      let H := fresh in my_case H p
    | [|- ~_]=> let H:= fresh in intro H; inversion H; subst; clear H; auto
    | [|- rule_ok _]=> constructor; auto
    | [|- term_ok _ _ _]=> apply /check_term_okP; auto
    | [|- sort_ok _ _]=> apply /check_sort_okP; auto
    | [|- ctx_ok _]=> apply /check_ctx_okP; auto
    | [H : check_term_ok _ ?e ?t = false, H' : term_ok _ ?e ?t|- _]=>
      move: H' => /check_term_okP; rewrite H; auto
    | [H : check_sort_ok _ ?t = false, H' : sort_ok _ ?t|- _]=>
      move: H' => /check_sort_okP; rewrite H; auto
    | [H : check_ctx_ok _ = false, H' : ctx_ok _|- _]=>
      move: H' => /check_ctx_okP; rewrite H; auto
    | [H : check_is_exp ?e = false, H' : is_exp ?e|- _]=>
      move: H' => /check_is_expP; rewrite H; auto
    | [H : is_true(check_ctx_ok _)|- _]=>
      move: H => /check_ctx_okP H
    | [|- is_exp _]=> apply /check_is_expP; auto
    end; auto.
  Qed.
  
End TermsAndRules.


Inductive lang_ok : pf_lang -> Prop :=
| lang_ok_nil : lang_ok [::]
| lang_ok_cons : forall name l r,
    fresh name l ->
    lang_ok l ->
    rule_ok l r ->
    lang_ok ((name,r)::l).


Fixpoint check_lang_ok l :=
    match l with
    | [::] => true
    | (name,r)::l' =>
      (fresh name l') &&
      (check_rule_ok l' r) &&
      (check_lang_ok l')
    end.


Lemma check_lang_ok_all_fresh l : check_lang_ok l -> all_fresh l.
Proof using.
  induction l; intros; repeat (break; simpl in * ); break_goal; auto.
Qed.


Lemma check_lang_okP l : reflect (lang_ok l) (check_lang_ok l).
Proof using.
  induction l; intros; break; simpl; repeat constructor;
    repeat lazymatch goal with
    | [H : true = true |-_]=> clear H
    | [H : true = ?a |-_]=> symmetry in H
    | [H : ?a=true |-_]=> change (is_true a) in H
    | [H : false = false |-_]=> clear H
    | [H : false = ?a |-_]=> symmetry in H
    | [H : ?a = false, H': is_true ?a |-_]=> rewrite H in H'; inversion H'
    | [|- reflect _ true]=> constructor
    | [|- reflect _ false]=> constructor
    | [H:reflect ?a false, H' : ?a|-_]=>
      move: H' => /H H'; inversion H'
    | [|- reflect _ (_&&_)]=>
      (destruct_reflect_andb_l; simpl)
    | [|- reflect _ ?p]=>
      let H := fresh in my_case H p
    | [|- ~_]=> let H:= fresh in intro H; inversion H; subst; clear H; auto
    | [|- rule_ok _]=> constructor; auto
    | [|- term_ok _ _ _]=> apply /check_term_okP; auto
    | [|- sort_ok _ _]=> apply /check_sort_okP; auto
    | [|- ctx_ok _]=> apply /check_ctx_okP; auto
    | [H : check_term_ok _ ?e ?t = false, H' : term_ok _ ?e ?t|- _]=>
      move: H' => /check_term_okP; rewrite H; auto
    | [H : check_sort_ok _ ?t = false, H' : sort_ok _ ?t|- _]=>
      move: H' => /check_sort_okP; rewrite H; auto
    | [H : check_ctx_ok _ = false, H' : ctx_ok _|- _]=>
      move: H' => /check_ctx_okP; rewrite H; auto
    | [H : check_rule_ok _ _ = false, H' : rule_ok _ _|- _]=>
      move: H' => /check_rule_okP; rewrite H; auto
    | [H : check_is_exp ?e = false, H' : is_exp ?e|- _]=>
      move: H' => /check_is_expP; rewrite H; auto
    | [H : is_true(check_ctx_ok _)|- _]=>
      move: H => /check_ctx_okP H
    | [|- is_exp _]=> apply /check_is_expP; auto
    | [|- lang_ok (_::_)]=> constructor
           end; auto.
  apply /IHl; auto.
  apply /check_rule_okP; auto.
  apply check_lang_ok_all_fresh; auto.
  {
    move: H4 => /IHl /check_lang_ok_all_fresh; auto.
  }
  {
    simpl in H3; rewrite Heqb in H3; auto.
  }
Qed.


Lemma lang_ok_all_fresh l : lang_ok l -> all_fresh l.
Proof.
  induction l; break; simpl in *;
    intro H; inversion H; subst; break_goal; auto.
Qed.  

Ltac destruct_is_dom e :=
      destruct e; intros;
      [ eapply dom_var
      | eapply dom_con
      | eapply dom_ax_sort
      | eapply dom_ax_term
      | eapply dom_sym
      | eapply dom_trans
      | eapply dom_conv].
Ltac destruct_is_codom e :=
      destruct e; intros;
      [ eapply codom_var
      | eapply codom_con
      | eapply codom_ax_sort
      | eapply codom_ax_term
      | eapply codom_sym
      | eapply codom_trans
      | eapply codom_conv].

Lemma is_dom_monotonicity t t' n r l
  : is_dom l t t' -> is_dom ((n,r)::l) t t'
with is_codom_monotonicity t t' n r l
     : is_codom l t t' -> is_codom ((n,r)::l) t t'.
Proof.
    
    all:intro d; first [destruct_is_dom d | destruct_is_codom d];
      repeat match goal with
             |[H : List.Forall2 _ _ _ |-_]=>
              induction H; constructor; eauto
            |[|- is_true (_ \in _::_)]=>
             rewrite in_cons; apply /orP; right; eauto
             end; eauto.
Qed.


Ltac destruct_term_ok e :=
  destruct e; intros;
  [ eapply term_ok_ax
  | eapply term_ok_con
  | eapply term_ok_trans
  | eapply term_ok_sym
  | eapply term_ok_var
  | eapply term_ok_conv].


Ltac destruct_sort_ok s :=
  destruct s; intros;
  [ eapply sort_ok_ax
  | eapply sort_ok_con
  | eapply sort_ok_trans
  | eapply sort_ok_sym].

Fixpoint sort_lang_monotonicity l c t name r
     (les : sort_ok l c t) {struct les}
     : sort_ok ((name,r)::l) c t
with term_lang_monotonicity l c e t name r
     (letm: term_ok l c e t) {struct letm}
     : term_ok ((name,r)::l) c e t
with args_lang_monotonicity l c al c' name r
     (lea : args_ok l c al c') {struct lea}
     : args_ok ((name,r)::l) c al c'.
Proof.
  {
    destruct_sort_ok les; 
      repeat match goal with
             |[|- is_true (_ \in _::_)]=>
              rewrite in_cons; apply /orP; right; eauto
             end; eauto using is_dom_monotonicity, is_codom_monotonicity.
  }
  {
      destruct_term_ok letm;
      repeat match goal with
             |[|- is_true (_ \in _::_)]=>
              rewrite in_cons; apply /orP; right; eauto
             end; eauto using is_dom_monotonicity, is_codom_monotonicity.
  }
  {
    destruct lea; constructor; eauto.
  }
Qed.

(*TODO: move to pf.v*)
Lemma pf_subst_nil p : pf_subst [::] p = p.
Proof.
  induction p; simpl; auto.
  { revert H; induction l; intros; simpl in *; break; simpl in *; auto.
    f_equal; f_equal; auto.
    pose proof (IHl H0) as H'; inversion H'.
    rewrite H2.
    assumption.
  }
  { revert H; induction pfs; intros; simpl in *; break; simpl in *; auto.
    f_equal; f_equal; auto.
    pose proof (IHpfs H0) as H'; inversion H'.
    rewrite H2.
    assumption.
  }
  {
    rewrite IHp; reflexivity.
  }
  {
    rewrite IHp1 IHp2; reflexivity.
  }
  {
    rewrite IHp1 IHp2; reflexivity.
  }
Qed.

Lemma map_pf_subst_nil pl : map (pf_subst [::]) pl = pl.
Proof.
  induction pl; simpl; rewrite ?pf_subst_nil; f_equal; auto.
Qed.

Lemma is_dom_subst_monotonicity l t t' s s'
  : is_dom l t t' -> List.Forall2 (fun p1 p2 => p1.1 = p2.1 /\ is_dom l p1.2 p2.2) s s' -> is_dom l (pf_subst s t) (pf_subst s' t')
with is_codom_subst_monotonicity l t t' s s'
     : is_codom l t t' -> List.Forall2 (fun p1 p2 => p1.1 = p2.1 /\ is_codom l p1.2 p2.2) s s' -> is_codom l (pf_subst s t) (pf_subst s' t').
Proof.
  all: intro d; destruct d; simpl; try solve [constructor; eauto].
  {
    intro lfs; induction lfs;  break; simpl in *; subst; [constructor | case_match; auto].    
  }
  {
    intro lfs; constructor.
    induction H; break; simpl in *; subst; constructor; auto.
  }
  {
    admit
    (*TODO: subst distribution require ok terms *).
  }
  {
    admit
    (*TODO: subst distribution require ok terms *).
  }
  {
    constructor.
    eauto.
    TODO: issue;
  sym needs List.forall2 for codom;
  better to compute dom/codom or add s'' the codom?
  }
  
Qed.*)

(*TODO: figure out which ctxs need to be ok (could be all)
*)
Lemma sort_subst_monotonicity l c t c' s
  : sort_ok l c t -> ctx_ok l c -> ctx_ok l c' ->
    subst_ok l c' s c ->
    sort_ok l c' (pf_subst s t)
with term_subst_monotonicity l c e t c' s t'
  : term_ok l c e t -> ctx_ok l c -> ctx_ok l c' ->
    subst_ok l c' s c ->
    is_dom l (pf_subst s t) t' ->
    term_ok l c' (pf_subst s e) t'
with args_subst_monotonicity l c ss c' s c''
  : args_ok l c ss c' -> ctx_ok l c -> ctx_ok l c'' ->
    subst_ok l c'' s c ->
    args_ok l c'' (map (pf_subst s) ss) c'.
Proof.
  {
    intro sok;
      destruct_sort_ok sok; fold pf_subst; eauto.
    TODO: need monotonicity for dom/codom too again
    eapply args_subst_monotonicity.
    repeat match goal with
             |[|- is_true (_ \in _::_)]=>
              rewrite in_cons; apply /orP; right; eauto
             end; eauto using is_dom_monotonicity, is_codom_monotonicity.
  }
  {
      destruct_term_ok letm;
      repeat match goal with
             |[|- is_true (_ \in _::_)]=>
              rewrite in_cons; apply /orP; right; eauto
             end; eauto using is_dom_monotonicity, is_codom_monotonicity.
  }
  {
    destruct lea; constructor; eauto.
  }
Qed.
