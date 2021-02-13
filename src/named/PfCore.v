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

  (*TODO: rename these to dom and codom? *)
  (*Pressupposition: p is ok *)
  Fixpoint proj_l (p:pf) :=
    match p with
    | pvar x => (pvar x)
    | pcon name pl => pcon name (map proj_l pl)
    | ax name pl =>
      match named_list_lookup_err l name with
      | Some (sort_le_pf c p' _)
      | Some (term_le_pf c p' _ _) =>
        pf_subst (with_names_from c (map (proj_l) pl)) p'
      | _ => pcon "ERR" [::]
      end
    | sym p => proj_r p
    | trans p1 p2 => proj_l p1
    | conv pt p' => conv pt (proj_l p')
    end
  (*Pressupposition: p is ok *)
  with proj_r (p:pf) :=
    match p with
    | pvar x => (pvar x)
    | pcon name pl => pcon name (map proj_l pl)
    | ax name pl =>
      match named_list_lookup_err l name with
      | Some (sort_le_pf c _ p')
      | Some (term_le_pf c _ p' _) =>
        pf_subst (with_names_from c (map (proj_l) pl)) p'
      | _ => pcon "ERR" [::]
      end
    | sym p => proj_l p
    | trans p1 p2 => proj_r p2
    | conv pt p' => conv pt (proj_l p')
    end.

  (* Strips components of the proof that we consider
     irrelevant for the purpose of equality.
     TODO: generalize this, e.g. (sym (sym x)) ~ x.
     Probably not necessary as long as this is only
     used on projections
   *)
  Fixpoint strip_irrelevant (e : pf) : pf :=
    match e with
    | pvar x => (pvar x)
    | pcon name pl => 
      match named_list_lookup_err l name with
      | Some (sort_rule_pf c args)
      | Some (term_rule_pf c args _) =>
        match get_subseq args (with_names_from c (map (proj_l) pl)) with
        | Some pl' => pcon name (map snd pl')
        | None => pcon "ERR" [::]
        end
      | _ => pcon name (map strip_irrelevant pl)
      end
    | ax name pl => ax name (map strip_irrelevant pl)
    | sym p => sym (strip_irrelevant p)
    | trans p1 p2 => trans (strip_irrelevant p1) (strip_irrelevant p2)
    | conv _ p' => (strip_irrelevant p')
    end.

  (* TODO: this is a shortcut; it's probably safe but should
     be generalized at some point.
     Current potential issues: 
     -sym, trans in sorts
     Should definitely be safe when used on projections

    TODO: define (proj_l a `eq_pf_irr` proj_r b) as a
    relation for ease-of-proof?
   *)
  Definition eq_pf_irr (e1 e2 : pf): bool :=
    (strip_irrelevant e1) == (strip_irrelevant e2).
  
  (*
    Judgments for checking proofs of relations between programs.
    Can check wfness of a program by identifying it with its
    identity relation.

    All assume lang_ok.
    All ctxs (other than in ctx_ok) are assumed to satisfy ctx_ok.
    Judgments whose assumptions take ctxs must ensure they are ok.
    Sorts are not assumed to be ok; the term judgments should guarantee
    that their sorts are ok.
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
  | sort_ok_trans : forall c t1 t2,
      sort_ok c t1 ->
      sort_ok c t2 ->
      eq_pf_irr (proj_r t1) (proj_l t2) ->
      sort_ok c (trans t1 t2)
  | sort_ok_sym : forall c t, sort_ok c t -> sort_ok c (sym t)
  with term_ok : pf_ctx -> pf -> pf -> Prop :=
  | term_ok_ax : forall c c' name e1 e2 t s,
      (name, term_le_pf c' e1 e2 t) \in l ->
      args_ok c s c' ->
      (*non-obvious fact: the sort may not be a wfness proof;
        may be a non-identity relation due to s
       *)
      term_ok c (ax name s) (pf_subst (with_names_from c' s) t)
  | term_ok_con : forall c name c' args t s,
      (name, (term_rule_pf c' args t)) \in l ->
      args_ok c s c' ->
      (* same as above *)
      term_ok c (pcon name s) (pf_subst (with_names_from c' s) t)
  | term_ok_trans : forall c e1 t1 e2 t2,
      term_ok c e1 t1 ->
      term_ok c e2 t2 ->
      eq_pf_irr (proj_r e1) (proj_l e2) ->
      eq_pf_irr (proj_r t1) (proj_l t2) ->
      term_ok c (trans e1 e2) (trans t1 t2)
  | term_ok_sym : forall c e t, term_ok c e t -> term_ok c (sym e) (sym t)
  | term_ok_var : forall c x t,
      (x,t) \in c ->
      term_ok c (pvar x) t
  (* Conversion:

c |- e1 = e2 : t = t'
                 ||
c |- e1 = e2 : t' = t''
   *)
  | term_ok_conv : forall c e t t',
      sort_ok c t' ->
      term_ok c e t ->
      eq_pf_irr (proj_r t) (proj_l t') ->
      term_ok c (conv t' e) (trans t t')
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
        (eq_pf_irr (proj_r p1) (proj_l p2))
      | conv _ _ => false
      | pvar _ => false
      end.

    Hint Constructors reflect : pfcore.
         
  End InnerLoop.

  Fixpoint check_term_ok (c : pf_ctx) e t {struct e} : bool :=
    match e with
    | pvar x =>
      match named_list_lookup_err c x with
      | Some t' => t == t' (*TODO: this lines up w/ the inductive, 
                             but maybe should be pf_eq_irr?
                             Might want to change the inductive.
                             Can be worked around w/ extra convs as is,
                             but that might be easier.
                             Same for other cases.
                            *)
      | None => false
      end
    | pcon name pl =>
      match named_list_lookup_err l name with
      | Some (term_rule_pf c' _ t') =>
        (check_args_ok' (check_term_ok c) pl c') &&
        (t == pf_subst (with_names_from c' pl) t')
      | _ => false
      end
    | ax name pl =>
      match named_list_lookup_err l name with
      | Some (term_le_pf c' _ _ t') => 
        (check_args_ok' (check_term_ok c) pl c') &&
        (t == pf_subst (with_names_from c' pl) t')
      | _ => false
      end
    | sym p =>
      match t with
      | sym t' => check_term_ok c p t'
      | _ => false (*TODO: same thing as ==s above.
                     This works, but it feels like I should use a looser
                     defn of equivalence. Should come back to these if it
                     ends up as a pain point.
                    *)
      end
    | trans p1 p2 => 
      match t with
      | trans t1 t2 =>
        (check_term_ok c p1 t1) &&
        (check_term_ok c p2 t2) &&
        (eq_pf_irr (proj_r p1) (proj_l p2)) &&
        (eq_pf_irr (proj_r t1) (proj_l t2))
      | _ => false (*TODO: same thing as ==s above.
                     This works, but it feels like I should use a looser
                     defn of equivalence. Should come back to these if it
                     ends up as a pain point.
                    *)
      end
    | conv pt p' =>
      match t with
      | trans t1 t2 =>
      (pt == t2) &&
      (eq_pf_irr (proj_r t1) (proj_l t2)) &&
      (check_sort_ok' (check_term_ok c) pt) &&
      (check_term_ok  c p' t1)
      | _ => false (*TODO: same thing as ==s above.
                     This works, but it feels like I should use a looser
                     defn of equivalence. Should come back to these if it
                     ends up as a pain point.
                    *)
      end
    end.

  
  (*TODO: build right induction*)
  Lemma check_term_okP c e t
    : all_fresh l ->
      all_fresh c ->
      reflect (term_ok c e t) (check_term_ok c e t)
  with check_args_ok'P c pl c'
       : all_fresh l ->
         all_fresh c ->
         reflect (args_ok c pl c') (check_args_ok' (check_term_ok c) pl c')
  with check_sort_ok'P c t
      : all_fresh l ->
        all_fresh c ->
        reflect (sort_ok c t) (check_sort_ok' (check_term_ok c) t).
  Proof using.
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
    | [H : is_true(check_term_ok _ ?e ?t) |- term_ok _ ?e ?t]=>
      apply /check_term_okP; auto
    | [H : is_true(check_args_ok' _ ?e ?t) |- args_ok _ ?e ?t]=>
      apply /check_args_ok'P; auto
    | [H : is_true(check_sort_ok' _ ?t) |- sort_ok _ ?t]=>
      apply /check_sort_ok'P; auto
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
    | [|- rule_ok _]=> constructor; auto
    | [|- term_ok _ _ _]=> constructor
    | [|- ctx_ok _]=> apply /check_ctx_okP; auto
    | [H : ~(is_true(check_args_ok' _ ?e ?t)), H' : args_ok _ ?e ?t|- _]=>
      move: H => /negP /check_args_ok'P H;
      exfalso; apply H; auto
    | [H : ~(is_true(check_term_ok _ ?e ?t)), H' : term_ok _ ?e ?t|- _]=>
      move: H => /negP /check_term_okP H;
      exfalso; apply H; auto
    | [H : ~(is_true(check_sort_ok' _ ?t)), H' : sort_ok _ ?t|- _]=>
      move: H => /negP /check_sort_ok'P H;
      exfalso; apply H; auto
    | [H : check_term_ok _ ?e ?t = false, H' : term_ok _ ?e ?t|- _]=>
      move: H' => /check_term_okP; rewrite H; auto
    | [H : check_args_ok' _ ?e ?t = false, H' : args_ok _ ?e ?t|- _]=>
      move: H' => /check_args_ok'P; rewrite H; auto
    | [H : check_sort_ok' _ ?t = false, H' : sort_ok _ ?t|- _]=>
      move: H' => /check_sort_ok'P; rewrite H; auto
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
             end.
    { (*TODO: automate*)
      eapply term_ok_con.
      apply named_list_lookup_err_in; eauto.
      apply /check_args_ok'P; auto.
    }
    { (*TODO: automate*)
      eapply term_ok_ax.
      apply named_list_lookup_err_in; eauto.
      apply /check_args_ok'P; auto.
    }
    { (*TODO: automate*)
      eapply sort_ok_con; eauto.
      apply /check_args_ok'P; auto.
    }
    { (*TODO: automate*)
      eapply sort_ok_ax; eauto.
      apply /check_args_ok'P; auto.
    }
   (* TODO: break 2 directions up to make the fixpoint go through?
                reflection harder to reason about wrt termination
      prob not necessary w/ right recursion*)
    (*Guarded.*)
  Admitted.

  Definition check_sort_ok c t := check_sort_ok' (check_term_ok c) t.
  Definition check_args_ok c s c' := check_args_ok' (check_term_ok c) s c'.

  
  Lemma check_sort_okP c t
      : all_fresh l -> all_fresh c -> reflect (sort_ok c t) (check_sort_ok c t).
  Proof using.
    eauto using check_term_okP, check_sort_ok'P.
  Qed.

  
  Lemma check_args_okP c s c'
    : all_fresh l -> all_fresh c ->
      reflect (args_ok c s c') (check_args_ok c s c').
  Proof using.
    eauto using check_term_okP, check_args_ok'P.
  Qed.

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
  
