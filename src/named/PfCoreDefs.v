Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Pf.

Require Import String.


Create HintDb pfcore discriminated.


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
Hint Constructors is_exp : pfcore.

Fixpoint check_is_exp e : bool :=
  match e with
  | pvar _ => true
  | pcon _ s => List.forallb check_is_exp s
  | conv _ p => check_is_exp p
  | _ => false
  end.
  
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
    : List.Forall2 is_codom pl pl_r ->
      (n, sort_le_pf c p_l p') \in l ->
      is_codom (ax n pl) (pf_subst (with_names_from c pl_r) p')
  | codom_ax_term n pl pl_r c p' p_l t
    : List.Forall2 is_codom pl pl_r ->
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

      
  (*TODO: move to OptionMonad *)
  (*TODO: unused here*)
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
    
  (*Pressupposition: p is ok and l is ok *)
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
 (*Pressupposition: p is ok and l is ok *)
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

   *)
  | term_ok_conv : forall c e t tp t',
      sort_ok c tp ->
      term_ok c e t ->
      is_dom tp t ->
      is_codom tp t' ->
      term_ok c (conv tp e) t'
  with args_ok : pf_ctx -> list pf -> pf_ctx -> Prop :=
  | args_ok_nil : forall c, args_ok c [::] [::]
  | args_ok_cons : forall c s c' name e t t',
      args_ok c s c' ->
      (* assumed because the output ctx is wf: fresh name c' ->*)
      is_dom (pf_subst (with_names_from c' s) t) t' ->
      term_ok c e t' ->
      args_ok c (e::s) ((name, t)::c').
  
  Inductive subst_ok : pf_ctx -> named_list pf -> pf_ctx -> Prop :=
  | subst_ok_nil : forall c, subst_ok c [::] [::]
  | subst_ok_cons : forall c s c' name e t t',
      subst_ok c s c' ->
      (* assumed because the output ctx is wf: fresh name c' ->*)
      is_dom (pf_subst s t) t' ->
      term_ok c e t' ->
      subst_ok c ((name,e)::s) ((name, t)::c').

  Inductive ctx_ok : pf_ctx -> Prop :=
  | ctx_ok_nil : ctx_ok [::]
  | ctx_ok_cons : forall name c v,
      fresh name c ->
      ctx_ok c ->
      sort_ok c v ->
      ctx_ok ((name,v)::c).

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
  
  Section InnerLoop.
    Context (check_term_ok : pf -> pf -> bool).

    Fixpoint check_args_ok' (pl : list pf) (c' : pf_ctx) {struct pl} : bool :=
      match pl, c' with
      | [::], [::] => true
      | p::pl', (_,t)::c'' =>
        match dom (pf_subst (with_names_from c'' pl') t) with
        | Some t' => (check_term_ok p t') &&
                    (check_args_ok' pl' c'')
        | None => false
        end
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
         
  End InnerLoop.
  
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

  Fixpoint check_ctx_ok c :=
    match c with
    | [::] => true
    | (name,t)::c' =>
      (fresh name c') &&
      (check_sort_ok c' t) &&
      (check_ctx_ok c')
    end.

    
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

Hint Constructors is_dom is_codom : pfcore.
Hint Constructors sort_ok term_ok subst_ok args_ok ctx_ok rule_ok lang_ok : pfcore.
