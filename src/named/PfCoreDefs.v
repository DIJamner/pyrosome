Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Pf.

Require Import String.


Create HintDb pfcore discriminated.
  
Section TermsAndRules.
  Context (l : wfexp_lang).


  Inductive is_dom : pf -> wfexp -> Prop :=
  | dom_refl e : is_dom (pf_refl e) e
  | dom_ax_sort n c p' p_r
    : (n, wf_sort_le c p' p_r) \in l ->
      is_dom (ax n) p_r
  | dom_ax_term n c p' p_r t
    : (n, wf_term_le c p' p_r t) \in l ->
      is_dom (ax n) p_r
  | dom_sym p p_r
    : is_codom p p_r ->
      is_dom (sym p) p_r
  | dom_trans p1 p2 p1_l
    : is_dom p1 p1_l ->
      is_dom (trans p1 p2) p1_l
  | dom_conv pt p p_l
    : is_dom p p_l ->
      is_dom (pf_conv pt p) (wf_conv pt p_l)
  | dom_subst p e s s'
    : List.Forall2 is_dom (map snd s) s' ->
      is_dom p e ->
      is_dom (pf_subst s p) (wfexp_subst (with_names_from s s') e)
  with is_codom : pf -> wfexp -> Prop :=
  | codom_refl e : is_codom (pf_refl e) e
  | codom_ax_sort n c p' p_r
    : (n, wf_sort_le c p' p_r) \in l ->
      is_codom (ax n) p_r
  | codom_ax_term n c p' p_r t
    : (n, wf_term_le c p' p_r t) \in l ->
      is_codom (ax n) p_r
  | codom_sym p p_r
    : is_dom p p_r ->
      is_codom (sym p) p_r
  | codom_trans p1 p2 p1_l
    : is_codom p1 p1_l ->
      is_codom (trans p1 p2) p1_l
  | codom_conv pt p p_l
    : is_codom p p_l ->
      is_codom (pf_conv pt p) (wf_conv pt p_l)
  | codom_subst p e s s'
    : List.Forall2 is_codom (map snd s) s' ->
      is_codom p e ->
      is_codom (pf_subst s p) (wfexp_subst (with_names_from s s') e).

      
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
    Context (dom : pf -> option wfexp)
            (codom : pf -> option wfexp).
    Fixpoint dom_args (pl : subst_pf) :=
      match pl with
      | [::] => do ret [::]
      | (n,a)::pl' =>
        do pl'_dom <- dom_args pl';
           b <- dom a;
           ret ((n,b)::pl'_dom)
      end.

    Fixpoint codom_args (pl : subst_pf) :=
         match pl with
         | [::] => do ret [::]
         | (n,a)::pl' =>
           do pl'_codom <- codom_args pl';
              b <- codom a;
              ret ((n,b)::pl'_codom)
         end.
  End DomInnerLoop.
    
  (*Pressupposition: p is ok and l is ok *)
  Fixpoint dom (p:pf) :=
    match p with
    | pf_refl e => do ret e
    | ax name =>
      match named_list_lookup_err l name with
      | Some (wf_sort_le c p' _)
      | Some (wf_term_le c p' _ _) =>
        do ret p'
      | _ => None
      end
    | sym p => codom p
    | trans p1 p2 => dom p1
    | pf_conv pt p' => omap (wf_conv pt) (dom p')
    | pf_subst s p' => 
      do s' <- dom_args dom s;
         e <- dom p';
      ret wfexp_subst s' e
    end
 (*Pressupposition: p is ok and l is ok *)
  with codom (p:pf) :=
    match p with
    | pf_refl e => do ret e
    | ax name =>
      match named_list_lookup_err l name with
      | Some (wf_sort_le c _ p')
      | Some (wf_term_le c _ p' _) =>
        do ret p'
      | _ => None
      end
    | sym p => dom p
    | trans p1 p2 => codom p1
    | pf_conv pt p' => omap (wf_conv pt) (codom p')
    | pf_subst s p' => 
      do s' <- codom_args codom s;
         e <- codom p';
      ret wfexp_subst s' e
      end.

  (*All assume wf_lang.
    All ctxs (other than in wf_ctx) are assumed to satisfy wf_ctx.
    Judgments whose assumptions take ctxs must ensure they are wf.
    Sorts are not assumed to be wf; the term judgments should guarantee
    that their sorts are wf.
   *)

  (* TODO: not using dom/codom here is probably easier for my current
     purposes, but should I reconsider later? can always connect 2 relations
     via proofs
     TODO: double-check definitions
   *)
  Inductive le_sort : wfexp_ctx -> pf -> wfexp -> wfexp -> Prop :=
  | le_sort_by : forall c name t1 t2,
      (name, wf_sort_le c t1 t2) \in l ->
      le_sort c (ax name) t1 t2
  | le_sort_subst : forall c ps pt s1 s2 c' t1' t2',
      (* Need to assert wf_ctx c here to satisfy
         assumptions' presuppositions
       *)
      wf_ctx c' ->
      le_subst c c' ps s1 s2 ->
      le_sort c' pt t1' t2' ->
      le_sort c (pf_subst ps pt) (wfexp_subst s1 t1') (wfexp_subst s2 t2')
  | le_sort_refl : forall c t,
      wf_sort c t ->
      le_sort c (pf_refl t) t t
  | le_sort_trans : forall c p1 p2 t1 t12 t2,
      le_sort c p1 t1 t12 ->
      le_sort c p2 t12 t2 ->
      le_sort c (trans p1 p2) t1 t2
  | le_sort_sym : forall c p t1 t2, le_sort c p t1 t2 -> le_sort c (sym p) t2 t1
  with le_term : wfexp_ctx -> pf -> wfexp (*sort*) -> wfexp -> wfexp -> Prop :=
  | le_term_subst : forall c s1 s2 c' ps p t e1 e2,
      (* Need to assert wf_ctx c' here to satisfy
         assumptions' presuppositions
       *)
      wf_ctx c' ->
      le_subst c c' ps s1 s2 ->
      le_term c' p t e1 e2 ->
      le_term c (pf_subst ps p) (wfexp_subst s2 t)
              (wfexp_subst s1 e1) (wfexp_subst s2 e2)
  | le_term_by : forall c name t e1 e2,
      (name,wf_term_le c e1 e2 t) \in l ->
      le_term c (ax name) t e1 e2
  | le_term_refl : forall c e t,
      wf_term c e t ->
      le_term c (pf_refl e) t e e
  | le_term_trans : forall c t p1 p2 e1 e12 e2,
      le_term c p1 t e1 e12 ->
      le_term c p2 t e12 e2 ->
      le_term c (trans p1 p2) t e1 e2
  | le_term_sym : forall c p t e1 e2, le_term c p t e1 e2 -> le_term c (sym p) t e2 e1
  (* Conversion:

c |- e1 = e2 : t 
               ||
c |- e1 = e2 : t'
   *)
  | le_term_conv : forall c t t' pt p,
      le_sort c pt t t' ->
      forall e1 e2,
        le_term c p t e1 e2 ->
        le_term c (pf_conv pt p) t' (wf_conv pt e1) (wf_conv pt e2)
  with le_subst : wfexp_ctx -> wfexp_ctx -> subst_pf -> subst_wf -> subst_wf -> Prop :=
  | le_subst_nil : forall c, le_subst c [::] [::] [::] [::]
  | le_subst_cons : forall c c' pfs s1 s2,
      le_subst c c' pfs s1 s2 ->
      forall name p t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        le_term c p (wfexp_subst s2 t) e1 e2 ->
        le_subst c ((name, t)::c') ((name,p)::pfs) ((name,e1)::s1) ((name,e2)::s2)
  with wf_term : wfexp_ctx -> wfexp -> wfexp (*sort*) -> Prop :=
  | wf_term_by : forall c n s args es c' t,
      (n, wf_term_rule c' args t) \in l ->
      wf_args c es c' ->
      wf_term c (wf_con n s) (wfexp_subst (with_names_from c' es) t)
  | wf_term_conv : forall c p e t t',
      (* We add this condition so that we satisfy the assumptions of le_sort
         TODO: necessary? not based on current judgment scheme.
         wf_term c e t should imply wf_sort c t,
         and le_sort c t t' should imply wf_sort c t


      wf_sort c t -> 
       *)
      wf_term c e t ->
      le_sort c p t t' ->
      wf_term c (wf_conv p e) t'
  | wf_term_var : forall c n t,
      (n, t) \in c ->
                 wf_term c (wf_var n) t
  with wf_args : wfexp_ctx -> list wfexp -> wfexp_ctx -> Prop :=
  | wf_args_nil : forall c, wf_args c [::] [::]
  | wf_args_cons_ex : forall c es c' name e t,
      wf_term c e (wfexp_subst (with_names_from c' es) t) ->
      wf_args c es c' ->
      wf_args c (e::es) ((name,t)::c')
  with wf_sort : wfexp_ctx -> wfexp (*sort*) -> Prop :=
  | wf_sort_by : forall c n s args es c',
      (n, (wf_sort_rule c' args)) \in l ->
      wf_args c es c' ->
      wf_sort c (wf_con n s)
  with wf_ctx : wfexp_ctx -> Prop :=
  | wf_ctx_nil : wf_ctx [::]
  | wf_ctx_cons : forall name c v,
      fresh name c ->
      wf_ctx c ->
      wf_sort c v ->
      wf_ctx ((name,v)::c).

  Inductive wf_subst c : subst_wf -> wfexp_ctx -> Prop :=
  | wf_subst_nil : wf_subst c [::] [::]
  | wf_subst_cons : forall s c' name e t,
      (* assumed because the output ctx is wf: fresh name c' ->*)
      wf_subst c s c' ->
      wf_term c e (wfexp_subst s t) ->
      wf_subst c ((name,e)::s) ((name,t)::c').

  (*
  Inductive le_args : ctx -> ctx -> list exp -> list exp -> list string -> list exp -> list exp -> Prop :=
  | le_args_nil : forall c, le_args c [::] [::] [::] [::] [::] [::]
  | le_args_cons_ex : forall c c' s1 s2 args es1 es2,
      le_args c c' s1 s2 args es1 es2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        le_term c t[/with_names_from c' es2/] e1 e2 ->
        le_args c ((name, t)::c') (e1::s1) (e2::s2) (name::args) (e1::es1) (e2::es2)
  | le_args_cons_im : forall c c' s1 s2 args es1 es2,
      le_args c c' s1 s2 args es1 es2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        le_term c t[/with_names_from c' es2/] e1 e2 ->
        le_args c ((name, t)::c') s1 s2 args (e1::es1) (e2::es2)
   *)

  (*TODO: fix naming*)
  Variant wf_rule : wfexp_rule -> Prop :=
  | wf_sort_rule : forall c args,
      wf_ctx c ->
      subseq args (map fst c) ->
      wf_rule (wf_sort_rule c args)
  | wf_term_rule : forall c args t,
      wf_ctx c ->
      wf_sort c t ->
      subseq args (map fst c) ->
      wf_rule (wf_term_rule c args t)
  | le_sort_rule : forall c t1 t2,
      wf_ctx c ->
      wf_sort c t1 ->
      wf_sort c t2 ->
      wf_rule (wf_sort_le c t1 t2)
  | le_term_rule : forall c e1 e2 t,
      wf_ctx c ->
      wf_sort c t ->
      wf_term c e1 t ->
      wf_term c e2 t ->
      wf_rule (wf_term_le c e1 e2 t).

  (*
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
         d <-(dom (pf_subst (with_names_from c' pl) t'));
         ret d
    | ax name pl =>
      do (term_le_pf c' _ _ t') <- named_list_lookup_err l name;
         ! check_args_ok' check_term_ok pl c';
         d <-(dom (pf_subst (with_names_from c' pl) t'));
         ret d
    | sym p => synth_term_ok c p
    | trans p1 p2 =>
      do t1 <- synth_term_ok c p1;
         t2 <- synth_term_ok c p2;
         (* would be nicer to write it like this, but it makes proofs harder:
         ! codom p1 == dom p2;
         TODO: figure out for case above
          *)
         cd1 <- codom p1;
         d2 <- dom p2;
         !cd1 == d2;
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
*)
  
End TermsAndRules.

Inductive wf_lang : wfexp_lang -> Prop :=
| lang_ok_nil : wf_lang [::]
| lang_ok_cons : forall name l r,
    fresh name l ->
    wf_lang l ->
    wf_rule l r ->
    wf_lang ((name,r)::l).

(*
Fixpoint check_lang_ok l :=
    match l with
    | [::] => true
    | (name,r)::l' =>
      (fresh name l') &&
      (check_rule_ok l' r) &&
      (check_lang_ok l')
    end.
*)

Hint Constructors is_dom is_codom : pfcore.

Hint Constructors le_sort le_term le_subst (*le_args*)
     wf_sort wf_term wf_subst wf_args wf_ctx wf_rule wf_lang : pfcore.
