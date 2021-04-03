Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils BoolAsProp.
From Named Require Import Pf.
From Named Require Export PfCoreDefs.
Import OptionMonad.

Require Import String.

Lemma invert_is_exp_var x : is_exp (pvar x) <-> True.
Proof.
  split; [intro H; inversion H| intros; subst];
    eauto with pfcore.
Qed.
Hint Rewrite invert_is_exp_var : pfcore.
Lemma invert_is_exp_con n1 pl
  : is_exp (pcon n1 pl) <-> List.Forall is_exp pl.
Proof.
  split.
  - intro H; inversion H; eauto with pfcore.
  - firstorder; subst; eauto with pfcore.
Qed.
Hint Rewrite invert_is_exp_con : pfcore.  
Lemma invert_is_exp_ax n pfs
  : is_exp (ax n pfs) <-> False.
Proof.
  split;intro H; inversion H; subst; eauto with pfcore.
Qed.
Hint Rewrite invert_is_exp_ax : pfcore.

Lemma invert_is_exp_sym p : is_exp (sym p) <-> False.
Proof.
  split; [intro H; inversion H| intros; subst];
    firstorder;
    eauto with pfcore.
Qed.
Hint Rewrite invert_is_exp_sym : pfcore.

Lemma invert_is_exp_trans p1 p2 : is_exp (trans p1 p2) <-> False.
Proof.
  split; [intro H; inversion H| intros; subst]; intuition;
    eauto with pfcore.
Qed.
Hint Rewrite invert_is_exp_trans : pfcore.

Lemma invert_is_exp_conv pt p
  : is_exp (conv pt p) <-> is_exp p.
Proof.
  split; [intro H; inversion H| intros; subst];
    firstorder; subst;
      eauto with pfcore.
Qed.
Hint Rewrite invert_is_exp_conv : pfcore.

(*TODO: move to utils/rewriting package*)
Lemma invert_list_Forall_nil A (P : A -> Prop)
  : List.Forall P [::] <-> True.
Proof.
  intuition; intro H; safe_invert H.
Qed.
Hint Rewrite invert_list_Forall_nil : utils.
Lemma invert_list_Forall_cons A (P : A -> Prop) a l
  : List.Forall P (a::l) <-> P a /\ List.Forall P l.
Proof.
  intuition;
  safe_invert H; auto.  
Qed.
Hint Rewrite invert_list_Forall_cons : utils.


Lemma check_is_exp_iff e : (check_is_exp e) <-> (is_exp e).
Proof.
  induction e; simpl; autorewrite with pfcore bool_utils utils; try solve [intuition].
  revert H; induction l; simpl; autorewrite with pfcore bool_utils utils in *;
    intuition.
Qed.  
Hint Rewrite check_is_exp_iff : pfcore.

Lemma check_is_expP e : reflect (is_exp e) (check_is_exp e).
Proof using.
  reflect_from_iff check_is_exp_iff.
Qed.

(*TODO: pull/duplicate appropriate hints outside the section*)
Section TermsAndRules.
  Context (l : pf_lang).
  Context (l_ok : lang_ok l).

  
  Lemma lang_ok_all_fresh : all_fresh l.
  Proof.
    revert l_ok; induction l; break; simpl in *;
      intro H; inversion H; subst; break_goal; auto.
  Qed.
  Hint Resolve lang_ok_all_fresh : pfcore.

  Local Notation is_dom := (@is_dom l).
  Local Notation is_codom := (@is_codom l).
  Local Notation dom := (@dom l).
  Local Notation codom := (@codom l).

  (*
    Congruence lemmas for rewriting
    TODO: go in Pf?
   *)
  Lemma pvar_cong x y : pvar x = pvar y <-> x = y.
  Proof.
    intuition; inversion H; eauto with pfcore.
  Qed.
  Hint Rewrite pvar_cong : pfcore.
  Lemma pcon_cong n1 n2 pl1 pl2 : pcon n1 pl1 = pcon n2 pl2 <-> (n1 = n2 /\ pl1 = pl2).
  Proof.
    intuition; subst; try inversion H; eauto with pfcore.
  Qed.
  Hint Rewrite pcon_cong : pfcore.
    
  (*Inversion lemmas for rewriting is_dom and is_codom
    when we know the top-level structure of their arguments
   *)
  Lemma invert_is_dom_var x p : is_dom (pvar x) p <-> p = pvar x.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_dom_var : pfcore.
  Lemma invert_is_dom_con n1 p pl
    : is_dom (pcon n1 pl) p
      <-> (exists pl_r, (List.Forall2 is_dom pl pl_r) /\ p = pcon n1 pl_r).
  Proof.
    split.
    - intro H; inversion H; eauto with pfcore.
    - firstorder; subst; eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_dom_con : pfcore.
  
  Lemma invert_is_dom_ax n pfs p'
    : is_dom (ax n pfs) p' <->
      (exists r, (n,r) \in l /\ 
                 match r with
                 | sort_le_pf c p _
                 | term_le_pf c p _ _ =>
                   exists pl_r, List.Forall2 is_dom pfs pl_r /\
                                p' = pf_subst (with_names_from c pl_r) p
                 | _ => False
                 end).
  Proof.
    split.
    - intro H; inversion H; subst;
      match goal with [H : is_true((_, ?r) \in _)|-_] =>
                        exists r
        end; eauto with pfcore.
    - move => [r [rin ]].
      destruct r; cbn; try easy;
      move => [pl_r [ peq fall]]; subst; eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_dom_ax : pfcore.
  
  Lemma invert_is_dom_sym p p' : is_dom (sym p) p' <-> is_codom p p'.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_dom_sym : pfcore.
  
  Lemma invert_is_dom_trans p1 p2 p' : is_dom (trans p1 p2) p' <-> is_dom p1 p'.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_dom_trans : pfcore.
  
  Lemma invert_is_dom_conv pt p p'
    : is_dom (conv pt p) p' <->
      exists p'', is_dom p p'' /\ p' = (conv pt p'') .
  Proof.
    split; [intro H; inversion H| intros; subst];
      firstorder; subst;
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_dom_conv : pfcore.

  Lemma invert_is_codom_var x p : is_codom (pvar x) p <-> p = pvar x.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_codom_var : pfcore.
  Lemma invert_is_codom_con n1 p pl
    : is_codom (pcon n1 pl) p
      <-> exists pl_r, List.Forall2 is_codom pl pl_r /\ p = pcon n1 pl_r.
  Proof.
    split.
    - intro H; inversion H; eauto with pfcore.
    - firstorder; subst; eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_codom_con : pfcore.
  
  Lemma invert_is_codom_ax n pfs p'
    : is_codom (ax n pfs) p' <->
      (exists r, (n,r) \in l /\ 
                 match r with
                 | sort_le_pf c _ p
                 | term_le_pf c _ p _ =>
                   exists pl_r, List.Forall2 is_codom pfs pl_r /\
                                p' = pf_subst (with_names_from c pl_r) p                                
                 | _ => False
                 end).
  Proof.
    split.
    - intro H; inversion H; subst;
      match goal with [H : is_true((_, ?r) \in _)|-_] =>
                        exists r
        end; eauto with pfcore.
    - move => [r [rin ]].
      destruct r; cbn; try easy;
      move => [pl_r [ peq fall]]; subst; eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_codom_ax : pfcore.

  Lemma invert_is_codom_sym p p' : is_codom (sym p) p' <-> is_dom p p'.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_codom_sym : pfcore.
  
  Lemma invert_is_codom_trans p1 p2 p' : is_codom (trans p1 p2) p' <-> is_codom p2 p'.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_codom_trans : pfcore.
  
  Lemma invert_is_codom_conv pt p p'
    : is_codom (conv pt p) p' <->
      exists p'', is_codom p p'' /\ p' = (conv pt p'').
  Proof.
    split; [intro H; inversion H| intros; subst];
      firstorder; subst;
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_is_codom_conv : pfcore.


  (*We want this as a lemma so it can be part of autorewrite
    instead of using both autorewrite and cbn
   *)
  Lemma omap_eval_Some (A B:eqType) (f : A -> B) a
    : omap f (Some a) = Some (f a).
  Proof. reflexivity. Qed.
  Hint Rewrite omap_eval_Some : utils.
  
  Lemma omap_eval_None (A B:eqType) (f : A -> B)
    : omap f None = None.
  Proof. reflexivity. Qed.
  Hint Rewrite omap_eval_None : utils.


  Ltac prepare_crush :=
    repeat(autorewrite with utils bool_utils pfcore in *;
           try match goal with
           | [H : exists _,_|- _] => destruct H
           | [H : _ /\ _ |- _] => destruct H
           end;
           subst).
  
  (*TODO: separate inversion database,
    custom plugin to greedily run database?
    Or: inversion lemmas, rewriting
   *)
  Hint Extern 1 => match goal with [H : is_dom _ _|-_] => safe_invert H end : pfcore.
  Hint Extern 1 => match goal with [H : is_codom _ _|-_] => safe_invert H end : pfcore.
  Hint Extern 1 => match goal with [H : List.Forall2 _ _ _|-_] => safe_invert H end : pfcore.
  Hint Extern 1 => match goal with [H : Some _ = None|-_] => safe_invert H end : pfcore.
  Hint Extern 1 => match goal with [H : None = Some _|-_] => safe_invert H end : pfcore.
  Hint Extern 1 => match goal with [H : Some _ = Some _|-_] => safe_invert H end : pfcore.
  Hint Extern 1 => match goal with [H : omap _ ?e = Some _|-_] => let H:=fresh in my_case H e;
                prepare_crush end : pfcore.

  (*
  Hint Extern 2 (reflect _ (omap _ ?e == _)) =>
  (let H:= fresh in my_case H e; prepare_crush) : pfcore.
  Hint Extern 4 (reflect _ (_ == _)) =>
  (destruct_reflect_bool; prepare_crush) : pfcore.
   *)
  (*TODO: move to utils*)
  (*
  Hint Extern 10 => match goal with
                    |[H : forall x, reflect (?A x) _ |- ?A _] =>
                      apply /H; prepare_crush
                    |[H : reflect ?A _ |- ?A] =>
                      apply /H; prepare_crush
                    end : bool_utils.
  Hint Extern 10 => match goal with
                    | [H : forall x, reflect (?A x) _, H': ?A _ |-_] =>
                      move: H' => /H H'; prepare_crush
                    | [H : reflect ?A _, H':?A|-_] =>
                      move: H' => /H H'; prepare_crush
                    end : bool_utils.
   *)
  
  Lemma dom_args_eval_cons p ps
    : dom_args dom (p :: ps) = do l_dom <- dom_args dom ps; a_dom <- dom p; ret (a_dom::l_dom).
  Proof.
    reflexivity.
  Qed.
  Hint Rewrite dom_args_eval_cons : pfcore.  
  Lemma codom_args_eval_cons p ps
    : codom_args codom (p :: ps) = do l_codom <- codom_args codom ps; a_codom <- codom p; ret (a_codom::l_codom).
  Proof.
    reflexivity.
  Qed.
  Hint Rewrite codom_args_eval_cons : pfcore.

  
  Hint Rewrite @named_list_lookup_err_inb : pfcore.
  Lemma named_list_lookup_err_inb' (A:eqType)
    : forall (l0 : named_list A) (x : string) (v : A),
      all_fresh l0 ->
      (named_list_lookup_err l0 x = Some v) <-> ((x, v) \in l0).
  Proof.
    intros; rewrite <- named_list_lookup_err_inb; auto.
    split.
    move => -> //.
    move => /eqP //.
  Qed.    
  Hint Rewrite named_list_lookup_err_inb' : pfcore.

  
  Hint Extern 4 False =>
  match goal with
    [ H_fr : is_true(all_fresh ?l),
             H : is_true((?n, ?a) \in ?l),
                 H' : is_true((?n, ?b) \in ?l)
      |-_]=>
    let Heq := fresh in
    assert(a = b) as Heq; [ eapply in_all_fresh_same; solve[eauto]| safe_invert Heq]
  end : pfcore.

  
  Hint Extern 1 (~ is_dom (ax _ _) _) => let H := fresh in intro H; inversion H; clear H; subst : pfcore.
  
  Ltac crush_n n := prepare_crush; eauto n with pfcore bool_utils.
  Ltac crush := crush_n integer:(5).


  Lemma lookup_is_exp pl x
    :List.Forall (fun p => is_exp p) (map snd pl) ->
     is_exp (named_list_lookup (pvar x) pl x).
  Proof.
    induction pl; break; simpl in *; crush.
    case_match; crush; intuition.
  Qed.
    
  Lemma subst_is_exp p pl
    : is_exp p ->
      List.Forall (fun p=> is_exp p) (map snd pl) ->
      is_exp (pf_subst pl p).
  Proof.
    induction p; simpl; crush.
    {
        intros; by apply lookup_is_exp.
    }
    {
      revert dependent l0;
        induction l0;
        simpl; crush;
          intuition.
    }
  Qed.
  Hint Resolve subst_is_exp : pfcore.

  
  Lemma sort_le_in_left_is_exp n c p p_r
    : (n, sort_le_pf c p p_r)\in l -> is_exp p.
  Proof.
    induction l_ok; simpl; try easy.
    rewrite in_cons.
    move => /orP [/eqP []|]; intros; subst; eauto.
      by inversion H0.
  Qed.
  
  Lemma sort_le_in_right_is_exp n c p p_l
    : (n, sort_le_pf c p_l p)\in l -> is_exp p.
  Proof.
    induction l_ok; simpl; try easy.
    rewrite in_cons.
    move => /orP [/eqP []|]; intros; subst; eauto.
      by inversion H0.
  Qed.
    
  Lemma term_le_in_left_is_exp n c p p_r t
    : (n, term_le_pf c p p_r t)\in l -> is_exp p.
  Proof.
    induction l_ok; simpl; try easy.
    rewrite in_cons.
    move => /orP [/eqP []|]; intros; subst; eauto.
      by inversion H0.
  Qed.
    
  Lemma term_le_in_right_is_exp n c p_l p t
    : (n, term_le_pf c p_l p t)\in l -> is_exp p.
  Proof.
    induction l_ok; simpl; try easy.
    rewrite in_cons.
    move => /orP [/eqP []|]; intros; subst; eauto.
      by inversion H0.
  Qed.

  
  (*TODO: move to utils/rewriting package*)
  (*TODO: leave generic in second arg or no*)
  Lemma invert_list_Forall2_nil A B (P : A -> B -> Prop) es
    : List.Forall2 P [::] es <-> es = [::].
  Proof.
    intuition; subst; auto.
  Qed.
  Hint Rewrite invert_list_Forall2_nil : utils.
  Lemma invert_list_Forall2_cons A B (P : A -> B -> Prop) e es lst
    : List.Forall2 P (e::es) lst <->
      exists es', List.Forall2 P es es' /\
      exists e', P e e' /\ lst = e'::es'.
  Proof.
    intuition;
      safe_invert H; firstorder; subst; auto.  
  Qed.
  Hint Rewrite invert_list_Forall2_cons : utils.

  Lemma invert_cons_eq A (a a':A) lst lst'
    : a::lst = a' ::lst' <-> a = a' /\ lst = lst'.
  Proof.
    intuition; try safe_invert H; firstorder; subst; auto.
  Qed.
  Hint Rewrite invert_cons_eq : utils.
      
  Lemma dom_codom_is_exp p
    : (forall p', is_dom p p' -> is_exp p')
      /\ (forall p', is_codom p p' -> is_exp p').
  Proof.
    induction p; split; intros; crush.
    1,2:revert dependent l0; intro l0; revert x;
        induction l0; firstorder; crush.
    1,2:  destruct x; simpl in *; intuition; crush;
      apply subst_is_exp;
        eauto using
              sort_le_in_left_is_exp,
        term_le_in_left_is_exp,
        term_le_in_right_is_exp,
        sort_le_in_right_is_exp;
      clear H0;
      revert dependent pfs; intro l0; revert n0 x;
        induction l0; intros; destruct n0; break;
          destruct x as [|? x];
          simpl in *; crush; try easy.
  Qed.

  Definition dom_is_exp p := proj1 (dom_codom_is_exp p).
  Hint Resolve dom_is_exp : pfcore.
  Definition codom_is_exp p := proj2 (dom_codom_is_exp p).
  Hint Resolve codom_is_exp : pfcore.
   
  Lemma exists_pcon_eq s pl s' P
    : (exists pl', pcon s pl = pcon s' pl' /\ P pl')
      <-> (s = s' /\ P pl).
  Proof.
    firstorder; inversion H; eauto with pfcore.
  Qed.
  Hint Rewrite exists_pcon_eq : pfcore.

  
  Lemma invert_Forall2_cons (A B : eqType) R (e : A) es (e' : B) es'
    : List.Forall2 R (e::es) (e'::es') <-> (R e e' /\ List.Forall2 R es es').
  Proof.
    split; intuition.
  Qed.
  Hint Rewrite invert_Forall2_cons : utils.

  (*
  (*TODO: need to recover level of indirection;
   what is the best way? make use of hint resolve not rewrite
   *)
  Lemma exists_as_omap_eq (A B:eqType) P (f : A -> B) a b
    : (forall c, P c <-> b = Some c) ->
      (exists c : A, a = f c /\ P c) <-> omap f b = Some a.
  Proof.
    destruct b; cbn; firstorder; crush; firstorder.
    specialize (H x); firstorder; crush.
    exists s.
    specialize (H s); firstorder; crush.
    specialize (H x); firstorder; crush.
  Qed.
  Hint Resolve exists_as_omap_eq : pfcore.
*)

  (*
  Lemma exists_as_obind_eq (A B:eqType) P Q (f : A -> option B) a b
    : (forall c, P c <-> b = Some c) ->
      (forall c, Q c <-> f c = Some a) ->
      (exists c, P c /\ Q c) <-> obind f b = Some a.
  Proof.
    my_case beq b; cbn; firstorder; crush;
    specialize (H x); specialize (H0 x); firstorder; crush.
  Qed.
  Hint Resolve exists_as_obind_eq : pfcore.
*)

  (*
  Ltac fold_omap :=
    lazymatch goal with
      [|- context c[match ?e with Some p => Some (@?f p) | None => None end] ]=>
      let g := context c [omap f e] in
      change g
    end.

  
  Ltac fold_obind :=
    lazymatch goal with
      [|- context c[match ?e with Some p => (@?f p) | None => None end] ]=>
      let g := context c [obind f e] in
      change g
    end.
    *)
  (*
  Lemma rewrite_pair_exists A B P
    : (exists (a:A) (b: B), P a b) <-> exists (p : A * B), P p.1 p.2.
  Proof.
    firstorder.
    exists (x,x0); simpl; auto.
  Qed.
  Hint Rewrite rewrite_pair_exists : utils. *)

  (*
  Lemma rewrite_exists_match_cons (A:eqType) (Q : A -> _ -> Prop) x
    : (exists a b, x = a::b /\ Q a b) <-> match x with
                                          | [::] => False
                                          | a::b => Q a b
                                          end.
  Proof.
    destruct x; simpl; firstorder; safe_invert H; auto.
  Qed.
   *)


  (*TODO: go back to all rules, review;
    want to rewrite computations to props
   *)
  Lemma match_some_eq (A B: eqType) (ma : option A) f (b :B)
    : match ma with Some a => f a | None => None end = Some b
      <-> match ma with Some a => f a = Some b | None => False end.
  Proof.
    destruct ma; intuition; crush.
  Qed.
  Hint Rewrite match_some_eq : pfcore.
  
  Lemma some_to_exists_equal A (ma : option A) P
    : match ma with
      | Some e => P e
      | None => False
      end
      <-> (exists e, ma = Some e /\ P e).
  Proof.
    destruct ma; simpl; firstorder; crush.
  Qed.
  Hint Rewrite some_to_exists_equal : pfcore.

  
  Lemma list_to_exists_equal A (ma : list A) P
    : match ma with
      | e::es => P e es
      | [::] => False
      end
      <-> (exists e es, ma = e::es /\ P e es).
  Proof.
    destruct ma; simpl; firstorder; crush.
    inversion H.
  Qed.
  Hint Rewrite list_to_exists_equal : pfcore.

  
  
  Lemma rewrite_pair_let_to_proj A B (p : A*B) (P : A -> B -> Prop)
    : (let (a,b) := p in P a b)
      <-> P p.1 p.2 .
  Proof.
    destruct p; simpl; firstorder; crush.
  Qed.
  Hint Rewrite rewrite_pair_let_to_proj : pfcore.



  
  Ltac safe_specialize :=
    match goal with
      [ H : forall x, ?A -> _, H' : ?A|-_] =>
      let H1 := fresh in
      rename H into H1;
        pose proof (fun x => H1 x H') as H;
        clear H1
    end.

  Hint Extern 20 => match goal with
       [ H : forall x, _ <-> _ |- _] =>
       rewrite !H
     end : bool_utils.

  Local Lemma domP_inner_induction l0 l2
    : List.fold_right
        (fun t : pf =>
           and ((forall p' : pf, (dom t = Some p') <-> (is_dom t p')) /\
                 forall p' : pf, (codom t = Some p') <-> (is_codom t p'))) True
        l0 ->
      (dom_args dom l0 = Some l2) <->
      (List.Forall2 is_dom l0 l2).
  Proof.
    revert l2; induction l0; cbn; intros; prepare_crush; repeat safe_specialize; crush.
    apply peel_exists_iff; intro; crush.
    apply and_iff_compat; crush.
    apply peel_exists_iff; intro; crush.
  Qed.
  Hint Rewrite domP_inner_induction : pfcore.
  
   Local Lemma codomP_inner_induction l0 l2
    : List.fold_right
        (fun t : pf =>
           and ((forall p' : pf, (dom t = Some p') <-> (is_dom t p')) /\
                 forall p' : pf, (codom t = Some p') <-> (is_codom t p'))) True
        l0 ->
      (codom_args codom l0 = Some l2) <->
      (List.Forall2 is_codom l0 l2).
  Proof.
    revert l2; induction l0; cbn; intros; prepare_crush; repeat safe_specialize; crush.
    apply peel_exists_iff; intro; crush.
    apply and_iff_compat; crush.
    apply peel_exists_iff; intro; crush.
  Qed.
  Hint Rewrite codomP_inner_induction : pfcore.
 
  Lemma omap_eq_some A B (f : A -> B) ma b
    : injective f ->
      omap f ma = Some b <-> exists a, ma = Some a /\ f a = b.
  Proof.
    intro injf.
    destruct ma; simpl; intuition; crush.
  Qed.
  Hint Rewrite omap_eq_some : pfcore.


  Ltac injective_constructor :=
    let H := fresh in intros ? ? H; safe_invert H; reflexivity.

  
  Hint Extern 1 (injective _) => injective_constructor : pfcore.

  Lemma rewrite_none_eq_some A (a :A)
    : None = Some a <-> False.
  Proof.
    intuition.
  Qed.
  Hint Rewrite rewrite_none_eq_some : pfcore.
   
  Lemma dom_codomP p
    :(forall p', (dom p = Some p') <-> (is_dom p p'))
       /\ (forall p', (codom p = Some p') <-> (is_codom p p')).
  Proof.
    induction p; split; cbn [dom codom]; fold dom; fold codom; intros;
      crush;
      try match goal with
        [H : forall p', ?P p' <-> _ |- ?P _ <-> _] =>
        rewrite H; crush
          end;
      (*TODO: why not auto?*)
      apply peel_exists_iff; intro; crush.
    all: apply and_iff_compat; crush.
    all: destruct e; crush.
    
    all: apply peel_exists_iff; intro; crush.
  Qed.

  Definition rewrite_dom_eq p := proj1 (dom_codomP p).
  Hint Rewrite rewrite_dom_eq : pfcore.
  Definition rewrite_codom_eq p := proj2 (dom_codomP p).
  Hint Rewrite rewrite_codom_eq : pfcore.

    
  Lemma is_domP p p' : reflect (is_dom p p') (dom p == Some p').
  Proof.
    eapply rewrite_reflect.
    rewrite <- rewrite_dom_eq.
    apply iff_refl.
    apply eqP.
  Qed.
  Definition is_codomP p p' : reflect (is_codom p p') (codom p == Some p').
  Proof.
    eapply rewrite_reflect.
    rewrite <- rewrite_codom_eq.
    apply iff_refl.
    apply eqP.
  Qed.  
      
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
 

  
  Lemma invert_term_ok_var c x t : term_ok l c (pvar x) t <-> (x,t) \in c.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore.
  Qed.
  Hint Rewrite invert_term_ok_var : pfcore.
  Lemma invert_sort_ok_var c x : sort_ok l c (pvar x) <-> False.
  Proof.
    split; [intro H; inversion H| intros; subst];
      eauto with pfcore; easy.
  Qed.
  Hint Rewrite invert_sort_ok_var : pfcore.

  Lemma invert_term_ok_con c n pl t
    : term_ok l c (pcon n pl) t <->
      exists r, (n,r) \in l /\
      match r with
      | term_rule_pf c' args t' =>
        is_dom (pf_subst (with_names_from c' pl) t') t /\
        args_ok l c pl c'
      | _ => False
      end.
  Proof.
    split; [intro H; inversion H| intros];
      crush.
    {
      exists (term_rule_pf c' args t0); cbn;
        intuition; crush.
    }
    {
      destruct x; cbn in *; crush.
    }
  Qed.
  Hint Rewrite invert_term_ok_con : pfcore.
  
  Lemma invert_sort_ok_con c n pl
    : sort_ok l c (pcon n pl) <->
      exists r, (n,r) \in l /\
      match r with
      | sort_rule_pf c' args =>
        args_ok l c pl c'
      | _ => False
      end.
  Proof.
    split; [intro H; inversion H| intros];
      intuition crush.
    destruct x; crush.
  Qed.
  Hint Rewrite invert_sort_ok_con : pfcore.

  Hint Resolve idP : bool_utils.

  
  Lemma invert_args_ok_nil c c'
    : args_ok l c [::] c' <-> c' = [::].
  Proof.
    intuition crush.
    safe_invert H; crush.
  Qed.
  Hint Rewrite invert_args_ok_nil : pfcore.

  (*TODO: handle cases on snd arg?*)
  Lemma invert_args_ok_cons c a pl c'
    : args_ok l c (a::pl) c' <->
      exists p c'', c' = p::c'' /\
      exists t', is_dom (pf_subst (with_names_from c'' pl) p.2) t' /\
                 term_ok l c a t' /\ args_ok l c pl c''.
  Proof.
    split; [intro H; inversion H| intros; subst]; firstorder; crush.
    {
      exists (name,t).
      exists c'0.
      split; crush.
    }
    {
      destruct x; simpl in *; econstructor; crush.
    }
  Qed.
  Hint Rewrite invert_args_ok_cons : pfcore.

  
  Lemma is_true_match_some A (ma : option A) f b
    : is_true(match ma with Some a => f a | None => b end)
      = match ma with Some a => is_true (f a) | None => is_true b end.
  Proof.
    destruct ma; reflexivity.
  Qed.
  Hint Rewrite is_true_match_some : bool_utils.

  
  Lemma is_true_match_list A (ma : list A) f b
    : is_true(match ma with | a::ma' => f a ma' | [::] => b end)
      = match ma with | a::ma' => is_true (f a ma') | [::] => is_true b end.
  Proof.
    destruct ma; reflexivity.
  Qed.
  Hint Rewrite is_true_match_list : bool_utils.


  
  Lemma rewrite_cons_eq_nil A (a : A) lst
    : a::lst = [::] <-> False.
  Proof.
    intuition; inversion H.
  Qed.
  Hint Rewrite rewrite_cons_eq_nil : bool_utils.

  (*A hack to get around rewrites that aren't working
    under the match
   *)
  Lemma TMP_match_list_to_bool A (P : A -> list A -> Prop) c'
    : match c' with
      | [::] => false
      | a0 :: ma' => P a0 ma'
      end <->
      match c' with
      | [::] => False
      | a0 :: ma' => P a0 ma'
      end.
  Proof.
    destruct c'; simpl; crush.
  Qed.

  
  Lemma TMP_match_option_to_bool A (P : A -> Prop) c'
    : match c' with
      | None => false
      | Some a0 => P a0
      end <->
      match c' with
      | None => False
      | Some a => P a
      end.
  Proof.
    destruct c'; simpl; crush.
  Qed.
  
  
  Lemma check_args_okP' c pl c'
    : all_fresh c ->
      List.fold_right
        (fun t : pf =>
           and
             (forall c : named_list pf,
                 all_fresh c -> (forall t0 : pf,(check_term_ok l c t t0) <->  (term_ok l c t t0))/\
                                ((check_sort_ok l c t) <-> (sort_ok l c t))))
        True pl ->
      (check_args_ok l c pl c') <-> (args_ok l c pl c').
  Proof.
    intro frc.
    revert c'.
    induction pl; intro c'; cbn; crush.
    {
      destruct c'; intuition crush.
      inversion H0.
    }
    {
      intros; crush.
      (*TODO: why does rewrite fail?
      setoid_rewrite false_False.*)
      rewrite TMP_match_list_to_bool.
      crush.
      apply peel_exists_iff; intro; crush.
      apply peel_exists_iff; intro; crush.
      apply and_iff_compat; crush.
      crush.
      (*TODO: get working?
      rewrite rewrite_pair_let_to_proj *)
      destruct e; crush.
      rewrite TMP_match_option_to_bool.
      crush.
      apply peel_exists_iff; intro; crush.
      apply and_iff_compat;
        safe_specialize;
        crush.
      specialize (H c frc).
      destruct H as [H H'].
      crush.
      specialize (H e); crush.
    }
  Qed.

  
  Lemma rewrite_if_eq_some A (a : A) (b : bool) c
    : (if b then c else None) = Some a <-> (c = Some a) /\ b.
  Proof.
    destruct b; simpl; intuition crush.
  Qed.
  Hint Rewrite rewrite_if_eq_some : bool_utils.

  
  Lemma invert_term_ok_ax c n pfs t'
    : term_ok l c (ax n pfs) t' <->
      exists r, (n, r) \in l /\
                           match r with
                           | term_le_pf c' _ _ t =>
                             is_dom (pf_subst (with_names_from c' pfs) t) t' /\
                             args_ok l c pfs c'
                           | _ => False
                           end.
  Proof.
    intuition crush; inversion H; clear H; subst.
    exists (term_le_pf c' e1 e2 t); intuition; crush.
    destruct x; crush.
  Qed.
  Hint Rewrite invert_term_ok_ax : pfcore.

  
  Lemma invert_sort_ok_ax c n pfs
    : sort_ok l c (ax n pfs) <->
      exists r, (n, r) \in l /\
                           match r with
                           | sort_le_pf c' _ _ =>
                             args_ok l c pfs c'
                           | _ => False
                           end.
  Proof.
    intuition crush; inversion H; clear H; subst.
    exists (sort_le_pf c' t1 t2); intuition; crush.
    destruct x; crush.
  Qed.
  Hint Rewrite invert_sort_ok_ax : pfcore.

  Lemma invert_term_ok_sym c e t
    : term_ok l c (sym e) t <-> term_ok l c e t.
  Proof.
    intuition crush; inversion H; crush.
  Qed.
  Hint Rewrite invert_term_ok_sym : pfcore.
  
  Lemma invert_sort_ok_sym c t
    : sort_ok l c (sym t) <-> sort_ok l c t.
  Proof.
    intuition crush; inversion H; crush.
  Qed.
  Hint Rewrite invert_sort_ok_sym : pfcore.

  Lemma invert_term_ok_trans c e1 e2 t
    : term_ok l c (trans e1 e2) t <->
      (term_ok l c e1 t /\
       term_ok l c e2 t /\
      exists e, is_codom e1 e /\ is_dom e2 e).
  Proof.
    intuition crush;
    inversion H; crush.
  Qed.
  Hint Rewrite invert_term_ok_trans : pfcore.

  
  Lemma invert_sort_ok_trans c t1 t2
    : sort_ok l c (trans t1 t2) <->
      (sort_ok l c t1 /\
       sort_ok l c t2 /\
      exists t, is_codom t1 t /\ is_dom t2 t).
  Proof.
    intuition crush;
    inversion H; crush.
  Qed.
  Hint Rewrite invert_sort_ok_trans : pfcore.

  
  Lemma invert_sort_ok_conv c pt p
    : sort_ok l c (conv pt p) <-> False.
 Proof.
    intuition crush;
    inversion H; crush.
  Qed.
  Hint Rewrite invert_sort_ok_conv : pfcore.
  
  Lemma rewrite_exists_snd_determined_from_injectivity A B (f : A -> B) P x
    : injective f -> (exists e : A, P e /\ f e = f x) <-> P x.
  Proof.
    intros ?.
    firstorder crush.
  Qed.
  Hint Rewrite rewrite_exists_snd_determined_from_injectivity : bool_utils.

  Lemma fold_eq_pf p1 p2 : eq_pf p1 p2 = (p1 == p2).
  Proof.
    reflexivity.
  Qed.
  Hint Rewrite fold_eq_pf : pfcore.
  
  Lemma check_okP c e
    : all_fresh c ->
      (forall t, check_term_ok l c e t <-> term_ok l c e t)
        /\ (check_sort_ok l c e <-> sort_ok l c e).
  Proof.
    revert c.
    induction e; intros c cfr; split;
      cbn;intros; crush; simpl; crush.  (*TODO: figure out why simpl *)
    {
      apply peel_exists_iff; intro; crush.
      apply and_iff_compat; crush.
      destruct e; simpl; crush.
      rewrite check_args_okP'; crush.
    }
    {
      rewrite TMP_match_option_to_bool; crush.
      apply peel_exists_iff; intro; crush.
      apply and_iff_compat; crush.
      destruct e; crush.
      rewrite check_args_okP'; crush.
    }
    {                      
      apply peel_exists_iff; intro; crush.
      apply and_iff_compat; crush.
      destruct e; crush.
      rewrite check_args_okP'; crush.
    }
    {
      rewrite TMP_match_option_to_bool; crush.
      apply peel_exists_iff; intro; crush.
      apply and_iff_compat; crush.
      destruct e; crush.
      rewrite check_args_okP'; crush.
    }
    {
      unfold check_term_ok in *.
      specialize (IHe c cfr); destruct IHe as [IHe1 IHe2].
      specialize (IHe1 t); crush.
    }
    {
      specialize (IHe c cfr); destruct IHe as [IHe1 IHe2]; crush.
    }
    {
      etransitivity.
      apply peel_exists_iff; intro.
      apply and_iff_compat.
      specialize (IHe1 c cfr); destruct IHe1 as [IHe11 IHe12].
      specialize (IHe11 e); unfold check_term_ok in *; prepare_crush.
      rewrite IHe11; crush.
      prepare_crush.
      apply peel_exists_iff; intro.
      apply and_iff_compat.
      specialize (IHe2 c cfr); destruct IHe2 as [IHe21 IHe22].
      specialize (IHe21 e0); unfold check_term_ok in *; prepare_crush.
      rewrite IHe21; crush.
      prepare_crush.
      apply peel_exists_iff; intro.
      apply and_iff_compat.
      rewrite rewrite_codom_eq; reflexivity.
      prepare_crush.
      apply peel_exists_iff; intro.
      apply and_iff_compat.
      rewrite rewrite_dom_eq; reflexivity.
      rewrite rewrite_if_eq_some.
      rewrite rewrite_if_eq_some.
      reflexivity.
      simpl.
      intuition crush.
      exists t; split; crush.
      exists t; split; crush.
      exists x; split; crush.
      exists x; split; crush.
    }
  Admitted.    

  Definition rewrite_term_okP c e (fr : all_fresh c) :=
    proj1 (check_okP e fr).
  Hint Rewrite rewrite_term_okP : pfcore.

  Definition rewrite_sort_okP c e (fr : all_fresh c) :=
    proj2 (check_okP e fr).
  Hint Rewrite rewrite_sort_okP : pfcore.
  
  Lemma check_term_okP c e t
    : all_fresh c ->
      reflect (term_ok l c e t) (check_term_ok l c e t).
  Proof using l_ok.
    pose proof (@check_okP c e).
    intuition.
    eapply rewrite_reflect; [| apply idP].
    rewrite H; reflexivity.
  Qed.
    
  Lemma check_sort_okP c t
      : all_fresh l ->
        all_fresh c ->
        reflect (sort_ok l c t) (check_sort_ok l c t).
  Proof using l_ok.
    pose proof (@check_okP c t).
    intuition.
    eapply rewrite_reflect; [| apply idP].
    intuition.
  Qed.
  
  Lemma ctx_ok_all_fresh c
    : ctx_ok l c -> all_fresh c.
  Proof using.
    induction c; intro cok; inversion cok; subst; clear cok; break; simpl in *;
      break_goal; auto.
  Qed.
  Hint Resolve ctx_ok_all_fresh : pfcore.

  
  Lemma check_ctx_okP c : reflect (ctx_ok l c) (check_ctx_ok l c).
  Proof using l_ok.
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
      apply /check_sort_okP; auto using ctx_ok_all_fresh with pfcore.
    }
    all: intro cok; inversion cok; subst; clear cok.
      match goal with
        [ H : reflect _ false |-_]=> inversion H
      end; auto using ctx_ok_all_fresh.
      {
        rewrite <- rewrite_sort_okP in H4; eauto with pfcore.
      }
      eauto with pfcore.
  Qed.

  
  Lemma rewrite_ctx_okP c : (check_ctx_ok l c) <-> (ctx_ok l c).
  Proof using l_ok.
    split.
    - move /check_ctx_okP; auto.
    - intros; apply /check_ctx_okP; auto.
  Qed.
  Hint Rewrite rewrite_ctx_okP : pfcore.
  
  Lemma invert_sort_rule_ok c args
    : rule_ok l (sort_rule_pf c args) <-> ctx_ok l c /\ subseq args (map fst c).
  Proof.
    intuition ;inversion H; crush.
  Qed.
  Hint Rewrite invert_sort_rule_ok : pfcore.

  
  Lemma invert_term_rule_ok c args t
    : rule_ok l (term_rule_pf c args t) <-> ctx_ok l c /\ subseq args (map fst c) /\ sort_ok l c t.
  Proof.
    intuition ;inversion H; crush.
  Qed.
  Hint Rewrite invert_term_rule_ok : pfcore.
  
  Lemma invert_sort_le_ok c t1 t2
    : rule_ok l (sort_le_pf c t1 t2) <->
      ctx_ok l c /\ sort_ok l c t1 /\ sort_ok l c t2 /\
      is_exp t1 /\ is_exp t2.
  Proof.
    intuition;
    inversion H; crush.
  Qed.
  Hint Rewrite invert_sort_le_ok : pfcore.

  
  Lemma invert_term_le_ok c e1 e2 t
    : rule_ok l (term_le_pf c e1 e2 t) <->
      ctx_ok l c /\ term_ok l c e1 t /\ term_ok l c e2 t /\ sort_ok l c t /\
      is_exp e1 /\ is_exp e2 /\ is_exp t.
  Proof.
    intuition;
    inversion H; crush.      
  Qed.
  Hint Rewrite invert_term_le_ok : pfcore.
  
  Lemma rewrite_rule_okP r : (check_rule_ok l r) <-> (rule_ok l r).
  Proof using l_ok.
    pose proof ctx_ok_all_fresh.
    destruct r; intros; break; simpl.
    all: intuition.
    crush.
    crush.
    {
      (*TODO: why does crush have an issue?*)
      autorewrite with utils bool_utils in *;
      intuition.
      autorewrite with pfcore in *; eauto with pfcore.
    }
    {
      (*TODO: why does crush have an issue?*)
      autorewrite with utils bool_utils in *;
      intuition;
      autorewrite with pfcore in *; intuition; eauto with pfcore.
      inversion H0; auto.
    }
    {
      (*TODO: why does crush have an issue?*)
      autorewrite with utils bool_utils in *;
      intuition;
      autorewrite with pfcore in *; intuition; eauto with pfcore.
    }
    crush.
    {
      (*TODO: why does crush have an issue?*)
      autorewrite with utils bool_utils in *;
      intuition;
      autorewrite with pfcore in *; intuition; eauto with pfcore.
    }
    {
      my_case H' (check_ctx_ok l n); simpl;
      crush; intuition crush.
      move: H' => /negP.
      crush.
    }
  Qed.
  Hint Rewrite rewrite_rule_okP : pfcore.
  
  
  Lemma check_rule_okP r : reflect (rule_ok l r) (check_rule_ok l r).
  Proof using l_ok.
    reflect_from_iff rewrite_rule_okP.
  Qed.
  
End TermsAndRules.

(*TODO: pull crush out of section*)

Lemma check_lang_ok_all_fresh l : check_lang_ok l -> all_fresh l.
Proof using.
  induction l; intros; repeat (break; simpl in * ); break_goal; auto.
Qed.
Hint Resolve check_lang_ok_all_fresh : pfcore.

Lemma rewrite_lang_okP l : check_lang_ok l <-> lang_ok l.
Proof.
  induction l; intros; break; simpl.
  split; eauto with pfcore.
  autorewrite with bool_utils.
  rewrite IHl.
  intuition.
  {
    constructor; eauto.
    unfold fresh; autorewrite with bool_utils; auto.
    apply /check_rule_okP; auto.
  }
  all: inversion H1; subst; auto.
  apply /check_rule_okP; auto.
Qed.

Lemma check_lang_okP l : reflect (lang_ok l) (check_lang_ok l).
Proof using.
    reflect_from_iff rewrite_lang_okP.
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
  | try eapply term_ok_var
  | eapply term_ok_conv].


Ltac destruct_sort_ok s :=
  destruct s; intros;
  [ eapply sort_ok_ax
  | eapply sort_ok_con
  | eapply sort_ok_trans
  | eapply sort_ok_sym].


Ltac destruct_args_ok s :=
  destruct s; intros;
  [ eapply args_ok_nil
  | eapply args_ok_cons].

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
    destruct_args_ok lea; eauto using is_dom_monotonicity.
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

(*TODO: move to Pf*)
(*TODO: requires wfness or altered definition; can't have both the
  above and below thms
 *)

Inductive ws_pf {c : list string} : pf -> Prop :=
| ws_var x : x \in c -> ws_pf (pvar x)
| ws_con n l : List.Forall ws_pf l -> ws_pf (pcon n l)
| ws_ax n l : List.Forall ws_pf l -> ws_pf (ax n l)
| ws_sym p : ws_pf p -> ws_pf (sym p)
| ws_trans p1 p2 : ws_pf p1 -> ws_pf p2 -> ws_pf (trans p1 p2)
| ws_conv p1 p2 : ws_pf p1 -> ws_pf p2 -> ws_pf (conv p1 p2).

Arguments ws_pf : clear implicits.

Lemma pf_subst_lookup s s' n
  : n \in (map fst s') ->
    pf_subst s (named_list_lookup (pvar n) s' n)
    = named_list_lookup (pvar n) (named_map (pf_subst s) s') n.
Proof.
  induction s'; simpl; [easy |].
  rewrite in_cons.
  break; simpl in *.
  change (n =? s0)%string with (n == s0).
  case neq: (n == s0); simpl; auto.
Qed.        

Lemma pf_subst_distributes s s' p
  : ws_pf (map fst s') p ->
    pf_subst s (pf_subst s' p)
    = pf_subst (named_map (pf_subst s) s') p.
Proof.
  induction p; intro wsp; inversion wsp; subst; clear wsp; simpl.
  by apply pf_subst_lookup.
  1,2: match goal with
         [l : seq pf |- _]=>
         revert dependent l; intro l; induction l; simpl; intros;
           f_equal; f_equal;
             match goal with
             | [H : List.Forall _ (_::_)|-_] => inversion H; clear H; subst
             end;
             intuition;
             match goal with
             | [H : pcon _ _ = pcon _ _ |-_] => inversion H; clear H; subst
             | [H : ax _ _ = ax _ _ |-_] => inversion H; clear H; subst
             end; auto
       end.
  all:intuition; f_equal; auto.
Qed.

    

Lemma named_map_with_names_from {A B C:Set} (f : A -> B) (c : named_list C) s
  : named_map f (with_names_from c s)
    = with_names_from c (map f s).
Proof.
  revert c; induction s; intro c; destruct c; break; simpl; auto.
  f_equal; eauto.
Qed.


Lemma is_dom_unique l p p1 p2
  : lang_ok l -> is_dom l p p1 -> is_dom l p p2 -> p1 = p2.
Proof.
  intro lok.
  move /(is_domP lok) /eqP => d1.
  move /(is_domP lok) /eqP => d2.
  congruence.
Qed.

Lemma is_codom_unique l p p1 p2
  : lang_ok l -> is_codom l p p1 -> is_codom l p p2 -> p1 = p2.
Proof.
  intro lok.
  move /(is_codomP lok) /eqP => d1.
  move /(is_codomP lok) /eqP => d2.
  congruence.
Qed.
  
Lemma is_dom_and_codom_subst_monotonicity l tc t td sc s sd
  : is_dom l t td -> is_codom l t tc ->
    List.Forall2 (fun p1 p2 => p1.1 = p2.1 /\ is_codom l p1.2 p2.2) s sc ->
    List.Forall2 (fun p1 p2 => p1.1 = p2.1 /\ is_dom l p1.2 p2.2) s sd ->
    (is_dom l (pf_subst s t) (pf_subst sd td)
     /\ is_codom l (pf_subst s t) (pf_subst sc tc)).
Proof.
  revert tc td s sc sd;
    induction t; intros tc td s.
  {
    induction s; intros sc sd is_d is_c allc alld;
      inversion allc; inversion alld; clear allc; clear alld;
        break;simpl in *; subst; rewrite ?pf_subst_nil; auto;
          inversion is_d; inversion is_c; clear is_d is_c; subst.
    inversion H; inversion H4; subst; clear H H4.
    simpl; case_match; auto.
    apply IHs; eauto; constructor.
  }
  {
    intros sc sd is_d is_c allc alld;
      inversion is_c; inversion is_d; clear is_c is_d;
      break;simpl in *; subst.
    revert pl_r pl_l H H7 H3; induction l0; simpl;
      intros pl_r pl_l IH fl1 fl2; inversion fl1; inversion fl2; clear fl1 fl2;
        subst; simpl; repeat constructor;
      break;
      try eapply H; eauto;
      specialize IHl0 with l'0 l';
      specialize (IHl0 H0 H3 H8);
      destruct IHl0 as [IHd IHc].
      by inversion IHd.
      by inversion IHc.
  }
  {
    intros sc sd is_d is_c allc alld;
      inversion is_c; inversion is_d; clear is_c is_d;
      break;simpl in *; subst.

    rewrite !pf_subst_distributes.
    rewrite !named_map_with_names_from.    
    
    revert pl_r pl_l H H7 H2; induction pfs; simpl;
      intros pl_r pl_l IH fl1 fl2; inversion fl1; inversion fl2; clear fl1 fl2;
        subst; simpl;
          (split; [eapply dom_ax_sort | eapply codom_ax_sort]); try constructor;
            intuition; try eapply H; eauto.
    admit (*TODO: forall from fold_right; induction not strong enough*).
    admit.
    (*TODO: need ws assumptions*)    
Admitted.

  
Lemma is_dom_subst_monotonicity l t t' s s'
  : is_dom l t t' -> List.Forall2 (fun p1 p2 => p1.1 = p2.1 /\ is_dom l p1.2 p2.2) s s' -> is_dom l (pf_subst s t) (pf_subst s' t').
Proof.
  (*TODO: show dom/codom always exist, use w/ above to prove this*)
Admitted.
  
Lemma is_codom_subst_monotonicity l t t' s s'
     : is_codom l t t' -> List.Forall2 (fun p1 p2 => p1.1 = p2.1 /\ is_codom l p1.2 p2.2) s s' -> is_codom l (pf_subst s t) (pf_subst s' t').
Proof.
  (*TODO: show dom/codom always exist, use w/ above to prove this*)
Admitted.


(*TODO: move to utils*)
(*redefined to use the right concatenation*)
Definition flat_map {A B} (f : A -> list B) :=
  fix flat_map l :=
  match l with
  | [::] => [::]
  | x :: t => (f x ++ flat_map t)
  end.

(*TODO: move to Pf*)
Fixpoint fv (p : pf) :=
  match p with
  | pvar x => [:: x]
  | pcon _ l => flat_map fv l
  | ax _ l => flat_map fv l
  | sym p => fv p
  | trans p1 p2 => fv p1 ++ fv p2
  | conv p1 p2 => fv p1 ++ fv p2
  end.



Lemma fv_term_ok l c e t
  : term_ok l c e t ->
    included (fv e) (map fst c)
with fv_args_ok l c s c'
     : args_ok l c s c' ->
       included (flat_map fv s) (map fst c)
with fv_sort_ok l c t
  : sort_ok l c t ->
    included (fv t) (map fst c).
Proof.
  {
    intro tok; inversion tok; clear tok; subst; simpl;
      first [eapply fv_args_ok; eauto
            | rewrite included_app; apply /andP; split; eauto
            | eauto].
    rewrite Bool.andb_true_r.
    eapply pair_fst_in; eauto.
  }
  {
    intro tok; inversion tok; clear tok; subst; simpl;
      first [eapply fv_args_ok; eauto
            | rewrite included_app; apply /andP; split; eauto
            | eauto].
  }
  {
    intro tok; inversion tok; clear tok; subst; simpl;
      first [eapply fv_args_ok; eauto
            | rewrite included_app; apply /andP; split; eauto
            | eauto].
  }
Qed.

(* Will later be able to prove this by appealing to the fact that 
   sort in an ok ctx are ok, but we need monotonicity facts first
   so we prove this directly here.
*)
Lemma fv_in_ctx l c n t
  : ctx_ok l c ->
    (n,t) \in c ->
    included (fv t) (map fst c).
Proof.
  intro cok; induction cok; simpl; auto.
  rewrite in_cons.
  move /orP => [/eqP []|]; intros; subst.
  {
    apply included_rest.
    eapply fv_sort_ok; eauto.
  }
  {
    apply included_rest; eauto.
  }
Qed.

Lemma strengthen_pf_subst t s name x
  : name \notin (map fst s) ->
    included (fv t) (map fst s) ->
    pf_subst ((name, x)::s) t = pf_subst s t.
Proof.
  induction t; simpl; intros; try f_equal;
    repeat match goal with
           |[H : is_true (included (_++_) _)|-_] =>
            rewrite included_app in H;
              move: H => /andP []; intros
           |[H : is_true (included (flat_map _ ?l) _)|-_] =>
            revert dependent l; intro l; induction l; simpl; auto;
              intuition; f_equal; eauto
           end; eauto.
  {
    rewrite Bool.andb_true_r in H0.
    change (n =? name)%string with (n == name).
    my_case neq (n == name); auto.
    move: neq => /eqP neq; subst.
    rewrite H0 in H.
    easy.
  }
Qed.

Lemma subst_ok_names_eq l c s c'
  : subst_ok l c s c' -> [seq i.1 | i <- s] = [seq i.1 | i <- c'].
Proof.
  induction 1; simpl in *; f_equal; eauto.
Qed.

Lemma term_ok_lookup l c' s c t x
  : lang_ok l ->
    ctx_ok l c ->
    subst_ok l c' s c ->
    (x,t) \in c ->
    forall t',
    is_dom l (pf_subst s t) t' ->
    term_ok l c' (named_list_lookup (pvar x) s x) t'.
Proof.
  intros lok allf.
  induction 1; simpl in *; break; try easy.
  rewrite in_cons.
  cbn.
  inversion allf; clear allf; subst.
  case xeq: (x =? name)%string; simpl; [move: xeq => /eqP xeq; subst|].
  {
    change (eq_pf t t0) with (t == t0).
    case teq: (t == t0); [move: teq => /eqP teq; subst|];
      intros ? t'0.
    {
      replace (pf_subst ((name,e)::s) t0) with (pf_subst s t0).
      intro isd.
      pose proof (is_dom_unique lok H0 isd); subst; auto.
      symmetry; apply strengthen_pf_subst;
        erewrite subst_ok_names_eq; eauto.
      eapply fv_sort_ok; eauto.
    }
    {
      simpl in *.
      apply pair_fst_in in H2.
      rewrite H2 in H5.
      easy.
    }
  }
  {
    intros tin t'0.
    rewrite strengthen_pf_subst; eauto;
      erewrite subst_ok_names_eq; eauto.
      eapply fv_in_ctx; eauto.
  }
Qed.


Lemma Forall2_pair_from_maps A B P Q (l1 l2 : list (A*B))
  : List.Forall2 P (map fst l1) (map fst l2) ->
    List.Forall2 Q (map snd l1) (map snd l2) ->
    List.Forall2 (fun p1 p2 => P p1.1 p2.1 /\ Q p1.2 p2.2) l1 l2.
Proof.
  revert l2; induction l1; intro l2; destruct l2;
    break;
    simpl;
    intro lfp; inversion lfp;
      intro lfq; inversion lfq;
        subst;auto.
Qed.


Lemma Forall2_eq_refl A (lst : list A) : List.Forall2 eq lst lst.
Proof.
  induction lst; simpl; eauto.
Qed.

(* TODO: move to utils? need more general types to do so*)
Lemma map_fst_with_names_from (A B:Set) (c:named_list_set A) (s : list B)
  : size s = size c -> map fst (with_names_from c s) = map fst c.
Proof using .
  elim: c s; intros until s; case: s; intros; break;simpl in *; auto.
  { inversion H0. }
  {
    f_equal; auto.
  }
Qed.


Lemma map_snd_with_names_from (A B:Set) (c:named_list_set A) (s : list B)
  : size s = size c -> map snd (with_names_from c s) = s.
Proof using .
  elim: c s; intros until s; case: s; intros; break;simpl in *; auto.
  { inversion H. }
  {
    f_equal; auto.
  }
Qed.


Lemma is_dom_codom_exists_sort l c p
  : sort_ok l c p ->
    (exists p', is_dom l p p') /\
    (exists p', is_codom l p p')
with is_dom_codom_exists_term l c p t
  : term_ok l c p t ->
    (exists p', is_dom l p p') /\
    (exists p', is_codom l p p').
Proof.
Admitted.

Lemma is_dom_codom_exists_args l c pfs c'
  : args_ok l c pfs c' ->
    (exists p', List.Forall2 (is_dom l) pfs p') /\
    (exists p', List.Forall2 (is_codom l) pfs p').
Proof.
  induction 1; simpl; firstorder.
  eexists; constructor; eauto with pfcore.
  eexists; constructor; eauto with pfcore.
  destruct (is_dom_codom_exists_term H1); firstorder.
  eauto.
  destruct (is_dom_codom_exists_term H1); firstorder.
  eauto.
Qed.


Lemma with_names_from_subst_ok l c s c'
  : subst_ok l c s c' -> map fst s = map fst c'.
Proof.
  induction 1; break; simpl; f_equal; eauto.
Qed.

Lemma subst_ok_args_ok l c s c'
  : subst_ok l c s c' -> args_ok l c (map snd s) c'.
Proof.
  induction 1; simpl; eauto with pfcore.
  econstructor; eauto with pfcore.
  replace (with_names_from c' (map snd s)) with s; auto.
    
  erewrite with_names_from_names_eq.
  symmetry.
  apply with_names_from_snd.
  symmetry; eapply with_names_from_subst_ok; eauto.
Qed.
Hint Resolve subst_ok_args_ok.  

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
    intros sok cok c'ok subok.
    pose proof (is_dom_codom_exists_args (subst_ok_args_ok subok)).
    revert cok c'ok subok H.
    destruct sok; intuition.

    {
      eapply sort_ok_ax; eauto.
    }
    {
      eapply sort_ok_con; eauto.
    }
    {
      eapply sort_ok_trans; eauto; fold pf_subst.
      known issue:
        when applying a subst to a trans, need to project left or right out
      alternatives/ideas:
          embed l and r terms in ax to avoid lang in pf_subst
          lean into non-canonical proofs, make pf_subst a constructor
          may want to re-separate proof-terms
    }
    | eapply sort_ok_con | eapply sort_ok_trans | eapply sort_ok_sym ]
    apply 
    destruct_sort_ok sok; fold pf_subst;
    eauto.
        [ apply is_codom_subst_monotonicity; intuition; firstorder; eauto
        | apply is_dom_subst_monotonicity; intuition; firstorder; eauto].
      {
        let x := open_constr:(with_names_from s _) in
        instantiate (1:=x).
        apply Forall2_pair_from_maps.
        rewrite map_fst_with_names_from.
        apply Forall2_eq_refl.
        2: rewrite map_snd_with_names_from; eauto.
        admit.
        admit. (*TODO: size lemma*)
      }
      {
        TODO: why the same x?
        apply Forall2_pair_from_maps.
        rewrite map_fst_with_names_from.
        apply Forall2_eq_refl.
        2: rewrite map_snd_with_names_from; eauto.
        TODO: what is x0; 
        admit.
        admit. (*TODO: size lemma*)
      }
        
    admit
    (*TODO: need existence of dom/codom
      for substitutions
     *).
    admit.
  }
  {
    intro sok;
    destruct_term_ok sok; fold pf_subst; simpl; eauto; cycle 4.
    TODO: need lookup wfness lemma
        
      
        [ apply is_codom_subst_monotonicity; eauto
        | apply is_dom_subst_monotonicity; eauto].
    admit
    (*TODO: need existence of dom/codom
      for substitutions
     *).
    admit.
  }
                                          
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
