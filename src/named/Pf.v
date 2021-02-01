Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils.
From Named Require Import Exp ARule Matches ImCore.
Import OptionMonad.

(* Proofs of relatedness; todo: separate sort from term pf? *)
Unset Elimination Schemes.
Inductive pf : Set :=
(* variable name; congruence for variables *)
| pvar : string -> pf
(* Rule label, list of subterms*)
(* congruence for constructors *)
| pcon : string -> list pf -> pf
(* appealing to a language axiom *)
| ax : string -> list pf -> pf
| sym : pf -> pf
| trans : pf -> pf -> pf
| conv : pf (*term*) -> pf (*sort*) -> pf.
Set Elimination Schemes.

Ltac break_monadic_do :=
  repeat (lazymatch goal with
          | [H : Some _ = Some _|-_] => inversion H; clear H
          | [H : Some _ = None|-_] => inversion H
          | [H : None = Some _ |-_] => inversion H
          | [H : Some _ = named_list_lookup_err _ _ |-_] =>
            apply named_list_lookup_err_in in H;
            try (let H' := fresh H in
                 pose proof H as H';
                 apply rule_in_wf in H'; inversion H'; clear H')
          | [H : true = (?a == ?b) |-_] =>
            symmetry in H;
            move: H => /eqP H
          | [H : false = true |-_] =>inversion H
          | [H : false = (?a == ?a) |-_] =>
            rewrite eq_refl in H; inversion H
          | |- context [ match ?e with
                         | _ => _
                         end ] => let e' := fresh in
                                  remember e as e'; destruct e'
          | [H:context [ match ?e with
                         | _ => _
                         end ] |-_] => let e' := fresh in
                                       remember e as e'; destruct e'
          end; subst; simpl in * ).

(*Stronger induction principle w/ better subterm knowledge
 *)
Fixpoint pf_ind
         (P : pf -> Prop)
         (IHV : forall n, P(pvar n))
         (IHC : forall n l,
             List.fold_right (fun t => and (P t)) True l ->
             P (pcon n l))
         (IHA : forall n pfs, 
             List.fold_right (fun p => and (P p)) True pfs -> P(ax n pfs))
         (IHSY : forall e', P e' -> P (sym e'))
         (IHT : forall e1 e2,
             P e1 -> P e2 -> P (trans e1 e2))
         (IHCV : forall e1 e2,
             P e1 -> P e2 -> P (conv e1 e2))
         (e : pf) { struct e} : P e :=
  match e with
  | pvar n => IHV n
  | pcon n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [::] => I
        | e' :: l' => conj (pf_ind IHV IHC IHA IHSY IHT IHCV e') (loop l')
        end in
    IHC n l (loop l)
  | ax n pfs => 
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [::] => I
        | e' :: l' => conj (pf_ind IHV IHC IHA IHSY IHT IHCV e') (loop l')
        end in
    IHA n pfs (loop pfs)
  | sym e' =>
    IHSY e' (pf_ind IHV IHC IHA IHSY IHT IHCV e')
  | trans e1 e2 =>
    IHT e1 e2 (pf_ind IHV IHC IHA IHSY IHT IHCV e1)
        (pf_ind IHV IHC IHA IHSY IHT IHCV e2)
  | conv e1 e2 =>
    IHCV e1 e2 (pf_ind IHV IHC IHA IHSY IHT IHCV e1)
        (pf_ind IHV IHC IHA IHSY IHT IHCV e2)
  end.

(* TODO
Fixpoint exp_rect
         (P : exp -> Type)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))
         (e : exp) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [::] => tt
        | e' :: l' => (exp_rect IHV IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition exp_rec := 
[eta exp_rect]
     : forall P : exp -> Set,
       (forall n, P (var n)) ->
       (forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))-> forall e : exp, P e.
*)

Definition subst_pf : Set := named_list_set pf.


(*TODO:move to Utils*)
Fixpoint get_subseq {A} (args : list string) (l : named_list A) :=
  match args, l with
  | [::],_ => do ret [::]
  | x::args', (x',e)::l' =>
    if x == x'
    then do sq <- get_subseq args' l';
         ret (x,e)::sq
    else get_subseq args l'
  | _::_,[::]=> None
  end.

                 
Lemma get_subseq_exact (s : subst)
  : Some s = get_subseq (map fst s) s.
Proof.
  induction s; intros; break; simpl in *; auto.
  rewrite ?eq_refl.
  rewrite <-IHs; eauto.
Qed.

Lemma get_subseq_nil (s : subst)
  : Some [::] = get_subseq [::] s.
Proof.
  destruct s; simpl; reflexivity.
Qed.
             
Section RuleChecking.
  Context (l : lang) (wfl : wf_lang l).

  Section InnerLoop.
    Context (synth_le_term : pf -> ctx -> option (sort*exp*exp)).

    Fixpoint synth_le_args (pl : list pf) (c c' : ctx) {struct pl}
      : option (list exp * list exp) :=
      match pl with
      | [::] => do [::] <- do ret c'; ret ([::],[::])
      | p::pl' =>
        do (_,t)::c'' <- do ret c';
           (t',e1,e2) <- synth_le_term p c;
           (el1,el2) <- synth_le_args pl' c c'';
           ! t' == t[/with_names_from c'' el2/];
           ret (e1::el1, e2::el2)
     end.

    Fixpoint synth_le_sort (pt : pf) (c : ctx) : option (sort * sort) :=
      match pt with
      | pvar x => None
      | pcon name pl =>
        do (sort_rule c' args) <- named_list_lookup_err l name;
           (el1, el2) <- synth_le_args pl c c';
           al1 <- get_subseq args (with_names_from c' el1);
           al2 <- get_subseq args (with_names_from c' el2);
           ret (scon name (map snd al1), scon name (map snd al2))
      | ax name pfs =>
        do (sort_le c' e1 e2) <- named_list_lookup_err l name;
           (el1, el2) <- synth_le_args pfs c c';
           let s1 := with_names_from c' el1;
           let s2 := with_names_from c' el2;
           ret (e1[/s1/],e2[/s2/])
      | sym p =>
        do (e1,e2) <- synth_le_sort p c;
           ret (e2,e1)
      | trans p1 p2 =>
        do (e1,e2) <- synth_le_sort p1 c;
           (e2',e3) <- synth_le_sort p2 c;
           !e2 == e2';
           ret (e1,e3)
      | conv pt p => None
    end.

    Lemma synth_le_args_size_l l0 l1 l2 c c0
      : Some (l1, l2) = synth_le_args l0 c c0 ->
        size l1 = size c0.
    Proof.
      revert l1 l2 c0.
      induction l0; intros; destruct c0; break; simpl in *; try by (inversion H; subst; auto).
      revert H.
      case_match; [| intro H; inversion H];
        break.
      case_match; [| intro H; inversion H];
        break.
      case_match; [| intro H; inversion H];
        break.
      symmetry in HeqH1.
      case.
      move: HeqH1 => /eqP.
      intros.
      subst.
      simpl.
      f_equal; eauto.
    Qed.

    Lemma synth_le_args_size_r l0 l1 l2 c c0
      : Some (l1, l2) = synth_le_args l0 c c0 ->
        size l2 = size c0.
    Proof.
      revert l1 l2 c0.
      induction l0; intros; destruct c0; break; simpl in *; try by (inversion H; subst; auto).
      revert H.
      case_match; [| intro H; inversion H];
        break.
      case_match; [| intro H; inversion H];
        break.
      case_match; [| intro H; inversion H];
        break.
      symmetry in HeqH1.
      case.
      move: HeqH1 => /eqP.
      intros.
      subst.
      simpl.
      f_equal; eauto.
    Qed.


  End InnerLoop.

  (* Defined over proof and implicit terms
   *)
  Fixpoint synth_le_term (p : pf) (c : ctx) {struct p} : option (sort*exp*exp) :=
    match p with
    | pvar x =>
      do t <- named_list_lookup_err c x;
         ret (t,var x, var x)
    | pcon name pl =>
      do (term_rule c' args t) <- named_list_lookup_err l name;
         (el1, el2) <- synth_le_args synth_le_term pl c c';
         al1 <- get_subseq args (with_names_from c' el1);
         al2 <- get_subseq args (with_names_from c' el2);
         ret (t[/with_names_from c' el2/],
              con name (map snd al1), con name (map snd al2))
      | ax name pfs =>
        do (term_le c' e1 e2 t) <- named_list_lookup_err l name;
           (el1, el2) <- synth_le_args synth_le_term pfs c c';
           let s1 := with_names_from c' el1;
           let s2 := with_names_from c' el2;
           ret (t[/s2/],e1[/s1/],e2[/s2/])
    | sym p' =>
      do (t,e1,e2) <- synth_le_term p' c;
         ret (t,e2,e1)
    | trans p1 p2 =>
      do (t,e1,e2) <- synth_le_term p1 c;
         (t',e2',e3) <- synth_le_term p2 c;
         ! t == t';
         ! e2 == e2';
         ret (t,e1,e3)
    | conv pt p' =>
      do (t, e1, e2) <- synth_le_term p' c;
         (t', t1) <- synth_le_sort synth_le_term pt c;
         ! t == t';
         ret (t1,e1,e2)
  end.

  Inductive pf_term_ind : pf -> Set :=
  | ind_var x : pf_term_ind (pvar x)
  | ind_con n pl : pf_args_ind pl -> pf_term_ind (pcon n pl)
  | ind_ax n pl : pf_args_ind pl -> pf_term_ind (ax n pl)
  | ind_sym p : pf_term_ind p -> pf_term_ind (sym p)
  | ind_trans p1 p2 : pf_term_ind p1 -> pf_term_ind p2 -> pf_term_ind (trans p1 p2)
  | ind_conv pt p : pf_sort_ind pt -> pf_term_ind p -> pf_term_ind (conv pt p)
  with pf_args_ind : list pf -> Set :=
  | pf_args_ind_nil : pf_args_ind [::]
  | pf_args_ind_cons p pl : pf_args_ind pl -> pf_term_ind p -> pf_args_ind (p::pl)
  with pf_sort_ind : pf -> Set :=
    (*TODO: include or no?*)
  | sind_var x : pf_sort_ind (pvar x)
  | sind_con n pl : pf_args_ind pl -> pf_sort_ind (pcon n pl)
  | sind_ax n pl : pf_args_ind pl -> pf_sort_ind (ax n pl)
  | sind_sym p : pf_sort_ind p -> pf_sort_ind (sym p)
  | sind_trans p1 p2 : pf_sort_ind p1 -> pf_sort_ind p2 -> pf_sort_ind (trans p1 p2)
  (* TODO: include or no?*)
  | sind_conv pt p : pf_sort_ind (conv pt p).


  Section InnerLoop.
    Context (pf_term_ind_trivial : forall p, pf_term_ind p).
    Fixpoint pf_args_ind_trivial pl : pf_args_ind pl :=
          match pl as pl return pf_args_ind pl with
          | [::] => pf_args_ind_nil
          | p :: pl' =>
            pf_args_ind_cons (pf_args_ind_trivial pl') (pf_term_ind_trivial p)
          end.
  End InnerLoop.

  Fixpoint pf_term_ind_trivial p : pf_term_ind p :=
    match p with
    | pvar x => ind_var x
    | pcon name pl =>
      ind_con name (pf_args_ind_trivial pf_term_ind_trivial pl)
    | ax name pl => ind_ax name (pf_args_ind_trivial pf_term_ind_trivial pl)
    | sym p' => ind_sym (pf_term_ind_trivial p')
    | trans p1 p2 =>
      ind_trans (pf_term_ind_trivial p1) (pf_term_ind_trivial p2)
    | conv pt p' =>
      ind_conv (pf_sort_ind_trivial pt) (pf_term_ind_trivial p')
    end
  with pf_sort_ind_trivial p : pf_sort_ind p :=
    match p with
    | pvar x => sind_var x
    | pcon name pl => sind_con name (pf_args_ind_trivial pf_term_ind_trivial pl)
    | ax name pl => sind_ax name (pf_args_ind_trivial pf_term_ind_trivial pl)
    | sym p' => sind_sym (pf_sort_ind_trivial p')
    | trans p1 p2 =>
      sind_trans (pf_sort_ind_trivial p1) (pf_sort_ind_trivial p2)
    | conv pt p' =>
      sind_conv pt p'
    end.

 

   Lemma synth_le_args_related' (pl : list pf)  (pa : pf_args_ind pl) c c' el1 el2 args al1 al2 al1' al2'
       : Some (el1,el2) = synth_le_args synth_le_term pl c c' ->
         Some al1 = get_subseq args (with_names_from c' el1) ->
         Some al2 = get_subseq args (with_names_from c' el2) ->
         al1' = (map snd al1) ->
         al2' = (map snd al2) ->
         le_args l c c' al1' al2' args el1 el2
   with synth_le_sort_related' (p : pf)  (ps : pf_sort_ind p) c e1 e2
    : Some (e1,e2) = synth_le_sort synth_le_term p c ->
      le_sort l c e1 e2
   with synth_le_term_related' (p : pf) (pt : pf_term_ind p) c t e1 e2
    : Some (t,e1,e2) = synth_le_term p c ->
      le_term l c t e1 e2.
   Proof using wfl.
     {
       inversion pa; intros; break; simpl in *;
         break_monadic_do; constructor;
           eauto using get_subseq_nil with imcore.
     }
    
     {
       inversion ps; intros; break; simpl in *;
       break_monadic_do; eauto with imcore.
      {
        eapply le_sort_subst; eauto with imcore.
        eapply le_subst_from_args.
        eapply synth_le_args_related'; eauto.
        eapply get_subseq_exact.
        assert (map fst (with_names_from c0 l0) = map fst (with_names_from c0 l1)).
        {
          rewrite !map_fst_with_names_from; eauto using synth_le_args_size_r, synth_le_args_size_l.
        }
        rewrite H1.
        eapply get_subseq_exact.
      }
     }
     {
       inversion pt; intros; break; simpl in *;
       break_monadic_do; eauto with imcore.
       {
         eapply le_term_subst; eauto with imcore.
         eapply le_subst_from_args.
         eapply synth_le_args_related'; eauto.
         eapply get_subseq_exact.
         assert (map fst (with_names_from c0 l0) = map fst (with_names_from c0 l1)).
         {
           rewrite !map_fst_with_names_from; eauto using synth_le_args_size_r, synth_le_args_size_l.
         }
         rewrite H1.
         eapply get_subseq_exact.
       }
     }
   Qed.

   Lemma synth_le_args_related (pl : list pf) c c' el1 el2 args al1 al2
       : Some (el1,el2) = synth_le_args synth_le_term pl c c' ->
         Some al1 = get_subseq args (with_names_from c' el1) ->
         Some al2 = get_subseq args (with_names_from c' el2) ->
         le_args l c c' (map snd al1) (map snd al2) args el1 el2.
   Proof using wfl.
     intros; eapply synth_le_args_related'; eauto using pf_args_ind_trivial,pf_term_ind_trivial.
   Qed.
   Hint Resolve synth_le_args_related : imcore.
   
   Lemma synth_le_sort_related (p : pf) c e1 e2
    : Some (e1,e2) = synth_le_sort synth_le_term p c ->
      le_sort l c e1 e2.
   Proof using wfl.
     apply synth_le_sort_related'; eauto using pf_sort_ind_trivial, pf_args_ind_trivial,pf_term_ind_trivial.
   Qed.
   Hint Resolve synth_le_sort_related : imcore.

   Lemma synth_le_term_related (p : pf) c t e1 e2
    : Some (t,e1,e2) = synth_le_term p c ->
      le_term l c t e1 e2.
   Proof using wfl.
     apply synth_le_term_related'; eauto using pf_term_ind_trivial.
   Qed.
   Hint Resolve synth_le_term_related : imcore.
   

  Section InnerLoop.
    Context (synth_wf_term : pf -> ctx -> option (sort*exp)).

    Fixpoint synth_wf_args (pl : list pf) (c c' : ctx) {struct pl}
      : option (list exp) :=
      match pl with
      | [::] => do [::] <- do ret c'; ret ([::])
      | p::pl' =>
        do (_,t)::c'' <- do ret c';
           (t',e) <- synth_wf_term p c;
           el <- synth_wf_args pl' c c'';
           ! t' == t[/with_names_from c'' el/];
           ret (e::el)
     end.
  End InnerLoop.

  (* Defined over proof and implicit terms
   *)
  Fixpoint synth_wf_term (p : pf) (c : ctx) {struct p} : option (sort*exp) :=
    match p with
    | pvar x =>
      do t <- named_list_lookup_err c x;
         ret (t,var x)
    | pcon name pl =>
      do (term_rule c' args t) <- named_list_lookup_err l name;
         el <- synth_wf_args synth_wf_term pl c c';
         al <- get_subseq args (with_names_from c' el);
         ret (t[/with_names_from c' el/], con name (map snd al))
    | ax _ _ => None
    | sym p' => None
    | trans p1 p2 => None
    | conv pt p' =>
      do (t, e) <- synth_wf_term p' c;
         (t', t1) <- synth_le_sort synth_le_term pt c;
         ! t == t';
         ret (t1,e)
  end.

  Definition synth_wf_sort (pt : pf) (c : ctx) : option sort :=
      match pt with
      | pvar x => None
      | pcon name pl =>
        do (sort_rule c' args) <- named_list_lookup_err l name;
           el <- synth_wf_args synth_wf_term pl c c';
           al <- get_subseq args (with_names_from c' el);
           ret (scon name (map snd al))
      | ax _ _ => None
      | sym p => None
      | trans p1 p2 => None
      | conv pt p => None
  end.
  

  Fixpoint synth_wf_ctx pl : option ctx :=
    match pl with
    | [::] => do ret [::]
    | (name,p)::pl' =>
      do c' <- synth_wf_ctx pl';
         ! fresh name c';
         t <- synth_wf_sort p c';
         ret (name,t)::c'
  end.

   Lemma synth_wf_args_related' (pl : list pf) (ipl : pf_args_ind pl) c c' el args al al'
       : Some (el) = synth_wf_args synth_wf_term pl c c' ->
         Some al = get_subseq args (with_names_from c' el) ->
         al' = map snd al -> 
         wf_args l c al' args el c'
   with synth_wf_term_related' (p : pf) (ip : pf_term_ind p) c t e
    : Some (t,e) = synth_wf_term p c ->
      wf_term l c e t.
   Proof using wfl.
     {
       inversion ipl; intros; break; simpl in *;
         break_monadic_do; constructor;
           eauto using get_subseq_nil with imcore.
     }
     {
       inversion ip; intros; break; simpl in *;
       break_monadic_do; eauto with imcore.
     }
   Qed.

   Lemma synth_wf_args_related (pl : list pf) c c' el args al
     : Some (el) = synth_wf_args synth_wf_term pl c c' ->
       Some al = get_subseq args (with_names_from c' el) ->
       wf_args l c (map snd al) args el c'.
   Proof using wfl.
     intros; eapply synth_wf_args_related'; eauto using pf_args_ind_trivial,pf_term_ind_trivial.
   Qed.
   Hint Resolve synth_wf_args_related : imcore.
    
   Lemma synth_wf_term_related (p : pf) c e t
    : Some (t,e) = synth_wf_term p c ->
      wf_term l c e t.
   Proof using wfl.
     intros; eapply synth_wf_term_related'; eauto using pf_args_ind_trivial,pf_term_ind_trivial.
   Qed.
   Hint Resolve synth_wf_term_related : imcore.

   Lemma synth_wf_sort_related (p : pf) c t
    : Some t = synth_wf_sort p c ->
      wf_sort l c t.
   Proof using wfl.
     destruct p; intros; break; simpl in *;
       break_monadic_do; eauto with imcore.
   Qed.
   Hint Resolve synth_wf_sort_related : imcore.

   Lemma synth_wf_ctx_related pl c
    : Some c = synth_wf_ctx pl ->
      wf_ctx l c.
   Proof using wfl.
     revert c; induction pl; intros; break; simpl in *;
       break_monadic_do; constructor; eauto with imcore.
   Qed.
   
   Hint Resolve synth_wf_ctx_related : imcore.

   Variant rule_pf : Set :=
   | sort_rule_pf : named_list_set pf -> list string -> rule_pf
   | term_rule_pf : named_list_set pf -> list string -> pf -> rule_pf
   | sort_le_pf : named_list_set pf -> pf -> pf -> rule_pf
   | term_le_pf : named_list_set pf -> pf -> pf -> pf (*sort; TODO: not needed*)-> rule_pf.
   
   Definition synth_wf_rule rp : option rule :=
    match rp with
    | sort_rule_pf pl args =>
      do c <- synth_wf_ctx pl;
         ! subseq args (map fst c);
         ret sort_rule c args
    | term_rule_pf pl args p =>
      do c <- synth_wf_ctx pl;
         t <- synth_wf_sort p c;
         ! subseq args (map fst c);
         ret term_rule c args t
    | sort_le_pf pl p1 p2 =>
      do c <- synth_wf_ctx pl;
         t1 <- synth_wf_sort p1 c;
         t2 <- synth_wf_sort p2 c;
         ret sort_le c t1 t2
    | term_le_pf pl p1 p2 pt =>
      do c <- synth_wf_ctx pl;
         (t1,e1) <- synth_wf_term p1 c;
         (t2,e2) <- synth_wf_term p2 c;
         t <- synth_wf_sort p2 c;
         ! t == t1;
         ! t == t2;
         ret term_le c e1 e2 t
    end.

  Lemma synth_wf_rule_related pr r
    : Some r = synth_wf_rule pr ->
      wf_rule l r.
   Proof using wfl.
     revert r; destruct pr; intros; break; simpl in *;
       break_monadic_do; constructor; eauto with imcore.
   Qed.
   Hint Resolve synth_wf_rule_related : imcore.
       
End RuleChecking.

Fixpoint synth_wf_lang rpl : option lang :=
  match rpl with
  | [::] => do ret [::]
  | (name,rp)::rpl' =>
    do l' <- synth_wf_lang rpl';
       ! fresh name l';
       r <- synth_wf_rule l' rp;
       ret (name,r)::l'
  end.


Lemma synth_wf_lang_related pl l
  : Some l = synth_wf_lang pl ->
    wf_lang l.
Proof.
  revert l; induction pl; intros; break; simpl in *;
    break_monadic_do; constructor; eauto with imcore.
  eapply synth_wf_rule_related; eauto with imcore.
Qed.

(*TODO: put in right place*)
Definition get_rule_args (r : rule) : list string :=
  match r with
  | sort_rule _ args => args
  | term_rule _ args _ => args
  | sort_le c _ _ => map fst c
  | term_le c _ _ _ => map fst c
  end.

Definition get_rule_ctx (r : rule) : ctx :=
  match r with
  | sort_rule c _ => c
  | term_rule c _ _ => c
  | sort_le c _ _ => c
  | term_le c _ _ _ => c
  end.


(* For using the structure of an expression to derive
   its proof
 *)
Inductive elab_term_structure {l : lang} : exp -> pf -> Prop :=
| elab_con le n s ps
  : let r := named_list_lookup (sort_rule [::][::]) l n in
    elab_args_structure s (get_rule_args r) ps (map fst (get_rule_ctx r)) ->
    elab_term_structure (con n s) (conv le (pcon n ps))
| elab_var le x : elab_term_structure (var x) (conv le (pvar x))
with elab_args_structure {l : lang} : list exp -> list string -> list pf -> list string -> Prop :=
| elab_args_nil : elab_args_structure [::] [::] [::] [::]
| elab_args_cons_ex e s a args p ps pargs
  : elab_term_structure e p ->
    elab_args_structure s args ps pargs ->
    elab_args_structure (e::s) (a::args) (p::ps) (a::pargs)
| elab_args_cons_im s args p ps a pargs
  : elab_args_structure s args ps pargs -> elab_args_structure s args (p::ps) (a::pargs).

Arguments elab_term_structure l : clear implicits.
Arguments elab_args_structure l : clear implicits.

Variant elab_sort_structure (l : lang) : sort -> pf -> Prop :=
| elab_scon n s ps
  : let r := named_list_lookup (sort_rule [::][::]) l n in
    elab_args_structure l s (get_rule_args r) ps (map fst (get_rule_ctx r)) ->
    elab_sort_structure l (scon n s) (pcon n ps).

Inductive elab_ctx_structure (l : lang) : ctx -> named_list pf -> Prop :=
| elab_ctx_nil : elab_ctx_structure l [::] [::]
| elab_ctx_cons t c a p ps
  : elab_sort_structure l t p ->
    elab_ctx_structure l c ps -> elab_ctx_structure l ((a,t)::c) ((a,p)::ps).

Variant elab_rule_structure (l : lang) : rule -> rule_pf -> Prop :=
| elab_sort_rule c args p
  : elab_ctx_structure l c p -> elab_rule_structure l (sort_rule c args) (sort_rule_pf p args)
| elab_term_rule c t args pc pt
  : elab_ctx_structure l c pc -> 
    elab_sort_structure l t pt ->
    elab_rule_structure l (term_rule c args t) (term_rule_pf pc args pt)
| elab_sort_le c t1 t2 pc pt1 pt2
  : elab_ctx_structure l c pc -> 
    elab_sort_structure l t1 pt1 ->
    elab_sort_structure l t2 pt2 ->
    elab_rule_structure l (sort_le c t1 t2) (sort_le_pf pc pt1 pt2)
| elab_term_le c t e1 e2 pc pt pe1 pe2
  : elab_ctx_structure l c pc -> 
    elab_sort_structure l t pt ->
    elab_term_structure l e1 pe1 ->
    elab_term_structure l e2 pe2 ->
    elab_rule_structure l (term_le c e1 e2 t) (term_le_pf pc pe1 pe2 pt).

Inductive elab_lang_structure :  lang -> named_list rule_pf -> Prop :=
| elab_lang_nil : elab_lang_structure [::] [::]
| elab_lang_cons l a r pr pl
  : elab_rule_structure l r pr ->
    elab_lang_structure l pl -> elab_lang_structure ((a,r)::l) ((a,pr)::pl).

Hint Constructors elab_term_structure
     elab_args_structure
     elab_sort_structure
     elab_ctx_structure
     elab_rule_structure
     elab_lang_structure : imcore.

