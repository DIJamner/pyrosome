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

   Lemma synth_le_args_related' (pl : list pf)  (pa : pf_args_ind pl) c c' el1 el2 args al1 al2
       : Some (el1,el2) = synth_le_args synth_le_term pl c c' ->
         Some al1 = get_subseq args (with_names_from c' el1) ->
         Some al2 = get_subseq args (with_names_from c' el2) ->
         le_args l c c' (map snd al1) (map snd al2) args el1 el2
   with synth_le_sort_related' (p : pf)  (ps : pf_sort_ind p) c e1 e2
    : Some (e1,e2) = synth_le_sort synth_le_term p c ->
      le_sort l c e1 e2
   with synth_le_term_related' (p : pf) (pt : pf_term_ind p) c t e1 e2
    : Some (t,e1,e2) = synth_le_term p c ->
      le_term l c t e1 e2.
   Proof.
     inversion pa;
        destruct c'; destruct args; break; simpl in *; repeat case_match; intros; simpl in *;
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
                end; subst; simpl in* ).          
      { constructor. }
      {
        constructor; eauto with imcore.
        change (le_args l c c' (map (snd (A:=string))  [::]) (map (snd (A:=string)) [::]) [::] l0 l1).
        eapply synth_le_args_related'; eauto using get_subseq_nil with imcore.
      }  
      {
        revert H5 H6.
        case seq: (s == s0).
        {
          move:seq => /eqP ->.
          repeat case_match; intros; simpl in *;
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
               end; subst; simpl in* ).
          constructor; eauto with imcore.
        }
        {
          intros; constructor; eauto with imcore.
        }
      }
      {
        inversion ps; simpl; repeat case_match; intros;
        repeat lazymatch goal with
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
               end; subst;
          eauto with imcore.
      {
        eapply le_sort_subst; eauto with imcore.
        eapply le_subst_from_args.
        eapply synth_le_args_related'; eauto.
        eapply get_subseq_exact.
        assert (map fst (with_names_from c0 l0) = map fst (with_names_from c0 l1)).
        {
          rewrite !map_fst_with_names_from; eauto using synth_le_args_size_r, synth_le_args_size_l.
        }
        rewrite H0.
        eapply get_subseq_exact.
      }
      }
      {
        inversion pt; simpl; repeat case_match; intros;
        repeat lazymatch goal with
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
               end; subst;
          eauto with imcore.
      {
        eapply le_term_subst; eauto with imcore.
        eapply le_subst_from_args.
        eapply synth_le_args_related'; eauto.
        eapply get_subseq_exact.
        assert (map fst (with_names_from c0 l0) = map fst (with_names_from c0 l1)).
        {
          rewrite !map_fst_with_names_from; eauto using synth_le_args_size_r, synth_le_args_size_l.
        }
        rewrite H0.
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
     apply synth_le_args_related'; eauto using pf_args_ind_trivial,pf_term_ind_trivial.
   Qed.

   
   Lemma synth_le_sort_related (p : pf) c e1 e2
    : Some (e1,e2) = synth_le_sort synth_le_term p c ->
      le_sort l c e1 e2.
   Proof using wfl.
     apply synth_le_sort_related'; eauto using pf_sort_ind_trivial, pf_args_ind_trivial,pf_term_ind_trivial.
   Qed.

   Lemma synth_le_term_related (p : pf) c t e1 e2
    : Some (t,e1,e2) = synth_le_term p c ->
      le_term l c t e1 e2.
   Proof using wfl.
     apply synth_le_term_related'; eauto using pf_term_ind_trivial.
   Qed.
   

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

   Lemma synth_wf_args_related (pl : list pf) c c' el args al
       : Some (el) = synth_wf_args synth_wf_term pl c c' ->
         Some al = get_subseq args (with_names_from c' el) ->
         wf_args l c (map snd al) args el c'
   with synth_wf_term_related (p : pf) c t e1 e2
    : Some (t,e1,e2) = synth_le_term p c ->
      le_term l c t e1 e2.
   Proof.
     {
       
       
End RuleChecking.

Fixpoint refl_pf (e : exp) : pf :=
  match e with
  | var x => pvar x
  | con n l => pcon n (map refl_pf l)
  end.
  
Fixpoint term_step_redex (l : lang) (e : exp) : option (pf*exp) :=
    match l with
    | [::] => None
    | (name,term_le c e1 e2 t)::l' =>
      (*TODO: check that rule is executable, i.e. FV(e1) >= FV(e2)*)
      match term_step_redex l' e with
      | Some t' => Some t'
      | None => do s <- matches_unordered e e1;
                ret (ax name (map refl_pf (map snd s)), e2[/s/])
      end
    | _::l' => term_step_redex l' e
    end.

  Fixpoint sort_step_redex (l : lang) (t : sort) : option (pf*sort) :=
    match l with
    | [::] => None
    | (name,sort_le c t1 t2)::l' =>
      (*TODO: check that rule is executable, i.e. FV(t1) >= FV(t2)*)
      match sort_step_redex l' t with
      | Some t' => Some t'
      | None => do s <- matches_unordered_sort t t1;
                ret (ax name (map refl_pf (map snd s)),t2[/s/])
      end
    | _::l' => sort_step_redex l' t
    end.

  Section InnerLoop.
    Context (term_par_step : forall (l : lang) (e : exp), option (pf*exp)).
    (*TODO: might run afoul of implicits here; probably needs to operate on 
      full proof terms
     *)
    Fixpoint args_par_step l s {struct s} : option (list pf * list exp) :=
         match s with
         | [::] => None
         | e::s' =>
           match term_par_step l e, args_par_step l s' with
           | Some e', Some s'' => Some (e'::s'')
           | Some e', None => Some (e'::s')
           | None, Some s'' => Some (e::s'')
           | None, None => None
           end
         end.
  End InnerLoop.

  Fixpoint term_par_step (l : lang) (e : exp) {struct e} : option exp :=
    match term_step_redex l e, e with
    | Some e',_ => Some e'
    | None, var _ => None
    | None, con name s =>
      do s' <- args_par_step term_par_step l s;
      ret (con name s')
    end.
  
  Definition sort_par_step (l : lang) (t:sort) : option sort :=
    match sort_step_redex l t, t with
    | Some e',_ => Some e'
    | None, scon name s =>
      do s' <- args_par_step term_par_step l s;
      ret (scon name s')
    end.

  Fixpoint term_par_step_n (l : lang) (e : exp) (fuel : nat) : exp :=
    match fuel, term_par_step l e with
    | 0,_ => e
    | S _, None => e
    | S fuel', Some e' => term_par_step_n l e' fuel'
    end.
  
  Fixpoint sort_par_step_n (l : lang) (t : sort) (fuel : nat) : sort :=
    match fuel, sort_par_step l t with
    | 0,_ => t
    | S _, None => t
    | S fuel', Some t' => sort_par_step_n l t' fuel'
    end.



