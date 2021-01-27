Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils.
Require Import Named.Exp Named.ARule.
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
| ax : string -> pf
(* applying a substitution;
   can't be distributed over axioms
   unless in the context of a given language
   
   TODO: use a named list or regular list?
   Can I figure out appropriate names given the language?
   Not in the var case. Should I add a ctx argument to
   the var case? Seems like it might be a good idea.
   A relevant is how these terms will be checked.
   I'll leave this consideration until I get to my proves_wf function.

   TODO: do I want this or no?
   Might be able to eliminate it, but probably
   not worth it at the moment.
 *)
| sub : pf -> ctx (*TODO: hack to beat fixpoint checker; remove when able*) ->
        named_list_set pf (* interface ctx wf*) -> list pf (* subst le *) -> pf
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
         (IHA : forall n, P(ax n))
         (IHS : forall e' c pfc l,
             P e' ->
             List.fold_right (fun p => and (P p.2)) True pfc ->
             List.fold_right (fun p => and (P p)) True l ->
             P (sub e' c pfc l))
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
        | e' :: l' => conj (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e') (loop l')
        end in
    IHC n l (loop l)
  | ax n => IHA n
  | sub e' c pfc l =>
    let fix cloop l :=
        match l return List.fold_right (fun t => and (P t.2)) True l with
        | [::] => I
        | (_,e') :: l' => conj (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e') (cloop l')
        end in
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [::] => I
        | e' :: l' => conj (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e') (loop l')
        end in
    IHS e' c pfc l (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e') (cloop pfc) (loop l)
  | sym e' =>
    IHSY e' (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e')
  | trans e1 e2 =>
    IHT e1 e2 (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e1)
        (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e2)
  | conv e1 e2 =>
    IHCV e1 e2 (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e1)
        (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e2)
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
             
Section RuleChecking.
  Context (l : lang).

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
      | ax name =>
        do (sort_le c' e1 e2) <- named_list_lookup_err l name;
           ! c == c';
           ret (e1,e2)
      | sub p c' _ pl =>
        do (e1, e2) <- synth_le_sort p c';
           (el1, el2) <- synth_le_args pl c c';
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

    Fixpoint synth_le_sort_ex (pt : pf) (c : ctx) : option (sort * sort) :=
      match pt with
      | pvar x => None
      | pcon name pl =>
        do (sort_rule c' args) <- named_list_lookup_err l name;
           (el1, el2) <- synth_le_args pl c c';
           ret (scon name el1, scon name el2)
      | ax name =>
        do (sort_le c' e1 e2) <- named_list_lookup_err l name;
           ! c == c';
           ret (e1,e2)
      | sub p c' _ pl =>
        do (e1, e2) <- synth_le_sort p c';
           (el1, el2) <- synth_le_args pl c c';
           let s1 := with_names_from c' el1;
           let s2 := with_names_from c' el2;
           ret (e1[/s1/],e2[/s2/])
      | sym p =>
        do (e1,e2) <- synth_le_sort_ex p c;
           ret (e2,e1)
      | trans p1 p2 =>
        do (e1,e2) <- synth_le_sort_ex p1 c;
           (e2',e3) <- synth_le_sort_ex p2 c;
           !e2 == e2';
           ret (e1,e3)
      | conv pt p => None
    end.    
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
    | ax name =>
      do (term_le c' e1 e2 t) <- named_list_lookup_err l name;
         !c == c';
         ret (t,e1,e2)
    | sub p' c' _ pl =>
      do (t,e1, e2) <- synth_le_term p' c';
         (el1, el2) <- synth_le_args synth_le_term pl c c';
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

  Fixpoint synth_le_term_ex (p : pf) (c : ctx) {struct p}
    : option (sort*exp*exp) :=
    match p with
    | pvar x =>
      do t <- named_list_lookup_err c x;
         ret (t,var x, var x)
    | pcon name pl =>
      do (term_rule c' args t) <- named_list_lookup_err l name;
         (el1, el2) <- synth_le_args synth_le_term_ex pl c c';
         ret (t[/with_names_from c' el2/],
              con name el1, con name el2)
    | ax name =>
      do (term_le c' e1 e2 t) <- named_list_lookup_err l name;
         !c == c';
         ret (t,e1,e2)
    | sub p' c' _ pl =>
      do (t,e1, e2) <- synth_le_term_ex p' c';
         (el1, el2) <- synth_le_args synth_le_term_ex pl c c';
         let s1 := with_names_from c' el1;
         let s2 := with_names_from c' el2;
         ret (t[/s2/],e1[/s1/],e2[/s2/])
    | sym p' =>
      do (t,e1,e2) <- synth_le_term_ex p' c;
         ret (t,e2,e1)
    | trans p1 p2 =>
      do (t,e1,e2) <- synth_le_term_ex p1 c;
         (t',e2',e3) <- synth_le_term_ex p2 c;
         ! t == t';
         ! e2 == e2';
         ret (t,e1,e3)
    | conv pt p' =>
      do (t, e1, e2) <- synth_le_term_ex p' c;
         (t', t1) <- synth_le_sort_ex synth_le_term_ex pt c;
         ! t == t';
         ret (t1,e1,e2)
  end.

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
    | ax name => None
    | sub p' c' _ pl => None
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
      | ax name => None
      | sub p c' _ pl => None
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

  Fixpoint all_ctxs_ok p : bool :=
    match p with
    | pvar _ => true
    | pcon _ pl => foldr andb true (map all_ctxs_ok pl)
    | ax name => true
    | sub p c' plc pl =>
      (Some c' == synth_wf_ctx plc) &&
      (foldr andb true (map (fun q => (all_ctxs_ok q.2)) plc)) &&
      (foldr andb true (map all_ctxs_ok pl))
    | sym p => all_ctxs_ok p
    | trans p1 p2 => (all_ctxs_ok p1) && (all_ctxs_ok p2)
    | conv pt p => (all_ctxs_ok pt) && (all_ctxs_ok p)
    end.

  Definition list_all_ctxs_ok pl :=
    foldr andb true (map all_ctxs_ok pl).

  
  Definition named_list_all_ctxs_ok (pl : named_list pf) :=
    foldr andb true (map (fun p => all_ctxs_ok p.2) pl).

  
  Definition check_le_term p c t e1 e2 : bool :=
    (Some (t,e1, e2) == synth_le_term p c) &&
    (all_ctxs_ok p).
  Arguments check_le_term p c t e1 e2/.
  
  Definition check_le_sort p c t1 t2 : bool :=
    (Some (t1, t2) == synth_le_sort synth_le_term p c)&&
    (all_ctxs_ok p).
  Arguments check_le_sort p c t1 t2/.

  
  Definition check_le_args pl c c' el1 el2 : bool :=
    (Some (el1, el2) == synth_le_args synth_le_term pl c c')&&
    (list_all_ctxs_ok pl).
  Arguments check_le_args pl c c' el1 el2/.

  
  Definition check_wf_term p c e t : bool :=
    (Some (t,e) == synth_wf_term p c) &&
    (all_ctxs_ok p).
  Arguments check_wf_term p c e t/.
  
  Definition check_wf_sort p c t : bool :=
    (Some t == synth_wf_sort p c) &&
    (all_ctxs_ok p).
  Arguments check_wf_sort p c t/.
  
  Definition check_wf_ctx pl c : bool :=
    (Some c == synth_wf_ctx pl) &&
    (named_list_all_ctxs_ok pl).
  Arguments check_wf_ctx pl c/.

  
  Definition check_wf_args pl c el c' : bool :=
    (Some el == synth_wf_args synth_wf_term pl c c')&&
    (list_all_ctxs_ok pl).
  Arguments check_wf_args pl c el c'/.
  

  Variant rule_pf : Set :=
  | sort_rule_pf : named_list_set pf -> list string -> rule_pf
  | term_rule_pf : named_list_set pf -> list string -> pf -> rule_pf
  | sort_le_pf : named_list_set pf -> pf -> pf -> rule_pf
  | term_le_pf : named_list_set pf -> pf -> pf -> pf (*sort; TODO: not needed*)-> rule_pf.
      
  Definition synth_wf_rule rp : option rule :=
    match rp with
    | sort_rule_pf pl args =>
      do !named_list_all_ctxs_ok pl;
         c <- synth_wf_ctx pl;
         ! subseq args (map fst c);
         ret sort_rule c args
    | term_rule_pf pl args p =>
      do !named_list_all_ctxs_ok pl;
         !all_ctxs_ok p;
         c <- synth_wf_ctx pl;
         t <- synth_wf_sort p c;
         ! subseq args (map fst c);
         ret term_rule c args t
    | sort_le_pf pl p1 p2 =>
      do !named_list_all_ctxs_ok pl;
         !all_ctxs_ok p1;
         !all_ctxs_ok p2;
         c <- synth_wf_ctx pl;
         t1 <- synth_wf_sort p1 c;
         t2 <- synth_wf_sort p2 c;
         ret sort_le c t1 t2
    | term_le_pf pl p1 p2 pt =>
      do !named_list_all_ctxs_ok pl;
         !all_ctxs_ok p1;
         !all_ctxs_ok p2;
         !all_ctxs_ok pt;
         c <- synth_wf_ctx pl;
         (t1,e1) <- synth_wf_term p1 c;
         (t2,e2) <- synth_wf_term p2 c;
         t <- synth_wf_sort p2 c;
         ! t == t1;
         ! t == t2;
         ret term_le c e1 e2 t
  end.

  Definition check_wf_rule rp r : bool :=
    Some r == synth_wf_rule rp.
  Arguments check_wf_rule rp r/.

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

Definition check_wf_lang rpl l : bool :=
  Some l == synth_wf_lang rpl.
Arguments check_wf_lang rpl l/.


Arguments check_wf_args l pl c el c'/.
Arguments check_wf_ctx l pl c/.
Arguments check_wf_sort l p c t/.
Arguments check_wf_term l p c e t/.
Arguments check_le_args l pl c c' el1 el2/.
Arguments check_le_sort l p c t1 t2/.
Arguments check_le_term l p c t e1 e2/.
Arguments check_wf_rule l rp r/.
