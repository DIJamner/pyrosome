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
| sub : pf -> ctx -> list pf -> pf
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
         (IHS : forall e' c l,
             P e' ->
             List.fold_right (fun p => and (P p)) True l ->
             P (sub e' c l))
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
  | sub e' c l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [::] => I
        | e' :: l' => conj (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e') (loop l')
        end in
    IHS e' c l (pf_ind IHV IHC IHA IHS IHSY IHT IHCV e') (loop l)
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
      | sub p c' pl =>
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
      | sub p c' pl =>
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
    | sub p' c' pl =>
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
    | sub p' c' pl =>
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

  Definition check_le_term p c t e1 e2 : bool :=
    synth_le_term p c == Some (t,e1,e2).
  
  Definition check_le_sort p c t1 t2 : bool :=
    synth_le_sort synth_le_term p c == Some (t1,t2).

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
    | sub p' c' pl => None
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
      | sub p c' pl => None
      | sym p => None
      | trans p1 p2 => None
      | conv pt p => None
    end.

  Definition check_wf_term p c e t : bool :=
    synth_wf_term p c == Some (t,e).
  
  Definition check_wf_sort p c t : bool :=
    synth_wf_sort p c == Some t.

  Fixpoint check_wf_ctx pl c : bool :=
    match pl, c with
    | [::], [::] => true
    | [::], _::_ => false
    | _::_,[::] => false
    | p::pl', (name,t)::c' =>
      (fresh name c') &&
      (check_wf_sort p c' t) &&
      (check_wf_ctx pl' c')
    end.

  Variant rule_pf : Set :=
  | sort_rule_pf : list pf -> rule_pf
  | term_rule_pf : list pf -> pf -> rule_pf
  | sort_le_pf : list pf -> pf -> pf -> rule_pf
  | term_le_pf : list pf -> pf -> pf -> pf (*sort*)-> rule_pf.
      
  Definition check_wf_rule rp r : bool :=
    match rp, r with
    | sort_rule_pf pl, sort_rule c args =>
      (subseq args (map fst c)) &&
      (check_wf_ctx pl c)
    | term_rule_pf pl p, term_rule c args t =>
      (subseq args (map fst c)) &&
      (check_wf_ctx pl c) &&
      (check_wf_sort p c t)
    | sort_le_pf pl p1 p2, sort_le c t1 t2 =>
      (check_wf_ctx pl c) &&
      (check_wf_sort p1 c t1) &&
      (check_wf_sort p2 c t2)
    | term_le_pf pl p1 p2 pt, term_le c e1 e2 t =>
      (check_wf_ctx pl c) &&
      (check_wf_sort pt c t) &&
      (check_wf_term p1 c e1 t) &&
      (check_wf_term p2 c e2 t)
    | _, _=> false
    end.

End RuleChecking.
  
Fixpoint check_wf_lang rpl l : bool :=
  match rpl, l with
  | [::], [::] => true
  | [::], _::_ => false
  | _::_,[::] => false
  | rp::rpl', (name,r)::l' =>
    (fresh name l') &&
    (check_wf_rule l' rp r)
  end.
