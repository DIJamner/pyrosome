Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Named Require Import Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

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

  
  (* The type doesn't discriminate between term and sort equalities *)
  Unset Elimination Schemes.
  Inductive pf : Type :=
  (* variable name *)
  | pvar : V -> pf
  (* Rule label, list of subterms*)
  | pcon : V -> list pf -> pf
  | ptrans : pf -> pf -> pf
  | psym : pf -> pf
  | pconv : pf -> pf -> pf.
  Set Elimination Schemes.

  Coercion pvar : V >-> pf.

  (*Stronger induction principle w/ better subterm knowledge
   *)
  Fixpoint pf_ind
           (P : pf -> Prop)
           (IHV : forall n, P(pvar n))
           (IHC : forall n l, all P l ->
                              P (pcon n l))
           (IHT : forall p1, P p1 -> forall p2, P p2 -> P(ptrans p1 p2))
           (IHS : forall p, P p -> P(psym p))
           (IHCV : forall p1, P p1 -> forall p2, P p2 -> P(pconv p1 p2))
           (e : pf) { struct e} : P e :=
    match e with
    | pvar n => IHV n
    | pcon n l =>
        let fix loop l :=
          match l return List.fold_right (fun t => and (P t)) True l with
          | [] => I
          | e' :: l' => conj (pf_ind _ IHV IHC IHT IHS IHCV e') (loop l')
          end in
        IHC n l (loop l)
    | ptrans p0 p1 => IHT p0 (pf_ind _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_ind _ IHV IHC IHT IHS IHCV p1)
    | psym p0 => IHS p0 (pf_ind _ IHV IHC IHT IHS IHCV p0)
    | pconv p0 p1 => IHCV p0 (pf_ind _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_ind _ IHV IHC IHT IHS IHCV p1)
    end.

  Fixpoint pf_rect
           (P : pf -> Type)
           (IHV : forall n, P(pvar n))
           (IHC : forall n l,
               List.fold_right (fun t => prod (P t)) unit l ->
               P (pcon n l))
           (IHT : forall p1, P p1 -> forall p2, P p2 -> P(ptrans p1 p2))
           (IHS : forall p, P p -> P(psym p))
           (IHCV : forall p1, P p1 -> forall p2, P p2 -> P(pconv p1 p2))
           (e : pf) { struct e} : P e :=
    match e with
    | pvar n => IHV n
    | pcon n l =>
        let fix loop l :=
          match l return List.fold_right (fun t => prod (P t)) unit l with
          | [] => tt
          | e' :: l' => (pf_rect _ IHV IHC IHT IHS IHCV e', loop l')
          end in
        IHC n l (loop l)
    | ptrans p0 p1 => IHT p0 (pf_rect _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_rect _ IHV IHC IHT IHS IHCV p1)
    | psym p0 => IHS p0 (pf_rect _ IHV IHC IHT IHS IHCV p0)
    | pconv p0 p1 => IHCV p0 (pf_rect _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_rect _ IHV IHC IHT IHS IHCV p1)
    end.

  Definition pf_rec := 
    pf_rect
      : forall P : pf -> Set,
        (forall n : V, P n) ->
        (forall (n : V) (l : list pf), fold_right (fun t : pf => prod (P t)) unit l -> P (pcon n l)) ->
        (forall p1 : pf, P p1 -> forall p2 : pf, P p2 -> P (ptrans p1 p2)) ->
        (forall p : pf, P p -> P (psym p)) ->
        (forall p1 : pf, P p1 -> forall p2 : pf, P p2 -> P (pconv p1 p2)) -> forall e : pf, P e.

  Variant pf_fact :=
    | tm_eq (e1 : term) (e2 : term) (t : sort)
    | srt_eq (t1:sort) (t2:sort).

  

  Section WithLang.

    Context (l : lang).
    (*TODO: change section name?*)
    Context (c : ctx).

    Section Inner.
      Context (check_proof : pf -> option pf_fact).
      Fixpoint check_args_proof (args : list pf) (c' : ctx) :=
        match args, c' with
        | [], [] => Some ([],[])
        | p::args, (_,t)::c'=>
            @! let (lhs, rhs) <- check_args_proof args c' in
               let (tm_eq e1 e2 t') <?- check_proof p in
               (*TODO: use Eqb instance*)
               let ! sort_eq_dec t[/with_names_from c' lhs/] t' in
               ret (e1::lhs, e2::rhs)
        | _,_=> None
        end.
    End Inner.
    
    (*TODO: split fn by output*)
    Fixpoint check_proof (p : pf) : option pf_fact :=
      match p with
      | pvar n =>
          @! let t <- named_list_lookup_err c n in
             ret tm_eq (var n) (var n) t
      | pcon n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | sort_rule c' _ =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    ret srt_eq (scon n lhs) (scon n rhs)
             | term_rule c' _ t =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    ret tm_eq (con n lhs) (con n rhs) t[/with_names_from c' lhs/]
             | sort_eq_rule c' t1 t2 =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret srt_eq t1[/lsub/] t2[/rsub/]
             | term_eq_rule c' e1 e2 t =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret tm_eq e1[/lsub/] e2[/rsub/] t[/lsub/]
             end
               (*TODO: needs to run on sort eqs*)
      | ptrans p0 p1 =>
          @! let (tm_eq e1 e2 t) <?- check_proof p0 in
             let (tm_eq e1' e2' t') <?- check_proof p1 in
             let ! sort_eq_dec t t' in
             let ! term_eq_dec e2 e1' in
             ret tm_eq e1 e2' t
      | psym p =>
          @! let (tm_eq e1 e2 t) <?- check_proof p in
             ret (tm_eq e2 e1 t)
      | pconv p0 p1 =>
          @! let (tm_eq e1 e2 t) <?- check_proof p0 in
             let (srt_eq t1 t2) <?- check_proof p1 in
             let ! sort_eq_dec t t1 in
             ret tm_eq e1 e2 t2
      end.
