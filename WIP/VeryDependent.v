Set Implicit Arguments.
Set Universe Polymorphism.
Set Definitional UIP.

Require Import Lists.List.
Import List.ListNotations.

(*TODO: make SProp utils*)
Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.

Notation "a == b" := (seq a b) (at level 70, no associativity) : type_scope.

Arguments srefl {_ _}.

Definition conv {A B} (Heq : A == B) : A -> B :=
  match Heq in _ == B return A -> B with srefl => @id _ end.

Record box (A : SProp) : Set :=
  box_pf { unbox : A }.
Notation "^ p" := (box p) (at level 75, right associativity) : type_scope.
Notation "^^ p" := (box_pf p) (at level 5, right associativity).
Notation "# p" := (unbox p) (at level 5, right associativity).
  
    
(*
Inductive sigST (A : SProp) (P : A -> Type) : Type :=  existST : forall x : A, P x -> @sigST A P.

Arguments sigST [A]%type_scope P%type_scope.
Arguments existST [A]%type_scope P%function_scope x _.

Notation "{ x : A !& P }" := (sigST (fun x : A => P)) (x at level 99).
*)



(* This is the mutual definition that we want. *)
Fail Inductive ctx : Type :=
| ctx_nil : ctx
| ctx_cons : forall c : ctx, (subst c -> Type) -> ctx
    with subst : ctx -> Type :=
| subst_nil : subst ctx_nil
| subst_cons c (s : subst c) (A : subst c -> Type) : A s -> subst (ctx_cons c A).

Section Inner.
  
  Context (subst_n : nat -> forall A : Type, A -> Type).
  Fixpoint ctx_n (n : nat) : Type :=
    match n with
    | 0 => unit
    | S n0 => {c : ctx_n n0 & subst_n n0 c -> Type}
    end.

End Inner.

Fixpoint subst_n (n : nat) A (a : A) : Type :=
  let ctx_n := ctx_n subst_n in
  match n with
  | 0 => unit
  | S n' =>
      { Heq : ^(A == ctx_n (S n'))
              & {s : subst_n n' (projT1 (conv #Heq a))
                     & projT2 (conv #Heq a) s}}
  end.

Definition ctx := { n & ctx_n subst_n n}.
Definition subst (c : ctx) := subst_n (projT1 c) (projT2 c).

Definition ctx_nil : ctx := existT _ 0 tt.
Definition ctx_cons : forall (c : ctx), (subst c -> Type) -> ctx :=
  fun c => let (n, cn) as c return (subst c -> Type) -> ctx := c in
           fun A => existT _ (S n) (existT _ cn A).

(* Note: this fails. TODO: bug report? *)
Fail Definition ctx_cons' (c : ctx) : (subst c -> Type) -> ctx :=
  let (n, cn) as c return ((subst c -> Type) -> ctx) := c in
  (fun A => existT _ (S n) (existT _ cn A)).



Notation "{# x1 #}" := x1.
                               
Notation "{# x1 ; .. ; xn ; xr #}" :=
  (existT _ x1 .. (existT _ xn xr) ..)
    (format "'{#'  '[hv' x1 ;  .. ;  xn ;  xr ']'  '#}'").

Definition subst_nil : subst ctx_nil := tt.
Definition subst_cons : forall (c : ctx) (s : subst c) (A : subst c -> Type) (e : A s), subst (@ctx_cons c A) :=
  fun c : ctx =>
    let (n, c) as c return (forall (s : subst c) (A : subst c -> Type), A s -> subst (ctx_cons c A)) := c
    in fun s _ e => existT _ ^^srefl {#s; e #}.


Section Elimination.
  Context {P_ctx : ctx -> Type}
      {P_subst : forall {c : ctx}, P_ctx c -> subst c -> Type}
      (P_ctx_nil : P_ctx ctx_nil)
      (P_ctx_cons : forall {c} A, P_ctx c -> P_ctx (@ctx_cons c A))
      (P_subst_nil : P_subst P_ctx_nil subst_nil)
      (P_subst_cons : forall {c} (P_c : P_ctx c) (s : subst c) A e,
          P_subst P_c s ->
          P_subst (P_ctx_cons A P_c) (subst_cons c s A e)).

  Fixpoint ctx_rect' (n : nat) : forall (c : ctx_n _ n), P_ctx {# n; c#} :=
    match n as n return forall (c : ctx_n _ n), P_ctx {# n; c#} with
    | 0 => fun 'tt => P_ctx_nil
    | S n' => fun '{#c'; A #} => P_ctx_cons (c := {#n';c'#}) A (ctx_rect' n' c')
    end.
  
  Definition ctx_rect (c : ctx) : P_ctx c :=
    let (n, c) as c return P_ctx c := c in
    ctx_rect' n c.

  
  Fixpoint subst_rect' (n : nat)
    : forall c (s : subst_n n c), P_subst (ctx_rect' n c) s :=
    match n as n return forall c (s : subst_n n c),
        P_subst (ctx_rect' n c) s with
    | 0 => fun 'tt 'tt => P_subst_nil
    | S n' => fun '{#c'; A#} '(existT _ ^^Heq {# s'; e#})=>
                P_subst_cons (c:={#n';c'#}) _ _ (subst_rect' _ _ _)
    end.    

  Definition subst_rect (c : ctx)
    : forall (s : subst c), P_subst (ctx_rect c) s :=
    let (n, c) as c return forall (s : subst c), P_subst (ctx_rect c) s := c in
    subst_rect' n c.

End Elimination.

Section SimpleElimination.

  (*Simple elmination is the same for contexts *)
  Context
    {P_subst : forall {c : ctx}, subst c -> Type}
      (P_subst_nil : P_subst subst_nil)
      (P_subst_cons : forall {c} (s : subst c) A e,
          P_subst s ->
          P_subst (subst_cons c s A e)).

  
  Lemma simple_subst_rect : forall c (s : subst c), P_subst c s.
  Proof.
    apply @subst_rect with (P_ctx := fun _ => unit) (P_subst := fun c _ => P_subst c);
      auto.
    constructor.
  Defined.

End SimpleElimination.

  
Section Induction.
  Context {P_ctx : ctx -> Prop}
      {P_subst : forall {c : ctx}, P_ctx c -> subst c -> Prop}
      (P_ctx_nil : P_ctx ctx_nil)
      (P_ctx_cons : forall {c} A, P_ctx c -> P_ctx (@ctx_cons c A))
      (P_subst_nil : P_subst P_ctx_nil subst_nil)
      (P_subst_cons : forall {c} (P_c : P_ctx c) (s : subst c) A e,
          P_subst P_c s ->
          P_subst (P_ctx_cons A P_c) (subst_cons c s A e)).

  
Lemma ctx_ind : forall c : ctx, P_ctx c.
Proof.
  apply ctx_rect; assumption.
Defined.

Lemma subst_ind : forall c (s : subst c), P_subst (ctx_ind c) s.
Proof.
  apply subst_rect; assumption.
Qed.

End Induction.

Section SimpleInduction.

  (*Simple elmination is the same for contexts *)
  Context
    {P_subst : forall {c : ctx}, subst c -> Prop}
      (P_subst_nil : P_subst subst_nil)
      (P_subst_cons : forall {c} (s : subst c) A e,
          P_subst s ->
          P_subst (subst_cons c s A e)).

  
  Lemma simple_subst_ind : forall c (s : subst c), P_subst c s.
  Proof.
    apply simple_subst_rect; assumption.
  Qed.

End SimpleInduction.

Definition open : forall (c : ctx) (A : subst c -> Type), Type :=
  (ctx_rect (fun A => A subst_nil)
   (fun c (B : subst c -> Type) open (A : subst (ctx_cons c B) -> Type) =>
      open (fun s : subst c => forall x : B s, A (subst_cons c s B x)))).

Definition apply_subst : forall (c : ctx) (s : subst c) (A : subst c -> Type), open _ A -> A s.
  refine (simple_subst_rect (fun A oa => oa) (fun c =>_)).
  destruct c.
  intros s A e apply_subst B OB.
  refine (apply_subst _ OB _).
Defined.

Lemma open_ctx_cons c B A
  : open (ctx_cons c B) A = open _ (fun s : subst c => forall x : B s, A (subst_cons c s B x)).
Proof.
  destruct c.
  simpl.
  reflexivity.
Qed.


Definition term_to_open : forall (c : ctx) (A : subst c -> Type), (forall s: subst c, A s) -> open _ A.
  refine (ctx_rect (fun _ b => b _) _).
  destruct c.
  intros A term_to_open B e.
  eapply term_to_open.
  intros s a.
  eapply e.
Defined.


Definition open_to_term : forall (c : ctx) (A : subst c -> Type), open _ A -> forall s : subst c, A s.
  intros; eapply apply_subst; eassumption.
Defined.




Definition open_ty c := open c (fun _ => Type).
Definition open' c (A : open_ty c) := open c (open_to_term _ _ A).

Definition ctx_cons' : forall c : ctx, open_ty c -> ctx.
  intros.
  eapply ctx_cons.
  apply (open_to_term _ _ X).
Defined.

Notation "|# #|" := ctx_nil.
                               
Notation "|# x1 ; .. ; xn #|" :=
  (ctx_cons' .. (ctx_cons' ctx_nil x1) .. xn)
    (format "'|#'  '[hv' x1 ;  .. ;  xn ']'  '#|'").



Declare Custom Entry open.
Notation "#! e !#" := e
    (e custom open).

Notation "|- B" := (open' |##| B) (in custom open at level 90, B constr). 
Notation "x1 : A1 |- B" :=
  (open' |# A1%type #| (fun  (x1 : A1%type) => B%type))
     (in custom open at level 0, x1 name, A1 constr, B constr).

Notation "x1 : A1 , x2 : A2 |- B" :=
  (open' |# A1%type; fun  (x1 : A1%type) => A2%type #|
         (fun (x1 : A1%type) (x2 : A2%type) => B%type))
    (in custom open at level 0,
        x1 name, A1 constr, x2 name, A2 constr, B constr).

Notation "x1 : A1 , x2 : A2 , x3 : A3 |- B" :=
  (open' |# A1%type;
            fun (x1 : A1%type) => A2%type;
            fun (x1 : A1%type) (x2 : A2%type) => A2%type #|
     (fun (x1 : A1%type) (x2 : A2%type) (x3 : A3%type) => B%type))
    (in custom open at level 0,
        x1 name, A1 constr, x2 name, A2 constr, x3 name, A3 constr, B constr).
(*
Notation "b1 .. bn |- A" :=

Notation "x : T , A" :=
  {# ctx_cons' (projT1 A) T ; fun x => projT2 A #}
    (in custom open at level 0, right associativity, x name, T constr).


Notation "|- A" := {# ctx_nil; A#} (in custom open at level 70, A constr).


Check #! x : nat , |- nat !#.*)

Check (open' |##| nat).
Require Fin.
Compute (open' |# nat #| (fun n => Fin.t n)).
Compute (open' |# nat; fun n => Fin.t n #| (fun n f => f = f)).
Compute #! n : nat, f : Fin.t n |- f = f !#.

Arguments apply_subst c s {A}%function_scope _.

Definition ctx_cons'' (c : ctx) (H : open_ty c) : ctx :=
  ctx_cons c (open_to_term c (fun _ : subst c => Type) H).

Definition Pi {c} (A : open_ty c) (B : open_ty (ctx_cons'' c A)) : open_ty c := 
 term_to_open c (fun _ : subst c => Type)
   (fun s : subst c =>
    let A' := open_to_term c (fun _ : subst c => Type) A in
    let B' := open_to_term (ctx_cons'' c A) (fun _ : subst (ctx_cons'' c A) => Type) B in
    forall x : A' s, B' (subst_cons c s A' x)).


Lemma subst_inv c0 A P (s : subst (ctx_cons c0 A))
  : (forall s' a, P (subst_cons c0 s' A a)) -> P s.
Proof.
  destruct c0.
  cbn in *.
  destruct s as [Heq [s' a]].
  destruct Heq.
  intros H.
  apply H.
Defined.

Lemma ctx_rect_cons P_ctx P_ctx_nil P_ctx_cons c A
  : ctx_rect (P_ctx := P_ctx) P_ctx_nil P_ctx_cons (ctx_cons c A)
    = P_ctx_cons c A (ctx_rect P_ctx_nil P_ctx_cons c).
Proof.
  destruct c.
  reflexivity.
Defined.
  

Lemma simple_subst_rect_cons P_subst P_subst_nil P_subst_cons c A s a
  : simple_subst_rect (P_subst := P_subst) P_subst_nil P_subst_cons
      (ctx_cons c A) (subst_cons c s A a)
    = P_subst_cons c s A a (simple_subst_rect  P_subst_nil P_subst_cons c s).
Proof.
  destruct c.
  reflexivity.
Defined.

Definition forall' {c} (A : subst c -> Type) (B : subst (ctx_cons c A) -> Type) :=
  fun s => forall x : A s, B (subst_cons c s A x).

Definition app' {c A B}
  : open c (forall' A B) ->
    forall y : open c A, open c (fun s => B (subst_cons c s A (apply_subst c s y))) :=
  fun f v => 
 term_to_open c (fun s : subst c => B (subst_cons c s A (apply_subst c s v)))
   (fun s : subst c => let f0 := apply_subst c s f in f0 (apply_subst c s v)).

Lemma seq_trans {A} (a b c : A)
  : a == b -> b == c -> a == c.
Proof. destruct 1; eauto. Qed.

Definition lam' {c A B} (e : open (ctx_cons c A) B) : open c (forall' A B).
  unfold forall'.
  revert dependent c.
  destruct c.
  revert c.
  induction x; destruct c; cbn; intros; eauto.
Defined. (*TODO: simpler def; use ctx_ind? Do same for app'?*)


Definition app'' {c A B}
  : open c (forall' A B) ->
    open (ctx_cons c A) B.
  unfold forall'.
  intros.
  revert dependent c.
  destruct c.
  revert c.
  induction x; destruct c; cbn; intros; eauto.
Defined. (*TODO: simpler def; use ctx_ind?*)

Lemma apply_subst_cons c s A B a (e : open c (forall' A B))
  : apply_subst (ctx_cons c A) (subst_cons c s A a) (app'' e)
    = apply_subst c s e a.
Proof.
  revert dependent c.
  destruct c as [x c].
  revert c.
  induction x; destruct c; cbn; intros; eauto.
Qed.


Lemma lam'_term_to_open c0 A A0 e
  : (lam' (term_to_open (ctx_cons c0 A) A0 e))
    = term_to_open c0 (forall' A A0) (fun s a => e (subst_cons c0 s A a)).
Proof.
  revert dependent c0;
    destruct c0 as [n c0].
  revert c0.
  induction n; destruct c0;
    cbn.
  all: intros; eauto.
Qed.


Lemma apply_subst_cons' c s A B a (e : open (ctx_cons c A) B)
  : apply_subst (ctx_cons c A) (subst_cons c s A a) e
    = apply_subst c s (lam' e) a.
Proof.
  revert dependent c.
  destruct c as [x c].
  revert c.
  induction x; destruct c; cbn; intros; eauto.
Qed.

Definition open_eq c A : open c A -> open c A -> Prop :=
  fun a b => forall s, apply_subst c s a = apply_subst c s b.

Lemma apply_subst_lam' c A B s' (e : open (ctx_cons c A) B) a
  : apply_subst c s' (lam' e) a = apply_subst (ctx_cons c A) (subst_cons c s' A a) e.
Proof.
  revert A B e a.
  pattern c, s'.
  apply simple_subst_ind with (c:=c) (s:=s').
  {
    reflexivity.
  }
  {
    intros.
    rewrite !apply_subst_cons'.
    rewrite H.
    reflexivity.
  }
Qed.

Lemma app''_lam' c A B  (e : open (ctx_cons c A) B) : open_eq _ _ (app'' (lam' e)) e.
Proof.
  unfold open_eq.  
  intros s.
  pattern s.
  eapply subst_inv.
  clear s.
  intros.
  rewrite ! apply_subst_cons.
  apply apply_subst_lam'.
Qed.

Lemma open_to_term_inverse c
                           (*TODO: Set should be Type. Universe issue when replaced. *)
  : forall (A : subst c -> Set) e s, open_to_term c A (term_to_open c A e) s = e s.
Proof.
  unfold open_to_term.  
  pattern c.
  eapply ctx_ind with (c:=c).
  {
    cbn.
    intros.
    destruct s.
    constructor.
  }
  {
    cbn; intros.
    pattern s.
    eapply subst_inv with (c0:=c0) (A:=A) (s:= s).
    clear s; intros.
    enough (open_eq _ _ (term_to_open (ctx_cons c0 A) A0 e) (app'' (lam' (term_to_open (ctx_cons c0 A) A0 e)))).
    {
      rewrite H0.
      erewrite apply_subst_cons.
      rewrite  lam'_term_to_open.
      erewrite H.
      reflexivity.
    }
    intro s.
    rewrite app''_lam'.
    reflexivity.
  }
Qed.
(*TODO: repeat for open' layer? How important is open_ty vs subst -> Type? *)


(******)
Require Import Coq.Wellfounded.Well_Ordering.

(*For inference reasons*)
Inductive Empty : Type :=.
Inductive unitty : Type := Ity.

Notation B := (fun (x:bool) => if x then unitty else Empty).
Definition WO_nat := WO bool (fun x => if x then unitty else Empty).
Definition O : WO_nat := sup _ _ false (fun (x : Empty) => match x with end).
Definition S n : WO_nat := sup _ _ true (fun x => n).


Record dep_fun1 (A : Type) (G : A -> Type) (alpha : forall {a}, G a -> A) : Type := {
    placeholder : A;
    dep_fun_data : G placeholder;
    dep_fun_eqn : placeholder == alpha dep_fun_data
  }.


Record dep_fun2 (A : Type) (G : A -> Type) (alpha : forall {a}, G a -> A) : Type := {
    placeholder : A;
    dep_fun_data : G placeholder;
    dep_fun_eqn : placeholder == alpha dep_fun_data
  }.

Context (A:Type).
Check (fun B => forall (a:A) (f: A -> B f a), Type).

(*Idea: close the loop on B first, then f.*)
Definition dep_fun_ty
  (A : Type)(*TODO: WO for proofs*)
  := (B : (forall (a:A) (f: A -> B a), Type)).

Section Inner.
  
  Context (subst_n : unitty -> forall A : Type, A -> Type).
  Fixpoint ctx_n' (n : WO_nat) : Type :=
    match n with
    | sup _ _ false f => unitty
    | sup _ _ true f => {c : ctx_n' (f Ity) & subst_n Ity c -> Type}
    end.

End Inner.

(*TODO: how to restrict A to substn'? it does 2 things:
  untie the very dependent knot & accept the recursive argument

  A gets B[f,x], not f
 *)
Definition f_subst_n' (b : bool)
  (f : (if b then unitty else Empty) -> WO bool B)
  (subst_n' : (if b then unitty else Empty) -> forall A : Type, A -> Type)
  (A:Type) (a:A)
  : Type :=
  let ctx' : (B b -> forall A : Type, A -> Type) -> WO_nat -> Type :=
    if b as b return ((B b -> forall A : Type, A -> Type) -> WO_nat -> Type)
    then ctx_n'
    else fun x _ => unit in
  { Heq : ^(A == ctx' subst_n' (sup _ _ b f)) &
            (if b as a1 return
                       forall (f : B a1 -> WO bool B)
                     (subst_n' : B a1 -> forall A : Type, A -> Type)
                     (Heq : ^(A == ctx' subst_n' (sup _ _ a1 f))), Type
             then fun f subst_n' Heq =>  {s : subst_n' Ity _ (projT1 (conv #Heq a))
                                                           & projT2 (conv #Heq a) s}
             else fun _ _ _ => unitty)
              f
              subst_n'
              Heq }.

Definition subst_n' : WO_nat -> forall A (a : A), Type :=
  WO_rect _ _ _ f_subst_n'.

Definition ctx' := { n & ctx_n subst_n n}.
Definition subst' (c : ctx) := subst_n (projT1 c) (projT2 c).

Definition f_subst_n'' (b:bool) (f : (if b then unitty else Empty) -> WO bool B)
       (subst_n' : (if b then unitty else Empty) -> forall A : Type, A -> Type) : forall A : Type, A -> Type :=


  f_subst_n'
     : forall b : bool,
       ((if b then unitty else Empty) -> WO bool B) ->
       ((if b then unitty else Empty) -> forall A : Type, A -> Type) -> forall A : Type, A -> Type
  if b as a1 return
          (B a1 -> WO bool B) ->
          (B a1 -> forall A : Type, A -> Type) ->
          forall A : Type, A -> Type
  then fun f subst_n' (A : Type) (a:A) =>
         (*TODO: to lift this out, have to reckon w/ f*)
         { Heq : ^(A == ctx_n' subst_n' (S (f Ity)))
                 & {s : subst_n' Ity _ (projT1 (conv #Heq a))
                        & projT2 (conv #Heq a) s}}
  else fun _ _ (A:Type) (a:A) => unitty.


Section VD_nat.
  (* Use a WO as A to guarantee a known ordering on it *)
  Notation A := nat.
  Context (B : (forall (a:A), {RecB & RecB a}) -> A -> Type).
  Context (f' : forall (f : forall (a:A), {RecB & RecB a}), forall (a:A), B f a).
  (*TODO: need knowledge of B, can't be an arbitrary parameter?\
   TODO: need to do a match*)
  Fixpoint f_rec (a:A) : {RecB & RecB a}.
    destruct a.
    {
      unshelve eapply existT with (x:=B _).
      exact f_rec.
      apply f'.
    }
    {
      unshelve eapply existT with (x:=B _).
      exact f_rec.
      apply f'.
      
    }
    Show Proof.
  Defined.
      construc
    match a with
    | 0 => _
    let (w1,w2) := a in (*TODO: call f_rec only on w2???*)
    existT _ (B f_rec) (f' f_rec a).

                                              
    match a with
    | sup _ _ w1 w2 => ?
    end.

    
Section VD.
  Context (W1 :Type) (W2 : W1 -> Type).
  (* Use a WO as A to guarantee a known ordering on it *)
  Notation A := (WO W1 W2).
  Context (B : (forall (a:A), {RecB & RecB a}) -> A -> Type).
  Context (f' : forall (f : forall (a:A), {RecB & RecB a}), forall (a:A), B f a).
  (*TODO: need knowledge of B, can't be an arbitrary parameter?\
   TODO: need to do a match*)
  Fixpoint f_rec (a:A) : {RecB & RecB a} :=
    let (w1,w2) := a in (*TODO: call f_rec only on w2???*)
    existT _ (B f_rec) (f' f_rec a).

                                              
    match a with
    | sup _ _ w1 w2 => ?
    end.

Notes: ctx a bit of a detour, subst the real meat.
W/ self-very-dependence handled, ctx should be a standard nested def?.



Section SimpleGeneric.
  (* Idea: F-algebras: (F,a, i : F a -> a) *)
  Parameter (F : Type -> Type).

  Record alg : Type :=
    {
      carrier : Type;
      interp : F carrier -> carrier;
    }.

  Parameter (WO_A : Type) (WO_B : WO_A -> Type).

  Notation WO := (WO WO_A WO_B).

  
  

  (******)

Definition lam {c} (A : open_ty c) (B : open_ty (ctx_cons'' c A))
  : open' (ctx_cons'' c A) B ->
    open' c (Pi A B).
  intro e.
  eapply (term_to_open c).
  intro s.
  unfold Pi.
  (*TODO: do this in a way that computes*)
  rewrite open_to_term_inverse with (c := c) (A:=(fun _ : subst c => Type)).
  TODO: open_to_term inverse
  cbn.

  
Section Inner.   
  Context (pair_to_subst' : forall c, { A & A -> subst c}).
  (*TODO: try to remove Heq from this definition. *)  
  Definition subst' : ctx -> Type :=
    ctx_rect (P_ctx := fun _ => Type) unit
      (fun (c' : ctx) (B : subst c' -> Type) (rec : (fun _ : ctx => Type) c') =>
         let (A,s2s) := pair_to_subst' c' in
         {s : rec & {Heq : ^(rec == A) & B (s2s (conv #Heq s))}}).
End Inner.

(*  TODO: subst' is basically duplicating subst c. What did I want subst c without the Heq?.
  TODO: is there a way to extract the Heqs from subst c into a separate structure?.*)

Definition pair_to_subst'' c : subst' c -> subst c :=
  

(*TODO: it turns out that for generic functions to consume these, they will often be very dependent.
  Can my encoding work for fns too?
*)

Fixpoint ctx_to_sum (c : ctx) : Type
  with subst_to_pair c (subst : c) : ctx_to_sum c.
  refine (ctx_rect (P_ctx := fun _ => Type) unit _ c).
  intros.
  apply sigT with (A:= X).

Definition open_ty_lift (F : Type -> Type) [c : ctx] (A : open_ty c) : open_ty c :=
  term_to_open c (fun _ => Type)
    (fun s => F (open_to_term c (fun _ => Type) A s)).

Fixpoint nary_app' {c : ctx} {A : subst c -> Type} (l : list (forall s, A s)) : forall s, list (A s) :=
  match l with
  | [] => fun s => []
  | a::l' => fun s => a s :: nary_app' l' s
  end.

  

Definition nary_app {c : ctx} {A : open_ty c} (l : list (open' c A)) : open' c (open_ty_lift list A).
  eapply term_to_open with (c:=c).
  intros.
  assert (open_to_term c (fun _ : subst c => Type) (open_ty_lift list A) = (fun s : subst c => list (open_to_term c (fun _ : subst c => Type) A s))).
  2:{
    rewrite H.
    induction l; [ apply [] | apply cons]; eauto.
    apply (open_to_term c _ a s).
  }
  
    exact l.
  eapply nary_app'.
  intro s.
  eappl
  {
    eapply nary_app'.
  2:{

  refine (ctx_rect _ _ c).


Inductive cc : Type :=
(*TODO: what to do with levels?*)
| cc_ty (n:nat) : cc
| cc_bool : cc
| cc_true : cc
| cc_false : cc
| cc_if : cc -> cc -> cc -> cc
| cc_pi : cc -> cc -> cc
| cc_app : cc -> cc -> cc
| cc_lam : cc -> cc -> cc
| cc_var (n : nat) : cc.

Definition cc_ctx := list cc.

Axiom (cc_sub1 : cc -> cc -> cc).

Inductive cc_wf : cc_ctx -> cc -> cc -> Type :=
| cc_ty_wf c (n:nat) : cc_wf c (cc_ty n) (cc_ty (S n))
| cc_bool_wf c : cc_wf c cc_bool (cc_ty 0)
| cc_true_wf c : cc_wf c cc_true cc_bool
| cc_false_wf c : cc_wf c cc_false cc_bool
| cc_if_wf c A ec e e'
  : cc_wf c ec cc_bool ->
    cc_wf c e A ->
    cc_wf c e' A ->
    cc_wf c (cc_if ec e e') A
| cc_pi_wf c n m A B
  : cc_wf c A (cc_ty n) -> 
    cc_wf (A::c) B (cc_ty m) ->
    cc_wf c (cc_pi A B) (cc_ty (max (S n) m))
| cc_app_wf c A B e e'
  : cc_wf c e (cc_pi A B) ->
    cc_wf c e' A ->
    cc_wf c (cc_app e e') (cc_sub1 B e)
| cc_lam_wf c A n e B
  : cc_wf c A (cc_ty n) ->
    cc_wf (A::c) e B ->
    cc_wf c (cc_lam A e) (cc_pi A B)
| cc_var_wf c n A
  (*TODO: wrong nth; need no default*)
  : nth n c (cc_var n) = A ->
    cc_wf c (cc_var n) A.

Inductive cc_wf_ctx : cc_ctx -> Type :=
| cc_ctx_nil : cc_wf_ctx []
| cc_ctx_cons c A n : cc_wf_ctx c -> cc_wf c A (cc_ty n) -> cc_wf_ctx (A::c).

Inductive cc_wf_ty : cc_ctx -> cc -> Type :=
| cc_ty_wrap c t n : cc_wf c t (cc_ty n) -> cc_wf_ty c t.

Section WithCtx.
  Context (cc_denote_ctx : forall c, cc_wf_ctx c -> ctx).

  Section Inner.
    Context (cc_denote_ty : forall c t (cwf : cc_wf_ctx c),
                cc_wf_ty c t -> subst (cc_denote_ctx cwf) -> Type).

    Fixpoint cc_denote c e t (ewf : cc_wf c e t)
      : forall (cwf : cc_wf_ctx c) (twf : cc_wf_ty c t)
               (s : subst (cc_denote_ctx cwf)), cc_denote_ty cwf twf s.
    Proof.
      induction ewf;
        intros.
      {
        TODO: functions really need to be mutual?.
        Is there a sim. trick I can do as w/ the datatypes?.
        Issue: need computational rules.
        Question: in the pyrosome (finite map) case, can I break the recursion?.
        the c, t are 'less than'
        dependent inversion twf; subst.
        inversion ewf.
      

TODO: this function is very dependent. Is there a way for me to use the same trick?
Fixpoint cc_denote c e t
  : forall (cwf : cc_wf_ctx c), cc_wf c e t -> open (cc_denote_ctx cwf) (cc_denote_ty c t)
  with cc_denote_ty c t
  : forall (cwf : cc_wf_ctx c), cc_wf c t (cc_ty n) -> open_ty (cc_denote_ctx cwf)
  with cc_denote_ctx c : cc_wf_ctx c -> ctx.


Definition wkn_ty c A: (subst c -> Type) -> subst (ctx_cons c A) -> Type.
Proof.
  intros B s.
  eapply B.
  TODO: subst_tl
  destruct s.
  eauto.
  eapply apply_subst.
Admitted.
  

(*Definition wkn c A B : open c A -> open (ctx_cons c B) A.*)

