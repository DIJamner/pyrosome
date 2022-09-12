Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.


Require Import List.

(* What I want:
Inductive ctx : Type :=
| ctx_nil : ctx
| ctx_cons : forall c : ctx, (subst c -> Type) -> ctx
with subst : ctx -> Type :=
| subst_nil : subst ctx_nil
| subst_cons c (s : subst c) (A : subst c -> Type) : A s -> subst (ctx_cons c A).

But: can't have ctx in type of subst
 *)

(*
Definition eq_conv : forall A, A -> forall B, B -> Prop.
  intros A a B b.
  refine {Heq : A = B | _}.
  rewrite Heq in a; (exact (a = b)).
Defined. *)

Section Inner.
  
  Context (subst_n : nat -> forall A : Type, A -> Type).
  Fixpoint ctx_n (n : nat) : Type :=
    match n with
    | 0 => unit
    | S n0 => {c : ctx_n n0 & subst_n n0 c -> Type}
    end.

End Inner.

Set Definitional UIP.

Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.

Arguments srefl {_ _}.


Definition conv {A B} (Heq : seq A B) : A -> B :=
  match Heq in seq _ B return A -> B with srefl => @id _ end.

Inductive sigST (A : SProp) (P : A -> Type) : Type :=  existST : forall x : A, P x -> @sigST A P.

Arguments sigST [A]%type_scope P%type_scope.
Arguments existST [A]%type_scope P%function_scope x _.

Fixpoint subst_n (n : nat) A (a : A) {struct n} : Type :=
  let ctx_n := ctx_n subst_n in
  match n with
  | 0 => unit
  | S n' =>
      @sigST (seq A (ctx_n (S n')))
            (fun Heq =>
               let c := conv Heq a in
               {s : subst_n n' (projT1 c) & projT2 c s})
  end.


Definition ctx := { n & ctx_n subst_n n}.
Definition subst (c : ctx) := subst_n (projT1 c) (projT2 c).

Definition ctx_nil : ctx := existT _ 0 tt.
Definition ctx_cons : forall (c : ctx), (subst c -> Type) -> ctx :=
  fun c => let (n, cn) as c return ((subst c -> Type) -> ctx) := c in
           (fun A => existT _ (S n) (existT _ cn A)).
(* Note: this fails: *)
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
    let (n, c) as c return (forall (s : subst c) (A : subst c -> Type),
                        A s -> subst (ctx_cons c A)) := c
    in fun s _ e => existST _ srefl {#s; e #}.


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

  (*TODO: make better for computation*)
  Lemma subst_rect : forall c (s : subst c), P_subst (ctx_rect c) s.
Proof.
  destruct c as [n c].
  revert c.
  induction n; simpl; intros.
  {
    destruct c.
    destruct s.
    eapply P_subst_nil.
  }
  {
    destruct c as [c A].
    destruct s as [Heq [s e]].
    simpl in Heq.
    match goal with
      [Heq : seq ?A ?A |- _] =>
        change Heq with (@srefl _ A) in *
    end.
    simpl in *.
    eapply (@P_subst_cons {#n;c#} _ s A e).
    eapply IHn.
  }
Defined.

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


(*TODO: naming on closed vs open subst*)


(*
Require Import Program.Basics.

Local Open Scope program_scope.*)

(*TODO: return an option?*)
Definition ctx_tl' n : ctx_n subst_n n -> ctx_n subst_n (pred n) :=
  match n as n' return ctx_n subst_n n' -> ctx_n subst_n (pred n') with
  | 0 => fun c => tt
  | S _ => @projT1 _ _
  end.

Definition ctx_tl (c : ctx) : ctx :=
  let (n, c') := c in
  {# pred n; ctx_tl' n c' #}.


Definition ctx_hd' n
  : forall (c : ctx_n subst_n n),
    subst {# pred n; ctx_tl' n c #} -> Type :=
    match n as n
          return forall (c : ctx_n subst_n n),
        subst {# pred n; ctx_tl' n c #} -> Type
    with
    | 0 => fun c s => False
    | S _ => @projT2 _ _
    end.

Definition ctx_hd : forall (c : ctx), subst (ctx_tl c) -> Type :=
  fun c =>
  let (n, c') as c' return subst (ctx_tl c') -> Type := c in ctx_hd' _ _.

(*
(*TODO: check that this computes*)
Definition subst_tl' n
  : forall (c : ctx_n subst_n n),
    msubst {# n; c #} (ctx_tl {# n; c #}).
  refine (
      match n as n
            return forall (c : ctx_n subst_n n),
          msubst {# n; c #} (ctx_tl {# n; c #})
      with
      | 0 => fun _ _ => tt
      | S n0 =>
          fun c =>
            let (c, A) as c return msubst {# S n0; c #} (ctx_tl {# S n0; c #})
              := c in  _
      end).
  simpl in c.
  intro s.
  simpl.
  destruct s.
  revert x s.
  simpl.
  eapply projT1.
Defined.

Definition subst_tl : forall (c : ctx), msubst c (ctx_tl c).
  refine (fun c => _).
  destruct c.
  (*TODO: universe issues with this:
  refine (let (n,c') as c return msubst c (ctx_tl c) := c in _).*)
  refine (fun s => _).
  eapply subst_tl'; eauto.
Defined.
*)


(* for convenience so that code can use names, not projections
open [nat;fun s => Vec (proj2 s)] (fun s => len (proj2 s) = proj2 (proj1 s))
=>
forall (x : nat) (v : Vec x), len v = x

 *)
Definition open : forall (c : ctx) (A : subst c -> Type), Type :=
  (ctx_rect (fun A => A subst_nil)
   (fun c (B : subst c -> Type) open (A : subst (ctx_cons c B) -> Type) =>
      open (fun s : subst c => forall x : B s, A (subst_cons c s B x)))).

Definition apply_subst : forall (c : ctx) (s : subst c) (A : subst c -> Type), open _ A -> A s.
  refine (simple_subst_rect (fun A oa => oa) (fun c =>_)).
  destruct c.
(*  refine (let (n,c) as c return forall (s : subst c) (A : sort c) (e : A s),
                           (forall A0 : sort c, open c A0 -> A0 s) ->
                           forall A0 : sort (ctx_cons c A), open (ctx_cons c A) A0 -> A0 (subst_cons c s A e) := c in _).*)
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
Notation "#! e !#" :=
  (let (c, A) := e in
  open' c A)
    (e custom open).
(*
Notation "b1 .. bn |- A" :=

Notation "x : T , A" :=
  {# ctx_cons' (projT1 A) T ; fun x => projT2 A #}
    (in custom open at level 0, right associativity, x name, T constr).


Notation "|- A" := {# ctx_nil; A#} (in custom open at level 70, A constr).


Check #! x : nat , |- nat !#.*)

Check (open' |##| nat).
(*TODO: does not compute away as I'd want; blocked on UIP_refl*)
Require Fin.
Compute (open' |# nat #| (fun n => Fin.t n)).
Compute (open' |# nat; fun n => Fin.t n #| (fun n f => f = f)).

Notation msubst c c' := (open c (fun _ => subst c')).
Notation sort c := (open c (fun _ => Type)).
Notation term c A := (open c A).

 *)

Arguments apply_subst c s {A}%function_scope _.

(*                      
Definition msubst_to_fn
  : forall (c c' : ctx) (s : msubst c c'),
    subst c -> subst c'.
  intros c c'.
  refine (open_to_term _ _).
Defined.
                      
Definition apply_tysubst : forall (c c' : ctx) (s : msubst c c'), sort c' -> sort c.
  intros.
  apply term_to_open.
  intro s'.
  apply open_to_term in X.
  exact X.
  apply open_to_term in s; auto.
Defined.

Arguments apply_tysubst {c c'} s _.


Definition apply_msubst
  : forall (c c' : ctx) (s : msubst c c') A,
    open c' A -> open c (fun s' => A (open_to_term _ _ s s')).
  intros.
  eapply term_to_open.
  intros s'.
  eapply open_to_term in X.
  apply X.
Defined.


Example test : open |##| (fun _ => Type).
 *)
Require Import List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Named Require Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation Sterm := (@Term.term V).
  Notation Sctx := (@Term.ctx V).
  Notation Ssort := (@Term.sort V).
  Notation Ssubst := (@Term.subst V).
  Notation rule := (@Rule.rule V).
  Notation lang := (@Rule.lang V).

  Section Inner.
    Context (compile_ctx : Sctx -> ctx).
    Context (compile_sort : forall c : Sctx, Ssort -> subst (compile_ctx c) -> Type).
    Context (compile_term : forall (c : Sctx) (t : Ssort),
                Sterm -> forall s : subst (compile_ctx c), compile_sort c t s).

    Variant compiler_case : rule -> Type :=
      | sort_case c args
        : (subst (compile_ctx c) -> Type) ->
          (compiler_case (Rule.sort_rule c args))
      | term_case c args t 
        : (forall s : subst (compile_ctx c), compile_sort c t s) ->
          (compiler_case (Rule.term_rule c args t))
      (* TODO: generalize to setoids *)
      | sort_eq_case c t1 t2
        : (forall s : subst (compile_ctx c), compile_sort c t1 s = compile_sort c t2 s) ->
          (compiler_case (Rule.sort_eq_rule c t1 t2))
      | term_eq_case c e1 e2 t
        : (forall s : subst (compile_ctx c),
              compile_term c t e1 s = compile_term c t e2 s) ->
          (compiler_case (Rule.term_eq_rule c e1 e2 t)).
    (*TODO: will probably need equality cases*)

    
  
  Fixpoint compile_lang (l : lang) : Type :=
    match l with
    | [] => unit
    | (_, r)::l' =>
        (* TODO: constrain this string or no? *)
        compiler_case r * compile_lang l'
    end.

  Instance rule_default : WithDefault rule := Rule.sort_rule [] [].
  
  Fixpoint cmp_lookup l n
    : compile_lang l -> compiler_case (named_list_lookup default l n) :=
    match l with
    | [] => fun _ => sort_case [] [] (fun _ => True)
    | (x,r)::l' =>
        fun '(c,cmp) =>
          match eqb n x as cond
                return compiler_case (if cond then r else named_list_lookup default l' n)
          with true => c | false => cmp_lookup l' n cmp end
    end.
    
  End Inner.

  Section WithCompiler.

    Context (l : lang)
              (*TODO: need my induction-recursion trick again*)
    (cmp : compile_lang _ _ l).

  
  

  
  
  Print Assumptions compile_lang.

            
(* TODO: make a version with a good definition for computing*)
Definition mwkn : forall (c : ctx) A, subst (ctx_cons c A) -> subst c.
  intro c.
  refine (let (n, c') as c return forall A : subst c -> Type, subst (ctx_cons c A) -> subst c := c in _).
  intros A s.
  unfold subst in *.
  simpl in *.
  refine (let (c, s0) := s in _).
  destruct c.
  destruct s0.
  (*TODO: lemma for inverting JMeq*)
  simpl in *.
  
    pose proof (Heq' := x0).
    apply JMeq_eq in Heq'.
    inversion Heq'.
    subst.
    destruct s0; auto.
    (*TODO: Universes
Defined.*)
Admitted.
Arguments mwkn {_} {_}.
  

(*TODO: difference between meta- and object-level substs. Need to make env sim. to ctx, but w/ open metavars.
Trying to reuse meta defns here.
 *)
Definition env : sort |##| := fun s => ctx.
(*TODO: need explicit weakening at the meta-level*)
Definition sub : sort |# env; env ∘ mwkn #|.
refine (fun s => _).
unfold subst in *.
simpl in *.
                                          


Definition hd : forall (c: ctx) A, term (ctx_cons c A) (ty_subst wkn A)
  
  refine (let '{# c; Heq; s; _ #} := s in _).
  

Definition wkn c A : subst (ctx_cons c A) -> subst c.
  refine 
  intro s.
  
  refine (let '{# c; Heq; s; _ #} := s in _).
  refine (subst_rect (P:=fun _ _ => subst c) _ _ _ s).
  {
    admit.
  }
  {
    auto.
  }
  Show Proof.
  unfold subst in *.
  simpl in *.
  intro s.
  refine (let '{# c'; Heq; s'; _ #} := s in _).
  destruct c'; simpl in *.
  inversion Heq.
  inversion H0.
  exact s'.
  refine (
  Show Proof.
  constructor.

Definition wkn c A : subst (ctx_cons c A) -> subst c.
  refine (let (n, c) as s return  subst (ctx_cons s A) -> subst s := c in _).
  destruct c.
  simpl.
  Show Proof.
  intro s.
  unfold ctx_cons in *.
  simpl.
  destruct s.
    as [s _].
