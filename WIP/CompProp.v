Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

From Coq Require Import Bool Lists.List Classes.DecidableClass.
Import ListNotations.
Import BoolNotations.
Open Scope list.

(*
Require Import Utils.Base Utils.Booleans Utils.Eqb.
*)
Require Import Utils (*TODO: temp*).
Require Import Utils.Monad.
Import StateMonad.

(* Not definitions so that they don't get in the way of evaluation
 *)
Notation lift1 f A := (fun a => f (A a)).
Notation lift2 f A B := (fun a => f (A a) (B a)).

Section WithTeleType.

  Context (A : Type)
    (*(E : A -> Type)*).

  (* Propositions that have Boolean computational behavior where possible.
     TODO: separate embedded props/vals out into subst so that we can compute A = A ~> True
   *)
Variant cProp : Type := cTrue | cFalse | cEmbed (P : forall (a : A), (* E a ->*) Prop).

Definition interp (a : A) (*(e : E a)*) (P : cProp) : Prop :=
  match P with
  | cTrue => True
  | cFalse => False
  | cEmbed P => P a
  end.

(* TODO: what args for A? *)
(*TODO: want exists (the same) e*)
Definition cCorresponds cA A :=
  (forall a (* (e : E a)*) , interp a cA <-> A a).

Existing Class cCorresponds.

Ltac solve_corresponds :=
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp |- _] => destruct P;try clear P end;
  cbn in *; intros a;
  repeat match goal with [H : forall a (* (e : E a)*), _ |- _] => specialize (H a) end;
  intuition fail.

(* Note: this hint needs to be last; make sure it works right *)
Definition cembed_corresponds B : cCorresponds (cEmbed B) B.
Proof. solve_corresponds. Qed.

#[export] Instance ctrue_corresponds : cCorresponds cTrue (fun _ => True).
Proof. solve_corresponds. Qed.

#[export] Instance cfalse_corresponds : cCorresponds cFalse (fun _ => False).
Proof. solve_corresponds. Qed.

Ltac inhabited_corresponds v :=
  unfold cCorresponds in *;
    cbn;
    intuition idtac;
  constructor; eauto;
  apply v.


#[export] Instance inhabited_Prop_corresponds : cCorresponds cTrue (fun t => inhabited Prop).
Proof. inhabited_corresponds True. Qed.

(*TODO: always use this one or defer to ones like above sometimes? *)
#[export] Instance inhabited_default_corresponds X `{WithDefault X} : cCorresponds cTrue (fun _ => inhabited X).
Proof. inhabited_corresponds default. Qed.

Definition cand (a b : cProp) :=
  match a, b with
  | cTrue, _ => b
  | cFalse, _ => cFalse
  | cEmbed P, cTrue => cEmbed P
  | cEmbed P, cFalse => cFalse
  | cEmbed P1, cEmbed P2 => cEmbed (lift2 and P1 P2)
  end.

Definition cor (a b : cProp) :=
  match a, b with
  | cTrue, _ => cTrue
  | cFalse, _ => b
  | cEmbed P, cTrue => cTrue
  | cEmbed P, cFalse => cEmbed P
  | cEmbed P1, cEmbed P2 => cEmbed (lift2 or P1 P2)
  end.

Definition cnot (a : cProp) :=
  match a with
  | cTrue => cFalse
  | cFalse => cTrue
  | cEmbed P => cEmbed (lift1 not P)
  end.

(* TODO: deprecated; replaced w/ cforall *)
Definition cimpl (a b : cProp) :=
  match a, b with
  | cTrue, _ => b
  | cFalse, _ => cTrue
  | cEmbed P, cTrue => cTrue
  | cEmbed P, cFalse => cEmbed (lift1 not P)
  | cEmbed P1, cEmbed P2 => cEmbed (fun a => P1 a -> P2 a)
  end.


Definition ciff (a b : cProp) :=
  match a, b with
  | cTrue, cTrue
  | cFalse, cFalse => cTrue
  | cTrue, cFalse 
  | cFalse, cTrue => cFalse
  | cEmbed P, cTrue
  | cTrue, cEmbed P => cEmbed P
  | cEmbed P, cFalse
  | cFalse, cEmbed P => cEmbed (lift1 not P)
  | cEmbed P1, cEmbed P2 => cEmbed (lift2 iff P1 P2)
  end.


Section WithParams.
  Context (cB' cB : cProp) (B' B : forall x : A, (*E x ->*) Prop)
    (B'_corr : cCorresponds cB' B')
    (B_corr : cCorresponds cB B).
 

#[export] Instance cand_corresponds : cCorresponds (cand cB' cB) (lift2 and B' B).
Proof. solve_corresponds. Qed.

#[export] Instance cor_corresponds : cCorresponds (cor cB' cB) (lift2 or B' B).
Proof. solve_corresponds. Qed.

#[export] Instance cnot_corresponds : cCorresponds (cnot cB') (lift1 not B').
Proof. solve_corresponds. Qed.

#[export] Instance cimpl_corresponds : cCorresponds (cimpl cB' cB) (fun a => B' a -> B a).
Proof. solve_corresponds. Qed.

#[export] Instance ciff_corresponds : cCorresponds (ciff cB' cB) (lift2 iff B' B).
Proof. solve_corresponds. Qed.

(*TODO: where to put this?*)
Lemma inhabited_prop C : C <-> inhabited C.
Proof.
  intuition eauto using inhabits.
  destruct H; auto.
Qed.

#[export] Instance inhabited_prop_corresponds : cCorresponds cB (lift1 inhabited B).
Proof using B_corr.
  clear B'_corr cB' B'.
   unfold cCorresponds in *; repeat lazymatch goal with
                                   | P:cProp |- _ => destruct P; try clear P
                                   end; cbn in *; intros a;
   repeat match goal with
          | H:forall a, _ |- _ => specialize (H a)
     end.
   all: try solve[intuition eauto using inhabited_prop].
   all: rewrite <- inhabited_prop; intuition fail.
Qed.
     


End WithParams.


End WithTeleType.


Lemma cProp_intro cB' B' `{c_Corr : cCorresponds unit cB' (fun _ => B')}
  : interp tt cB' -> B'.
Proof. apply c_Corr. Qed.
Lemma cProp_ex cB' B' `{c_Corr : cCorresponds unit cB' (fun _ => B')}
  : B' -> interp tt cB'.
Proof. apply c_Corr. Qed.

(*
Ltac solve_corresponds :=
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
  cbn in *; intuition fail.
*)
     
Arguments cProp_intro {cA}%type_scope {A}%type_scope {c_Corr} _ : rename.

Arguments cProp_ex {cA} {A}%type_scope {c_Corr} _ : rename.

#[export] Hint Extern 100 (cCorresponds _ ?A) => apply cembed_corresponds : typeclass_instances.


Definition cforall T A cA (cP : cProp {t : T & A t}) : cProp T :=
  match cA, cP with
  | cFalse _, _
  | _ , cTrue _ => cTrue _
  | cTrue _, cFalse _ => cFalse _
  | cEmbed P, cFalse _ => cEmbed (lift1 not P)
  | cTrue _, cEmbed P
  | cEmbed _, cEmbed P => cEmbed (fun t => forall x : A t, P (existT _ t x))
  end.


Instance cforall_corresponds T A cA cB (B : forall t : T, A t -> Prop)
  `{cCorresponds T cA (fun t => inhabited (A t))}
  `{cCorresponds (sigT A)%type cB (fun t' => B (projT1 t') (projT2 t'))}
  : cCorresponds (cforall A cA cB) (fun t => forall x : A t, B t x).
Proof.
  (*
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
    cbn in *; intros a;
    repeat match goal with [H : forall a (* (e : E a)*), _ |- _] => specialize (H a) end.
  {
    pose proof (fun a' => H0 (existT _ a a')).
    intuition idtac.
    specialize (H1 x).
    intuition idtac.
  }
  {
    pose proof (fun a' => H0 (existT _ a a')).
    intuition idtac.
    eapply H0 with (a:=existT _ _ _); eauto.
  }
    eapply H2.
  }
  {
    pose proof (fun a' => H0 (existT _ a a')).
    intuition idtac.
    {
       eapply H0 with (a:=existT _ _ _).
       eapply H2.
    }
  }
    {
      apply H0; simpl; eauto.
    }
  }
  Unshelve.
  auto.
Qed.
#[export] Hint Extern 90 (cCorresponds _ (fun t => forall x : _, _))
=> simple eapply cforall_corresponds : typeclass_instances.*)
Admitted.


Definition cexists T A (cA : cProp T) (cP : cProp {t : T & A t}) : cProp T :=
  match cA, cP with
  | _, cFalse _
  | cFalse _, _ => cFalse _
  | cTrue _, cTrue _ => cTrue _
  | cEmbed P, cTrue _ => cEmbed P
  | cTrue _, cEmbed P
  | cEmbed _, cEmbed P =>  cEmbed (fun t => exists x : A t, P (existT _ t x))
  end.
    
(*
#[export] Instance cexist_corresponds T A cB (B : forall t : T, A t -> Prop)
  `{cCorresponds (sigT A)%type cB (fun t' => B (projT1 t') (projT2 t'))}
  : cCorresponds (cexists A cA cB) (fun t => exists x : A t, B t x).
Proof.
  
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
    cbn in *; intros a.
  {
    pose proof (fun a' => H (existT _ a a')).
    intuition idtac.
    {
      destruct H1.
      exists X.
      eapply H0 with (a':= X).
      auto.
    }
    eapply exists_inhabited; eauto.
  }
  { pose proof (fun a' => H (existT _ a a')).    
    firstorder.
  }
  {
    firstorder.
  }
Qed.
*)

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C).
Proof.
  intros.
  eapply cProp_intro.
  eapply cProp_ex in H.
  cbn in *.
  tauto.
Abort.

(*
#[export] Hint Extern 90 (cCorresponds _ (fun t => _))
=> eapply cforall_corresponds : typeclass_instances.*)

Goal (forall A B C, C /\ False /\ A -> True /\ B /\ C).
Proof.
  eapply cProp_intro.
  cbn.
  tauto.
Qed.


Ltac solve_corresponds :=
  unfold cCorresponds in*;
  repeat lazymatch goal with [P : cProp _ |- _] => destruct P;try clear P end;
  cbn in *; intros a;
  repeat match goal with [H : forall a (* (e : E a)*), _ |- _] => specialize (H a) end;
  intuition fail.


Definition cIs_true {T} (b : bool) : cProp T := if b then cTrue _ else cFalse _.

#[export] Instance cIstrue_corresponds T b : cCorresponds (cIs_true b) (fun t : T=> Is_true b).
Proof. destruct b; solve_corresponds. Qed.



Fixpoint call2 {T A B} (R : A -> B -> cProp T) l1 l2 : cProp T :=
  match l1, l2 with
  | [], [] => cTrue _
  | a::l1, b::l2 => cand (R a b) (call2 R l1 l2)
  | _, _ => cFalse _
  end.


Instance call2_corresponds {T A B} cR (R : T -> A -> B -> Prop)
  `{forall a b, cCorresponds (cR a b) (fun t => R t a b)}
  l1 l2
  : cCorresponds (call2 cR l1 l2) (fun t:T => Forall2 (R t) l1 l2).
Proof.
  revert l2;
    induction l1; destruct l2; basic_goal_prep.
  1-3:cbv; intuition eauto; safe_invert H0.
  {
    assert (forall t, Forall2 (R t) (a :: l1) (b :: l2) <-> R t a b /\ Forall2 (R t) l1 l2).
    {
      intuition eauto;safe_invert H0; tauto.
    }
    unfold cCorresponds.
    intro t.
    rewrite H0.
    revert t.
    change (cCorresponds (cand (cR a b) (call2 cR l1 l2)) (fun t => R t a b /\ Forall2 (R t) l1 l2)).
    typeclasses eauto.
  }
Qed.

Require Import Pyrosome.Theory.Core Pyrosome.Elab.Elab.


Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

   Section WithLang.

     Context (l : lang).

     Section WithCtx.
    Context (c : ctx).

    Section Inner.
      Context (celab_term : term -> term -> sort -> cProp unit).
      Fixpoint celab_args s args es c' {struct es} : cProp unit :=
        match c', es, args, s with
        | [], [], [], [] => cTrue _
        | _, _, _::_, []
        | _, _, [],  _::_
        | [], _, _::_, _
        | [], _::_, _, _
        | _::_, [], _, _ => cFalse _
        | (name,t')::c'', ee::es', [], [] =>
            cand (cEmbed (fun _ => wf_term l c ee t'[/with_names_from c'' es'/]))
                 (celab_args [] [] es' c'')
        | (name,t')::c'', ee::es', name'::args', e::s' =>
            if eqb name name'
            then
              cand (celab_term e ee t'[/with_names_from c'' es'/])
                (celab_args s' args' es' c'')
            else
              cand (cEmbed (fun _ => wf_term l c ee t'[/with_names_from c'' es'/]))
                (celab_args s args es' c'')
        end.
    End Inner.

    Fixpoint celab_term (e ee : term) t : cProp unit :=
      match e, ee with
      | var x, var ex =>
          cIs_true (andb (eqb x ex)
                      (eqb (named_list_lookup_err c x) (Some t)))
      | con name s, con ename es =>
          cand (cIs_true (eqb name ename))
          match named_list_lookup_err l name with
          | Some (term_rule c' args t') =>
              (*TODO: use eq_term variant w/ full refl (TODO: finish that one's proof) *)
              (cand (cEmbed (fun _ => eq_sort l c t t'[/with_names_from c' es/]))
                 (celab_args celab_term s args es c'))
          | _ => cFalse _
          end
      | _, _ => cFalse _
      end.

    Definition celab_sort (t et : sort) : cProp unit :=
      let (name, s) := t in
      let (ename, es) := et in
      cand (cIs_true (eqb name ename))
        match named_list_lookup_err l name with
        | Some (sort_rule c' args) =>
            (celab_args celab_term s args es c')
        | _ => cFalse _
        end.

    Section __.
      Context (evars : nat -> term).
      (*TODO: generalizes Utils.Gensym; move there*)
      Definition fresh {M} `{Monad M} : stateT nat M nat :=
        fun n => Mret (n, S n).

      Section Inner.
        Context (gen_elab_term : term -> stateT nat option term).

        Definition gen_elab_args_body gen_elab_args1 gen_elab_args2
          s args (c' : ctx) : stateT nat option (list term) :=
          match c', args, s with
          | [], [], [] => @! ret []
          | _, _::_, []
          | _, [], _::_
          | [], _, _ => fun _ : nat => None
          | (n,_)::c'', [], [] =>
              @!let s_out <- gen_elab_args1 c'' in
                let x <- fresh (M:=option) in                
                let ee : term := evars x in
                ret (ee::s_out)
          | (n,_)::c'', n'::args', e::s' =>
              if eqb n n'
              then @!let s_out <- gen_elab_args2 s' args' c'' in
                     let ee <- gen_elab_term e in
                     ret (ee::s_out)
              else @!let s_out <- gen_elab_args1 c'' in
                     let x <- fresh (M:=option) in                
                     let ee := evars x in
                     ret (ee::s_out)
          end.

        Section InnerInner.
          
        Context (gen_elab_args : list term -> list V -> list (V * sort) -> stateT nat option (list term)).
        Context (s : list term) (args : list V).
        Fixpoint gen_elab_args1 (c' : ctx) {struct c'} : stateT nat option (list term) :=
          gen_elab_args_body gen_elab_args1 gen_elab_args s args c'.

        End InnerInner.
                             
        Fixpoint gen_elab_args s args (c' : ctx) {struct s} : stateT nat option (list term) :=
          gen_elab_args_body (gen_elab_args1 gen_elab_args s args) gen_elab_args s args c'.

      End Inner.

      Fixpoint gen_elab_term (e : term) :  stateT nat option term :=
        match e with
        | var x => Mret (var x)
        | con n s =>
          match named_list_lookup_err l n with
          | Some (term_rule c' args t') =>
              @!let s' <- gen_elab_args gen_elab_term s args c' in
                ret (con n s')
          | _ => fun _ : nat => None
          end
        end.

      
      Definition gen_elab_sort (t : sort) :  stateT nat option sort :=
        match t with
        | scon n s =>
          match named_list_lookup_err l n with
          | Some (sort_rule c' args) =>
              @!let s' <- gen_elab_args gen_elab_term s args c' in
                ret (scon n s')
          | _ => fun _ : nat => None
          end
        end.

      (*Definition gen_elab_term (e : term) : option term :=
        option_map fst (gen_elab_term' e 0).*)

    End __.

     End WithCtx.

     
     Fixpoint celab_ctx (c ec : ctx) :=
       match c, ec with
       | [], [] => cTrue _
       | (n,t)::c', (en,et)::ec' =>
           cand (cIs_true (eqb n en))
             (cand (celab_ctx c' ec')
                (celab_sort ec' t et))                  
       | _, _ => cFalse _
       end.
     
     (* TODO: check that evars from ectx ending up in eqbs isn't a problem
        (should probably end up in eq_sort, but worth checking)
      *)
    Definition celab_rule (r er : rule) : cProp unit :=
      match r, er with
      | sort_rule c args, sort_rule ec eargs =>
          cand (cIs_true (eqb args eargs))
               (celab_ctx c ec)
      | term_rule c args t, term_rule ec eargs et =>
          cand (cIs_true (eqb args eargs))
               (cand (celab_sort ec t et)
                  (celab_ctx c ec))
      | sort_eq_rule c t t', sort_eq_rule ec et et'=>
          cand (celab_sort ec t et)
            (cand (celab_sort ec t' et')
               (celab_ctx c ec))
      | term_eq_rule c e e' t, term_eq_rule ec ee ee' et =>
          cand (celab_sort ec t et)
            (cand (celab_term ec e ee et)
               (cand (celab_term ec e' ee' et)
                  (celab_ctx c ec)))
      | _, _ => cFalse _
      end.

    Section __.
      Context (evars : nat -> term).

      
     Definition gen_elab_ctx : ctx -> stateT nat option ctx :=
       list_Mmap
         (fun '(n,t) =>
            @!let t' <- gen_elab_sort evars t in
              ret (n,t')).
   
    
    Definition gen_elab_rule r : stateT nat option rule :=
      match r with
      | sort_rule c args =>
          @! let ec <- gen_elab_ctx c in
             ret sort_rule ec args
      | term_rule c args t =>
          @! let ec <- gen_elab_ctx c in
             let et <- gen_elab_sort evars t in
             ret term_rule ec args et
      | sort_eq_rule c t t'=>
          @! let ec <- gen_elab_ctx c in
             let et <- gen_elab_sort evars t in
             let et' <- gen_elab_sort evars t' in
             ret sort_eq_rule ec et et'
      | term_eq_rule c e e' t =>
          @! let ec <- gen_elab_ctx c in
             let et <- gen_elab_sort evars t in
             let ee <- gen_elab_term evars e in
             let ee' <- gen_elab_term evars e' in
             ret term_eq_rule ec ee ee' et
      end.

    End __.
    
   End WithLang.

   
     Fixpoint celab_lang (l el : lang) :=
       match l, el with
       | [], [] => cTrue _
       | (n,r)::l', (en,er)::el' =>
           cand (cIs_true (eqb n en))
             (cand (celab_lang l' el')
                (celab_rule el' r er))                  
       | _, _ => cFalse _
       end.
      
     Fixpoint gen_elab_lang evars (l : lang) : stateT nat option lang :=
       match l with
       | [] => Mret []
       | (n,r)::l' =>
           @!let el' <- gen_elab_lang evars l' in
             let r' <- gen_elab_rule el' evars r in
             ret {(stateT nat option)} (n,r')::el'
       end.
                                              
        

   End WithVar.
      
Require Import String List Pyrosome.Lang.SimpleVSubst
  Pyrosome.Lang.SimpleVSTLC.
Import Core.Notations ListNotations.

Goal False.
  epose (gen_elab_lang _ SimpleVSubst.value_subst_def 0) as vs.
  vm_compute in vs.
  let v := eval cbv in vs in
  match v with
  | Some ?vs' => clear vs; pose vs' as vs
  end.
  let l' := eval compute in value_subst in
  assert (interp tt (celab_lang (skipn 19 l') (skipn 19 (fst vs)))).
  {
    cbn [skipn fst vs].
    TODO: issue on first eqn
    vm_compute.
    cbn [celab_lang fst vs celab_rule celab_ctx celab_sort celab_term].
    cbn.
  Compute PolySubst.val_subst.
  epose (gen_elab_ctx value_subst _ [("G", {{s #"env" }})] 0) as c.
  cbn in c.
  epose (gen_elab_sort value_subst _  {{s #"env" }} 0) as t.
  cbn in t.
  TODO: ctx issues?
  TODO: why None?
  epose ((gen_elab_term (stlc++(SimpleVSubst.exp_subst ++ SimpleVSubst.value_subst)%list)
            _ {{e #"lambda" "A" #"hd" }}) 0).
  cbn in o.
  unfold Basics.compose, uncurry in s.
Eval cbn in .
      



Section WithDecidable.

  Context (P : Prop)
    `{Decidable P}.

  Definition cEmbed_dec := cIs_true Decidable_witness.
  
  #[export] Instance cEmbed_dec_corresponds : cCorresponds cEmbed_dec P.
  Proof.
    unfold cEmbed_dec, DecidableClass.Decidable_witness.
    destruct H.
    clear H.
    unfold cCorresponds.
    rewrite <- Decidable_spec.
    destruct Decidable_witness; simpl;
      intuition congruence.
  Qed.

End WithDecidable.


Fixpoint call {A} (R : A -> cProp) l : cProp :=
  match l with
  | []=> cTrue
  | a::l => cand (R a) (call R l)
  end.

Instance call_corresponds {A} cR (R : A -> Prop)
  `{forall a, cCorresponds (cR a) (R a)}
  l
  : cCorresponds (call cR l) (all R l).
Proof.
  induction l; basic_goal_prep; typeclasses eauto.
Qed.




Instance list_eq_corresponds {A} cEq
  `{forall a b, cCorresponds (cEq a b) (a = b)}
  (l1 l2 : list A)
  : cCorresponds (call2 cEq l1 l2) (l1 = l2).
Proof.
  revert l2;
    induction l1; destruct l2; basic_goal_prep.
  1-3:cbv; intuition eauto; safe_invert H0.
  {
    assert (a :: l1 = a0 :: l2 <-> a = a0 /\ l1 = l2).
    {
      intuition eauto; subst; auto; try (safe_invert H0; subst; eauto).
    }
    unfold cCorresponds.
    rewrite H0.
    change (cCorresponds (cand (cEq a a0) (call2 cEq l1 l2)) (a = a0 /\ l1 = l2)).
    typeclasses eauto.
  }
Qed.
  

Goal forall A B C : Type, [A; A; C] = [A; B; C].
Proof.
  intros.
  eapply cProp_intro.
  (*TODO: do I want to try to handle A=A? probably not? but would be good
    alt: could use both this and existing rewrites so that existing rules fire less,
    but that would be a bit disappointing
    related: am I rebuilding something related to itauto?
    -Doesn't seem exactly the same b/c of e.g. call2 for equality
    -can the 2 be separated into 2 phases?
         +If so, what's the analogue to call2 R corresponds?

   Should probably separate out computational equality first, then do props?
   but if I'm always doing both, may as well have 1 step

   on the other hand, computational equality lemmas might make it into stdlib
   - can still use lemmas in proofs here
   *)

(*TODO: move to eqb*)
#[export, refine]
Instance eqb_decidable {A} `{Eqb_ok A} (a b : A) : Decidable (a = b) :=
  {|
    Decidable_witness := eqb a b;
  |}.
Proof.
  pose proof (eqb_prop_iff a b).
  destruct (eqb a b); simpl in *; intuition congruence.
Defined.


