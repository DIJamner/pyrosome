Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core.

(* closed expressions *)
Unset Elimination Schemes.
Inductive cexp : Set := ccon : nat -> seq cexp -> cexp.
Set Elimination Schemes.

(*Stronger induction principle w/ better subterm knowledge 
  TODO: not so necessary anymore I think? remove?
*)
Fixpoint cexp_ind
         (P : cexp -> Prop)
         (IHC : forall n l,
             List.fold_right (fun t : cexp => and (P t)) True l ->
             P (ccon n l))
         (e : cexp) { struct e} : P e :=
  match e with
  | ccon n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [::] => I
        | e' :: l' => conj (cexp_ind IHC e') (loop l')
        end in
    IHC n l (loop l)
  end.

Fixpoint cexp_rect
         (P : cexp -> Type)
         (IHC : forall n l,
             List.fold_right (fun t : cexp => prod (P t)) unit l ->
             P (ccon n l))
         (e : cexp) { struct e} : P e :=
  match e with
  | ccon n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [::] => tt
        | e' :: l' => (cexp_rect IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition cexp_rec := 
[eta cexp_rect]
     : forall P : cexp -> Set,
       (forall n l,
             List.fold_right (fun t : cexp => prod (P t)) unit l ->
             P (ccon n l))-> forall e : cexp, P e.

(*an isomorphism*)
Fixpoint cexp_to_exp' c : exp :=
  match c with
  | ccon n s => con n (map cexp_to_exp' s)
  end.

Lemma ws_cexp c : ws_exp 0 (cexp_to_exp' c).
Proof using .
  elim: c; intros; simpl; auto.
  elim: l H; simpl; auto; intros.
  apply /andP; tauto.
Qed.

Definition cexp_to_exp (e : cexp) : {e : exp | ws_exp 0 e} :=
   exist _ (cexp_to_exp' e) (ws_cexp e).

(* simply returns a dummy value in the variable case *)
Fixpoint exp_to_cexp' (e : exp) : cexp :=
  match e with
  | var x => ccon 0 [::]
  | con n s => ccon n (map exp_to_cexp' s)
  end.

Lemma embed_cexp c : exp_to_cexp' (cexp_to_exp' c) = c.
Proof using .
  elim: c; simpl; auto.
  intros until l; elim: l; simpl; auto.
  intro_to and; case => IH1 /H; case.  
  intros; repeat (f_equal; try tauto).
Qed.

Lemma project_cexp e : ws_exp 0 e -> cexp_to_exp' (exp_to_cexp' e) = e.
Proof using .
  elim: e; simpl; first easy.
  intros until l; elim: l; simpl; auto.
  intro_to and; case => IH1 /H => IH2.
  move /andP => [H1 H2].
  move: (IH2 H2).
  case.
  intros; repeat (f_equal; try tauto).
Qed.

Definition exp_to_cexp (e : {e : exp | ws_exp 0 e}) : cexp :=
  let (e, pf) := e in exp_to_cexp' e.

(* TODO: what's the right thing to do? need intuition from denotations, compilers.

I have two paths/ objects of interest:
-a compiler as a finite map from constructor indices to terms
-a compiler as a function from constr cexp to cexp

The first gives the best reasoning properties:
-a compiler is "well-typed" if each index maps to a wf term under the matching context
-a term is translated by translating its substitution and applying the result 
 to the expression retrieved form the constructor map
-a compiler is rel preserving in the obvious way

However, this precludes any sort of optimization, even local ones.
More of a macro'like approach

The second allows for (at least) local optimization:
-only translates closed terms, i.e. terms w/out metavariables
-not so friendly to linking

Third option: constr exp -> exp
- strictly better than first; first is a special case of this
- allows, at least local, optimizations where possible

 *)

Variant constr (T : Set) : Set :=
| con' : nat -> seq T -> constr T.

Notation "[{ T } n | ]" := (con' T n [::]).
Notation "[{ T } n | e ]" := (con' T n [:: e]).
Notation "[{ T } n | e ; .. ; e' ]" := (con' T n (cons e .. (cons e' [::]) ..)).

(* S (Fix T) -> Fix T *)
Definition Alg := constr exp -> exp.

Fixpoint alg_fn (a : Alg) (e : exp) : exp :=
  match e with
  | var n => var n
  | con n l => a (con' n (map (alg_fn a) l))
  end.    

Definition id_alg : Alg := fun ce =>
  match ce with
  | con' n l => con n l
  end.


(* TODO: uniform inheritance condition? this feels like it would be nice to have
Coercion id_alg : constr exp >-> exp. *)
 
(* one idea: A compiler assumes a way to compile p2 to the target and then compiles p1 to the target

Definition compiler p1 p2 := forall {p'}, Alg p2 p' -> Alg p1 p'.

Issue: loses advantages of option 3
*)

Definition type_preserving (comp : Alg) (S T : lang) : Prop :=
  (forall c s c' n, is_nth_level S n (sort_rule c') ->
                   wf_subst T c s (map (alg_fn comp) c') ->
                   wf_sort T c (comp (con' n s)))
  /\ (forall c s c' t n, is_nth_level S n (term_rule c' t) ->
                   wf_subst T c s (map (alg_fn comp) c') ->
                   wf_term T c (comp (con' n s)) (alg_fn comp t)).

(*

MAJOR CONSIDERATION:
I would like to be able to remove parts of a language
and preserve some results. This is easier for constructors,
but hard for axioms since they can equate old constructors.

idea: augment term syntax to denote where rewrites are used.
observation: in judgments, rewrite use \in instead of is_nth_level.
    If we made that uniform, we could use the n in a constructor.
    Question: still use exp or a new datatype w/ dedicated constructor?
    prob. the latter, like: (rewrite n e); should only need 'input' term
This should make typechecking decideable: just match e to the left side of the rule
and apply the generated subst to the right side.

In the above system, I can remove any unreferenced rewrite rule.

Question: what does it mean to check le_sort/term in this system?

*)

Definition preserving (comp : Alg) (S T : lang) : Prop :=
  /\ (forall c s1 s2 c' t1 t2 , (sort_le c' t1 t2) \in S ->
                   le_subst T c s1 s2 (map (alg_fn comp) c') ->
                   le_sort T c (alg_fn comp t1) (alg_fn comp t2)). (*TODO: what to do w/ substitutions?*)

(* This must hold for the above def to be reasonable *)
Lemma preserving_preserves_sort (comp : Alg) (S T : lang)
  : preserving comp S T ->
    forall c t1 t2, le_sort S c t1 t2 -> le_sort T (map (alg_fn comp) c) (alg_fn comp t1) (alg_fn comp t2).















Definition ccompose {p1 p2 p3} (C : compiler p1 p2) (C' : compiler p2 p3) : compiler p1 p3 :=
  fun _ CR => C _ (C' _ CR).

Section Preserving.

Variable p1 p2 : polynomial.

Variable l1 : lang p1.
Variable l2 : lang p2.
Variable C : compiler p1 p2.


Fixpoint compile (e : exp p1) : exp p2 :=
  match e with
  | var n => var n
  | con n s v => C id_alg (ccon s (Vector.map compile v))
  end.


Definition compile_var : ctx_var p1 -> ctx_var p2 := ctx_var_map compile.

Definition compile_ctx : ctx p1 -> ctx p2 := List.map compile_var.

Definition preserving :=
  (forall c1 c2 t1 t2,
            le_sort l1 c1 c2 t1 t2 ->
            le_sort l2 (compile_ctx c1) (compile_ctx c2) (compile t1) (compile t2))
        /\ (forall c1 c2 s1 s2 c1' c2',
               le_subst l1 c1 c2 s1 s2 c1' c2' ->
               le_subst l2
                        (compile_ctx c1) (compile_ctx c2)
                        (List.map compile s1) (List.map compile s2)
                        (compile_ctx c1') (compile_ctx c2'))
        /\ (forall c1 c2 e1 e2 t1 t2,
               le_term l1 c1 c2 e1 e2 t1 t2 ->
               le_term l2
                       (compile_ctx c1) (compile_ctx c2)
                       (compile e1) (compile e2)
                       (compile t1) (compile t2))
        /\ (forall c1 c2,
               le_ctx l1 c1 c2 ->
               le_ctx l2 (compile_ctx c1) (compile_ctx c2))
        /\ (forall c1 c2 v1 v2,
               le_ctx_var l1 c1 c2 v1 v2 ->
               le_ctx_var l2
                          (compile_ctx c1) (compile_ctx c2)
                          (compile_var v1) (compile_var v2))
        /\ (forall c t, 
            wf_sort l1 c t ->
            wf_sort l2 (compile_ctx c) (compile t))
        /\ (forall c s c',
               wf_subst l1 c s c' ->
               wf_subst l2 (compile_ctx c) (List.map compile s) (compile_ctx c'))
        /\ (forall c e t, 
               wf_term l1 c e t ->
               wf_term l2 (compile_ctx c) (compile e) (compile t))
        /\ (forall c,  wf_ctx l1 c -> wf_ctx l2 (compile_ctx c))
        /\ (forall c v,
               wf_ctx_var l1 c v ->
               wf_ctx_var l2 (compile_ctx c) (compile_var v))
        /\ (forall r,  wf_rule l1 r -> wf_rule l2 (rule_map compile r))
        /\ (wf_lang l1 -> wf_lang l2).
End Preserving.

Lemma compile_id p (t : exp p) : compile (fun x : polynomial => id) t = t.
Proof.
  elim t; simpl; intros; f_equal; eauto.
  elim: v H; simpl; eauto.
  intros; f_equal.
    by case: H0.
    apply: H.
    by case: H0.
Qed.

Lemma compile_var_id p (v : ctx_var p) : compile_var (fun x : polynomial => id) v = v.
Proof.
  case: v; simpl; eauto.
  intro.
    by rewrite !compile_id.
Qed.

Lemma compile_ctx_id p (c : ctx p) : compile_ctx (fun x : polynomial => id) c = c.
Proof.
  elim: c; simpl; intros; f_equal; eauto.
    by rewrite compile_var_id.
Qed.

Lemma compile_subst_id p (s : subst p) : List.map (compile (fun x => id)) s = s.
Proof.
  elim: s; simpl; intros; f_equal; eauto.
    by rewrite compile_id.
Qed.

Lemma compile_rule_id p (r : rule p) : rule_map (compile (fun x => id)) r = r.
Proof.
  elim: r; simpl; intros; f_equal; eauto;
    (try by rewrite ?compile_id ?compile_subst_id ?compile_ctx_id ?compile_var_id);
  move: compile_ctx_id  => cid;
  unfold compile_ctx in cid;
  unfold compile_var in cid;
    by apply: cid.
Qed.
    
Lemma preserve_id p (l : lang p) : preserving l l (fun x C => C).
Proof.
  unfold preserving.
  repeat match goal with
  | |- _ /\ _ => split
  | _ => intros; simpl;
           try by rewrite ?compile_id
                          ?compile_subst_id
                          ?compile_ctx_id
                          ?compile_var_id
                          ?compile_rule_id
  end.
Qed.



(* Non-cpsed versions *)
Definition wf_sort_preserving : Prop :=
  forall c t, wf_sort l1 c t -> wf_sort l2 (compile_ctx c) (compile t).
Definition wf_term_preserving : Prop :=
  forall c e t, wf_term l1 c e t -> wf_term l2 (compile_ctx c) (compile e) (compile t).
Definition wf_ctx_var_preserving : Prop :=
  forall c v, wf_ctx_var l1 c v -> wf_ctx_var l2 (compile_ctx c) (compile_var v).
Definition wf_ctx_preserving : Prop :=
  forall c, wf_ctx l1 c -> wf_ctx l2 (compile_ctx c).
Definition le_sort_preserving : Prop :=
  forall c1 c2 t1 t2,
    le_sort l1 c1 c2 t1 t2 ->
    le_sort l2 (compile_ctx c1) (compile_ctx c1) (compile t1) (compile t2).
Definition le_term_preserving : Prop :=
  forall c1 c2 e1 e2 t1 t2,
    le_term l1 c1 c2 e1 e2 t1 t2 ->
    le_term l2 (compile_ctx c1) (compile_ctx c1) (compile e1) (compile e2) (compile t1) (compile t2).
Definition le_ctx_var_preserving : Prop :=
  forall c1 c2 v1 v2,
    le_ctx_var l1 c1 c2 v1 v2 ->
    le_ctx_var l2 (compile_ctx c1) (compile_ctx c1) (compile_var v1) (compile_var v2).
Definition le_ctx_preserving : Prop :=
  forall c1 c2, le_ctx l1 c1 c2 -> le_ctx l2 (compile_ctx c1) (compile_ctx c1).

(* Add once lemma is proven
TODO: is the reverse also true? (Should be)
Lemma wf_ctx_var_suffices : wf_ctx_var_preserving -> wf_ctx_preserving.
Proof.
  move => wfcv c wfc.
  Fail apply: wf_ctx_var_ctx. (*TODO: need this lemma first *)
  eapply wfcv.
  eassumption.
Qed.

Lemma wf_sort_suffices : wf_sort_preserving -> wf_ctx_var_preserving.
Proof.
  move => wfs c wfc.
  ???
Qed.
 *)




  
(*
  
Definition Type_Preserving {p1 p2} (l1 : lang p1) (l2 : lang p2) (C : Compiler p1 p2) : Prop :=
  forall {p3} (l3 : lang p3) (C' : Compiler p2 p3),
  forall c e t,
    wf_term 


            Preserving : (L1 L2 : Lang I) → Compiler (desc L1) (desc L2) → Set₁
  Preserving L1 L2 C = ∀ L3 → (C' : Compiler (desc L2) (desc L3))
                         → (L2.prec ⟨ Compiler.compile C' ⟩⇒ᴿ prec L3)
                         → L1.prec ⟨ Compiler.compile C' ∘ Compiler.compile C ⟩⇒ᴿ prec L3
    where
      module L1 = Lang L1
      module L2 = Lang L2
*)
