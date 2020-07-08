
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils.

(* These terms are complex, so we will need to write our own schemes *)
Unset Elimination Schemes.
Set Boolean Equality Schemes.
(* we build in substitutions to all necessary proof constructors
   to make substitution admissible, just like for terms
 *)
Inductive term_le : Set :=
(* proof by axiom with subst built in; we prove relatedness of substitutions by pointwise proofs *)
| tle_by : nat -> seq term_le -> term_le
(* proof by reflexivity with subst built in.
   Since the subst is built in, it suffices to 
   just give the level of a term constructor.
   To build reflexivity for complex terms,
   use the right substitution.
   This is the key to decidable typechecking. *)
| tle_refl_con : nat -> seq term_le -> term_le
| tle_refl_var : nat -> term_le
(* Substitutions should be able to be pushed under these last two constructors *)
| tle_trans : term_le -> term_le -> term_le
(* applies a sort relation to the type of a term relation *)
| tle_conv : sort_le -> term_le -> term_le
with sort_le : Set :=
(* proof by axiom like term_le *)
| sle_by : nat -> seq term_le -> sort_le
(* proof by reflexivity like term_le *)
| sle_refl : nat -> seq term_le -> sort_le
(* like term_le *)
| sle_trans : sort_le -> sort_le -> sort_le.

Inductive term : Set :=
(* variable deBruijn level *)
| var : nat -> term
(* Rule deBruijn level, list of subterms*)
| con : nat -> seq term -> term
(* sort rewrite *)
| conv : sort_le -> term -> term.
Variant sort : Set :=
(* Rule deBruijn level, list of subterms*)
| srt : nat -> seq term -> sort.
Unset Boolean Equality Schemes.
Set Elimination Schemes.

Notation subst_le := (seq term_le).
Notation subst := (seq term).
Notation ctx := (seq sort).


Fixpoint term_le_ind
         (* mutual propositions to prove *)
         (Ptle : term_le -> Prop)
         (Psle : sort_le -> Prop)

         (* assumptions *)
         (IH_tle_by : forall n ps, List.Forall Ptle ps -> Ptle (tle_by n ps))
         (IH_tle_refl_con : forall n ps, List.Forall Ptle ps -> Ptle (tle_refl_con n ps))
         (IH_tle_refl_var : forall n, Ptle (tle_refl_var n))
         (IH_tle_trans : forall p1 p2, Ptle p1 -> Ptle p2 -> Ptle (tle_trans p1 p2))
         (IH_tle_conv : forall sp p, Psle sp -> Ptle p -> Ptle (tle_conv sp p))
         
         (IH_sle_by : forall n ps, List.Forall Ptle ps -> Psle (sle_by n ps))
         (IH_sle_refl : forall n ps, List.Forall Ptle ps -> Psle (sle_refl n ps))
         (IH_sle_trans : forall p1 p2, Psle p1 -> Psle p2 -> Psle (sle_trans p1 p2))

         p : Ptle p :=
  let tl_ind := term_le_ind IH_tle_by IH_tle_refl_con IH_tle_refl_var IH_tle_trans IH_tle_conv
                            IH_sle_by IH_sle_refl IH_sle_trans in
  let sl_ind := sort_le_ind IH_tle_by IH_tle_refl_con IH_tle_refl_var IH_tle_trans IH_tle_conv
                            IH_sle_by IH_sle_refl IH_sle_trans in
  let fix subst_le_ind s : List.Forall Ptle s :=
      match s with
      | [::] => List.Forall_nil _
      | e::s' => List.Forall_cons _ (tl_ind e) (subst_le_ind s')
      end in
  match p with
  | tle_by n ps => IH_tle_by n ps (subst_le_ind ps)
  | tle_refl_con n ps => IH_tle_refl_con n ps (subst_le_ind ps)
  | tle_refl_var n => IH_tle_refl_var n
  | tle_trans p1 p2 => IH_tle_trans p1 p2 (tl_ind p1) (tl_ind p2)
  | tle_conv sp p => IH_tle_conv sp p (sl_ind sp) (tl_ind p)
  end
with sort_le_ind
       (* mutual propositions to prove *)
       (Ptle : term_le -> Prop)
       (Psle : sort_le -> Prop)

       (* assumptions *)
       (IH_tle_by : forall n ps, List.Forall Ptle ps -> Ptle (tle_by n ps))
       (IH_tle_refl_con : forall n ps, List.Forall Ptle ps -> Ptle (tle_refl_con n ps))
       (IH_tle_refl_var : forall n, Ptle (tle_refl_var n))
       (IH_tle_trans : forall p1 p2, Ptle p1 -> Ptle p2 -> Ptle (tle_trans p1 p2))
       (IH_tle_conv : forall sp p, Psle sp -> Ptle p -> Ptle (tle_conv sp p))
       
       (IH_sle_by : forall n ps, List.Forall Ptle ps -> Psle (sle_by n ps))
       (IH_sle_refl : forall n ps, List.Forall Ptle ps -> Psle (sle_refl n ps))
       (IH_sle_trans : forall p1 p2, Psle p1 -> Psle p2 -> Psle (sle_trans p1 p2))

       sp : Psle sp :=
       let tl_ind := term_le_ind IH_tle_by IH_tle_refl_con IH_tle_refl_var IH_tle_trans IH_tle_conv
                                 IH_sle_by IH_sle_refl IH_sle_trans in
       let sl_ind := sort_le_ind IH_tle_by IH_tle_refl_con IH_tle_refl_var IH_tle_trans IH_tle_conv
                                 IH_sle_by IH_sle_refl IH_sle_trans in
       let fix subst_le_ind s : List.Forall Ptle s :=
           match s with
           | [::] => List.Forall_nil _
           | e::s' => List.Forall_cons _ (tl_ind e) (subst_le_ind s')
           end in
       match sp with
       | sle_by n ps => IH_sle_by n ps (subst_le_ind ps)
       | sle_refl n ps => IH_sle_refl n ps (subst_le_ind ps)
       | sle_trans p1 p2 => IH_sle_trans p1 p2 (sl_ind p1) (sl_ind p2)
       end.

Combined Scheme le_ind from term_le_ind, sort_le_ind.

Fixpoint term_ind (P : term -> Prop)
  (* assumptions *)
  (IH_var : forall x, P (var x))
  (IH_con : forall n s, List.Forall P s -> P (con n s))
  (IH_conv : forall sp e, P e -> P (conv sp e))
   e : P e :=
    let fix subst_ind s : List.Forall P s :=
    match s with
    | [::] => List.Forall_nil _
    | e::s' => List.Forall_cons _ (term_ind IH_var IH_con IH_conv e) (subst_ind s')
    end in
    match e with
    | var x => IH_var x
    | con n s => IH_con n s (subst_ind s)
    | conv sp e => IH_conv sp e (term_ind IH_var IH_con IH_conv e)
    end.


(* TODO: Prove*)
Axiom term_le_eq_dec : forall p1 p2, reflect (p1 = p2) (term_le_beq p1 p2).
Axiom sort_le_eq_dec : forall p1 p2, reflect (p1 = p2) (sort_le_beq p1 p2).
Axiom term_eq_dec : forall e1 e2, reflect (e1 = e2) (term_beq e1 e2).
Axiom sort_eq_dec : forall p1 p2, reflect (p1 = p2) (sort_beq p1 p2).

Canonical term_le_eqType := @Equality.Pack term_le (Equality.Mixin term_le_eq_dec).
Canonical sort_le_eqType := @Equality.Pack sort_le (Equality.Mixin sort_le_eq_dec).
Canonical term_eqType := @Equality.Pack term (Equality.Mixin term_eq_dec).
Canonical sort_eqType := @Equality.Pack sort (Equality.Mixin sort_eq_dec).

Fixpoint term_to_refl (e : term) : term_le :=
  match e with
  | var x => tle_refl_var x
  | con n s => tle_refl_con n (map term_to_refl s)
  | conv sp e => tle_conv sp (term_to_refl e)
  end.

Definition subst_to_refl := map term_to_refl.

Definition sort_to_refl (t : sort) : sort_le :=
  match t with srt n s => sle_refl n (subst_to_refl s) end.

Definition var_lookup (s : subst) (n : nat) : term :=
  nth_level (con 0 [::]) s n.
Global Transparent var_lookup.

Definition var_lookup_type (c : ctx) (n : nat) : sort :=
  nth_level (srt 0 [::]) c n.
Global Transparent var_lookup_type.

Definition var_lookup_le (s : subst_le) (n : nat) : term_le :=
  nth_level (tle_refl_con 0 [::]) s n.
Global Transparent var_lookup_le.

(* TODO: the right way (?): subst subst_Les into term_les
   and subts into terms? just need to change this to take a subst_le *)
Fixpoint term_le_subst s p : term_le :=
  match p with
  | tle_by n ps => tle_by n (map (term_le_subst s) ps)
  | tle_refl_var x => var_lookup_le s x
  | tle_refl_con n ps => tle_refl_con n (map (term_le_subst s) ps)
  | tle_conv sp p' => tle_conv (sort_le_subst s sp) (term_le_subst s p')
  | tle_trans p1 p2 => tle_trans (term_le_subst s p1) (term_le_subst s p2)
  end
with sort_le_subst s sp : sort_le :=
  match sp with
  | sle_by n ps => sle_by n (map (term_le_subst s) ps)
  | sle_refl n ps => sle_refl n (map (term_le_subst s) ps)
  | sle_trans sp1 sp2 => sle_trans (sort_le_subst s sp1) (sort_le_subst s sp2)
  end.

Definition subst_le_subst s s' : subst_le :=
  map (term_le_subst s) s'.

Fixpoint term_subst s e : term :=
  match e with
  | var n => var_lookup s n
  | con n l => con n (map (term_subst s) l)
  | conv pf e' => conv (sort_le_subst (subst_to_refl s) pf) (term_subst s e')
  end.

Definition subst_subst s s' : subst :=
  map (term_subst s) s'.

Definition sort_subst s (t : sort) : sort :=
  let (n, s') := t in
  srt n (subst_subst s s').

Lemma subst_le_cmp_size s1 s2 : size (subst_le_subst s2 s1) = size s1.
Proof using .
  elim: s1; simpl; eauto.
Qed.

Lemma subst_cmp_size s1 s2 : size (subst_subst s2 s1) = size s1.
Proof using .
  elim: s1; simpl; eauto.
Qed.

Lemma var_lookup_le_cmp n s1 s2  : term_le_subst s2 (var_lookup_le s1 n) = var_lookup_le (subst_le_subst s2 s1) n.
Proof using .
  unfold var_lookup_le.
  unfold nth_level.
  rewrite subst_le_cmp_size.
  case (n < size s1); simpl; eauto.
  generalize (size s1 - n.+1) => n'.
  elim: n' s1; intros until s1; case: s1; simpl; eauto.
Qed.

Lemma var_lookup_cmp n s1 s2  : term_subst s2 (var_lookup s1 n) = var_lookup (subst_subst s2 s1) n.
Proof using .
  unfold var_lookup.
  unfold nth_level.
  rewrite subst_cmp_size.
  case (n < size s1); simpl; eauto.
  generalize (size s1 - n.+1) => n'.
  elim: n' s1; intros until s1; case: s1; simpl; eauto.
Qed.
  
Lemma le_successive_subst_cmp
  : (forall (e : term_le) s1 s2, term_le_subst s2 (term_le_subst s1 e) = term_le_subst (subst_le_subst s2 s1) e)
    /\ ((forall (e : sort_le) s1 s2, sort_le_subst s2 (sort_le_subst s1 e) = sort_le_subst (subst_le_subst s2 s1) e)).
Proof using .
  eapply le_ind; simpl; intros; f_equal; auto;
    try by apply: var_lookup_le_cmp.
  all: elim: ps H; simpl; eauto; intro_to List.Forall; inversion; subst; f_equal; eauto.
Qed.

Lemma subst_to_refl_size s : size (subst_to_refl s) = size s.
Proof using .
  elim: s; simpl; eauto.
Qed.

Lemma lookup_to_refl s x : var_lookup_le (subst_to_refl s) x = term_to_refl (var_lookup s x).
Proof using.
  unfold var_lookup_le.
  unfold var_lookup.
  unfold nth_level.
  rewrite subst_to_refl_size.
  case (x < size s); simpl; eauto.
  generalize (size s - x.+1) => x'.
  elim: x' s; intros until s; case: s; simpl; auto.  
Qed.

Lemma term_to_refl_distributes s e : term_le_subst (subst_to_refl s) (term_to_refl e) = term_to_refl (term_subst s e).
Proof using .
  elim: e; simpl; auto; intros; (try by apply: lookup_to_refl); f_equal; auto.
  elim: s0 H; simpl; auto; intro_to List.Forall; inversion; subst; f_equal; auto.
Qed.  

Lemma subst_to_refl_distributes s1 s2
  : subst_le_subst (subst_to_refl s2) (subst_to_refl s1) = subst_to_refl (subst_subst s2 s1).
Proof using .
  elim: s1 s2; simpl; eauto; intros; f_equal; eauto using term_to_refl_distributes.
Qed.

Lemma le_successive_subst_cmp_refl
  : (forall (e : term_le) s1 s2,
        term_le_subst (subst_to_refl s2) (term_le_subst (subst_to_refl s1) e)
        = term_le_subst (subst_to_refl (subst_subst s2 s1)) e)
    /\ (forall (e : sort_le) s1 s2,
        sort_le_subst (subst_to_refl s2) (sort_le_subst (subst_to_refl s1) e)
        = sort_le_subst (subst_to_refl (subst_subst s2 s1)) e).
Proof using .
  split; intros; rewrite -!subst_to_refl_distributes; eapply le_successive_subst_cmp.
Qed.

Lemma subst_le_assoc s1 s2 s3
  : subst_le_subst (subst_le_subst s3 s2) s1 = subst_le_subst s3 (subst_le_subst s2 s1).
Proof using .
  elim: s1; simpl; intros; f_equal; auto.
  by rewrite (proj1 le_successive_subst_cmp).
Qed.

Lemma term_successive_subst_cmp
  : forall (e : term) s1 s2, term_subst s2 (term_subst s1 e) = term_subst (subst_subst s2 s1) e.
Proof using .
  elim; simpl; intros; f_equal; auto using var_lookup_cmp.
  - elim: s H; simpl; intro_to List.Forall; inversion; subst; f_equal; auto.
  - by rewrite (proj2 le_successive_subst_cmp_refl).
Qed.

Lemma subst_assoc s1 s2 s3
  : subst_subst (subst_subst s3 s2) s1 = subst_subst s3 (subst_subst s2 s1).
Proof using .
  elim: s1; simpl; intros; f_equal; auto.
  by rewrite term_successive_subst_cmp.
Qed.

Lemma sort_successive_subst_cmp
  : forall (e : sort) s1 s2, sort_subst s2 (sort_subst s1 e) = sort_subst (subst_subst s2 s1) e.
Proof using .
  case; simpl; intros; f_equal; auto.
  by rewrite subst_assoc.
Qed.

Class Substable (sub : Set) (stx : Set) : Set :=
  { apply_subst : sub -> stx -> stx
    ; subst_cmp : sub -> sub -> sub
    ; successive_subst_cmp : forall e s1 s2, apply_subst s2 (apply_subst s1 e) = apply_subst (subst_cmp s2 s1) e
    ; subst_cmp_assoc : forall s1 s2 s3, subst_cmp (subst_cmp s3 s2) s1 = subst_cmp s3 (subst_cmp s2 s1)
  }.
Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).

Instance term_le_Substable : Substable subst_le term_le :=
  { apply_subst := term_le_subst
    ; subst_cmp := subst_le_subst
    ; successive_subst_cmp := proj1 le_successive_subst_cmp
    ; subst_cmp_assoc := subst_le_assoc
  }.
  
Instance term_le_Substable_refl : Substable subst term_le :=
  { apply_subst s := term_le_subst (subst_to_refl s)
    ; subst_cmp := subst_subst
    ; successive_subst_cmp := proj1 le_successive_subst_cmp_refl
    ; subst_cmp_assoc := subst_assoc }.


Instance sort_le_Substable : Substable subst_le sort_le :=
  { apply_subst := sort_le_subst
    ; subst_cmp := subst_le_subst
    ; successive_subst_cmp := proj2 le_successive_subst_cmp
    ; subst_cmp_assoc := subst_le_assoc }.

Instance sort_le_Substable_refl : Substable subst sort_le :=
  { apply_subst s := sort_le_subst (subst_to_refl s) 
    ; subst_cmp := subst_subst
    ; successive_subst_cmp := proj2 le_successive_subst_cmp_refl
    ; subst_cmp_assoc := subst_assoc }.

#[refine] Instance subst_le_Substable : Substable subst_le subst_le :=
  { apply_subst := subst_le_subst
    ; subst_cmp := subst_le_subst
    ; subst_cmp_assoc := subst_le_assoc }.
Proof.
  intros; by rewrite subst_le_assoc.
Defined.

#[refine] Instance subst_le_Substable_refl : Substable subst subst_le :=
  { apply_subst s := subst_le_subst (subst_to_refl s) 
    ; subst_cmp := subst_subst 
    ; subst_cmp_assoc := subst_assoc }.
Proof.
  pose tssp := proj1 le_successive_subst_cmp_refl.
  elim; simpl; intros; f_equal; eauto.
Defined.
  
Instance term_Substable : Substable subst term :=
  { apply_subst := term_subst 
    ; subst_cmp := subst_subst
    ; successive_subst_cmp := term_successive_subst_cmp
    ; subst_cmp_assoc := subst_assoc }.
  
Instance sort_Substable : Substable subst sort :=
  { apply_subst := sort_subst 
    ; subst_cmp := subst_subst
    ; successive_subst_cmp := sort_successive_subst_cmp
    ; subst_cmp_assoc := subst_assoc }.

#[refine] Instance subst_Substable : Substable subst subst :=
  { apply_subst := subst_subst 
    ; subst_cmp := subst_subst
    ; subst_cmp_assoc := subst_assoc }.
Proof.
  intros; by rewrite subst_assoc.
Defined.



Definition exp_shift (m : nat) e : exp :=
  exp_var_map (fun n => var (m + n)) e.

Notation "e ^! n" := (exp_shift n e) (at level 7, left associativity).
Notation "s ^!! n" := (map (exp_shift n) s) (at level 7, left associativity).

Fixpoint shift_subst (sz start : nat) : subst :=
  match sz with
  | 0 => [::]
  | sz'.+1 => (var start)::(shift_subst sz' (start.+1))
  end.

(*TODO: this is in the library. Why can't I find it? *)
Lemma sub_0_r : forall n, n - 0 = n.
Proof using .
  elim; done.
Qed.  

Lemma lookup_ge : forall c n, ~n < size c -> var_lookup c n = var n.
Proof using .
  intros; unfold var_lookup; unfold nth_level.
  case nlt: (n < size c) => //=.
Qed.

(*TODO*)
(* Well-scoped languages
   a presupposition of well-formed languages
   Written as functions that decide the properties
   determines that variables (but not constructor symbols) are well-scoped
 *)

Fixpoint ws_exp csz (e : exp) : bool :=
  match e with
  | var n => n < csz
  | con _ v => List.fold_right (fun e f => (ws_exp csz e) && f) true v
  | conv _ e => ws_exp csz e
  end.

Fixpoint ws_ctx (c : ctx) : bool :=
  match c with
  | [::] => true
  | t :: c' => ws_ctx c' && ws_exp (size c') t
  end.


(* replaces m variables with terms with n free vars*)
Definition ws_subst n : subst -> bool :=
  List.fold_right (fun e b => ws_exp n e && b) true.


Lemma unandb : forall (a b : bool) (C : Prop), (a -> b -> C) <-> (a && b -> C).
Proof using .
  move => a b C; split.
  - move => CF ab.
    apply andb_prop in ab.
    case: ab.
    done.
  - move => CF aa bb.
    apply CF.
    rewrite andb_true_intro //=.
Qed.

Lemma ws_nth : forall n (s : subst) e n',
    ws_subst n s -> ws_exp n e -> ws_exp n (nth e s n').
Proof using .
  move => n ; elim.
  - move => e; elim; [done|].
    move => n' IH //=.
  - move => x l IH e.
    elim => [| n' _].
    + rewrite /ws_subst //=.
      repeat case /andb_prop.
      done.
    + rewrite /ws_subst //=.
      repeat case /andb_prop.
      move => _ lf wse.
      apply: IH.
      rewrite /ws_subst //=. 
      done.
Qed.

Lemma ws_empty : forall n, ws_subst n [::].
Proof using .
  move => n.
  rewrite /ws_subst //=.
Qed.

Lemma sub_n_n n : n - n = 0.
Proof using .
  elim: n => //=.
Qed.

Lemma ltn_lte a b : a < b -> a <= b.
Proof using .
  elim: b a; simpl; auto.
Qed.  

Lemma sub_flip a b c : a < b -> c = b - a.+1 -> a = b -c.+1.
Proof using .
  move => alt ->.
  clear c.
  rewrite subnSK //.
  rewrite subKn //.
  auto using ltn_lte.
Qed.


Lemma level_ind sz m (R: nat -> nat -> Prop)
  : (forall n, n < sz -> R n (sz - n.+1)) -> m < sz -> R (sz - m.+1) m.
Proof using .
  intros.
  remember (sz - m.+1) as n.
  move: (sub_flip H0 Heqn) ->.
  apply: H.
  rewrite Heqn; clear Heqn.
  case: sz H0 => //= sz.
  rewrite !subSS.
  intros.
  apply: sub_ord_proof.
Qed.


(* TODO: use above principle *)
Lemma ws_lookup : forall n (s : subst) (n' : nat),
    ws_subst n s -> n' < size s -> ws_exp n (var_lookup s n').
Proof using .  
  move => n.
  unfold var_lookup;
    unfold nth_level.
  intros.
  pose p := H0; move: p; case: (n'< size s) => //= _.
  remember (size s - n'.+1) as y.
  suff: n' = size s - y.+1.
  move => n'eq.
  suff: y < size s.
  {
    move: n'eq => -> ylt.
    clear Heqy H0 n'.
    elim: y s ylt H;
      intros until s;
      case: s => //= e s nlt /andP [wse wss] //=.
    rewrite subSS.
    suff: n0 < size s; auto.
  }
  move: H0 Heqy n'eq.
  generalize (size s) as z.
  case => //= n0.
  rewrite !subSS.
  intros.
  rewrite Heqy.
  apply: sub_ord_proof.
  auto using sub_flip.
Qed.


Theorem subst_preserves_ws
  : forall e (s : subst) (csz : nat),
    ws_exp (size s) e ->
    ws_subst csz s ->
    ws_exp csz (exp_subst s e).
Proof using .
  move => e s c wse.
  move => wss.
  pose (wss' := wss).
  move: wss'.
  rewrite /ws_subst.
  move => elem_ws.
  elim: e wse => //= => n.
  - apply: ws_lookup => //=;
    move: size_eq => /eqP -> //=.
  - elim => //= x l' IHA IHB.
    case /andP => xexp rexp.
    inversion IHB.
    apply /andP. split; [auto|].
    move: IHA -> => //=.
Qed.


Lemma map_ext {B C : Type} (f g : B -> C) (l : seq B)
  : (forall e, f e = g e) -> map f l = map g l.
Proof.
  move => ext.
  elim: l; try done.
  move => e1 l' IH.
  simpl.
    by rewrite ext IH.
Qed.

Lemma map_ext' {B C : Type} (f g : B -> C) (v : seq B)
  : forall (P : B -> bool),
    (forall e, P e -> f e = g e) ->
    List.fold_right (fun e => [eta andb (P e)]) true v ->
    map f v = map g v.
Proof.
  move => P ext.
  elim: v;[> done|].
  move => e1 v' IH vfr.
  simpl.
  f_equal.
  - rewrite ext => //.
    move: vfr.
    simpl.
    by case /andP.
  - apply: IH.
    move: vfr; simpl; by case /andP.
Qed.

Lemma exp_var_map_map g fn (e : exp)
  : exp_var_map g (exp_var_map (fun n => var (fn n)) e) = exp_var_map (fun n => g (fn n)) e.
Proof using .
  elim: e => //.
  - simpl. intros.
    f_equal.
    rewrite map_comp.
    fold exp_var_map.
    elim: l H => //.
    simpl.
    move => h t vfr.
    inversion; subst.
    intros.
    f_equal => //.
    by apply: vfr.
  - simpl.
    move => pf e -> //.
Qed.

Lemma exp_var_map_ext f1 f2 (e : exp)
  : (forall n, f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof.
  move => ext.
  elim: e; eauto.
  move => s l H.
  unfold exp_var_map.
  fold exp_var_map.
  f_equal.
  elim: l H => //.
  simpl.
  intros.
  inversion H0; subst.
  f_equal; auto.
  simpl.
  move => pf e -> //.
Qed.

Lemma exp_var_map_ext' f1 f2 (e : exp) m
  : ws_exp m e -> (forall n, n < m -> f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof using .
  move => wse ext.
  elim: e wse ; eauto.
  move => n l H wsv.
  unfold exp_var_map.
  fold exp_var_map.
  f_equal.
  simpl in wsv.
  elim: l H wsv => //.
  simpl.
  intros.
  inversion H0; subst.
  move: wsv.
  case /andP.
  move /H3 ->.
  move /H.
  intros.
  f_equal.
  auto.
  
  simpl.
  intros; f_equal.
  apply: H; done.
Qed.

(*
Lemma shift1_decomp (e : exp) n : e^!(n.+1) = e^!n^!1.
Proof.
  elim: e n.
  - simpl; auto.
  - intros.
    unfold exp_shift.
    simpl.
    f_equal.
    rewrite -map_comp.
    eapply map_ext.
    intro e.
    simpl.
    rewrite exp_var_map_map.
    f_equal.
  - intros; simpl; f_equal; eauto.
Qed.
  
Theorem shift_preserves_ws (e : exp) (n m : nat)
  : ws_exp n e -> ws_exp (m + n) e^!m. 
Proof.
  elim: m e n.
  - intros; rewrite shiftz.
      by change (0 + n) with n.
  - intros.
    rewrite addSn.
    rewrite shift1_decomp.
    apply: shift1_preserves_ws.
    auto.
Qed.*)

(* TODO: needed?
Lemma lookup_in_shift_subst n' n m
  : n' < n -> var_lookup (shift_subst n m) n' = var (n' + m).
Proof.
  Print shift_subst.
  elim: n' n m.
  - case => //.
  - move => n IH.
    case => //.
    simpl.
    intros.
    change (n.+1 + m) with (n + m).+1.
    rewrite addnC.
    change (m + n).+1 with (m.+1 + n).
    rewrite addnC.
    eauto.
Qed. 

Theorem shift_subst_shift (e : exp) : forall n m, ws_exp n e ->  e [/shift_subst n m/] = e^!m.
Proof.
  elim: e.
  - unfold exp_shift.
    unfold exp_subst.
    unfold exp_var_map.
    intros; rewrite addnC;
    eapply lookup_in_shift_subst.
    auto.
  - intros.
    unfold exp_shift.
    unfold exp_subst.
    unfold exp_var_map.
    f_equal.
    pose H0' := H0.
    simpl in H0'.
    fold exp_var_map.
    apply: map_ext'.
    move => e ppf.
    apply: exp_var_map_ext'.
    exact ppf.
    move => n1 n1lt.
    rewrite addnC.
    eapply lookup_in_shift_subst.
    exact n1lt.
    done.
Qed.*)

(* TODO: is this true? if so, prove
Lemma id_subst {p} (e : exp p) : forall n m, e [/shift_subst n 0/] = e [/shift_subst m 0/].
*)

(*
Lemma extract_var_shift n : var n = (var 0)^!n.
Proof.
  elim: n; simpl; auto.
  intros.
  rewrite shift1_decomp.
  rewrite -H.
  auto.
Qed.
*)


(* TODO: is this needed? if so, prove
Lemma constr_shift_subst_comm e s n : e[/s/]%!n = e%!n[/s::%!n/].
Proof.
  elim: e s n.
  - elim ;intro_to subst; case => //.
  - intros; simpl;
      unfold exp_subst;
      unfold exp_var_map;
      fold exp_var_map;
      fold exp_subst.
    f_equal.
    fold exp_subst.
    elim: l H => //.
    simpl; intro_to and.
    case; intros.
    f_equal; eauto.
Qed.
*)

Fixpoint eq_lepf pf1 pf2 {struct pf1} : bool :=
  match pf1, pf2 with
  | lepf_by n1, lepf_by n2 => n1 == n2
  | lepf_subst pf1 pfs1, lepf_subst pf2 pfs2 =>
    (eq_lepf pf1 pf2) && (all2 eq_lepf pfs1 pfs2) 
  | lepf_refl, lepf_refl => true
  | lepf_trans pf11 pf12, lepf_trans pf21 pf22 =>
    (eq_lepf pf11 pf21) && (eq_lepf pf12 pf22)
  | lepf_conv pf11 pf12, lepf_conv pf21 pf22 =>
    (eq_lepf pf11 pf21) && (eq_lepf pf12 pf22)
  | _, _ => false
  end.

Ltac remember_and_case exp :=
  let H := fresh in
  let Heq := fresh in
  remember exp as H eqn:Heq; symmetry in Heq;
  case: H Heq.
  

Lemma eq_lepfP : forall pf1 pf2, reflect (pf1 = pf2) (eq_lepf pf1 pf2).
Proof.
  elim; intros until pf2; case: pf2; simpl.
  intros.
  all: try (intros; match goal with
             | |- context[reflect _ false] => constructor; easy
             | |- context[reflect _ true] => constructor; easy
             | |- context[?a == ?b] => remember_and_case (a== b); constructor
                    end).
  by move: H0 => /eqP ->.
  case.
  move /eqP.
  rewrite H0; done.
  give_up(*TODO: need improved IH*).
  intros; remember_and_case (eq_lepf l l1); simpl.
Admitted.


Definition lepf_eqMixin := Equality.Mixin eq_lepfP.

Canonical lepf_eqType := @Equality.Pack lepf lepf_eqMixin.
  
Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => x == y
  | con n1 l1, con n2 l2 =>
    (n1 == n2) && (all2 eq_exp l1 l2)
  | conv pf1 e1', conv pf2 e2' =>
    (pf1 == pf2) && (eq_exp e1' e2')
  | _,_ => false
  end.

(*
Lemma exp2_ind (P : exp -> exp -> Set)
  : (forall n m, P (var n) (var m)) ->
    (forall n c l, P (var n) (con c l)) ->
    (forall n c l, P (con c l) (var n)) ->
    (forall c1 c2, P (con c1 [::]) (con c2 [::])) ->
    (forall c1 c2 a l, P (con c1 [::]) (con c2 (a::l))) ->
    (forall c1 c2 a l, P (con c1 (a::l)) (con c2 [::])) ->
    (forall c1 c2 a1 a2 l1 l2,
        P a1 a2 ->
        P (con c1 l1) (con c2 l2) ->
        P (con c1 (a1::l1)) (con c2 (a2::l2))) ->
    forall e1 e2, P e1 e2.
Proof using .
  intro_to exp.
  elim.
  - intro_to exp; case; auto.
  - intro_to exp.
    case; auto.
    move => n0.
    elim: l X.
    + move => _; case; auto.
    + move => a l IH.
      simpl; case => pa fld.
      case; auto.
Qed.      *)

(*TODO: case neq does not use the right name*)
Tactic Notation "case_on_eqb" ident(a) ident(b) :=
  let neq := fresh "neq" in
  case neq: (a == b); constructor;
  [f_equal; apply /eqP
  | case => /eqP; rewrite neq].
  
(*
Lemma eq_exp_refl : forall e, eq_exp e e.
Proof.
  elim; simpl; auto.
  move => n.
  suff: n == n.
  move ->; simpl.
  elim; simpl; auto.
  intro_to and.
  case => eqaa fld.
  apply /andP.
  split; auto.
  elim: n; simpl; auto.
Qed.

Lemma all2_eq_exp_refl : forall l, all2 eq_exp l l.
  pose eqer := eq_exp_refl.
  elim; simpl; auto.
  intros; apply /andP; split; auto.
Qed.
*)
Lemma eq_expP : forall e1 e2, reflect (e1 = e2) (eq_exp e1 e2).
Proof.
(*  elim.
  - intro_to exp; case; simpl.
    + move => n0.
        by case_on_eqb n n0.
    + constructor; by case.
  - intro_to exp; case; simpl.
    + constructor; by case.
    + intros.
      case neq: (n == n0); simpl.
      * case alleq: (all2 eq_exp l l0).
        --constructor.
          f_equal.
            by apply /eqP; rewrite neq.
            elim: l X l0 alleq.
          ++ simpl; move => _; case; by auto.
          ++ simpl; move => a l IH.
             case => refla fld.
             case; try by auto.
             move => a0 l0.
             case /andP.
             move /refla => -> all2l.
             f_equal.
             eauto.
        -- constructor.
           case => _.
           elim: l X l0 alleq.
           ++ simpl; move => _; case; by auto.
          ++ simpl; move => a l IH.
             case => refla fld.
             case; try by auto.
             move => a0 l0.
             move /andP => oneof.
             case => aeq leq.
             apply oneof.
             split.
             rewrite aeq.
             apply: eq_exp_refl.
             rewrite leq.
             apply: all2_eq_exp_refl.
      * constructor.
        case; move /eqP; by rewrite neq.
Qed.*)
Admitted.

Definition exp_eqMixin := Equality.Mixin eq_expP.

Canonical proof_exp_eqType := @Equality.Pack exp exp_eqMixin.



Require Import String.
Section Printing.

  (* A lazily-written print nat fn *)
  Fixpoint printnat' fuel n : string :=
    match fuel with
    | 0 => "ERR"
    | fuel'.+1 =>
      match n with
      | 0 => "0"
      | 1 => "1"
      | 2 => "2"
      | 3 => "3"
      | 4 => "4"
      | 5 => "5"
      | 6 => "6"
      | 7 => "7"
      | 8 => "8"
      | 9 => "9"
      | _ => (printnat' fuel' (Nat.div n 10)) ++ (printnat' fuel' (Nat.modulo n 10))
      end
    end.

  Definition printnat x : string := printnat' (x.+1) x.

  Goal printnat 0 = "0"%string.
      by compute.
  Qed.
  
  Goal printnat 1 = "1"%string.
      by compute.
  Qed.
  
  Goal printnat 5 = "5"%string.
      by compute.
  Qed.
  
  Goal printnat 78 = "78"%string.
      by compute.
  Qed.
  
  Goal printnat 100 = "100"%string.
      by compute.
  Qed.
  
  Fixpoint print e : string :=
    match e with
    | var n => printnat n
    | con n s => "[" ++ printnat n ++ "|" ++ concat ";" (map print s) ++ "]"
    | conv pf e => "TODO: pfs; " ++ print e
    end.

  Goal print [1| (var 2); (var 2)] = "[1|2;2]"%string.
      by compute.
  Qed.

End Printing.

(* TODO: everything below
Lemma
  exp_subst_ind' (P : exp -> Prop) (Q : subst -> Prop)
  : (forall n,  P (var n)) ->
    (forall n s,  Q s -> P (con n s)) ->
    Q [::] ->
    (forall e s, P e -> Q s -> Q (e :: s)) ->
    forall e, P e.
Proof using .
  intros.
    elim: e; auto.
    move=> n.
    elim.
    auto.
    intros.
    simpl in H4.
    destruct H4.
    apply H0.
    apply H2; auto.
    clear H3.
    elim: l H5; auto.
    intros.
    destruct H5.
    apply H2; auto.
Qed.

Lemma
  exp_subst_ind (P : exp -> Prop) (Q : subst -> Prop)
  : (forall n,  P (var n)) ->
    (forall n s,  Q s -> P (con n s)) ->
    Q [::] ->
    (forall e s, P e -> Q s -> Q (e :: s)) ->
    (forall e, P e) /\ (forall s, Q s).
Proof using .
  intros.
  assert ( alleP : forall e, P e).
  apply (@exp_subst_ind' P Q); auto.
  split; auto.
  clear H0 H.
  suff: (forall e s, Q s -> Q (e :: s)).
  intro; elim; eauto.
  eauto.
Qed.

Lemma subst_cmp_size s1 s2 : size (subst_cmp s1 s2) = size s1.
Proof using .
  elim: s1; simpl; auto.
Qed.

Lemma exp_var_map_nth s' m s n
  : exp_var_map (var_lookup s') (nth (var m) s n)
    = nth (var_lookup s' m) (subst_cmp s s') n.
Proof using .
  elim: n s; intros until s; case: s => //=.
Qed.

Lemma var_lookup_cmp n s1 s2 : n < size s1 ->
                               var_lookup (subst_cmp s1 s2) n = exp_var_map (var_lookup s2) (var_lookup s1 n).
Proof using .
  unfold var_lookup at 1 3; unfold nth_level.
  rewrite !subst_cmp_size.
  move => nlt; pose p := nlt; move: p.
  case: (n < size s1) => //= _.
  rewrite exp_var_map_nth.
  move: nlt.
  rewrite -!(@subst_cmp_size s1 s2) => nlt.
  apply: set_nth_default.
  move: nlt.
  generalize (size (subst_cmp s1 s2)); case =>//.
  intros; rewrite subSS.
  apply: sub_ord_proof.
Qed.

Lemma subst_cmp_assoc'
  : (forall e s1 s2, ws_exp (size s1) e -> e[/subst_cmp s1 s2/] = e[/s1/][/s2/])
    /\ (forall s s1 s2, ws_subst (size s1) s -> subst_cmp (subst_cmp s s1) s2 = subst_cmp s (subst_cmp s1 s2)).
Proof using .
  apply exp_subst_ind; simpl; auto; intros.
  2: by rewrite !con_subst_cmp H.
  2: {
    move /andP in H1.
    destruct H1.
    rewrite H; auto.
    rewrite H0; auto.
  }
 intros.
 unfold exp_subst.
 simpl.
 by apply var_lookup_cmp.
Qed.

Lemma subst_cmp_assoc s s1 s2
  : List.fold_right (fun e : exp => andb (ws_exp (size s1) e)) true s ->
    subst_cmp (subst_cmp s s1) s2 = subst_cmp s (subst_cmp s1 s2).
Proof using .
    by eapply subst_cmp_assoc'.
Qed.

Lemma sep_subst_cmp e s1 s2 :  ws_exp (size s1) e -> e[/subst_cmp s1 s2/] = e[/s1/][/s2/].
Proof using .
    by eapply subst_cmp_assoc'.
Qed.

(*TODO: needed?
Fixpoint lift_subst sz n : subst :=
  match sz with
  | 0 => [::]
  | sz'.+1 => (var n)::(lift_subst sz' (n.+1))
  end.

Lemma lift_subst_lookup n n0 sz : n < sz -> var (n0 + n) = var_lookup (lift_subst sz n0) n.
Proof using .
elim: n sz n0.
    case; first easy; by simpl; intros; rewrite addn0.
    move => n IH.
    case; first easy.
    intros; simpl.
    rewrite -addSnnS.
    eauto.
Qed.

Lemma lift_is_subst sz e n : ws_exp sz e -> e^!n = e[/lift_subst sz n/].
Proof using .
  case: e; unfold exp_subst; unfold exp_shift; simpl; eauto using lift_subst_lookup.
  - intros.
    f_equal.
    apply: (map_ext' (P := ws_exp sz)); auto; intros.
    apply: (exp_var_map_ext' (m:=sz)); auto; intros.
    by apply: lift_subst_lookup.
Qed. 


Lemma subst_lift_is_subst sz s n : ws_subst sz s -> s^!!n = subst_cmp s (lift_subst sz n).
Proof using .
  elim: s n; simpl.
  - elim: sz; simpl; auto.
  - move => a l IH n /andP [wsa wsl].
    f_equal; eauto using lift_is_subst.
Qed.
*)

Fixpoint id_subst n : subst :=
  match n with
  | 0 => [::]
  | n'.+1 =>
    let s' := id_subst n' in
    (var (size s'))::s'
  end.

Lemma id_subst_size sz : size (id_subst sz) = sz.
Proof using .
  elim: sz => //=.
  intros; by f_equal.
Qed.

Lemma id_subst_lookup n sz : var_lookup (id_subst sz) n = var n.
Proof using .
  unfold var_lookup.
  unfold nth_level.
  rewrite id_subst_size.
  case nsz: (n < sz) => //.
  apply (level_ind (R:=fun m n => nth (var n) (id_subst sz) m = var n)); auto.
  intro m.
  elim: m n sz nsz; intros until sz; case: sz => //; simpl; intros.
  - f_equal.
    rewrite id_subst_size subn1.
    by rewrite <-pred_Sn.
  - rewrite !subSS.
    eauto.
Qed.    

Lemma id_subst_identity e sz : e[/id_subst sz/] = e.
Proof using .
  elim: e sz; intros; unfold exp_subst; simpl; first by apply id_subst_lookup.
  f_equal.
  elim: l H => //.
  simpl.
  intro_to and.
  case => [ aeq fld].
  f_equal; eauto.    
Qed.  
*)
