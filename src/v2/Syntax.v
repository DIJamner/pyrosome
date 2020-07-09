
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


(*TODO: update
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
*)

(* TODO: handle id_subst; choice of nth base matters again?
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

Set Boolean Equality Schemes.
Inductive rule : Type :=
| sort_rule : ctx -> rule
| term_rule : ctx -> sort -> rule
| sort_le_rule : ctx -> sort -> sort -> rule
| term_le_rule : ctx -> term -> term -> sort -> rule.
Unset Boolean Equality Schemes.

(* TODO: prove *)
Axiom rule_eq_dec : forall r1 r2, reflect (r1 = r2) (rule_beq r1 r2).

Canonical rule_eqType := @Equality.Pack rule (Equality.Mixin rule_eq_dec).

Notation lang := (seq rule).
