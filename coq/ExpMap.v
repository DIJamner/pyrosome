Load Exp.

Section Morphisms.
  
  Variable p1 p2 : polynomial.
  
  Definition exp_morph : Type := forall (S : Set), constr p1 S -> constr p2 S.
  
  Section MorphFns.

    Variable m : exp_morph.
    
    Definition morph_alg : Alg p1 p2 := fun ce => id_alg (m ce).
    
    Definition morph_fn := alg_fn morph_alg.
    
    Definition lang_fn := List.map (rule_map morph_fn).
    
  End MorphFns.

End Morphisms.

Lemma nth_in_bounds p n : (nth zterm p n).1 -> n < size p.
Proof.
  elim: n p.
  - elim; auto.
    simpl; case.
  - move => n IH; case.
    simpl; case.
    move => t p'.
    simpl.
    move => /IH => //=.
Qed.


Lemma nth_cat1 : forall p1 p2 n, n < size p1 -> nth zterm (p1 ++ p2) n = nth zterm p1 n.
Proof.
  intros.
  rewrite nth_cat.
  by rewrite H.
Qed.

Arguments nth_cat1 {p1} {p2} {n} nlt.

Definition eq_ccon p (T : Set) n elt (elteq : nth zterm p n = elt)
           (s : elt.1) (v : Vector.t T elt.2) : constr p T :=
  ccon (eq_rec_r fst s elteq)
       (eq_rect_r (fun elt => Vector.t _ elt.2) v elteq).
Arguments eq_ccon {p} {T} {n} {elt} elteq s.

(* TODO: make a reasonable computational defn *)
Definition sumL {p1 p2} : exp_morph p1 (p1 ++ p2) :=
  fun S e =>
    match e with
    | ccon n s v =>
      let bounds := (nth_in_bounds s) in
      let ncat := nth_cat1 bounds in
      eq_ccon ncat s v
    end.

Lemma nth_cat2 : forall p1 p2 n, nth zterm (p1 ++ p2) (size p1 + n) = nth zterm p2 n.
Proof.
  elim; auto.
Qed.

Definition sumR {p1 p2} : exp_morph p2 (p1 ++ p2) :=
  fun S e =>
    match e with
    | ccon n s v =>
      let bounds := (nth_cat2 p1 p2 n) in
      eq_ccon bounds s v
    end.
