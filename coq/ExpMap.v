Load Core.

Scheme le_sort_mono_ind' := Minimality for le_sort Sort Prop
  with le_subst_mono_ind' := Minimality for le_subst Sort Prop
  with le_term_mono_ind' := Minimality for le_term Sort Prop
  with le_ctx_mono_ind' := Minimality for le_ctx Sort Prop
  with le_ctx_var_mono_ind' := Minimality for le_ctx_var Sort Prop
  with wf_sort_mono_ind' := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ind' := Minimality for wf_subst Sort Prop
  with wf_term_mono_ind' := Minimality for wf_term Sort Prop
  with wf_ctx_mono_ind' := Minimality for wf_ctx Sort Prop
  with wf_ctx_var_mono_ind' := Minimality for wf_ctx_var Sort Prop
  with wf_rule_ind' := Minimality for wf_rule Sort Prop
  with wf_lang_ind' := Minimality for wf_lang Sort Prop.

Combined Scheme mono_ind' from
         le_sort_mono_ind',
         le_subst_mono_ind',
         le_term_mono_ind',
         le_ctx_mono_ind',
         le_ctx_var_mono_ind',
         wf_sort_mono_ind',
         wf_subst_mono_ind',
         wf_term_mono_ind',
         wf_ctx_mono_ind',
         wf_ctx_var_mono_ind',
         wf_rule_ind',
         wf_lang_ind'.

(*TODO: finish and put in the right place *)
Lemma empty_subst_id {p} (e : exp p) : e[/[::]/] = e.
Proof.
  elim: e; auto.
  intros.
  simpl.
  f_equal.
  elim: v H; auto.
  intros.
  simpl.
  inversion H0.
  rewrite H.
  rewrite H1.
  auto.
  assumption.
Qed.

Section Morphisms.
  
  Variable p1 p2 : polynomial.
  
  Definition exp_morph : Type := forall (S : Set), constr p1 S -> constr p2 S.
  
  Section MorphFns.

    Variable m : exp_morph.
    
    Definition morph_alg : Alg p1 p2 := fun ce => id_alg (m ce).
    
    Definition morph_fn := alg_fn morph_alg.
    
    Definition ctx_fn := List.map (ctx_var_map morph_fn).
    
    Definition lang_fn := List.map (rule_map morph_fn).

    Lemma morph_rule_in (l : lang p1) r : List.In r l -> List.In (rule_map morph_fn r) (lang_fn l).
    Proof.
      elim: l; auto.
      move => a l IH; case.
      move => -> //=; auto.
      move => inr.
      simpl.
      right.
      auto.
    Qed.

    Lemma morph_lookup s n
      : morph_fn (var_lookup s n) = var_lookup (List.map morph_fn s) n.
    Proof.
      elim: s n; simpl; auto.
      move => e s' IH.
      case; auto.
    Qed.

    Lemma morph_alg_comm n s v s'
      : (morph_alg (ccon s v)) [/ s' /]
        = morph_alg (@ccon _ _ n s (Vector.map (exp_subst^~ s') v)).
    Proof.
      unfold morph_alg.
      unfold id_alg.
      (*Issue: this is a sort of paramentricity here! (bad)
        the best thing is probably to do as I did before and construct an initial
        representation.
        Allowed operations:
        - intuitionistic treatment of subterms (dropping, swapping, duplicating)
        - functions over coefficients
       *)          
      simpl.
      elim: p1 p2 n s v s'.
      
    Lemma morph_sub_comm e s
      : morph_fn (e[/s/]) = (morph_fn e)[/List.map morph_fn s/].
    Proof.
      elim: e; simpl; auto.
      - by apply: morph_lookup.
      - intros.
        unfold morph_fn.
        simpl.
       
      
      elim: s; simpl; auto.
      rewrite !empty_subst_id => //=.
      move => a l.
      Admitted.
    
    (*TODO: reformulate using a def of preservation? *)
    (*NOTE!!! Assuming this is true, and it should be,
      it gives a generic definition of the image of a translation,
      i.e. target terms that are correspond to well-structured source terms
      Suffices to show that wf_transport (source l) x ->wf  (target l) x?
      I.e. every morphism gives rise to an equivalence preserving compiler
     *)
    Lemma wf_transport
      : (forall (l : lang p1) c1 c2 t1 t2,
            le_sort l c1 c2 t1 t2 ->
            le_sort (lang_fn l) (ctx_fn c1) (ctx_fn c2) (morph_fn t1) (morph_fn t2))
        /\ (forall (l : lang p1) c1 c2 s1 s2 c1' c2',
               le_subst l c1 c2 s1 s2 c1' c2' ->
               le_subst (lang_fn l)
                        (ctx_fn c1) (ctx_fn c2)
                        (List.map morph_fn s1) (List.map morph_fn s2)
                        (ctx_fn c1') (ctx_fn c2'))
        /\ (forall (l : lang p1) c1 c2 e1 e2 t1 t2,
               le_term l c1 c2 e1 e2 t1 t2 ->
               le_term (lang_fn l)
                       (ctx_fn c1) (ctx_fn c2)
                       (morph_fn e1) (morph_fn e2)
                       (morph_fn t1) (morph_fn t2))
        /\ (forall (l : lang p1) c1 c2,
               le_ctx l c1 c2 ->
               le_ctx (lang_fn l) (ctx_fn c1) (ctx_fn c2))
        /\ (forall (l : lang p1) c1 c2 v1 v2,
               le_ctx_var l c1 c2 v1 v2 ->
               le_ctx_var (lang_fn l)
                          (ctx_fn c1) (ctx_fn c2)
                          (ctx_var_map morph_fn v1) (ctx_var_map morph_fn v2))
        /\ (forall (l : lang p1) c t, 
            wf_sort l c t ->
            wf_sort (lang_fn l) (ctx_fn c) (morph_fn t))
        /\ (forall (l : lang p1) c s c',
               wf_subst l c s c' ->
               wf_subst (lang_fn l) (ctx_fn c) (List.map morph_fn s) (ctx_fn c'))
        /\ (forall (l : lang p1) c e t, 
               wf_term l c e t ->
               wf_term (lang_fn l) (ctx_fn c) (morph_fn e) (morph_fn t))
        /\ (forall (l : lang p1) c,  wf_ctx l c -> wf_ctx (lang_fn l) (ctx_fn c))
        /\ (forall (l : lang p1) c v,
               wf_ctx_var l c v ->
               wf_ctx_var (lang_fn l) (ctx_fn c) (ctx_var_map morph_fn v))
        /\ (forall (l : lang p1) r,  wf_rule l r -> wf_rule (lang_fn l) (rule_map morph_fn r))
        /\ (forall (l : lang p1),  wf_lang l -> wf_lang (lang_fn l)).
    Proof.
      apply: mono_ind'; simpl; eauto.
      all: try by intros; rewrite !morph_sub_comm; eauto.
      all: try by intros; (*TODO: write, use intro_to tactic *)
        apply morph_rule_in in H1; simpl in H1;
        auto.
      - intros.
        eapply le_subst_term;
          first by auto.
        rewrite -!morph_sub_comm; done.
      - move => l  s c' e t t'.
        rewrite !morph_sub_comm.
        auto.
    Qed.
        (* Note!!!!: probably a theorem:
           Derivable l r -> Preserving (r::l) -> l
           Maybe a Thm?
           Admissible l r -> Preserving (r::l) -> l 
           ---- 
           Derivable l {| c |- t} := wf_sort l c t
           Admissible l {| c |- t} <-> wf_sort l c t ?
         *)
    
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
