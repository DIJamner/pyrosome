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

  (* Inverted *)
  Inductive exp_morph' (p2 : polynomial) : polynomial -> Type :=
  | nil_morph : exp_morph' p2 [::]
  | cons_morph : forall (S : Set) n (idx : S -> nat) p1,
      (forall (s : S), (nth zterm p2 (idx s)).1) ->
      (forall (s : S), Vector.t (Fin.t n) (nth zterm p2 (idx s)).2) ->
      exp_morph' p2 p1 ->
      exp_morph' p2 [:: (S,n) & p1].
  
  Fixpoint morph_map {p1 p2} (m : exp_morph' p2 p1) : forall (T : Set), constr p1 T -> constr p2 T.
    refine( match m with
            | nil_morph => _
            | cons_morph S' n idx _ sfn nfn _ => _
            end).
    - refine (fun T ce => match ce with
                        | ccon n s v => _
                        end).
      case: n s v; simpl. 
      + exact (fun ep => match ep with end).
      + exact (fun _ ep => match ep with end).
    - refine (fun T ce =>  match ce with
                           | ccon 0 s v =>
                             ccon (sfn (s : S'))
                                  (Vector.map (Vector.nth (v : Vector.t T n))
                                              (nfn (s : S')))
                           | ccon n.+1 s v => morph_map _ _ e _ (ccon _ _)
                           end).
      exact s.
      exact v.
  Defined.
  (*TODO: finish writing out definition ~nicely *)
  
  Section MorphFns.

    Variable p1 p2 : polynomial.
    
    Variable m : exp_morph' p2 p1.
    
    Definition morph_alg : Alg p1 p2 := fun ce => id_alg (morph_map m ce).
    
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

  End MorphFns.
  
  Lemma vector_map_map {A B C : Type} (g : B -> C) (f : A -> B) n (v : Vector.t A n)
    : Vector.map g (Vector.map f v) = Vector.map (fun e => g (f e)) v.
  Proof.
    elim: v; simpl; auto.
    move => e1 n' v' ->; done.
  Qed.
  
  Lemma vector_map_nth {B C : Type} (g : B -> C) n (v : Vector.t B n) m
    : Vector.nth (Vector.map g v) m = g (Vector.nth v m).
  Proof.
    elim: v m.
    - top_inversion.
    - move => e1 n' v' IH m.
      move: v' IH.
      refine (match m as m in Fin.t n'.+1 with
              | Fin.F1 n'' => _
              | Fin.FS n'' m' => _
              end).
      auto.
      move => v' IH.
      simpl.
        by rewrite IH.
  Qed.

  Lemma vec_map_ext {B C : Type} (f g : B -> C) n (v : Vector.t B n)
    : (forall e, f e = g e) -> Vector.map f v = Vector.map g v.
  Proof.
    move => ext.
    elim: v; first done.
    move => e1 n' v' IH.
    simpl.
    by rewrite ext IH.
  Qed.


  Tactic Notation "intro_to" constr(ty) :=
    repeat lazymatch goal with
           | |- ty -> _ => idtac
           | |- ty _ -> _ => idtac
           | |- ty _ _-> _ => idtac
           | |- ty _ _ _ -> _ => idtac
           | |- _ -> _ => intro
           end.
  
  Ltac top_inversion :=
    let f := fresh in
    intro f; inversion f.

  Tactic Notation "intro_to" constr(ty) "and_invert" :=
    intro_to ty; top_inversion; subst.
  
  Ltac inst_hyp H :=
  lazymatch type of H with
  | forall  x : ?T, _ =>
    match goal with
      H' : T |- _ =>
      specialize (H H'); inst_hyp H
    end
  | ?T -> _ =>
    match goal with
      H' : T |- _ =>
      specialize (H H'); inst_hyp H
    end
  | _ => idtac
  end.
  
  Ltac top_swap :=
    let n1 := fresh in
    let n2 := fresh in
    move => n1 n2;
    move: n2 n1.
  
  Lemma morph_alg_comm {p1 p2} (m : exp_morph' p2 p1) n s v s'
    : (morph_alg m (ccon s v)) [/ s' /]
      = morph_alg m (@ccon _ _ n s (Vector.map (exp_subst^~ s') v)).
  Proof.
    elim: m n s v s'.
    - case => [|n]; case.
    - unfold morph_alg.
      move => S n.
      intro_to nat.
      case.
      + intros; simpl.
        f_equal.
        rewrite vector_map_map.
        apply: vec_map_ext.
        move => x.
        by rewrite vector_map_nth.
      + intros; simpl.
        repeat match goal with
               | |- context [id_alg (morph_map ?M ?E)] =>
                 change (id_alg (morph_map M E)) with (morph_alg M E)
               end.
        apply: H.
  Qed.        
      
  Lemma morph_sub_comm {p1 p2} (m : exp_morph' p2 p1) e s
    : morph_fn m (e[/s/]) = (morph_fn m e)[/List.map (morph_fn m) s/].
  Proof.
      elim: e; simpl; auto.
      - by apply: morph_lookup.
      - intros.
        unfold morph_fn.
        simpl.
        rewrite morph_alg_comm.
        repeat f_equal.
        elim: v H;[by simpl|].
        simpl.
        intro_to and.
        case.
        do 2 unfold morph_fn at 1.
        by move -> => /H => ->.
  Qed.

    
    (*TODO: reformulate using a def of preservation? *)
    (*NOTE!!! Assuming this is true, and it should be,
      it gives a generic definition of the image of a translation,
      i.e. target terms that are correspond to well-structured source terms
      Suffices to show that wf_transport (source l) x ->wf  (target l) x?
      I.e. every morphism gives rise to an equivalence preserving compiler
     *)
    Lemma wf_transport {p1 p2} (m : exp_morph' p2 p1)
      : (forall (l : lang p1) c1 c2 t1 t2,
            le_sort l c1 c2 t1 t2 ->
            le_sort (lang_fn m l) (ctx_fn m c1) (ctx_fn m c2) (morph_fn m t1) (morph_fn m t2))
        /\ (forall (l : lang p1) c1 c2 s1 s2 c1' c2',
               le_subst l c1 c2 s1 s2 c1' c2' ->
               le_subst (lang_fn m l)
                        (ctx_fn m c1) (ctx_fn m c2)
                        (List.map (morph_fn m) s1) (List.map (morph_fn m) s2)
                        (ctx_fn m c1') (ctx_fn m c2'))
        /\ (forall (l : lang p1) c1 c2 e1 e2 t1 t2,
               le_term l c1 c2 e1 e2 t1 t2 ->
               le_term (lang_fn m l)
                       (ctx_fn m c1) (ctx_fn m c2)
                       (morph_fn m e1) (morph_fn m e2)
                       (morph_fn m t1) (morph_fn m t2))
        /\ (forall (l : lang p1) c1 c2,
               le_ctx l c1 c2 ->
               le_ctx (lang_fn m l) (ctx_fn m c1) (ctx_fn m c2))
        /\ (forall (l : lang p1) c1 c2 v1 v2,
               le_ctx_var l c1 c2 v1 v2 ->
               le_ctx_var (lang_fn m l)
                          (ctx_fn m c1) (ctx_fn m c2)
                          (ctx_var_map (morph_fn m) v1) (ctx_var_map (morph_fn m) v2))
        /\ (forall (l : lang p1) c t, 
            wf_sort l c t ->
            wf_sort (lang_fn m l) (ctx_fn m c) (morph_fn m t))
        /\ (forall (l : lang p1) c s c',
               wf_subst l c s c' ->
               wf_subst (lang_fn m l) (ctx_fn m c) (List.map (morph_fn m) s) (ctx_fn m c'))
        /\ (forall (l : lang p1) c e t, 
               wf_term l c e t ->
               wf_term (lang_fn m l) (ctx_fn m c) (morph_fn m e) (morph_fn m t))
        /\ (forall (l : lang p1) c,  wf_ctx l c -> wf_ctx (lang_fn m l) (ctx_fn m c))
        /\ (forall (l : lang p1) c v,
               wf_ctx_var l c v ->
               wf_ctx_var (lang_fn m l) (ctx_fn m c) (ctx_var_map (morph_fn m) v))
        /\ (forall (l : lang p1) r,  wf_rule l r -> wf_rule (lang_fn m l) (rule_map (morph_fn m) r))
        /\ (forall (l : lang p1),  wf_lang l -> wf_lang (lang_fn m l)).
    Proof.
      apply: mono_ind'; simpl; eauto.
      all: try by intros; rewrite !morph_sub_comm; eauto.
      all: try by intros; (*TODO: write, use intro_to tactic *)
        eapply morph_rule_in in H1; simpl in H1;
          eauto.
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
