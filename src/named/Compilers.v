
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp Rule Core.

Require Import String.

(* each element is the map for that constructor *)
Variant compiler_case : Set :=
| sort_case : ((* target closing *) list exp -> (* target *) sort) -> compiler_case
| term_case : ((* target closing *) list exp -> (* target *) exp) -> compiler_case.

(* each element is the map for that constructor *)
Definition compiler := named_list compiler_case. 


Fixpoint compile_term (cmp : compiler) (close : subst) (e : exp) : exp :=
  match e with
  | var x => named_list_lookup (var x) close x
  | con n s =>
    let default := sort_case (fun _ => srt "ERR" [::]) in
    match named_list_lookup default cmp n with
    | term_case c_case => c_case (map (compile_term cmp close) s)
    | _ => con "ERR"%string [::]
    end
  end.

Definition compile_sort (cmp : compiler) (close : subst) (e : sort) : sort :=
  match e with
  | srt n s =>
    let default := term_case (fun _ => con "ERR" [::]) in
    match named_list_lookup default cmp n with
    | sort_case c_case => c_case (map (compile_term cmp close) s)
    | _ => srt"ERR"%string [::]
    end
  end.

Definition compile_subst (cmp : compiler) (close : subst) (e : subst) : subst :=
  map (fun p => (fst p, compile_term cmp close (snd p))) e.

Definition compile_ctx (cmp : compiler) (close : subst) (e : ctx) : ctx :=
  map (fun p => (fst p, compile_sort cmp close (snd p))) e.

(* TODO: ICompilers*)

(*TODO: necessary? 
 make inductive instead if so
Fixpoint wf_cmp_subst tgt_l tgt_s cmp src_c :=
  match tgt_s, src_c with
  | [::],[::] => True
  | e::s', t::c' =>
    wf_cmp_subst tgt_l s' cmp c'
    /\ wf_term tgt_l [::] e (compile cmp s' t)
  | _,_ => False
  end.

 Conjecture : wf_ctx src_l c -> 
           wf_cmp_subst l s cmp c <-> wf_subst l [::] s (map (compile cmp s) c))*)

(*
TODO: seems wrong; specializing c too much; seems artificial
Is it sufficient to talk about closed terms?

First we specify the properties in terms of compile,
then inductively on the compiler. TODO: prove equivalent
 *)
Definition sort_wf_preserving_sem cmp l1 l2 :=
  forall s c t, wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                wf_sort l1 c t ->
                wf_sort l2 [::] (compile_sort cmp s t).

Definition term_wf_preserving_sem cmp l1 l2 :=
  forall s c e t, wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                wf_term l1 c e t ->
                wf_term l2 [::] (compile_term cmp s e) (compile_sort cmp s t).

Definition sort_le_preserving_sem cmp l1 l2 :=
  forall s c t1 t2, wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                le_sort l1 c t1 t2 ->
                le_sort l2 [::] (compile_sort cmp s t1) (compile_sort cmp s t2).

Definition term_le_preserving_sem cmp l1 l2 :=
  forall s c e1 e2 t, wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                le_term l1 c t e1 e2 ->
                le_term l2 [::] (compile_sort cmp s t)
                        (compile_term cmp s e1) (compile_term cmp s e2).

Definition semantics_preserving cmp l1 l2 :=
  sort_wf_preserving_sem cmp l1 l2
  /\ term_wf_preserving_sem cmp l1 l2
  /\ sort_le_preserving_sem cmp l1 l2
  /\ term_le_preserving_sem cmp l1 l2.

(*TODO: this is an equal stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : lang) : compiler -> lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [::] [::]
| preserving_compiler_sort : forall cmp l cf n c,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    (forall s, wf_args target [::] s (compile_ctx cmp (with_names_from c s) c) ->
               wf_sort target [::] (cf s)) ->
    preserving_compiler target ((n, sort_case cf)::cmp) ((n,sort_rule c) :: l)
| preserving_compiler_term : forall cmp l cf n c t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    (forall s, wf_args target [::] s (compile_ctx cmp (with_names_from c s) c) ->
               wf_term target [::] (cf s)
                       (compile_sort cmp (with_names_from c s) t)) ->
    preserving_compiler target ((n,term_case cf)::cmp) ((n,term_rule c t) :: l)
| preserving_compiler_sort_le : forall cmp l n c t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    (forall s, wf_subst target [::] s (compile_ctx cmp s c) ->
               le_sort target [::] (compile_sort cmp s t1)
                       (compile_sort cmp s t2)) ->
    preserving_compiler target cmp ((n,sort_le c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp l n c e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    (forall s, wf_subst target [::] s (compile_ctx cmp s c) ->
               le_term target [::]
                       (compile_sort cmp s t)
                       (compile_term cmp s e1)
                       (compile_term cmp s e2)) ->
    preserving_compiler target cmp ((n,term_le c e1 e2 t) :: l).

Lemma wf_empty_sort c t : ~wf_sort [::] c t.
Proof using .
  by inversion.
Qed.

Lemma wf_empty_ctx c : wf_ctx [::] c -> c = [::].
Proof using .
  case; auto.
  intros.
  exfalso.
  eapply wf_empty_sort; eassumption.
Qed.


Lemma wf_empty_term c e t : wf_ctx [::] c -> ~wf_term [::] c e t.
Proof using .
  intros wfc wft.
  elim: wft wfc; eauto.
  intros c0 n t0 nin.
  move /wf_empty_ctx => wfe.
  move: wfe nin => ->.
  auto.  
Qed.


Lemma le_empty_term c e1 e2 t : le_term [::] c t e1 e2 -> e1 = e2
with le_empty_subst c s1 s2 c' : le_subst [::] c c' s1 s2 -> s1 = s2.
Proof using .
  all: case; intros.
  {
    f_equal; eauto.
  }
  { easy. }
  { reflexivity. }
  { apply le_empty_term in l.
    apply le_empty_term in l0.
    rewrite l l0; reflexivity.
  }
  {
    symmetry.
    eapply le_empty_term; eassumption.
  }
  {
    eapply le_empty_term; eassumption.
  }
  { reflexivity. }
  {
    f_equal.
    f_equal.
    eauto.
    eauto.
  }
Qed.
  
Lemma le_empty_sort c t1 t2 : le_sort [::] c t1 t2 -> t1 = t2.
Proof using .
  elim; intros; try by (cbv in *; eauto).
  f_equal; eauto using le_empty_subst.
  by rewrite H0 -H2.
Qed.    


Lemma in_lang_in_cmp_sort lt cmp ls n c
  : preserving_compiler lt cmp ls ->
    (n, sort_rule c) \in ls ->
    exists f, (forall d, named_list_lookup d cmp n = sort_case f)
              /\ (forall s, wf_args lt [::] s
                                    (compile_ctx cmp (with_names_from c s) c) ->
               wf_sort lt [::] (f s)). 
Proof.
Admitted.

(*TODO: move to core*)

Lemma with_names_from_nil_r c : with_names_from c [::] = [::].
Proof.
  case: c; simpl; auto.
Qed.


Lemma fresh_compile_ctx c cmp s n
  : fresh n c -> fresh n (compile_ctx cmp s c).
Proof using.
  elim: c; simpl; auto.
  move => [n' t] c'.
  unfold fresh.
  intro IH; simpl.
  rewrite !in_cons.
  move /norP => [nneq nnin].
  apply /norP.
  split; auto.
Qed.

Ltac f_equal_match :=
  match goal with
  | [|- match ?e with _ => _ end = match ?e with _ => _ end]
    => let e':= fresh in remember e as e'; destruct e'
  end.


Lemma fresh_tail {A} n (l1 l2 : named_list A)
  : fresh n (l1 ++ l2) -> fresh n l2.
Proof.
  elim: l1; simpl; auto.
  intros a l.
  unfold fresh; simpl; intro IH.
  rewrite !in_cons.
  move /norP => [_] //.
Qed.

Lemma fresh_neq_in {A : eqType} n l n' (t : A)
  : fresh n l -> (n',t) \in l -> ~~ (n'==n).
Proof.
  elim: l; unfold fresh; simpl.
  by cbv.
  move => [n1 t1] l IH.
  rewrite !in_cons.
  move /norP => //= [nn1 nnl].
  move /orP; case; eauto.
  {
    move /eqP.
    case.
    move -> => _.
    
    apply /negP.
    move /eqP.
    move: nn1=> /eqP.
    intros nnneq nneq.
    apply nnneq.
    by symmetry.
  }
Qed.
  
Lemma lookup_in_tail l cmp c0 c c' n t s s'
  : let cc := compile_ctx cmp in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    wf_args l c0 (s'++s) (cc cs' (c'++c)) ->
    (n,t) \in c ->
              named_list_lookup (var n) cs' n =
              named_list_lookup (var n) (with_names_from c s) n.
Proof.
  simpl.
 (* intro.
  elim: c' s'; intros until s'; case: s'; simpl; auto.
  {
    give_up (*TODO: show absurd*).
  }
  { give_up (*TODO: show absurd*).
  }
  {
    intro_to wf_args; inversion; subst; simpl.
    intro; suff: (n=?name = false)%string.
    {
      move -> => //.
      unfold with_names_from in *.
      eauto.
    }
    {
      replace ((n =? name)%string=false) with (is_true(n!=name)).
      eapply fresh_neq_in.
      eapply fresh_tail; eassumption.
      eassumption.
      give_up (*TODO*).
    }
  }*)
Admitted.

Lemma strengthen_compile_term l c0 c' c cmp s' s e t
  : wf_term l c e t ->
    let cc := compile_ctx cmp in
    let cce := compile_term cmp in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    wf_args l c0 (s'++s) (cc cs' (c'++c)) ->
    cce cs' e = cce (with_names_from c s) e
with strengthen_compile_args l c0 c' c cmp s' s s1 c1
  : wf_args l c s1 c1 ->
    let cc := compile_ctx cmp in
    let cca sub := map (compile_term cmp sub) in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    wf_args l c0 (s'++s) (cc cs' (c'++c)) ->
    cca cs' s1 = cca (with_names_from c s) s1.
Proof using .
  all: inversion; subst; simpl; eauto.
  {
    intros; f_equal_match; auto.
    f_equal.
    eauto.
  }
  {
    intros.
    eapply lookup_in_tail; eauto.
  }
  {
    intros; f_equal; eauto.
  }
Qed.
  
Lemma strengthen_compile_sort l c0 c' c cmp s' s t
  : let cc := compile_ctx cmp in
    let ccs := compile_sort cmp in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    wf_sort l c (cc cs' t) ->
    wf_args l c0 s (cc cs' c) ->
    wf_args l c0 (s'++s) (cc cs' (c'++c)) ->
    ccs cs' t = ccs (with_names_from c s) t.
Proof using .
  simpl.
  case.
  intros.
  simpl.
  f_equal_match; auto.
  f_equal.
  eapply strengthen_compile_args; by eauto.
Qed.


Lemma strengthen_compile_ctx l c0 c' c cmp s' s
  : let cc := compile_ctx cmp in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    wf_args l c0 s (cc cs' c) ->
    wf_args l c0 (s'++s) (cc cs' (c'++c)) ->
    cc cs' c = cc (with_names_from c s) c.
Proof using.
  simpl.
  elim: c c' s s'; auto.
  move => [n' t'] c1 // => IH c' s s'.
  inversion; subst.
  rewrite -!cat_rcons.
  intro.
  simpl.
  f_equal.
  f_equal.
  
  change (?a::?b) with ([::a]++b).
  erewrite !strengthen_compile_sort; eauto.

  change (?a::?b) with ([::a]++b).
  rewrite !IH; auto.
Qed.

  
  
Lemma strengthen_compile_ctx l c0 c' c cmp s' s
  : wf_args l c0 s c ->
    wf_args l c0 (s'++s) (c'++c) ->
    compile_ctx cmp
                (with_names_from (c'++ c)
                                 (s' ++ s)) c =
    compile_ctx cmp (with_names_from c s) c.
Proof using .
  elim: c c' s s'; auto.
  move => [n' t'] c1 // => IH c' s s'.
  inversion; subst.
  rewrite -!cat_rcons.
  intro.
  simpl.
  f_equal.
  f_equal.
  
  change (?a::?b) with ([::a]++b).
  erewrite !strengthen_compile_sort; eauto.

  change (?a::?b) with ([::a]++b).
  rewrite !IH; auto.
Qed.


  
Lemma inductive_implies_semantic_sort_wf cmp ls lt
  : preserving_compiler lt cmp ls ->
    sort_wf_preserving_sem cmp ls lt
with inductive_implies_semantic_term_wf cmp ls lt
  : preserving_compiler lt cmp ls ->
    term_wf_preserving_sem cmp ls lt
with inductive_implies_semantic_sort_le cmp ls lt
  : preserving_compiler lt cmp ls ->
    sort_le_preserving_sem cmp ls lt
with inductive_implies_semantic_term_le cmp ls lt
  : preserving_compiler lt cmp ls ->
    term_le_preserving_sem cmp ls lt.
Proof.
  all: intros pc s c.
  {
    intros t wfc wfs.
    case; intros.
    pose (i':=i).
    move: i' => /in_lang_in_cmp_sort => i'.
    pose (pc':=pc).
    move: pc' => /i'.
    case.
    intro.
    case.
    simpl.
    move -> => pres.
    apply pres.
    simpl.
    {
      (*wf args*)
      (*TODO: rewrite ...c'... to ...c'[/s0/]...?*)
      clear i i' x pres.
      elim: s0 c' w.
      {
        intro c'.
        simpl.
        rewrite !with_names_from_nil_r.
        inversion; constructor.
      }
      {
        intros e s' IH c'.
        inversion; subst.
        simpl; constructor.
        { by apply fresh_compile_ctx. }
        {
          move: (IH _ H3) => IH'.
          match goal with
          | [ H : wf_args _ _ ?s ?c
              |- wf_args _ _ ?s ?c']
            => suff: (c' = c); [ move ->; assumption |]
          end.
          change (?a::?l) with ([::a]++l).

          eapply strengthen_compile_ctx; eauto.





          Lemma strengthen_compile_ctx l c0 c' c cmp s' s
  : let cc := compile_ctx cmp in
    let ca := compile_args cmp in
    size s == size c ->
    wf_args l c0 (ca (s'++s)) (cc (c'++c)) ->
    cc (with_names_from (c'++ c) (s' ++ s)) c
    = cc (with_names_from c s) c.

          
                    TODO: doesn't quite line up yet
          give_up (* suffices to prove freshness condition*).
        }
        {
          same freshness condition

          TODO: apply IH        
        case c'.
        
        give_up (* TODO: the with_names_from issue bites me here;
                   need to switch handling *).
        intros p c''.
        inversion; subst.
        destruct p.
        move: H3.
        case.
        move ->.
        simpl.
        constructor.
        {
          give_up. }
        {

          
        eauto.
        {
          simpl in *.
          ; easy.
     TODO: addl prop for wf_args/subst?
    

Lemma inductive_implies_semantic cmp ls lt
  : preserving_compiler lt cmp ls ->
    semantics_preserving cmp ls lt.
Proof.
  intro
  elim.
  {
    repeat split; intros s c; intros.
    { exfalso; eapply wf_empty_sort; eassumption. }
    { exfalso; eapply wf_empty_term; eassumption. }
    { move: H1 => /le_empty_sort ->; reflexivity. }
    { move: H1 => /le_empty_term ->; reflexivity. }
  }
  {
    intros until c; intro cmp_preserves.
    move => [swf [twf [sle tle]]] IH.
    repeat split; intro s; intros.
    {
      TODO: wrong induction?
                  probably need to do induction on exprs
    
    inversion H1.
    
  unfold term_wf_preserving_sem.
  intros until e; move: s; elim: e; simpl.
  { give_up. }
  intros.
  (*TODO*) Admitted.
       

(*
    
  Lemma compiler_var_lookup
    :  wf_subst lt [::] s (map (compile cmp s) c) ->
       wf_term lt [::] (var_lookup s n) (compile cmp s t)

Lemma preserving_preserves_sort cmp ls lt
  : preserving_compiler lt cmp ls ->
    sort_wf_preserving_sem cmp ls lt.
Proof.
  unfold sort_wf_preserving_sem.
  
  elim; simpl.
  {
    intros; exfalso.
    by inversion H1.
  }
  {
    
    

(* something like this would be for closed ctxs
   Before using this one, the signature of compile should change though *)
Definition sort_wf_preserving_closed cmp l1 l2 :=
  forall t, wf_sort l1 [::] t -> wf_sort l2 [::] (compile cmp [::] t).

Lemma compiler_cat_sort_preserving cmp1 cmp2 l1 l2 lt
  : sort_wf_preserving cmp1 l1 lt ->
    sort_wf_preserving cmp2 l2 lt ->
    sort_wf_preserving (cmp1 ++ cmp2) (l1 ++ l2) lt.
Proof.
  elim: cmp1 l1; intros until l1; case l1; simpl; first easy.
  1,2: intro_to sort_wf_preserving.

(* =======================*)
Definition compiler := (* target closing *) subst -> (* src *) exp -> (* target *) exp.

Fixpoint compile_ctx cmp s c : ctx :=
  match s, c with
  | [::],[::] => [::]
  | e::s', t::c' => ::(compile_ctx cmp s' c')
  | _,_ => (* unreachable with wf inputs; is this okay? *) [::]
  end.

Definition sort_wf_preserving cmp l1 l2 :=
  forall s c t, wf_subst l2 [::] s (compile_ctx cmp s c) ->
                wf_sort l1 c t ->
                wf_sort l2 [::] (cmp s t).
(*================*)

(*
  TODO!!!: too weak; can't do eg closure conversion if the type is a metavar
*)
Definition optimizer := exp -> exp.
Definition translation := list exp.

Variant pass :=
| opt_pass : optimizer -> pass
| trans_pass : translation -> pass.

Definition compiler := list pass.

Fixpoint translate (t : translation) (e : exp) : exp :=
  match e with
  | var x => var x
  | con n s => (nth_level (con 0 [::]) t n)[/ map (translate t) s/]
  end.

Definition run_pass (p : pass) : exp -> exp :=
  match p with
  | opt_pass o => o
  | trans_pass t => translate t
  end.

Definition compile : compiler -> exp -> exp :=
  foldr (fun p => Basics.compose (run_pass p)) id.

Fixpoint compiler_translation (c: compiler) : list translation :=
  match c with
  | [::] => [::]
  | (opt_pass _)::c' => compiler_translation c'
  | (trans_pass p)::c' => p::compiler_translation c'
  end.

(*todo: can also precompute start-to-end translation table*)
Definition translate_n : list translation -> exp -> exp :=
  foldr (fun p => Basics.compose (translate p)) id.

(* Properties *)
Definition optimizer_refines (o : optimizer) l
  := forall c,
    (forall t1 t2, le_sort l c t1 t2 -> le_sort l c t1 (o t2))
    /\ (forall e1 e2 t, le_term l c e1 e2 t -> le_term l c e1 (o e2) (o t)).

(* A simpler statement, but not quite the right property:
Definition optimizer_refines (o : optimizer) l
  := forall c,
    (forall t, wf_sort l c t -> le_sort l c t (o t))
     /\ (forall e t, wf_term l c e t -> le_term l c e (o e) (o t)). 
TODO: I might be able to use something closer to this if I prove o
respects substitution/behaves like syntax.
idea: define a notion of fns that agree with a syntactic object, like:
add [:: e] |- so as a constructor, prove that (so e) > (o e)
and (o e) is universal in that, ie if (so e) > e' then exists (unique) e'' where e' > e''
and (o e) > e''
*)

Definition translation_preserves (t : translation) l1 l2
  := forall c,
    (forall t1 t2, le_sort l1 c t1 t2 ->
                    le_sort l2 (map (translate t) c) (translate t t1) (translate t t2))
     /\ (forall e1 e2 t', le_term l1 c e1 e2 t' ->
                          le_term l2 (map (translate t) c)
                                  (translate t e1) (translate t e2) (translate t t')).

Definition compiler_refines (cmp : compiler) l1 l2
  := forall c, (forall t1 t2, le_sort l1 c t1 t2 ->
                    le_sort l2 (map (translate_n (compiler_translation cmp)) c)
                            (translate_n (compiler_translation cmp) t1)
                            (compile cmp t2))
     /\ (forall e1 e2 t', le_term l1 c e1 e2 t' ->
                          le_term l2 (map (translate_n (compiler_translation cmp)) c)
                            (translate_n (compiler_translation cmp) e1)
                            (compile cmp e2) (compile cmp t')).

Inductive compiler_refines' : compiler -> lang -> lang -> Prop :=
| cref_nil : forall l, compiler_refines' [::] l l
| cref_trans : forall t c' l1 l2 l3,
    compiler_refines' c' l1 l2 ->
    translation_preserves t l2 l3 ->
    compiler_refines' (trans_pass t::c') l1 l3
| cref_opt : forall o c' l1 l2,
    compiler_refines' c' l1 l2 ->
    optimizer_refines o l2 ->
    compiler_refines' (opt_pass o::c') l1 l2.

Lemma compiler_empty_id : compile [::] = id.
Proof using .
  by compute.
Qed.
 
Lemma map_compose {A B C : Type} (f : B -> C) (g : A -> B) l
  : map (Basics.compose f g) l = map f (map g l).
Proof using .
  elim: l; simpl; eauto.
  move => a l ->; eauto.
Qed.

Lemma compiler_refines_translation t c' l1 l2 l3
  : compiler_refines c' l1 l2 ->
    translation_preserves t l2 l3 ->
    compiler_refines (trans_pass t::c') l1 l3.
Proof using .
  unfold compiler_refines; unfold translation_preserves; unfold optimizer_refines.
    intros.
    specialize H with c.
    destruct H.
    simpl.
    rewrite map_compose.
    unfold Basics.compose.
    specialize H0 with (map (translate_n (compiler_translation c')) c).
    destruct H0.
    split; intros; eauto.
Qed.

Lemma compiler_refines_optimization o c' l1 l2
  : compiler_refines c' l1 l2 ->
    optimizer_refines o l2 ->
    compiler_refines (opt_pass o::c') l1 l2.
Proof using .
  unfold compiler_refines; unfold translation_preserves; unfold optimizer_refines.
  intros.
  specialize H with c.
  destruct H.
  simpl.
  unfold Basics.compose.
  specialize H0 with (map (translate_n (compiler_translation c')) c).
  destruct H0.
  split; intros; eauto with judgment.
Qed.
  
Lemma compiler_refines_by_pass c l1 l2
  : compiler_refines' c l1 l2 -> compiler_refines c l1 l2.
Proof using .
  elim; eauto using compiler_refines_optimization,
        compiler_refines_translation
          with judgment.
  unfold compiler_refines;
    intros; split; intros; rewrite !compiler_empty_id !map_id; done.
Qed.  

(* TODO: is the ' ver useful?
   Interesting note: it is not clear how to extend optimizers;
   easiest way is to apply it iff a program fragment is in the core lang
   otherwise, not clear what they should do.
   TODO: come up with a more restrictive type that strikes the right balance?
 *)

Definition subst_respecting t :=
  forall e s, t e[/s/] = (t e)[/map t s/].

Definition var_respecting t :=
  forall x, t (var x) = var x.

Fixpoint trans_fn_to_table (t : exp -> exp) (src : lang) : translation :=
  match src with
  | [::] => [::]
  | (sort_rule c)::src'
  | (term_rule c _)::src' =>
    t (con (size src') (id_subst (size c)))::(trans_fn_to_table t src')
  | _::src' => (con 0 [::])::(trans_fn_to_table t src')
  end.


Lemma id_subst_cmp : forall (s : subst),  subst_cmp (id_subst (size s)) s = s.
Admitted.


Lemma trans_fn_to_table_size t l : size (trans_fn_to_table t l) = size l.
Admitted.

Lemma nth_level_trans_table t l n c t'
  : (is_nth_level l n (sort_rule c) \/ (is_nth_level l n (term_rule c t'))) ->
    nth_level [0 | ] (trans_fn_to_table t l) n
    = t (con n (id_subst (size c))).
Proof.
  case.
  all: unfold is_nth_level; unfold nth_level.
  all: move /andP => [nlt].
  all: rewrite !trans_fn_to_table_size.
  all: rewrite !nlt.
  all: suff: n = size l - (size l - n.+1).+1.
  1,3:remember (size l - n.+1) as m.
  1,2: rewrite -!Heqm.
  1,2: move ->.
Admitted.
  
  

(*Seems true, but have technical mechanics to work out*)
Lemma trans_fn_representation_term t l c e t'
  : subst_respecting t ->
    var_respecting t ->
    wf_term l c e t' -> translate (trans_fn_to_table t l) e = t e.
Proof.
  unfold subst_respecting; intro srt.
  unfold var_respecting; intro vrt.
  elim: e t'; simpl; eauto.
  intros.
  rewrite -{2}(id_subst_cmp l0).
  rewrite -con_subst_cmp.
  rewrite srt.
  f_equal.
  {
    elim: l0 H0 H; simpl; eauto with judgment.
    intros.
    destruct H1.
    f_equal; eauto with judgment.
    apply: H1.
    (*2:{
      apply: map_ext'.(*TODO: need map_ext' for props?*)
             eapply H1.*)
    give_up.
    give_up.
  }
  {
    eapply nth_level_trans_table.
    give_up.
  }
  Unshelve.
  all: auto.
Admitted.
    
Lemma trans_fn_representation_sort t l c t'
  : subst_respecting t ->
    var_respecting t ->
    wf_sort l c t' -> translate (trans_fn_to_table t l) t' = t t'.
Proof.
  unfold subst_respecting; intro srt.
  unfold var_respecting; intro vrt.
  case: t'; simpl; eauto.
  intros.
  rewrite -{2}(id_subst_cmp l0).
  rewrite -con_subst_cmp.
  rewrite srt.
  inversion H; subst.
  f_equal.      
  2:{
    suff: (size l0 = size c'); first move ->.
    eapply nth_level_trans_table.
    tauto.
    give_up.
  }
  TODO: subst. ver. of lemma
*)
