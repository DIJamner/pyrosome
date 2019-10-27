Load Core.

(* A compiler assumes a way to compile p2 to the target and then compiles p1 to the target *)
Definition compiler p1 p2 := forall {p'}, Alg p2 p' -> Alg p1 p'.

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
