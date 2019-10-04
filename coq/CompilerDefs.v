Load Core.


(* A compiler assumes a way to compile p2 to the target and then compiles p1 to the target *)
Definition compiler p1 p2 := forall {p'}, Alg p2 p' -> Alg p1 p'. 

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
