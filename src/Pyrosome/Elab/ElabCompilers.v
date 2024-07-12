Set Implicit Arguments.

Require Import Lists.List Datatypes.String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.Compilers Elab.Elab.
(*TODO: why does this generate warnings?*)
Import Core.Notations.


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
  Notation compiler_case := (@compiler_case V term sort).
  Notation compiler := (@compiler V term sort).

  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

Section Extension.
  Context (src_pre : lang) (*assumed to already be elaborated*)
          (cmp_pre : compiler) (*assumed to already be elaborated*).

  Notation compile cmp := (compile (cmp++cmp_pre)).
  Notation compile_sort cmp := (compile_sort (cmp++cmp_pre)).
  Notation compile_ctx cmp := (compile_ctx (cmp++cmp_pre)).


  Section WithModel.
    Context (target : lang).

    (* TODO: is there a nicer way of doing this? *)
    Let model := core_model target.
    Existing Instance model.
    Existing Instance term_default.
    Existing Instance sort_default.

  Inductive elab_preserving_compiler : compiler -> compiler -> lang -> Prop :=
  | elab_preserving_compiler_nil : elab_preserving_compiler [] [] []
  | elab_preserving_compiler_sort : forall cmp ecmp l n c args t et,
      elab_preserving_compiler cmp ecmp l ->
      elab_sort target (compile_ctx ecmp c) t et ->
      elab_preserving_compiler ((n,sort_case (map fst c) t)::cmp)
                               ((n,sort_case (map fst c) et)::ecmp)
                               ((n,sort_rule c args) :: l)
  | elab_preserving_compiler_term : forall cmp ecmp l n c args e ee t,
      elab_preserving_compiler cmp ecmp l ->
      elab_term target (compile_ctx ecmp c) e ee (compile_sort ecmp t) ->
      elab_preserving_compiler
                               ((n, term_case (map fst c) e)::cmp)
                               ((n, term_case (map fst c) ee)::ecmp)
                               ((n,term_rule c args t) :: l)
  | elab_preserving_compiler_sort_eq : forall cmp ecmp l n c t1 t2,
      elab_preserving_compiler cmp ecmp l ->
      eq_sort target (compile_ctx ecmp c) (compile_sort ecmp t1) (compile_sort ecmp t2) ->
      elab_preserving_compiler cmp ecmp ((n,sort_eq_rule c t1 t2) :: l)
  | elab_preserving_compiler_term_eq : forall cmp ecmp l n c e1 e2 t,
      elab_preserving_compiler cmp ecmp l ->
      eq_term target (compile_ctx ecmp c) (compile_sort ecmp t) (compile ecmp e1) (compile ecmp e2) ->
      elab_preserving_compiler cmp ecmp ((n,term_eq_rule c e1 e2 t) :: l).
  Hint Constructors elab_preserving_compiler : lang_core.
  
  Lemma elab_compiler_implies_preserving cmp ecmp src
    : elab_preserving_compiler cmp ecmp src ->
      preserving_compiler_ext cmp_pre ecmp src.
    Proof using.
    induction 1; basic_goal_prep; basic_core_crush.
    all:constructor; simpl; basic_core_crush.
  Qed.
  
  (*TODO: check that this works w/ prefix *)
  Lemma elab_compiler_cons_nth_tail cmp ecmp src n m name r
    : nth_error src m = Some (name,r) ->
      match r with
      | sort_rule c _ => 
        exists t et ecmp',
        nth_error cmp n = Some (name,sort_case (map fst c) t) /\
        nth_tail n ecmp = (name, sort_case (map fst c) et)::ecmp' /\
        let ecmp' := (nth_tail (S n) ecmp) in
        elab_preserving_compiler (nth_tail (S n) cmp) ecmp' (nth_tail (S m) src) /\
        elab_sort target (compile_ctx ecmp' c) t et
      | term_rule c _ t =>
        exists e ee ecmp',
        nth_error cmp n = Some (name,term_case (map fst c) e) /\
        nth_tail n ecmp = (name, term_case (map fst c) ee)::ecmp' /\
        let ecmp' := (nth_tail (S n) ecmp) in
        elab_preserving_compiler (nth_tail (S n) cmp) ecmp' (nth_tail (S m) src) /\
        elab_term target (compile_ctx ecmp' c) e ee (compile_sort ecmp' t)
      | sort_eq_rule c t1 t2 =>
        let ecmp' := (nth_tail n ecmp) in
        elab_preserving_compiler (nth_tail n cmp) ecmp' (nth_tail (S m) src)
        /\ eq_sort target (compile_ctx ecmp' c)
                   (compile_sort ecmp' t1)
                   (compile_sort ecmp' t2)
      | term_eq_rule c e1 e2 t => 
        let ecmp' := (nth_tail n ecmp) in
        elab_preserving_compiler (nth_tail n cmp) ecmp' (nth_tail (S m) src)
        /\ eq_term target (compile_ctx ecmp' c)
                   (compile_sort ecmp' t)
                   (compile ecmp' e1)
                   (compile ecmp' e2)
      end ->
      elab_preserving_compiler (nth_tail n cmp) (nth_tail n ecmp) (nth_tail m src).
  Proof.
    destruct r; intros; firstorder;
      repeat match goal with
             |[ H : nth_tail _ _ = _|-_] =>
              rewrite H; rewrite (nth_tail_equals_cons_res _ _ H); clear H
             |[ H : nth_error _ _ = _|-_] =>
              rewrite (nth_tail_to_cons _ _ H); clear H
             end;
      constructor; simpl; basic_utils_crush.
  Qed.

End WithModel.
    
End Extension.


End WithVar.

(*TODO: review how much of the following code is necessary/ put in better places*)

(*TODO: tactics might need fixing up below this line*)
 Ltac t :=
   match goal with
  | [|- fresh _ _ ]=> compute_fresh
  | [|- sublist _ _ ]=> compute_sublist
   (* TODO: if this works, use this pattern for other typeclass occurances *)
   | [|- In _ _ ]=> apply named_list_lookup_err_in with (EqbS_ok := _)
                    ; compute; reflexivity
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => eapply elab_args_cons_ex' || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_var || eapply elab_term_by'
  | [|-wf_term _ _ _ _] => shelve
  | [|-elab_rule _ _ _] => econstructor
  | [|- _ = _] => compute; reflexivity
  end.

  
 Ltac safe_eexists :=
   lazymatch goal with
     [|- exists _,_]=> eexists
   end.
 Ltac elab_compiler_cons:=
 eapply elab_compiler_cons_nth_tail;
 [ compute; reflexivity | cbn beta match; repeat (apply conj || safe_eexists) ].

 Ltac break_preserving :=
   (elab_compiler_cons; try reflexivity; [ break_preserving |..])
   || (compute; apply elab_preserving_compiler_nil).

#[export] Hint Constructors elab_preserving_compiler : lang_core.
#[export] Hint Constructors elab_preserving_compiler : lang_core.
#[export] Hint Resolve elab_compiler_implies_preserving : lang_core.

  
(*
  TODO: remove dependency on Matches or no?
 *)
From Pyrosome.Tools Require Import Matches.

Ltac setup_elab_compiler :=
  match goal with
  | |- elab_preserving_compiler _ ?tgt ?cmp ?ecmp ?src =>
        rewrite (as_nth_tail cmp); rewrite (as_nth_tail ecmp); rewrite (as_nth_tail src);
      assert (wf_lang tgt) by prove_from_known_elabs
  end; break_preserving.

Tactic Notation "cleanup_elab_after" tactic(tc) :=
  unshelve tc; repeat t'; eauto with elab_pfs auto_elab.


Ltac decompose_sort_eq :=
  lazymatch goal with
    |- _ = _ \/ eq_sort _ _ _ _ =>
      first [ left; reflexivity
            | right; compute_eq_compilation; sort_cong ]
  end.

Ltac auto_elab_compiler :=
  cleanup_elab_after setup_elab_compiler;
  repeat ([> repeat Matches.t;
           cleanup_elab_after try (try decompose_sort_eq; solve [ by_reduction ]) |..]).
