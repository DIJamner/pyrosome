(* TODO: move to another place *)
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core
  Compilers.SemanticsPreservingDef
  Compilers.Compilers.
Import Core.Notations.


Inductive star {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| star_refl a : star R a a
| star_step a b c : star R a b -> R b c -> star R a c. 

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
  Notation compiler := (@compiler V term sort).

  Definition rel_sound l R : Prop :=
    forall a b t, wf_term l [] a t -> R t a b -> eq_term l [] t a b.
  
  Section __.
    Context (l : lang).
    Context (step : sort -> term -> term -> Prop).

    Context (wfl : wf_lang l)
      (step_sound : rel_sound l step).

    Lemma step_wf t a b
      : wf_term l [] a t -> step t a b -> wf_term l [] b t.
    Proof.
      intros; eapply eq_term_wf_r; eauto; try typeclasses eauto.
      constructor.
    Qed.

    
    Lemma star_step_wf t a b
      : wf_term l [] a t -> star (step t) a b -> wf_term l [] b t.
    Proof.
      intros H H'; revert H; induction H';
        basic_goal_prep; eauto using step_wf.
    Qed.      
    
    Lemma star_step_sound : rel_sound l (fun t => star (step t)).
    Proof.
      intros a b t Hwf Hstep.
      revert Hwf.
      induction Hstep;
        basic_goal_prep.
      { basic_core_crush. }
      {
        eapply eq_term_trans; eauto using star_step_wf, step_sound.
      }
    Qed.    
    
  End __.

  #[local] Hint Resolve step_wf : lang_core.
  #[local] Hint Resolve star_step_wf : lang_core.
  #[local] Hint Resolve star_step_sound : lang_core.
  
  Context (src tgt : lang) (c : compiler).
  Context (wf_src : wf_lang src)
    (wf_tgt : wf_lang tgt).

  
  
  Notation semantics_preserving cmp :=
    (semantics_preserving (tgt_Model := core_model tgt)
       (compile cmp)
       (compile_sort cmp)
       (compile_ctx cmp)
       (compile_args cmp)
       (compile_subst cmp)).
  
  Context (c_preserving : semantics_preserving c src).
  Context (step_src step_tgt : sort -> term -> term -> Prop).
  Context (src_sound : rel_sound src step_src)
    (tgt_sound : rel_sound tgt step_tgt).

  Context (src_observable_value
             tgt_observable_value : term -> Prop)
    (values_related : term -> term -> Prop).


  Context (tgt_observable_value_injective
            : forall t a b,
              eq_term tgt [] t a b ->
              tgt_observable_value a ->
              tgt_observable_value b ->
              a = b).
  
  Context (values_equal_complete
            : forall t a,
              src_observable_value a ->
              exists b, eq_term tgt [] (compile_sort c t) (compile c a) b
                           /\ tgt_observable_value b
                           /\ values_related a b).
      
  Lemma operational_bridge t a b b'
    : wf_term src [] a t ->
      star (step_src t) a b ->
      star (step_tgt (compile_sort c t)) (compile c a) b' ->
      src_observable_value b ->
      tgt_observable_value b' ->
      values_related b b'.
  Proof.
    intros Hwf HstepS HstepT Hobsb Hobsb'.
    
    eapply values_equal_complete with (t:=t) in Hobsb.
    break.

    eapply tgt_observable_value_injective with (a:=x) in Hobsb'; subst;
      cycle 1.
    {
      eapply eq_term_trans; cycle 1.
      {
        eapply star_step_sound; eauto.
        change [] with (compile_ctx c []).
        eapply c_preserving; eauto with lang_core.
      }
      eapply eq_term_sym.
      eapply eq_term_trans.
      {
        change [] with (compile_ctx c []).
        eapply c_preserving; [|eauto with lang_core].
        eapply star_step_sound; eauto.
      }
      eauto.
    }
    { eauto. }
    eauto.
  Qed.
  
  
End WithVar.
