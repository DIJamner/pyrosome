Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils.
From Named Require Import Exp Rule Core.

Import OptionMonad.


Fixpoint wf_term_no_conv l c e {struct e} : option sort :=
  match e with
  | var x => named_list_lookup_err c x
  | con n s =>
    let wf_args_no_conv := fix wf_args_no_conv s c' {struct s} : option unit :=
       match s, c' with
       | [::], [::] => do ret tt
       | e::s', (n,t)::c'' =>
         do t0 <- wf_term_no_conv l c e;
         !t0 == t[/with_names_from c'' s'/];
         !wf_args_no_conv s' c'';
         ret tt
       | _,_ => None
       end in
    do term_rule c' t <- named_list_lookup_err l n;
    !wf_args_no_conv s c';
    ret t[/with_names_from c' s/]
end.

Fixpoint wf_args_no_conv l (c : ctx) s c' {struct s} : option unit :=
       match s, c' with
       | [::], [::] => do ret tt
       | e::s', (n,t)::c'' =>
         do t0 <- wf_term_no_conv l c e;
         !t0 == t[/with_names_from c'' s'/];
         !wf_args_no_conv l c s' c'';
         ret tt
       | _,_ => None
       end.

(* gets rid of the interior duplicate fixpoint*)
Lemma unfold_wf_term_no_conv l c e
  : wf_term_no_conv l c e
    =  match e with
  | var x => named_list_lookup_err c x
  | con n s =>
    do term_rule c' t <- named_list_lookup_err l n;
    !wf_args_no_conv l c s c';
    ret t[/with_names_from c' s/]
end.
Proof using .
  case: e; simpl; auto.
  intros.
  remember (named_list_lookup_err l s) as nlll.
  destruct nlll;[| done].
  destruct r; auto.
  match goal with
    [ |- match isSome ?a with _ => _ end = match isSome ?b with _ => _ end]=>
    suff: (a = b) => [-> //|]
  end.
  clear Heqnlll.
  elim: l0 c0; auto; intros until c0; case: c0; intros; break; simpl in *; auto.
  rewrite H.
  done.
Qed.  
  

Definition wf_sort_no_conv l c t : option unit :=
  match t with
  | scon n s =>
    do sort_rule c' <- named_list_lookup_err l n;
    _ <- wf_args_no_conv l c s c';
    ret tt
  end.
      
Lemma wf_term_no_conv_recognizes l c e t
  : wf_term_no_conv l c e = Some t -> wf_term l c e t.
Proof using .
  elim: e t.
  {
    intros; simpl in *.
    constructor.
    by apply named_list_lookup_err_in.
  }
  {
    intros n s IH t.
    rewrite unfold_wf_term_no_conv.
    remember (named_list_lookup_err l n) as nlll.
    destruct nlll;[| by inversion].
    destruct r;try by inversion.
    match goal with
      [ |- context[if isSome ?e then _ else _]] =>
      remember e as wfa
    end.
    destruct wfa; simpl; try by inversion.
    case => <-.
    constructor.
    {
        by apply named_list_lookup_err_in.
    }
    {
      destruct u.
      move: Heqwfa.
      (*duplicate proof of wf_args_no_conv_recognizes*)
      clear Heqnlll. 
      elim: s c0 IH; intros until c0; case: c0;
        intro_to (@eq (option unit));[constructor | inversion | inversion|].
      destruct a0.
      simpl in *; break.
      remember (wf_term_no_conv l c a) as wft.
      destruct wft;[|inversion].
      specialize (H0 s2 ).
      case s2eq: (s2 == sort_subst (with_names_from l1 l0) s1);[|inversion].
      move: s2eq => /eqP s2eq.
      subst.
      match goal with
        [ |- context[if isSome ?e then _ else _]] =>
        remember e as wfa
      end.
      destruct wfa; [destruct u|];inversion.
      constructor; simpl; auto.
    }
  }
Qed.

Lemma wf_args_no_conv_recognizes l c s c'
  : wf_args_no_conv l c s c' = Some tt -> wf_args l c s c'.
Proof.
  elim: s c'; intros until c'; case: c';
    intro_to (@eq (option unit));[constructor | inversion | inversion|];
      break; simpl in *; break.
      remember (wf_term_no_conv l c a) as wft.
      destruct wft;[|inversion].
      case s1eq: (s1 == sort_subst (with_names_from l1 l0) s0);[|inversion].
      move: s1eq => /eqP s1eq.
      subst.
      match goal with
        [ |- context[if isSome ?e then _ else _]] =>
        remember e as wfa
      end.
      destruct wfa; [destruct u|];inversion.
      constructor; simpl; auto using wf_term_no_conv_recognizes.
Qed.

Ltac monad_case e :=
  let H := fresh in
  remember e as H;
  destruct H;[| by inversion].
                  
Lemma wf_sort_no_conv_recognizes l c t
  : wf_sort_no_conv l c t = Some tt -> wf_sort l c t.
Proof using .
  destruct t; simpl.
  monad_case (named_list_lookup_err l s).
  destruct r; try by inversion.
  monad_case (wf_args_no_conv l c l0 c0).
  econstructor.
  {
    apply named_list_lookup_err_in.
    symmetry.
    eassumption.
  }
  {
    apply wf_args_no_conv_recognizes.
    symmetry.
    destruct u.
    done.
  }
Qed.


(*
(* general pattern here:
   - a little interaction-tree-like
   - have recognizer work in option monad + reader monad
   - TODO: good labelling for cases; is a string enough for interactive proving?
*)
Inductive elab_recognizer_output (A : Set) : Set :=
| elab_out : A -> elab_recognizer_output A
| fail_elab : elab_recognizer_output A 
| infer_term
    (* context to help the user know what's going on *)
  : IExp.exp (* expression one level up the AST *) ->
    sort (* sort of the expression *) ->
    string (* name of argument*) ->
    (*expects a wf term and its sort *)
    (exp -> sort -> elab_recognizer_output A) -> elab_recognizer_output A
(* TODO: would it be useful to specialize this to conversion? *)
| infer_conv
    (* context to help the user know what's going on *)
  : exp (* expression to convert *) ->
    sort (* sort to convert to *) ->
    (*expects a wf sort *)
    (sort -> elab_recognizer_output A) -> elab_recognizer_output A .
 (* TODO: how do I frame correctness? it's a 2-party kind of thing here *)

Inductive correct_out_exp l c :exp -> elab_recognizer_output -> Prop :=
| elab_out_correct
  : forall e t, elab_term l c e t -> elab_out_correct l c e (elab_out t)
| infer_term_correct
  : forall e' out e t,
    elab_term l c e t ->
    elab_out_correct l c e' (out t) ->
    elab_out_correct l c e (infter_term )
| 

Definition oracle A out := {f: elab_recognizer_output A -> A | wf (f out)}.

*)