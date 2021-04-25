Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers SimpleVSTLC Matches.
Import Core.Notations.

Require Coq.derive.Derive.

Definition stlc_bot :=
  ([:| 
      -----------------------------------------------
      #"bot" : #"ty"
  ])%arule:: stlc.



Derive stlc_bot_elab
       SuchThat (elab_lang stlc_bot stlc_bot_elab)
       As stlc_bot_wf.
Proof.
  auto_elab.
  Unshelve.
  all: cleanup_auto_elab.
Qed.


(*
Definition twkn g a b := {{#"ty_subst"(#"ext"(g,a),g,#"wkn"(g,a),b)}}.
Definition ewkn g a b e := {{#"el_subst"(#"ext"(g,a),g,#"wkn"(g,a),b,e)}}.*)
Fixpoint wkn_n n :=
  match n with
  | 0 => {{e #"id"}}
  | S n' =>
    {{e #"cmp" #"wkn" {wkn_n n'} }}
  end.

Fixpoint vwkn_n n e :=
  match n with
  | 0 => e
  | S n' =>
    {{e #"val_subst" #"wkn" {vwkn_n n' e} }}
  end.

(*n is how many wknings to do on e*)
Definition bind_k n e A k :=
  {{e #"el_subst" (#"snoc" {wkn_n n} (#"lambda" {A} {k})) {e} }}.
Arguments bind_k n e A k/.

Definition ret_val v :=
  {{e #"app" (#"ret" #"hd") (#"ret" {vwkn_n 1 v})}}.

Definition double_neg t : exp :=
  {{e #"->" (#"->" {t} #"bot") #"bot"}}.
Arguments double_neg t /.

Definition get_rule_args r :=
  match r with
  | sort_rule _ args => args
  | term_rule _ args _ => args
  | sort_eq_rule c _ _ => map fst c
  | term_eq_rule c _ _ _ => map fst c
  end.

Definition lookup_args l n :=
  get_rule_args ( named_list_lookup (ARule.sort_rule [] []) l n).

Definition cps_sort (c:string) args : sort :=
  match c, args with
  | "el", [A; G] =>
    {{s #"el" (#"ext" %G (#"->" %A #"bot")) #"bot" }}
  | _,_ => scon c (map var (lookup_args stlc c))
  end%string.
Definition cps (c : string) (args : list string) : exp :=
  match c, args with
  | "->", [B; A] =>
    {{e #"->" %A {double_neg (var B)} }}
  | "lambda", [e; B; A; G] =>
    {{e #"lambda" %A (#"ret" (#"lambda" (#"->" %B #"bot") %e))}}
  | "app", [e2; e1; B; A; G] =>
    let k := {{e #"ret" {vwkn_n 2 {{e #"hd"}} } }} in
    let x1 := {{e #"ret" {vwkn_n 1 {{e #"hd"}} } }} in
    let x2 := {{e #"ret" #"hd"}} in
    bind_k 1 (var e1) {{e #"->" %A {double_neg (var B)} }}
    (bind_k 2 (var e2) (var A)
    {{e #"app" (#"app" {x1} {x2}) {k} }})
  | "el_subst", [e; A; g; G'; G] =>
    {{e #"el_subst" (#"snoc" (#"cmp" #"wkn" %g) #"hd") %e }}
  (*| "hd", [:: A] =>
    ret_val {{e #"hd"}} (var A)*)
  | "ret", [v; A; G] =>
    ret_val (var v)
  | _,_ => con c (map var (lookup_args stlc c))
  end%string.

(*TODO: move to compiler elab or compilers
  TODO: revise; can be better now that arg names
  are in the compiler
*)
(*Note: args not helpful*)
Fixpoint make_compiler
           (cmp_sort : string -> list string -> sort)
           (cmp_exp : string -> list string -> exp)
           (l : lang) : compiler :=
  match l with
  | (n,sort_rule c args)::l' =>
    (n,sort_case (map fst c) (cmp_sort n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,term_rule c args _)::l' => (n,term_case (map fst c) (cmp_exp n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | _::l' => 
    (make_compiler cmp_sort cmp_exp l')
  | [] => []
  end.


Definition comp :=
  Eval compute in (make_compiler cps_sort cps (nth_tail 0 stlc)).

(*TODO: move to utils*)
Lemma nth_error_nil A n : @nth_error A [] n = None.
Proof.
  destruct n; simpl; auto.
Qed.
Hint Rewrite nth_error_nil : utils.

(*TODO: move to utils*)
Lemma nth_tail_to_cons A l n (x:A)
  : nth_error l n = Some x ->
    nth_tail n l = x::(nth_tail (S n) l).
Proof.
  revert l; induction n; destruct l;
    basic_goal_prep; basic_utils_crush.
Qed.

Lemma nth_tail_equals_cons_res A n l l' (x:A)
  : nth_tail n l = x :: l' -> l' = nth_tail (S n) l.
Proof.
  revert l l'; induction n; destruct l;
    basic_goal_prep; basic_utils_crush.
  cbv in H; inversion H; subst.
  reflexivity.
Qed.
  
      
Lemma elab_compiler_cons_nth_tail tgt cmp ecmp src n m name r
  : nth_error src m = Some (name,r) ->
    match r with
    | sort_rule c _ => 
      exists t et ecmp',
      nth_error cmp n = Some (name,sort_case (map fst c) t) /\
      nth_tail n ecmp = (name, sort_case (map fst c) et)::ecmp' /\
      let ecmp' := (nth_tail (S n) ecmp) in
      elab_preserving_compiler tgt (nth_tail (S n) cmp) ecmp' (nth_tail (S m) src) /\
      elab_sort tgt (compile_ctx ecmp' c) t et
    | term_rule c _ t =>
      exists e ee ecmp',
      nth_error cmp n = Some (name,term_case (map fst c) e) /\
      nth_tail n ecmp = (name, term_case (map fst c) ee)::ecmp' /\
      let ecmp' := (nth_tail (S n) ecmp) in
      elab_preserving_compiler tgt (nth_tail (S n) cmp) ecmp' (nth_tail (S m) src) /\
      elab_term tgt (compile_ctx ecmp' c) e ee (compile_sort ecmp' t)
    | sort_eq_rule c t1 t2 =>
      let ecmp' := (nth_tail n ecmp) in
      elab_preserving_compiler tgt (nth_tail n cmp) ecmp' (nth_tail (S m) src)
      /\ eq_sort tgt (compile_ctx ecmp' c)
                  (compile_sort ecmp' t1)
                  (compile_sort ecmp' t2)
    | term_eq_rule c e1 e2 t => 
      let ecmp' := (nth_tail n ecmp) in
      elab_preserving_compiler tgt (nth_tail n cmp) ecmp' (nth_tail (S m) src)
      /\ eq_term tgt (compile_ctx ecmp' c)
                  (compile_sort ecmp' t)
                  (compile ecmp' e1)
                  (compile ecmp' e2)
    end ->
    elab_preserving_compiler tgt (nth_tail n cmp) (nth_tail n ecmp) (nth_tail m src).
Proof.
  destruct r; intros; firstorder;
    repeat match goal with
    |[ H : nth_tail _ _ = _|-_] =>
     rewrite H; rewrite (nth_tail_equals_cons_res _ _ H); clear H
    |[ H : nth_error _ _ = _|-_] =>
     rewrite (nth_tail_to_cons _ _ H); clear H
           end;
    constructor; basic_utils_crush.
Qed.



  Local Ltac t :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> apply named_list_lookup_err_in; compute; reflexivity
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => eapply elab_args_cons_ex' || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_var || eapply elab_term_by'
  | [|-wf_term _ _ _ _] => shelve
  | [|-elab_rule _ _ _] => econstructor
  | [|- _ = _] => compute; reflexivity
  end.

  

  Ltac elab_compiler_cons :=
    eapply elab_compiler_cons_nth_tail;
    [ compute; reflexivity
    | cbn match beta; repeat (split || eexists)].

  Ltac auto_elab_compiler :=
  match goal with
  | [|- elab_preserving_compiler _ ?cmp ?ecmp ?src] =>
  rewrite (as_nth_tail cmp);
  rewrite (as_nth_tail ecmp);
  rewrite (as_nth_tail src);
  repeat (elab_compiler_cons || (compute; apply elab_preserving_compiler_nil));
  try solve [repeat t]
  (*break_down_elab_lang;
  solve[repeat t] TODO*)
  end.

  Ltac compute_eq_compilation :=
    match goal with
    |[|- eq_sort ?l ?ctx ?t1 ?t2] =>
     let ctx' := eval compute in ctx in
     let t1' := eval compute in t1 in
     let t2' := eval compute in t2 in
     change (eq_sort l ctx' t1' t2')
    |[|- eq_term ?l ?ctx ?e1 ?e2 ?t] =>
     let ctx' := eval compute in ctx in
     let e1' := eval compute in e1 in
     let e2' := eval compute in e2 in
     let t' := eval compute in t in
     change (eq_term l ctx' e1' e2' t')
    end.


  
(*TODO: optimize where this is used so that I don't
  duplicate work?
*)
Local Ltac t' :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> solve_in
  | [|- wf_term _ _ _ _] => assumption || eapply wf_term_var || eapply wf_term_by'
  | [|-wf_args _ _ _ _] => simple apply wf_args_nil
                           || simple eapply wf_args_cons2
                           || simple eapply wf_args_cons
  | [|-wf_subst _ _ _ _] => constructor
  | [|-wf_ctx _ _] => assumption || constructor
  | [|- wf_sort _ _ _] => eapply wf_sort_by
  | [|- wf_lang _] => lookup_wf_lang
  | [|- _ = _] => compute; reflexivity
  end.




Lemma cps_beta_preserved :
eq_term stlc_bot_elab
    {{c"G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e"
       : # "el" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         #"bot",
       "e'" : # "el" (# "ext" %"G" (# "->" %"A" #"bot")) #"bot",
       "G'" : #"env",
       "g" : # "sub" %"G'" %"G"}} {{s# "el" (# "ext" %"G'" (# "->" %"B" #"bot")) #"bot"}}
    {{e# "el_subst" (# "ext" %"G'" (# "->" %"B" #"bot")) (# "ext" %"G" (# "->" %"B" #"bot"))
       (# "snoc" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G" (# "->" %"B" #"bot")
        (# "cmp" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'" %"G"
         (# "wkn" %"G'" (# "->" %"B" #"bot")) %"g") (# "hd" %"G'" (# "->" %"B" #"bot"))) #"bot"
       (# "el_subst" (# "ext" %"G" (# "->" %"B" #"bot"))
        (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "snoc" (# "ext" %"G" (# "->" %"B" #"bot")) %"G"
         (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
         (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G" (# "wkn" %"G" (# "->" %"B" #"bot"))
          (# "id" %"G"))
         (# "lambda" (# "ext" %"G" (# "->" %"B" #"bot"))
          (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
          (# "el_subst"
           (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
            (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G" (# "->" %"A" #"bot"))
           (# "snoc"
            (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"G" (# "->" %"A" #"bot")
            (# "cmp"
             (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
              (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
             (# "ext" %"G" (# "->" %"B" #"bot")) %"G"
             (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
              (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
             (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G"
              (# "wkn" %"G" (# "->" %"B" #"bot")) (# "id" %"G")))
            (# "lambda"
             (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
              (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A" #"bot"
             (# "app"
              (# "ext"
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
              # "->" %"B" #"bot") #"bot"
              (# "app"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
               (# "->" (# "->" %"B" #"bot") #"bot")
               (# "ret"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                (# "val_subst"
                 (# "ext"
                  (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                   (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                 (# "wkn"
                  (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                   (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                 (# "hd" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))))
               (# "ret"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
                (# "hd"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")))
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
               # "->" %"B" #"bot")
               (# "val_subst"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "wkn"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
                # "->" %"B" #"bot")
                (# "val_subst"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                 (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "->" %"B" #"bot")
                 (# "hd" %"G" (# "->" %"B" #"bot")))))))) #"bot" %"e'"))) #"bot" %"e")}}
    {{e# "el_subst" (# "ext" %"G'" (# "->" %"B" #"bot"))
       (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
       (# "snoc" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'"
        (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
        (# "cmp" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'" %"G'"
         (# "wkn" %"G'" (# "->" %"B" #"bot")) (# "id" %"G'"))
        (# "lambda" (# "ext" %"G'" (# "->" %"B" #"bot"))
         (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
         (# "el_subst"
          (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
           (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G'" (# "->" %"A" #"bot"))
          (# "snoc"
           (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
            (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"G'" (# "->" %"A" #"bot")
           (# "cmp"
            (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
            (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'"
            (# "wkn" (# "ext" %"G'" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
            (# "cmp" (# "ext" %"G'" (# "->" %"B" #"bot")) %"G'" %"G'"
             (# "wkn" %"G'" (# "->" %"B" #"bot")) (# "id" %"G'")))
           (# "lambda"
            (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A" #"bot"
            (# "app"
             (# "ext"
              (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
             # "->" %"B" #"bot") #"bot"
             (# "app"
              (# "ext"
               (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
              (# "->" (# "->" %"B" #"bot") #"bot")
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
               (# "val_subst"
                (# "ext"
                 (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "wkn"
                 (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                (# "hd" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))))
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
               (# "hd"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")))
             (# "ret"
              (# "ext"
               (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
              # "->" %"B" #"bot")
              (# "val_subst"
               (# "ext"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
               (# "wkn"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
               # "->" %"B" #"bot")
               (# "val_subst"
                (# "ext" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "ext" %"G'" (# "->" %"B" #"bot"))
                (# "wkn" (# "ext" %"G'" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "->" %"B" #"bot")
                (# "hd" %"G'" (# "->" %"B" #"bot")))))))) #"bot"
          (# "el_subst" (# "ext" %"G'" (# "->" %"A" #"bot")) (# "ext" %"G" (# "->" %"A" #"bot"))
           (# "snoc" (# "ext" %"G'" (# "->" %"A" #"bot")) %"G" (# "->" %"A" #"bot")
            (# "cmp" (# "ext" %"G'" (# "->" %"A" #"bot")) %"G'" %"G"
             (# "wkn" %"G'" (# "->" %"A" #"bot")) %"g") (# "hd" %"G'" (# "->" %"A" #"bot"))) #"bot"
           %"e'")))) #"bot"
       (# "el_subst"
        (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "snoc" (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
         (# "cmp" (# "ext" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
          %"G'" %"G"
          (# "wkn" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")) %"g")
         (# "hd" %"G'" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))) #"bot"
        %"e")}}.
Proof.
Admitted.
(*  pose proof (elab_lang_implies_wf stlc_bot_wf).
  solve[by_reduction].
  Unshelve.
  all: repeat t'.
Qed.
*)

Lemma cps_subst_preserved
  : eq_term stlc_bot_elab
    {{c"G" : #"env",
       "A" : #"ty",
       "B" : #"ty",
       "e" : # "el" (# "ext" (# "ext" %"G" %"A") (# "->" %"B" #"bot")) #"bot",
       "v" : # "val" %"G" %"A"}} {{s# "el" (# "ext" %"G" (# "->" %"B" #"bot")) #"bot"}}
    {{e# "el_subst" (# "ext" %"G" (# "->" %"B" #"bot"))
       (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
       (# "snoc" (# "ext" %"G" (# "->" %"B" #"bot")) %"G"
        (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
        (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G" (# "wkn" %"G" (# "->" %"B" #"bot"))
         (# "id" %"G"))
        (# "lambda" (# "ext" %"G" (# "->" %"B" #"bot"))
         (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
         (# "el_subst"
          (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
           (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G" (# "->" %"A" #"bot"))
          (# "snoc"
           (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
            (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"G" (# "->" %"A" #"bot")
           (# "cmp"
            (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "ext" %"G" (# "->" %"B" #"bot"))
            %"G"
            (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
            (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" %"G"
             (# "wkn" %"G" (# "->" %"B" #"bot")) (# "id" %"G")))
           (# "lambda"
            (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
             (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A" #"bot"
            (# "app"
             (# "ext"
              (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
             # "->" %"B" #"bot") #"bot"
             (# "app"
              (# "ext"
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
              (# "->" (# "->" %"B" #"bot") #"bot")
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
               (# "val_subst"
                (# "ext"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "wkn"
                 (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                  (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
                (# "hd" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))))
              (# "ret"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") %"A"
               (# "hd"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")))
             (# "ret"
              (# "ext"
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
              # "->" %"B" #"bot")
              (# "val_subst"
               (# "ext"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A")
               (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
               (# "wkn"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) %"A") (
               # "->" %"B" #"bot")
               (# "val_subst"
                (# "ext" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")))
                (# "ext" %"G" (# "->" %"B" #"bot"))
                (# "wkn" (# "ext" %"G" (# "->" %"B" #"bot"))
                 (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))) (# "->" %"B" #"bot")
                (# "hd" %"G" (# "->" %"B" #"bot")))))))) #"bot"
          (# "app" (# "ext" %"G" (# "->" %"A" #"bot")) %"A" #"bot"
           (# "ret" (# "ext" %"G" (# "->" %"A" #"bot")) (# "->" %"A" #"bot")
            (# "hd" %"G" (# "->" %"A" #"bot")))
           (# "ret" (# "ext" %"G" (# "->" %"A" #"bot")) %"A"
            (# "val_subst" (# "ext" %"G" (# "->" %"A" #"bot")) %"G"
             (# "wkn" %"G" (# "->" %"A" #"bot")) %"A" %"v")))))) #"bot"
       (# "app" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
        (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"
        (# "ret" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")
         (# "hd" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")))
        (# "ret" (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
         (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
         (# "val_subst"
          (# "ext" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot")) %"G"
          (# "wkn" %"G" (# "->" (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot")) #"bot"))
          (# "->" %"A" (# "->" (# "->" %"B" #"bot") #"bot"))
          (# "lambda" %"G" %"A" (# "->" (# "->" %"B" #"bot") #"bot")
           (# "ret" (# "ext" %"G" %"A") (# "->" (# "->" %"B" #"bot") #"bot")
            (# "lambda" (# "ext" %"G" %"A") (# "->" %"B" #"bot") #"bot" %"e"))))))}}
    {{e# "el_subst" (# "ext" %"G" (# "->" %"B" #"bot"))
       (# "ext" (# "ext" %"G" %"A") (# "->" %"B" #"bot"))
       (# "snoc" (# "ext" %"G" (# "->" %"B" #"bot")) (# "ext" %"G" %"A") (
        # "->" %"B" #"bot")
        (# "cmp" (# "ext" %"G" (# "->" %"B" #"bot")) %"G" (# "ext" %"G" %"A")
         (# "wkn" %"G" (# "->" %"B" #"bot")) (# "snoc" %"G" %"G" %"A" (# "id" %"G") %"v"))
        (# "hd" %"G" (# "->" %"B" #"bot"))) #"bot" %"e"}}.
Proof.
Admitted.
(*  pose proof (elab_lang_implies_wf stlc_bot_wf).
  solve[by_reduction].
  Unshelve.
  all: repeat t'.
Qed. *)
  

Derive cps_elab
       SuchThat (elab_preserving_compiler stlc_bot_elab comp cps_elab stlc_elab)
       As cps_elab_preserving.
Proof.
  pose proof (elab_lang_implies_wf stlc_bot_wf).
  auto_elab_compiler; compute_eq_compilation.
  (*all: try solve [is_term_rule].*)
  solve[by_reduction].
  solve[by_reduction].
  solve[by_reduction].
  apply cps_subst_preserved.
  apply cps_beta_preserved.
  solve[by_reduction].
  Unshelve.
  all: repeat t'.
Qed.

Goal semantics_preserving stlc_bot_elab cps_elab stlc_elab.
Proof.
  apply inductive_implies_semantic.
  - eapply elab_lang_implies_wf; apply stlc_wf.
  - eapply elab_lang_implies_wf; apply stlc_bot_wf.
  -  eauto using cps_elab_preserving with lang_core.
Qed.
