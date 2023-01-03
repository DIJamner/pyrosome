Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Import Numbers.DecimalNat Numbers.DecimalString.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.

From bedrock2 Require Import Syntax Semantics.

From Utils Require Import Utils.
From Named Require Import Substable Model GeneralModel Term Rule Core CompilerDefs.
Import Core.Notations.


Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).
Print exec.exec.
Context (width : BinNums.Z)
        (word : Interface.word.word width)
        (key := Interface.word.rep (width := width))
        (value := Init.Byte.byte : Type)
        (mem : Interface.map.map key value)
        (locals : Interface.map.map string (Interface.word.rep (width := width)))
        (env : Interface.map.map string (list string * list string * cmd))
        (m : Interface.map.rep (key := key) (value := value) (map := mem))
        (l : Interface.map.rep (key := string) (value := key) (map := locals))
        (BW : Bitwidth.Bitwidth width)
        (ext_spec : ExtSpec)
        (e : Interface.map.rep (key := string) (value := list string * list string * cmd) (map := env)).



(* This the the `term` type that should get plugged into the general model.
   We'll be adding a few more sorts later, but this is good for now.
   If you see an `access_size` just assume it is `word` for the moment,
   and if you see a bopname, assume it is `add`.
   The general model that you've been developing is well-suited for simple sorts
   (i.e. sorts that don't contain terms) and my current thinking is that
   we might want to specialize it to this case since it's a common one and
   will make most of the proofs we do easier.
   We can leave that for later though.

   For now, it would be helpful to look at the syntax of bedrock programs
   and start thinking about how to most easily fit it to the general model.
   We'll also need a Pyrosome encoding of bedrock at some point,
   although I wouldn't worry about completeness there any time soon.
 *)

(* this *)
Variant bedrock_exp :=
  | bedrock_expr (e : expr)
  | bedrock_cmd (c : cmd)
  | bedrock_nat (n : nat).

(* Variant br_expr : Set := *)
(*   | br_expr_tt. *)
(* Variant br_cmd : Set := *)
(*   | br_cmd_tt. *)
(* Variant br_nat : Set := *)
(*   | br_nat_tt. *)

(* Variant bedrock_sort := *)
(*   | br_expr_srt *)
(*   | br_cmd_srt *)
(*   | br_nat_srt. *)



Notation bedrock_term := (GeneralModel.term (V := string) bedrock_exp).

(* This is just a copy of the lang in NatLang.v, temporarily
   placed here while Elab and a few other files are broken. *)
Definition nat_lang_def : lang := 
  {[l
  [s|
      -----------------------------------------------
      #"natural" srt
  ];
  [:|  
       -----------------------------------------------
       #"0" : #"natural"
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"1+" "n" : #"natural"
  ];
  [:|
       "a" : #"natural",
       "b" : #"natural" 
       -----------------------------------------------
       #"plus" "a" "b" : #"natural"
  ]
  (* [:= *)
  (*      "a" : #"natural" *)
  (*      ----------------------------------------------- ("plus_0") *)
  (*      #"plus" "a" #"0" = "a" : #"natural" *)
  (* ]; *)
  (* [:= *)
  (*      "a" : #"natural", *)
  (*      "b" : #"natural" *)
  (*      ----------------------------------------------- ("plus_1+") *)
  (*      #"plus" "a" (#"1+" "b") = #"plus" (#"1+" "a") "b" : #"natural" *)
  (* ] *)
    ]}.


Definition bedrock_subset_def : lang :=
  {[l
      [s|
      -----------------------------------------------
        #"expr" srt
      ];
    [:| "n" : #"natural"
      -----------------------------------------------
      #"literal" "n" : #"expr"
    ];
    [:| "n" : #"natural"
      -----------------------------------------------
      #"var" "n" : #"expr"
    ];
    [s|
      -----------------------------------------------
      #"cmd" srt
      ];
    [:|
       -----------------------------------------------
      #"skip" : #"cmd"
    ];
    [:|
        "lhs" : #"natural",
        "rhs" : #"expr"
        -----------------------------------------------
      #"set" "lhs" "rhs" : #"cmd"
    ];
    [:|
        "s1" : #"cmd",
        "s2" : #"cmd"
      -----------------------------------------------
     #"seq" "s1" "s2" : #"cmd"
    ];
    [:| "test" : #"expr",
        "body" : #"cmd"
      -----------------------------------------------
      #"while" "test" "body" : #"cmd"
    ]
    ]}.
     (* Add a few (1-2) interesting equalities from the original language *)


Local Notation compiler := (compiler string (tgt_term := bedrock_term) (tgt_sort := Type)).

Definition nat_to_string (n : nat) := NilZero.string_of_uint (Decimal.rev (Unsigned.to_lu n)).

Definition default_cmd : bedrock_exp := bedrock_cmd cmd.skip.
Definition default_expr : bedrock_exp := bedrock_expr (expr.literal BinNums.Z0).

Definition with_nat name ms f : bedrock_exp :=
  match named_list_lookup default_expr ms name with
  | bedrock_nat z => f z
  | _ => default_cmd
  end.

Definition with_cmd name ms f : bedrock_exp :=
  match named_list_lookup default_expr ms name with
  | bedrock_cmd c => f c
  | _ => default_cmd
  end.

Definition with_expr name ms f : bedrock_exp :=
  match named_list_lookup default_cmd ms name with
  | bedrock_expr e => f e
  | _ => default_cmd
  end.

Definition literal_term (n_str : string) : bedrock_term :=
  fun ms =>
    with_nat n_str ms (fun n =>
    bedrock_expr (expr.literal (BinInt.Z.of_nat n))).

Definition var_term n_str : bedrock_term :=
  fun ms =>
    with_nat n_str ms (fun n =>
    bedrock_expr (expr.var (nat_to_string n))).

Definition set_term lhs_str rhs_str : bedrock_term :=
  fun ms =>
    with_nat lhs_str ms (fun lhs =>
    with_expr rhs_str ms (fun rhs =>
    bedrock_cmd (cmd.set (nat_to_string lhs) rhs))).

Definition seq_term s1_str s2_str : bedrock_term :=
  fun ms =>
    with_cmd s1_str ms (fun s1 =>
    with_cmd s2_str ms (fun s2 =>
    bedrock_cmd (cmd.seq s1 s2))).

Definition while_term (t_str b_str : string) : bedrock_term :=
  fun ms =>
    with_expr t_str ms (fun test =>
    with_cmd b_str ms (fun body =>
    bedrock_cmd (cmd.while test body))).

Definition succ_term (n_str : string) : bedrock_term :=
  fun ms =>
    with_nat n_str ms (fun n =>
    bedrock_nat (S n)).

Definition plus_term (a_str b_str : string) : bedrock_term :=
  fun ms =>
    with_nat a_str ms (fun a =>
    with_nat b_str ms (fun b =>
    bedrock_nat (a + b))).


Notation eval_expr_old := (eval_expr_old (width := width) (mem := mem) (locals := locals) m l).
Notation exec_exec := (exec.exec (width := width) (BW := BW) (word := word) (mem := mem)
                                 (locals := locals) (env := env) (ext_spec := ext_spec) e).

Definition eq_exp (e1 e2 : bedrock_exp) :=
  match e1, e2 with
  | bedrock_expr e1', bedrock_expr e2' => eval_expr_old e1' = eval_expr_old e2'
  | bedrock_cmd c1, bedrock_cmd c2 => forall tr r1 r2 ml f, exec_exec c1 tr r1 r2 ml f <-> exec_exec c2 tr r1 r2 ml f
  | bedrock_nat n1, bedrock_nat n2 => n1 = n2
  | _, _ => False
  end.


Definition wf_exp (e : bedrock_exp) (t : Type) :=
    match e with
    | bedrock_cmd _ => t = cmd
    | bedrock_expr _ => t = expr
    | bedrock_nat _ => t = nat
    end.

Lemma exp_refl : forall e, eq_exp e e.
Proof.
  intros; destruct e0; unfold eq_exp; try constructor; intros; try trivial.
Qed.

Lemma exp_trans : forall e1 e2 e3, eq_exp e1 e2 -> eq_exp e2 e3 -> eq_exp e1 e3.
Proof.
  intros; destruct e1, e2, e3; unfold eq_exp in *; try contradiction.
  {rewrite H; trivial.}
  {constructor; specialize (H tr r1 r2 ml f); specialize (H0 tr r1 r2 ml f); destruct H, H0; intros; trivial.
   - apply H0; apply H; trivial.
   - apply H1; apply H2; trivial.
  }
  {rewrite H; trivial.}
Qed.

Lemma exp_symm : forall e1 e2, eq_exp e1 e2 -> eq_exp e2 e1.
Proof.
  intros; destruct e1, e2; unfold eq_exp in *; try contradiction; auto.
  constructor; specialize (H tr r1 r2 ml f); destruct H; trivial.
Qed.

Definition bedrock_model := GeneralModel.model (exp := bedrock_exp) default_cmd eq_exp wf_exp.
Definition bedrock_model_ok : Model.Model_ok bedrock_model :=
  GeneralModel.model_ok default_cmd eq_exp exp_symm exp_trans exp_refl wf_exp.

Definition bedrock_subset_compiler : compiler :=
  [
    ("while", term_case ["body"; "test"] (while_term "test" "body"));
    ("seq", term_case ["s2"; "s1"] (seq_term "s1" "s2"));
    ("set", term_case ["rhs"; "lhs"] (set_term "lhs" "rhs"));
    ("skip", term_case [] (fun _ => bedrock_cmd cmd.skip));
    ("cmd", sort_case [] (cmd : Type));
    ("var", term_case ["n"] (var_term "n"));
    ("literal", term_case ["n"] (literal_term "n"));
    ("expr", sort_case [] (expr : Type));
    ("plus", term_case ["b"; "a"] (plus_term "a" "b"));
    ("1+", term_case ["n"] (succ_term "n"));
    ("0", term_case [] (fun _ => bedrock_nat 0));
    ("natural", sort_case [] (nat : Type))
  ].

Definition example1 :=
  {{e #"seq" (#"while" (#"literal" #"0") (#"set" (#"1+" #"0") (#"literal" (#"1+" (#"1+" #"0"))))) (#"set" #"0" (#"var" #"0"))}}.

Definition example2 :=
  {{e #"while" (#"literal" #"0") (#"set" #"0" (#"literal" #"0"))}}.

Print compile.
Notation compile :=
  (compile (V := string) (V_Eqb := string_Eqb)
           (tgt_term := bedrock_term) (H := fun _ => default_expr)
           (tgt_Model := bedrock_model) bedrock_subset_compiler).

Definition compiled_example :=
  compile example1.

Compute (compiled_example).

Ltac break_preserving_compiler :=
  unfold bedrock_subset_compiler, bedrock_subset_def, nat_lang_def; simpl;
  repeat match goal with
         | [ |- preserving_compiler_ext _ _ ((_, term_rule ?c' _ _) :: _)] =>
             apply preserving_compiler_term with (c := c')
         | [ |- preserving_compiler_ext _ _ ((_, sort_rule ?c' _) :: _)] =>
             apply preserving_compiler_sort with (c := c')
         | [ |- preserving_compiler_ext _ [] []] =>
             apply preserving_compiler_nil
  end.

Ltac bedrock_crush :=
  unfold Model.wf_sort; simpl;
  unfold GeneralModel.wf_sort, GeneralModel.wf_term, GeneralModel.ws_term; simpl;
  try trivial;
  repeat match goal with
         | [ |- _ /\ _] => apply conj
         | [ |- NoDup []] => apply NoDup_nil
         | [ |- NoDup (_ :: _)] => apply NoDup_cons
         | [ |- ~ _] => unfold not
         | _ => idtac
         end;
  simpl; try trivial.

Theorem bedrock_compiler_preserving :
  preserving_compiler_ext (tgt_Model := bedrock_model) (H := fun _ => default_expr)
                          (H0 := nat) [] bedrock_subset_compiler (bedrock_subset_def ++ nat_lang_def).
Proof.
  break_preserving_compiler;
  bedrock_crush.
  1: {intros.
      unfold eq_exp, succ_term, with_nat.

  }
  
(*
  TODO:
  Describe project in text for other people to look at and understand.
  REMEMBER TO PUSH!!
  Prove that you can compile the language without any equalities.
  Add equations about nats.
  Add equations about expressions.
*)

Definition get_substable (m : Model.Model) : Substable.Substable.
