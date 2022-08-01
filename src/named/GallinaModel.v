Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Vector.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Substable Model Compilers.
From Named Require Term.

Local Notation mut_mod eq_sort eq_term wf_sort wf_term :=
    {|
      term_substable := _;
      sort_substable := _;
      Model.eq_sort := eq_sort;
      (*TODO: rename the conflict*)
      Model.eq_term := eq_term;
      Model.wf_sort := wf_sort;
      Model.wf_term := wf_term;
    |}.

(*generalized terms *)
Definition gterm G A := forall (g : G), A g.
Arguments gterm G A : clear implicits.

Definition subst G G' := G -> G'.

Definition emp : Type := unit.
Definition ext G A := {g : G & A g}.
Arguments ext G A : clear implicits.

Definition wkn {G} {A} : subst (ext G A) G := fun g => projT1 g.

Definition term_subst {G G' A} (g : subst G G') (e : gterm G' A) :=
  fun x => e (g x).

Check term_subst.

Definition ty_subst {G G'} (g : subst G G') (t : G' -> Type) :=
  fun x => t (g x).

Definition forget {G} : subst G emp := fun _ => tt.

Definition snoc {G G' A} (g : subst G G') (e : gterm G' A) : subst G (ext G' A) :=
  fun x => let x' := g x in existT _ x' (e x').

Definition arr G (A : G -> Type) (B : ext G A -> Type) : G -> Type :=
  fun x => forall a : A x, B (existT _ x a).
Arguments arr {G} A B.

Definition lam G A B (e : gterm (ext G A) B) : gterm G (arr A B).
  unfold gterm, arr, ext.
  intuition.
Defined.


Definition app G A B (e1 : gterm G (arr A B)) e2 : gterm G (ty_subst (snoc id e2) B).
  unfold gterm, arr, ext, ty_subst, snoc, id in *.
  simpl.
  intuition.
Defined.

Lemma beta G A B (e : gterm (ext G A) B) e'
  : app (lam e) e' = term_subst (snoc id e') e.
  unfold gterm, arr, ext, ty_subst, snoc, id, app, lam in *.
  intuition.
Qed. 

Fixpoint hlist l : Type :=
  match l with
  | [] => unit
  | A::l => A * hlist l
  end.

Section Inner.
  Context (ctx : nat -> Type).
          
  Fixpoint telescope n : Type :=
    match n with
    | 0 => unit
    | S n => { t : telescope n & ctx n t}
    end.
  
with ctx n :=
       match n with
       | 0 => unit
       | S n => (telescope n -> Type * ctx n)
       end.

tele0 = unit
tele1 A = {t:unit& A t}
tele2 A B = {t:{t:unit& A t} & B t}
tele3 A B C = {t:{t:{t:unit& A t} & B t} & C t}

                
Fixpoint telescope l : Type :=
  match l with
  | [] => (unit, unit -> Type)
  | A::l => { t : telescope l & A t}
  end.

(*TODO: hlists to telescopes*)
Inductive code : forall G, (telescope G -> Type) -> Type :=
| cpi {G A B} : code G A -> code (A::G) B -> code G (fun s => forall (x:A s), B (x,s))
| cunit {G} : code G (fun _ => unit).

Inductive dyn : Type :=
| dfun : (dyn -> dyn) -> dyn.

(*
  #[export] Instance core_model : Model := mut_mod eq_sort eq_term wf_sort wf_term.*)

(*TODO: should this be split differently? Model_ok for core should be in Core.v*)
Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.


  (*TODO: generalize hlist to telescope*)
  (*Definition tag_data := ({ l : list Type & hlist l -> Type }). *)
  (* could just be a notatin to avoid polymophism*)
  Polymorphic Definition tag_data := ({ n & Vector.t Type n -> Type }). 

  (*
  Instance default_tag_data : WithDefault tag_data :=
    existT (fun _ => _ -> Type) [] (fun _ => False).*)
  
  Instance default_tag_data : WithDefault tag_data :=
    existT (fun _ => _ -> Type) 0 (fun _ => False).

  Definition type_table := @named_list V tag_data.

  Section WithTable.

    Context (tbl : type_table).

    Notation lookup_tag := (named_list_lookup default tbl).
    
    Polymorphic Variant tagged : Type -> Type :=
      | tag x : forall v, projT2 (lookup_tag x) v -> tagged (projT2 (lookup_tag x) v).

    (*Definition hastype '(@tag x v _) := projT2 (named_list_lookup default tbl x) v.*)

    Notation etagged := {A : Type & tagged A}.
    
    Polymorphic Definition unwrap_plain {A} (t : tagged A) : A :=
      match t with
      | tag _ _ v => v
      end.

    Polymorphic Definition get_tag_plain {A} '(tag x _ _ : tagged A) := x.
    Polymorphic Definition get_tag (t : etagged) := get_tag_plain (projT2 t).

    Polymorphic Definition ground_type '(existT _ n F : tag_data) :=
      F (Vector.const etagged n).
    
    Polymorphic Definition unwrap (t : etagged)
      : ground_type (lookup_tag (get_tag t)) :=
      match t with
      | tag _ H v => (v,H)
      end.

    
    Definition eunwrap (t : etagged) : projT1 t * tagpred (get_tag (projT2 t)) (projT1 t) :=
      unwrap (projT2 t).

    Definition cast : V -> tagged -> option tagged.
      refine (fun (x:V) '(@tag x' v e) => _).
      refine (match Eqb_dec x x' with left peq => Some (tag x _) | right _ => None end).
      subst.
      Show Proof.
      subst.
      exact e.
     
      option {v & projT2 (named_list_lookup default tbl x)} :=
      match t return option {v & projT2 (named_list_lookup default tbl x)} with
      | tag _ v => v
      end.
      
    
    (*  TODO: fix
  Notation "$$ A_1 .. A_n |- B $$" :=
    (existT (fun H : nat => Vector.t Type H -> Type)
            (S .. (S O) ..)
            (fun '(cons A_1 .. (cons A_n nil) ..) => B))
      (A_1 binder, A_n binder).*)
    
  (*Notation "[$ p |- B $]" :=
    (existT (fun H : nat => Vector.t Type H -> Type)
            _
            (fun p => B))
      (p pattern at level 0).*)
 
    Definition basic_table : type_table :=
      [(default, existT (fun l => hlist l -> Type)
            [Type ; Type]
            (fun '(A,(B,tt)) => (A -> B)))].
  
with gallina_sort :=
| gsort_term : named_list V gallina_term -> gallina_term -> gallina_sort.

  
  Section Inner.

    Context (sort_cmp : @named_list V (Term.subst V -> Type)).
    Context (
    
    Context (compile_sort : Term.sort V -> Type).
  
    Definition term := Term.subst V -> { s : Term.sort V & compile_sort s }.
    Definition sort := Term.subst V -> Type.

  End Inner.

  Context (cmp : 
  
  Notation term := (term
    
  Notation subst := (@subst V).




                       compiler = fun V tgt_term tgt_sort : Type => named_list (@compiler_case V tt ts)
  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  
  Section WithLang.
    Context (l : lang V)
            (wfl : wf_lang l).
    Notation core_model := (core_model l). 
