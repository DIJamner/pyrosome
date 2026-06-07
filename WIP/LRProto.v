(* Prototype: validate the metamltt Rel_tot+Sig member-relation encoding,
   ported abstractly, WITHOUT the Small/Large universe tower (OTT has no
   universe code, so the impredicative recursion is absent).  Goal: confirm
   strict positivity of the dependent-codomain Pi premise and universe
   consistency of the Type-valued inductive + sigma packaging. *)

(* Abstract "term" and the foundational relations as opaque parameters. *)
Parameter tm : Type.
Parameter reds : tm -> tm -> Prop.
Parameter ne_eq : tm -> tm -> Prop.
Parameter is_pi : tm -> tm -> tm -> Prop.   (* `is_pi A F C` : A is whnf Pi F C *)
Parameter is_nat : tm -> Prop.
Parameter app : tm -> tm -> tm.             (* application head *)
Parameter cod_subst : tm -> tm -> tm.       (* C[a] *)

(* Member relations, parameterized by the sub-relations they recurse through
   (exactly metamltt's RelAtNat / RelAtNe / RelAtPi). *)

Inductive RedAtNat (t u : tm) : Type :=
| at_nat_ne : ne_eq t u -> RedAtNat t u.

Inductive RedAtNe (t u : tm) : Type :=
| at_ne_ne : ne_eq t u -> RedAtNe t u.

(* The Pi member: for every domain-related pair (a,a'), the applications are
   codomain-related.  RDom is the domain member relation; RCod is the
   (a,a')-indexed codomain member relation. *)
Inductive RedAtPi
  (F C F' C' : tm)
  (RDom : tm -> tm -> Type)
  (RCod : forall a a', RDom a a' -> tm -> tm -> Type)
  (t u : tm) : Type :=
| at_pi_app
    (f g : tm)
    (redl : reds t f) (redr : reds u g)
    (do_app : forall a a' (raa' : RDom a a'),
        RCod a a' raa' (app f a) (app g a'))
  : RedAtPi F C F' C' RDom RCod t u.

(* The type-reducibility relation, with the member relation as OUTPUT index
   (the Sig trick avoids indexing RedTm by a RedTy derivation).  NO universe
   tower: a single plain inductive. *)
Inductive RedTy_tot : tm -> tm -> (tm -> tm -> Type) -> Type :=
| rtt_nat : forall A B,
    reds A B -> is_nat B ->
    RedTy_tot A B RedAtNat
| rtt_ne : forall A B na nb,
    reds A na -> reds B nb -> ne_eq na nb ->
    RedTy_tot A B RedAtNe
| rtt_pi : forall A B F C F' C',
    reds A F (* placeholder: A reduces to Pi F C; abstracted *) ->
    is_pi A F C -> is_pi B F' C' ->
    forall (RDom : tm -> tm -> Type)
           (DomRed : RedTy_tot F F' RDom)
           (RCod : forall a a', RDom a a' -> tm -> tm -> Type)
           (CodRed : forall a a' (raa' : RDom a a'),
               RedTy_tot (cod_subst C a) (cod_subst C' a') (RCod a a' raa')),
    RedTy_tot A B (RedAtPi F C F' C' RDom RCod).

(* Sig packaging: RedTy A B := { R & RedTy_tot A B R }, and the member relation
   is the first projection. *)
Definition RedTy (A B : tm) : Type := { R : tm -> tm -> Type & RedTy_tot A B R }.
Definition RedTy_R {A B} (r : RedTy A B) : tm -> tm -> Type := projT1 r.
Definition RedTm {A B} (r : RedTy A B) (t u : tm) : Type := RedTy_R r t u.

(* Smart constructors. *)
Definition RedTy_nat {A B} (rd : reds A B) (h : is_nat B) : RedTy A B :=
  existT _ _ (rtt_nat A B rd h).

Definition RedTy_pi {A B F C F' C'}
  (rd : reds A F) (hA : is_pi A F C) (hB : is_pi B F' C')
  (DomRed : RedTy F F')
  (CodRed : forall a a', RedTm DomRed a a' -> RedTy (cod_subst C a) (cod_subst C' a'))
  : RedTy A B.
Proof.
  unshelve eexists.
  - exact (RedAtPi F C F' C' (RedTy_R DomRed)
             (fun a a' raa' => RedTy_R (CodRed a a' raa'))).
  - eapply rtt_pi; try eassumption.
    + exact (projT2 DomRed).
    + intros a a' raa'. exact (projT2 (CodRed a a' raa')).
Defined.

(* The eliminator: induction principle threading the Pi sub-derivations. *)
Theorem RedTy_rect
  (P : forall A B, RedTy A B -> Type)
  (Hnat : forall A B (rd : reds A B) (h : is_nat B), P A B (RedTy_nat rd h))
  (Hne : forall A B na nb (ra : reds A na) (rb : reds B nb) (h : ne_eq na nb),
      P A B (existT _ _ (rtt_ne A B na nb ra rb h)))
  (Hpi : forall A B F C F' C'
           (rd : reds A F) (hA : is_pi A F C) (hB : is_pi B F' C')
           (DomRed : RedTy F F')
           (CodRed : forall a a', RedTm DomRed a a' -> RedTy (cod_subst C a) (cod_subst C' a')),
        P F F' DomRed ->
        (forall a a' (raa' : RedTm DomRed a a'), P _ _ (CodRed a a' raa')) ->
        P A B (RedTy_pi rd hA hB DomRed CodRed))
  : forall A B (r : RedTy A B), P A B r.
Proof.
  intros A B [R r].
  induction r as [ A B rd h
                 | A B na nb ra rb h
                 | A B F C F' C' rd hA hB RDom DomRed IHDom RCod CodRed IHCod ].
  - apply Hnat.
  - apply Hne.
  - apply (Hpi A B F C F' C' rd hA hB (existT _ RDom DomRed)
             (fun a a' raa' => existT _ (RCod a a' raa') (CodRed a a' raa'))).
    + exact IHDom.
    + intros a a' raa'. exact (IHCod a a' raa').
Defined.

(* Check it is consistent (Type-valued, no tower needed). *)
Check RedTy_rect.
Print Assumptions RedTy_rect.
