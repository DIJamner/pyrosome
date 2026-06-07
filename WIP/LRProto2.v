(* Prototype 2: validate the Kripke-enriched RedTy encoding = LRProto.v's clean
   single-inductive + Sig trick, PLUS the object-substitution Kripke
   quantification in the Pi case (NEXT_SESSION UPDATE-s item 3: "build the
   object-sub Kripke into the Pi case FROM THE START").

   The working value-domain dev (LogRel2.v) uses the heavyweight logrel-coq
   PolyRedPack+adequacy split.  Here we test whether the lighter Sig trick
   (member relation as OUTPUT index) still keeps RedTy_tot strictly positive
   once the Pi case is Kripke.  It does: RedTy_tot stays in strictly positive
   position under the extra `forall G' (g : osub G' G)` quantifiers.

   Object substitutions abstract; in OTT: `osub G' G` := a well-typed term of
   sort `sub G' G`; `act g X` := `exp_subst g X`; `ext G F` := `ext G (El F)`. *)

Parameter tm  : Type.
Parameter env : Type.
Parameter reds  : tm -> tm -> Prop.
Parameter ne_eq : tm -> tm -> Prop.
Parameter is_pi  : tm -> tm -> tm -> Prop.    (* `is_pi A F C` : A whnf= Pi F C *)
Parameter is_nat : tm -> Prop.

Parameter osub : env -> env -> Type.          (* object substitution G' -> G *)
Parameter act  : forall {G' G}, osub G' G -> tm -> tm.
Parameter ext  : env -> tm -> env.            (* extend env by a domain code *)
Parameter app  : tm -> tm -> tm.
Parameter cod_subst : tm -> tm -> tm.         (* C[a] : codomain instantiation *)

(* Base member relations (unchanged). *)
Inductive RedAtNat (t u : tm) : Type :=
| at_nat_ne : ne_eq t u -> RedAtNat t u.

Inductive RedAtNe (t u : tm) : Type :=
| at_ne_ne : ne_eq t u -> RedAtNe t u.

(* Kripke Pi member relation, mirroring LogRel2's PiRedTmEq but with the member
   relation carried as parameters (RDom/RCod) rather than read from a pack.
   Two functions t,u are related at the home env G iff, for every object subst
   g : osub G' G and every domain-related pair (a,a'), the applications of the
   substituted functions to a,a' are codomain-related. *)
Inductive RedAtPi
  (G : env) (F C F' C' : tm)
  (RDom : forall G' (g : osub G' G), tm -> tm -> Type)
  (RCod : forall G' (g : osub G' G) a a', RDom G' g a a' -> tm -> tm -> Type)
  (t u : tm) : Type :=
| at_pi_app
    (do_app : forall G' (g : osub G' G) a a' (raa' : RDom G' g a a'),
        RCod G' g a a' raa' (app (act g t) a) (app (act g u) a'))
  : RedAtPi G F C F' C' RDom RCod t u.

(* The Kripke type-reducibility relation, indexed by the object env G the codes
   live in.  Member relation is the OUTPUT index (Sig trick). *)
Inductive RedTy_tot : env -> tm -> tm -> (tm -> tm -> Type) -> Type :=
| rtt_nat : forall G A B,
    reds A B -> is_nat B ->
    RedTy_tot G A B RedAtNat
| rtt_ne : forall G A B na nb,
    reds A na -> reds B nb -> ne_eq na nb ->
    RedTy_tot G A B RedAtNe
| rtt_pi : forall G A B F C F' C',
    reds A F -> is_pi A F C -> is_pi B F' C' ->
    forall (RDom : forall G' (g : osub G' G), tm -> tm -> Type)
           (DomRed : forall G' (g : osub G' G),
               RedTy_tot G' (act g F) (act g F') (RDom G' g))
           (RCod : forall G' (g : osub G' G) a a',
               RDom G' g a a' -> tm -> tm -> Type)
           (CodRed : forall G' (g : osub G' G) a a' (raa' : RDom G' g a a'),
               RedTy_tot (ext G' (act g F))
                 (cod_subst (act g C) a) (cod_subst (act g C') a')
                 (RCod G' g a a' raa')),
    RedTy_tot G A B (RedAtPi G F C F' C' RDom RCod).

(* Sig packaging. *)
Definition RedTy (G : env) (A B : tm) : Type :=
  { R : tm -> tm -> Type & RedTy_tot G A B R }.
Definition RedTy_R {G A B} (r : RedTy G A B) : tm -> tm -> Type := projT1 r.
Definition RedTm {G A B} (r : RedTy G A B) (t u : tm) : Type := RedTy_R r t u.

(* Smart constructors. *)
Definition RedTy_nat {G A B} (rd : reds A B) (h : is_nat B) : RedTy G A B :=
  existT _ _ (rtt_nat G A B rd h).

Definition RedTy_pi {G A B F C F' C'}
  (rd : reds A F) (hA : is_pi A F C) (hB : is_pi B F' C')
  (DomRed : forall G' (g : osub G' G), RedTy G' (act g F) (act g F'))
  (CodRed : forall G' (g : osub G' G) a a',
      RedTm (DomRed G' g) a a' ->
      RedTy (ext G' (act g F)) (cod_subst (act g C) a) (cod_subst (act g C') a'))
  : RedTy G A B.
Proof.
  unshelve eexists.
  - exact (RedAtPi G F C F' C'
             (fun G' g => RedTy_R (DomRed G' g))
             (fun G' g a a' raa' => RedTy_R (CodRed G' g a a' raa'))).
  - eapply rtt_pi; try eassumption.
    + intros G' g. exact (projT2 (DomRed G' g)).
    + intros G' g a a' raa'. exact (projT2 (CodRed G' g a a' raa')).
Defined.

(* Custom eliminator threading the Kripke domain/codomain IHs. *)
Theorem RedTy_rect
  (P : forall G A B, RedTy G A B -> Type)
  (Hnat : forall G A B (rd : reds A B) (h : is_nat B), P G A B (RedTy_nat rd h))
  (Hne : forall G A B na nb (ra : reds A na) (rb : reds B nb) (h : ne_eq na nb),
      P G A B (existT _ _ (rtt_ne G A B na nb ra rb h)))
  (Hpi : forall G A B F C F' C'
           (rd : reds A F) (hA : is_pi A F C) (hB : is_pi B F' C')
           (DomRed : forall G' (g : osub G' G), RedTy G' (act g F) (act g F'))
           (CodRed : forall G' (g : osub G' G) a a',
               RedTm (DomRed G' g) a a' ->
               RedTy (ext G' (act g F)) (cod_subst (act g C) a) (cod_subst (act g C') a')),
        (forall G' (g : osub G' G), P G' _ _ (DomRed G' g)) ->
        (forall G' (g : osub G' G) a a' (raa' : RedTm (DomRed G' g) a a'),
            P _ _ _ (CodRed G' g a a' raa')) ->
        P G A B (RedTy_pi rd hA hB DomRed CodRed))
  : forall G A B (r : RedTy G A B), P G A B r.
Proof.
  intros G A B [R r].
  induction r as [ G A B rd h
                 | G A B na nb ra rb h
                 | G A B F C F' C' rd hA hB RDom DomRed IHDom RCod CodRed IHCod ].
  - apply Hnat.
  - apply Hne.
  - apply (Hpi G A B F C F' C' rd hA hB
             (fun G' g => existT _ (RDom G' g) (DomRed G' g))
             (fun G' g a a' raa' => existT _ (RCod G' g a a' raa') (CodRed G' g a a' raa'))).
    + intros G' g. exact (IHDom G' g).
    + intros G' g a a' raa'. exact (IHCod G' g a a' raa').
Defined.

Check RedTy_rect.
Print Assumptions RedTy_rect.
