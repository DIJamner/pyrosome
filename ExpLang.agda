module ExpLang where

import Level as L

open import Size

open import Data.Nat hiding (pred)
open import Data.Fin hiding (cast)
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Data.Maybe.Categorical as MC
open import Category.Monad
open import Data.List hiding (tabulate; lookup)
open import Data.List.Properties
open import Data.List.Relation.Unary.All using (tabulate)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Function

open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic using (th^Tm; vl^Tm;_[_;_/0])

open import Path.Path renaming (id to path-id)

--TODO: move to utils
_∘₂_ : ∀ {a1 a2 b c} {A₁ : Set a1} {A₂ : Set a2} {B : Set b} {C : Set c} →
         (B → C) → (A₁ → A₂ → B) → (A₁ → A₂ → C)
_∘₂_ = _∘′_ ∘ _∘′_

module _ {a b} {A : Set a} {B : Set b} where

  infix 10 IUniversal2
  IUniversal2 : ∀ {ℓ} → (A → B → Set ℓ) → Set _
  IUniversal2 P = ∀ {x y} → P x y
  
  syntax IUniversal2 P = ∀²[ P ]
  
  infixr 8 _⇒²_
  
  _⇒²_ : ∀ {ℓ₁ ℓ₂} → (A → B → Set ℓ₁) → (A → B → Set ℓ₂) → A → B → Set _
  P ⇒² Q = λ x y → P x y → Q x y

cast : ∀{ℓ₁ ℓ₂} → ∀ {A : Set ℓ₁} → ∀ {a b : A} → a ≡ b → (P : A → Set ℓ₂) → P a → P b
cast refl P = id


cong-app' : ∀ {a b} {A : Set a} {B : Set b} → {x y : A} → x ≡ y → {f g : (x : A) → B} →
           f ≡ g  → f x ≡ g y
cong-app' refl refl = refl

private
  variable
    I : Set

Tm⟦_⟧$ : {d1 d2 : Desc I} → Path d1 d2 → ∀²[ Tm d1 ∞ ⇒² Tm d2 ∞ ]
Tm⟦ p ⟧$ = map^Tm (morph p)

Extensible : ∀{ℓ} → Desc I → (Desc I → Set ℓ) → Set _
Extensible d f = ∀{d'} → Path d d' → f d'

infix 10 Extensible
syntax Extensible d (λ d' → e) = Ex⟨ d ↑ d' ⟩ e

DescUnfix : ∀{I ℓ} → Desc I → (P : Desc I → Set ℓ) → Set _
DescUnfix d P = Ex⟨ d ↑ d' ⟩ (P d' → P d')

infix 10 DescUnfix
syntax DescUnfix d (λ d' → T) = Exᶠ⟨ d ↑ d' ⟩ T

-- Currently, this system is set up for untyped languages
-- this isn't ideal, but it's simpler than mucking with the generic syntax library or building on top of it
record Lang (I : Set) : Set₁ where
  field
    desc : Desc I
    --TODO: consistent type information
      -- envs for Γ mapping to types
        -- should be related if mapping give related types
        -- right now this allows for anything
      -- types should be related if type precision relates their terms
      --what's the best way to guarantee these properties? (may want typeof to be monotonic)
    -- Mendler semantics; represents one step of the precision derivation
    -- TODO: I might be able to avoid the natural number indexing if I handle sizes right here
      -- issue: the existing substitution is defined in terms of ∞; (maybe solve this later?)
    --TODO: rename? (approximation?)
    precision : Ex⟨ desc ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))

  -- TODO: build in transitivity, reflexivity or prove admissible ?
  -- TODO: Γ should be related by precision in base case
  -- and x should be mapped to type in Γ
  precⁿ : ℕ → Rel (Tm desc ∞) (Tm desc ∞)
  precⁿ zero .rel _ _ _ = ⊥
  precⁿ (suc n) = precision path-id (precⁿ n)

  
  -- two terms are related if they are related by a finite precision derivation
  -- TODO: remove t1,t2 from TTm? (use typeof) since terms in 0 don't have types
  -- environment relation ignores the output type
  --prec-env : Rel (TEnv tp desc) (TEnv tp desc)
  --prec-type : Rel (Tp tp desc) (Tp tp desc)
  prec : Rel (Tm desc ∞) (Tm desc ∞)

{-
  prec-env .rel _ {[]} · · = ⊤
  prec-env .rel i {x ∷ Γ} (x₁ ,ₜ Γ1) (x₂ ,ₜ Γ2) =
         rel prec-type x (Γ1 , x₁) (Γ2 , x₂)
         × rel prec-env i Γ1 Γ2
-}

  -- rel prec-env zero Γ1 Γ2
  -- TODO: where best to enforce that the environment is well-formed?
  -- does this suffice? also, make user prove that rules preserve well-formedness
  --prec-type .rel zero (Γ1 , _) (Γ2 , _) = rel prec-env zero Γ1 Γ2
  --prec-type .rel i = rel prec (tp i)
  prec .rel i e1 e2 = Σ[ n ∈ ℕ ] (rel (precⁿ n) i e1 e2)

open Lang public hiding (precⁿ)


open import DescUtils

_+ᴸ_ : ∀[ Lang ⇒ Lang ⇒ Lang ]
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .precision p R .rel i e1 e2 =
  rel (precision L1 (path-projₗ p) R) i e1 e2
  ⊎ rel (precision L2 (path-projᵣ p) R) i e1 e2

-- Automatically define congruence rules for a syntax
cong-prec : (d : Desc I) → ∀{X} → (∀ Δ → Rel (X Δ) (X Δ)) → Rel (⟦ d ⟧ X) (⟦ d ⟧ X)
cong-prec (`σ A d) R .rel i (fst , snd) (fst₁ , snd₁) =
  Σ(fst ≡ fst₁) λ{ refl → rel (cong-prec (d fst) R) i snd snd₁ }
cong-prec (`X Δ j d) R .rel i (fst , snd) (fst₁ , snd₁) =
  rel (R Δ) j fst fst₁ × rel (cong-prec d R) i snd snd₁
cong-prec (`∎ x) R .rel .x refl refl = ⊤

rel-embed : ∀{I} → {A B : I ─Scoped} → (F : ∀{i} → ∀[ A i ⇒ B i ]) → Rel A A → Rel B B
rel-embed F R .rel i e1 e2 = ∃₂ λ x₁ x₂ → e1 ≡ F x₁ × e2 ≡ F x₂

rel-map : ∀{I} → {A B : I ─Scoped} → (F : ∀{i} → ∀[ A i ⇒ B i ]) → Rel B B → Rel A A
rel-map F R .rel i e1 e2 = rel R i (F e1) (F e2)

congp1 : (d : Desc I) → ∀{X} → (∀ Δ → Rel (X Δ) (X Δ)) → Ex⟨ d ↑ d' ⟩ (Rel (⟦ d' ⟧ X) (⟦ d' ⟧ X))
congp1 d R p = rel-embed ⟦ p ⟧$ (cong-prec d R)

--TODO: parameterize this by a base relation
-- parameterization by the size is necessary here for the termination checker
cong-prec' : (d : Desc I) → ∀ {s} → (∀ Δ → Rel (Scope (Tm d s) Δ) (Scope (Tm d s) Δ))
cong-prec' d Δ .rel i (`var x) (`var x₁) = x ≡ x₁
cong-prec' d Δ .rel i (`var x) (`con x₁) = ⊥
cong-prec' d Δ .rel i (`con x) (`var x₁) = ⊥
cong-prec' d Δ .rel i (`con x) (`con x₁) = rel (cong-prec d (cong-prec' d)) i x x₁

cp'' : (d : Desc I) → (∀ Δ → Rel (Scope (Tm d ∞) Δ) (Scope (Tm d ∞) Δ))
cp'' d = cong-prec' d

-- TODO: is there a way to use Path knowledge to avoid the rel-embed existentials?
congp' : (d : Desc I) → Ex⟨ d ↑ d' ⟩ (∀ Δ → Rel (Scope (Tm d' ∞) Δ) (Scope (Tm d' ∞) Δ))
congp' d p Δ = rel-embed (map^Tm (morph p)) (cong-prec' d Δ)


scopeR : {A B : I ─Scoped} → Rel A B → ∀ Δ → Rel (Scope A Δ) (Scope B Δ)
scopeR R Δ .rel i e1 e2 = rel R i e1 e2

cprec' : (d : Desc I) → Ex⟨ d ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
cprec' d p R .rel i (`var x) (`var x₁) = x ≡ x₁
cprec' d p R .rel i (`var x) (`con x₁) = ⊥
cprec' d p R .rel i (`con x) (`var x₁) = ⊥
cprec' d p R .rel i (`con x) (`con x₁) = rel (rel-embed ⟦ p ⟧$ (cong-prec d (scopeR R))) i x x₁

--TODO: what's the best way to handle this?
-- I probably want it "built in", but right now that means adding it to every language
-- and this gives me multiple copies
transitivity :  (d : Desc I) → Ex⟨ d ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
transitivity d p R .rel i e1 e2 = ∃[ x ] (rel R i e1 x × rel R i x e2)

{-
--TODO: check first 3 cases
cprec' : (d : Desc I) → Exᶠ⟨ d ↑ d' ⟩ (∀ Δ → Rel (Scope (Tm d' ∞) Δ) (Scope (Tm d' ∞) Δ))
cprec' d p R Δ .rel i (`var x) (`var x₁) = x ≡ x₁
cprec' d p R Δ .rel i (`var x) (`con x₁) = ⊥
cprec' d p R Δ .rel i (`con x) (`var x₁) = ⊥
cprec' d {d'} p R Δ .rel i (`con x) (`con x₁) =
  rel (cong-prec d' (cprec' d p R)) i x x₁
-}

-- Simply typed languages (the types have no variables and only one kind)
-- note : this can definitely be generalized to n-level type systems
record TLang : Set₁ where
  field
    type-lang : Lang ⊤
    --TODO: better to just have term-lang?
    term-lang : ∀{td} → (m : DescMorphism (desc type-lang) td) →
              Lang (TM td tt)


  tdesc : ∀{td} → DescMorphism (desc type-lang) td → Desc (TM td tt)
  tdesc m = desc (term-lang m)
  tprecision : ∀{td} → (m : DescMorphism (desc type-lang) td) →
                 Ex⟨ tdesc m ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
  tprecision m = precision (term-lang m)

open TLang

_+ᵀ_ : TLang → TLang → TLang
_+ᵀ_ L1 L2 .type-lang = (type-lang L1) +ᴸ (type-lang L2)
_+ᵀ_ L1 L2 .term-lang m .desc = (tdesc L1 (m ∘ₘ minjₗ)) `+ (tdesc L2 (m ∘ₘ minjᵣ))
_+ᵀ_ L1 L2 .term-lang m .precision p R =
  tprecision L1 (m ∘ₘ minjₗ) (p ∘ₚ injₗ) R
  ⊎ᴿ tprecision L2 (m ∘ₘ minjᵣ) (p ∘ₚ injᵣ) R

free-lang : ∀{I} → Desc I → Lang I
free-lang d .desc = d
free-lang d .precision = cprec' d

module SIMPLE where

  ⑴t : ∀{d'} → DescMorphism (`∎ tt) d' → ∀{Γ} → TM d' Γ
  ⑴t m = map^Tm m (`con refl)

  UnitLang : TLang
  UnitLang .type-lang .desc = `∎ tt
  UnitLang .type-lang .precision = cprec' (`∎ tt)
  UnitLang .term-lang m .desc = `∎ (map^Tm m (`con refl))
  --TODO: eta law
  UnitLang .term-lang m .precision {d'} p R = cprec' (`∎ (map^Tm m (`con refl))) p R
    ⊎ᴿ unit-eta
    ⊎ᴿ transitivity _ p R where
    -- all terms at type unit are equivalent; not quite the traditional law,
    -- but a close enough approximation and simpler
    -- TODO: doesn't hold in the presence of effects
    --TODO: to think about: how can we tell there's an issue when we add
    -- a rule like this to a nonterminating language?
    unit-eta : Rel (Tm d' ∞) (Tm d' ∞)
    unit-eta .rel i e1 e2 = i ≡ ⑴t m
  
  ⑴e : ∀{td} → (m : DescMorphism (`∎ tt) td) → Ex⟨ `∎ (map^Tm m (`con refl)) ↑ d' ⟩
           (∀{Γ} → Tm d' ∞ (⑴t m) Γ)
  ⑴e m p = `con (⟦ p ⟧$ refl)


  LamTy : Lang ⊤
  LamTy = free-lang (`X [] tt (`X [] tt (`∎ tt)))

  ⟨_⟩_→t_ : ∀{td} → DescMorphism (desc LamTy) td → (TM td tt) → (TM td tt) → (TM td tt)
  ⟨ m ⟩ a →t b = `con (DescMorphism.apply m (a , (b , refl)))

  LamDesc : ∀{td} → (m : DescMorphism (desc LamTy) td) → Desc (TM td tt)
  LamDesc m = 
    --Lambda
    `σ (_ × _) (λ {(i , j) →  `X [ i ] j (`∎ (⟨ m ⟩ i →t j))})
    -- app
    `+ `σ (_ × _) (λ {(i , j) →  `X [] (⟨ m ⟩ i →t j) (`X [] i (`∎ j))})

  lamexp : ∀{td} → (m : DescMorphism (desc LamTy) td) → Ex⟨ LamDesc m ↑ d' ⟩
           ((i : TM td tt) → {j : TM td tt} →
           ∀{Γ} → Scope (Tm d' ∞) [ i ] j Γ → Tm d' ∞ (⟨ m ⟩ i →t j) Γ)
  lamexp m p i {j} e = `con (⟦ p ⟧$ (true , ((i , j) , (e , refl))))

  syntax lamexp m p i e = ⟨ m , p ⟩λ i →f e

  appexp : ∀{td} → (m : DescMorphism (desc LamTy) td) → Ex⟨ LamDesc m ↑ d' ⟩
           ({i j : TM td tt} →
           ∀{Γ} → Tm d' ∞ (⟨ m ⟩ i →t j) Γ → Tm d' ∞ i Γ → Tm d' ∞ j Γ)
  appexp m p {i} {j} e1 e2 =
    `con (⟦ p ⟧$ (false , ((i , j) , (e1 , (e2 , refl)))))

  syntax appexp m p e1 e2 = ⟨ m , p ⟩ e1 % e2

  beta :  ∀{td} → (m : DescMorphism (desc LamTy) td) → Ex⟨ LamDesc m ↑ d' ⟩
          (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
  -- TODO: use pattern synonyms/some form of pattern matching
  -- to reduce burden of all of these existentials
  beta m {d'} p R .rel i {Γ} e1 e2 =
    Σ (∃[ j ] (Scope (Tm d' ∞) [ j ] i Γ × Tm d' ∞ j Γ)) λ { (j , e1' , e2') →
    --TODO: application
    e1 ≡ ⟨ m , p ⟩ ⟨ m , p ⟩λ j →f e1' % e2'
    × e2 ≡ e1' [ e2' /0]}

  eta :  ∀{td} → (m : DescMorphism (desc LamTy) td) → Ex⟨ LamDesc m ↑ d' ⟩
          (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
  -- TODO: use pattern synonyms/some form of pattern matching
  -- to reduce burden of all of these existentials
  eta m {d'} p R .rel i {Γ} e1 e2 =
    Σ (_ × _) λ { (j1 , j2) →
    Σ (i ≡ ⟨ m ⟩ j1 →t j2) λ { refl →
    --TODO: is there a nicer way to write weakening?
    --TODO: should I be making a call to R here instead of using e1 directly?
            -- transitivity might handle this (but if so I should add it)
    e2 ≡ ⟨ m , p ⟩λ j1 →f ⟨ m , p ⟩ th^Tm e1 (pack (λ {i} → s)) % `var z }}

  LamLang : TLang
  LamLang .type-lang = LamTy
  LamLang .term-lang m .desc = LamDesc m
  LamLang .term-lang m .precision p R = cprec' (LamDesc m) p R
    ⊎ᴿ beta m p R
    ⊎ᴿ eta m p R
    ⊎ᴿ transitivity _ p R

  UL : TLang
  UL = UnitLang +ᵀ LamLang

  --TODO: make this proof go through;
  -- shows that any function that returns unit
  -- is equivalent to the specific function that immediately does so
  _ : ∀ {Γ} i e → rel (prec (term-lang UL mid)) (⟨ minjᵣ ⟩ i →t ⑴t minjₗ) {Γ}
      e (⟨ minjᵣ , injᵣ ⟩λ i →f ⑴e minjₗ injₗ)
      --transitivity
      --TODO: have "cartesian" base theory as per Shulman
      --use in all std. theories, deduplicate
      --"precision" then always becomes an equality
  _ = λ i e → 2 , inj₁ (inj₂ (inj₂ ((⟨ minjᵣ , injᵣ ⟩λ i →f ⟨ minjᵣ , injᵣ ⟩
        (th^Tm e (pack (λ {i} → s))) % `var z) ,
      -- eta
      (inj₂ (inj₂ (inj₂ (inj₁ ((i , ⑴t minjₗ) , refl , refl)))) ,
      -- fn congruence, unit rule(?)
      inj₂ (inj₁ ((true , (i , ⑴t minjₗ) ,
                 appexp minjᵣ injᵣ (th^Tm e (pack (λ {i = i₁} → s))) (`var z) , refl) ,
           (true , (((i , ⑴t minjₗ)) , ((⑴e minjₗ injₗ) , refl))) ,
      (refl , refl)))))))

    

module UNTYPED where
  data Kind : Set where
    KTm : Kind
  
  -- TODO: use congruence generation to add back in var eq
  UnitLang : Lang Kind
  UnitLang .desc = `∎ KTm
  UnitLang .precision = cprec' (desc UnitLang)
  
  
  LamDesc : Desc Kind
  LamDesc = `X [ KTm ] KTm (`∎ KTm)
          `+ `X [] KTm (`X [] KTm (`∎ KTm))
  
  LamPrec : Ex⟨ LamDesc ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
  LamPrec {d' = d'} p R .rel KTm {Γ} x x₁ =
    rel (cprec' LamDesc p R) KTm x x₁
    -- beta reduction
    ⊎ (Σ (Scope (Tm d' ∞) (KTm ∷ []) KTm Γ × Scope (Tm d' ∞) ([]) KTm Γ) λ { (y₁ , y₂) →
      x ≡ `con (⟦ p ⟧$ (false , `con (⟦ p ⟧$ (true , (y₁ , refl))) , (y₂ , refl)))
      × x₁ ≡ y₁ [ y₂ /0]})
  
  --TODO: define using congruences
  --LamPrec' : Ex⟨ LamDesc ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
  
  -- TODO: can we generate the congruence rules automatically?
  LamLang : Lang Kind
  LamLang .desc = LamDesc
  LamLang .precision = LamPrec
  
  UL : Lang Kind
  UL = UnitLang +ᴸ LamLang
  
  module UL = Lang UL
  
  UL⑴ : TM UL.desc KTm
  UL⑴ = `con (true , refl)
  
  ULλ : ∀{Γ} → Tm UL.desc ∞ KTm (KTm ∷ Γ) → Tm UL.desc ∞ KTm Γ
  ULλ b = `con (false , (true , (b , refl)))
  
  _ULApp_ :  ∀{Γ} → Tm UL.desc ∞ KTm Γ → Tm UL.desc ∞ KTm Γ → Tm UL.desc ∞ KTm Γ
  a ULApp b = `con (false , (false , (a , (b , refl))))
  
  --TODO: generalize to any language with a path into it
  _ : rel UL.prec KTm ((ULλ (`var z)) ULApp UL⑴) UL⑴
  _ = 2 , inj₂ (inj₂ (((`var z) , UL⑴) , (refl , refl)))
  
  record LPath (L1 L2 : Lang I) : Set₁ where
    module L1 = Lang L1
    module L2 = Lang L2
    field
      desc-path : Path L1.desc L2.desc
      --TODO: finish; is this correct?
      --TODO: do I need R1 => R2 or does R suffice? (probably the former)
      prec-path :  ∀ d' → (p : Path L2.desc d') → ∀ R1 R2 → (R1 ⇒ᴿ R2) →
                   (L1.precision (p ∘ₚ desc-path) R1) ⇒ᴿ (L2.precision p R2)
      
  
  -- Construct for ranging over all extensions of a given language
  ExtensibleLang : ∀{ℓ} → Lang I → (Lang I → Set ℓ) → Set _
  ExtensibleLang L f = ∀{L'} → LPath L L' → f L'
  
  infix 10 ExtensibleLang
  syntax ExtensibleLang L (λ L' → e) = ExL⟨ L ↑ L' ⟩ e
  
  
  -- precision preserving compilers
  -- TODO: expand to Lang I, Lang J (different types)
  record PComp (L1 L2 : Lang I) : Set₁ where
    module L1 = Lang L1
    module L2 = Lang L2
    field
      --compile : ∀ {i} → ∀[ Tm L1.desc ∞ i ⇒ Tm L2.desc ∞ i ]
      compile : Ex⟨ L2.desc ↑ d' ⟩ (∀ {i} → ∀[ Tm (d' `+ L1.desc) ∞ i ⇒ Tm d' ∞ i ])
      preserves : ExL⟨ L2 ↑ L' ⟩ (∀ R1 R2 → (R1 ⇒ᴿ R2) →
                  precision (L' +ᴸ L1) {!TODO: paths not expresive enough!} R1
                  ⇒ᴿ (precision L' path-id R2))
    --TODO: make this about precision rather than prec for extensibility
    -- precision : Ex⟨ desc ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
    {-
    preserves : Ex⟨ L2.desc ↑ d' ⟩ ((R : Rel (Tm d' ∞) (Tm d' ∞)) → ∀{i Γ} →
                (e1 e2 : Tm (d' `+ L1.desc) ∞ i Γ) → 
                R) where
                L+
    TODO: need Ex for languages (need to extend L2 with a semantics, not just a syntax)

    1. R1 => R2
    2. e1 e2 : Tm ?
    
    precision (L1 +L L') R1 e1 e2 => precision L' R2 (compile e1) (compile e2)
    -}
   
      --∀{i Γ} → (e1 e2 : Tm L1.desc ∞ i Γ) →
      --              rel L1.prec i e1 e2 → rel L2.prec i (compile e1) (compile e2)
    comp : ∀ {i} → ∀[ Tm L1.desc ∞ i ⇒ Tm L2.desc ∞ i ]
    comp e = compile path-id (Tm⟦ injᵣ ⟧$ e)
  
  open PComp
  
  ucomp : ∀ L1 → PComp L1 UnitLang
  ucomp L1 .compile p {KTm} e = Tm⟦ p ⟧$ (`con refl)
  {-
  ucomp L1 .preserve-prec {KTm} e1 e2 (suc fst , _) = (suc fst) , (refl , refl)
  -}
  
  
  +embed : (L1 L2 : Lang I) → PComp L1 (L1 +ᴸ L2) 
  +embed L1 L2 .compile p e = map^Tm (morph (path-id `+L (path-projₗ p))) e
  {-
  +embed L1 L2 .preserve-prec e1 e2 (suc zero , snd) = {!!} -- (suc zero) , inj₁ {!snd!}
  +embed L1 L2 .preserve-prec e1 e2 (suc (suc fst) , snd) = (suc (suc fst)) , inj₁ {!!}
  -}
