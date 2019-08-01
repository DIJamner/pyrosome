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
    precision : Ex⟨ desc ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))

  -- TODO: build in transitivity, reflexivity or prove admissible ?
  -- TODO: Γ should be related by precision in base case
  -- and x should be mapped to type in Γ
  precⁿ : ℕ → Rel (Tm desc ∞) (Tm desc ∞)
  precⁿ zero .rel i  (`var x) (`var x₁) = x ≡ x₁
  precⁿ zero .rel i (`var _) (`con _) = ⊥
  precⁿ zero .rel i (`con _) (`var _) = ⊥
  precⁿ zero .rel i (`con _) (`con _) = ⊥
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

congp' : (d : Desc I) → Ex⟨ d ↑ d' ⟩ (∀ Δ → Rel (Scope (Tm d' ∞) Δ) (Scope (Tm d' ∞) Δ))
congp' d p Δ = rel-embed (map^Tm (morph p)) (cong-prec' d Δ)

{-
--TODO: check first 3 cases
cong-prec' : (d : Desc I) → Exᶠ⟨ d ↑ d' ⟩ (∀ Δ → Rel (Scope (Tm d' ∞) Δ) (Scope (Tm d' ∞) Δ))
cong-prec' d p R Δ .rel i (`var x) (`var x₁) = x ≡ x₁
cong-prec' d p R Δ .rel i (`var x) (`con x₁) = ⊥
cong-prec' d p R Δ .rel i (`con x) (`var x₁) = ⊥
cong-prec' d {d'} p R Δ .rel i (`con x) (`con x₁) =
  rel (cong-prec d' (cong-prec' d p R)) i x x₁
-}

data Kind : Set where
  KTm : Kind


UnitLang : Lang Kind
UnitLang .desc = `∎ KTm
UnitLang .precision p R .rel KTm x x₁ =
   x ≡ `con (⟦ p ⟧$ refl) × x₁ ≡ `con (⟦ p ⟧$ refl)


LamDesc : Desc Kind
LamDesc = `X [ KTm ] KTm (`∎ KTm)
        `+ `X [] KTm (`X [] KTm (`∎ KTm))

LamPrec : Ex⟨ LamDesc ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
LamPrec {d' = d'} p R .rel KTm {Γ} x x₁ =
   -- congruence case for lambda
   (Σ (Scope (Tm d' ∞) (KTm ∷ []) KTm Γ × Scope (Tm d' ∞) (KTm ∷ []) KTm Γ) λ { (y₁ , y₂) → 
     x ≡ `con (⟦ p ⟧$ (true , (y₁ , refl))) × x₁ ≡ `con (⟦ p ⟧$ (true , (y₂ , refl)))
     × rel R KTm y₁ y₂})
   -- congruence case for app
   ⊎  (Σ (Scope (Tm d' ∞) [] KTm Γ × Scope (Tm d' ∞) [] KTm Γ) λ { (y₁ , y₂) →
     Σ (Scope (Tm d' ∞) [] KTm Γ × Scope (Tm d' ∞) [] KTm Γ) λ { (z₁ , z₂) → 
     x ≡ `con (⟦ p ⟧$ (false , y₁ , (z₁ , refl))) × x₁ ≡ `con (⟦ p ⟧$ (false , y₂ , (z₂ , refl)))
     × rel R KTm y₁ y₂ × rel R KTm z₁ z₂}})
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
