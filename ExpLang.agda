module ExpLang where

import Level as L

open import Size

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Data.Maybe.Categorical as MC
open import Category.Monad
open import Data.List hiding (tabulate)
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
open import Generic.Semantics.Syntactic using (th^Tm; vl^Tm)

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

Tm⟦_⟧$ : ∀{I} → {d1 d2 : Desc I} → Path d1 d2 → ∀²[ Tm d1 ∞ ⇒² Tm d2 ∞ ]
Tm⟦ p ⟧$ = map^Tm (morph p)

Extensible : ∀{ℓ I} → Desc I → (Desc I → Set ℓ) → Set _
Extensible d f = ∀{d'} → Path d d' → f d'

infix 10 Extensible
syntax Extensible d (λ d' → e) = Ex⟨ d ↑ d' ⟩ e

-- TODO: this currently only works for simple types
-- need to replace [] with the type environment
TTm : ∀{I} → (t d : Desc I) → I ─Scoped
TTm t d i Γ = Tm d ∞ i Γ × TM t i × (Γ ─Env) (Tm t ∞) []

-- TODO: this currently only works for simple types
-- get the indexing right in Poly/Syntax and it should work?
-- for more interesting types though
record Lang (I : Set) : Set₁ where
  field
    type : Desc I
    desc : Desc I
    type-precision : Ex⟨ type ↑ d' ⟩ (Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞))
    --TODO: consistent type information
      -- envs for Γ mapping to types
        -- should be related if mapping give related types
        -- right now this allows for anything
      -- types should be related iff type precision relates them
      --what's the best way to guarantee these properties?
    -- Mendler semantics; represents one step of the precision derivation
    precision : Ex⟨ type ↑ t' ⟩ Ex⟨ desc ↑ d' ⟩
                (Rel (TTm t' d') (TTm t' d') → Rel (TTm t' d') (TTm t' d'))
                
  -- TODO: build in transitivity
  type-precⁿ : ℕ → Rel (Tm type ∞) (Tm type ∞)
  type-precⁿ zero = Eqᴿ
  type-precⁿ (suc n) = type-precision path-id (type-precⁿ n)

  -- two types are related if they are related by a finite precision derivation
  -- TODO: possible to write using size types? (probably not)
  type-prec : Rel (Tm type ∞) (Tm type ∞)
  type-prec .rel i e1 e2 = ∃[ n ] rel (type-precⁿ n) i e1 e2
  
  -- TODO: build in transitivity
  precⁿ : ℕ → Rel (TTm type desc) (TTm type desc)
  precⁿ zero = Eqᴿ
  precⁿ (suc n) = precision path-id path-id (precⁿ n)

  -- two terms are related if they are related by a finite precision derivation
  -- TODO: possible to write using size types? (probably not)
  prec : Rel (TTm type desc) (TTm type desc)
  prec .rel i e1 e2 = ∃[ n ] rel (precⁿ n) i e1 e2

  -- We use the precision relation to simultaneously define well-typed terms
  -- Issue: this would work for an intrinsically typed language,
  -- but if we want type-based reasoning (and we really do)
  -- this is insufficient for a syntax with types on top
  -- TODO: is this solvable with an addl syntax for types
  -- WITHOUT indexing desc by that syntax?
  -- to give precision enough info, it needs the typing of Γ
  -- Question: would that be enough?
  well-typed : ∀{i Γ} → Pred (TTm type desc i Γ) L.0ℓ
  well-typed e = rel prec _ e e

open Lang public hiding (precⁿ)


open import DescUtils

private
  variable
    I : Set

--TODO: should be in path
path-projₗ : {d1 d2 d3 : Desc I} → Path (d1 `+ d2) d3 → Path d1 d3
path-projₗ (`σL .Bool x) = x true
path-projₗ (`σR A s₁ p) = `σR A s₁ (path-projₗ p)

path-projᵣ : {d1 d2 d3 : Desc I} → Path (d1 `+ d2) d3 → Path d2 d3
path-projᵣ (`σL .Bool x) = x false
path-projᵣ (`σR A s₁ p) = `σR A s₁ (path-projᵣ p)


--TODO: issue: precision does not take types of vars into account
_+ᴸ_ : Lang I → Lang I → Lang I
(L1 +ᴸ L2) .type  = type L1 `+ type L2
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .type-precision pt R .rel i t1 t2 =
  rel (type-precision L1 (path-projₗ pt) R) i t1 t2
  ⊎ rel (type-precision L2 (path-projᵣ pt) R) i t1 t2
(L1 +ᴸ L2) .precision pt pd R .rel i e1 e2 =
  rel (precision L1 (path-projₗ pt) (path-projₗ pd) R) i e1 e2
  ⊎ rel (precision L2 (path-projᵣ pt) (path-projᵣ pd) R) i e1 e2
