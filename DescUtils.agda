{-# OPTIONS --sized-types --safe #-}

-- This module is for utilities and standard features
-- based on the generic syntax library
module DescUtils where

open import Level

open import Data.Product
open import Data.Empty
open import Data.List using (List)

open import Relation.Binary hiding (_⇒_;Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; →-to-⟶)
open import Function.Inverse
open import Function.Equality using (_⟨$⟩_; _⟶_)
open import Function

open import Data.Relation
open import Data.Var
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Simulation

module _ {I : Set} where

  -- the empty description
  ⓪ : Desc I
  ⓪ = `σ ⊥ λ ()
           
  -- proof that the description is indeed empty
  ⓪-empty : ∀{X i Γ} → ⟦ ⓪ ⟧ X i Γ → ⊥
  ⓪-empty ()

  private
    variable
      d1 d2 : Desc I
      X : List I → I ─Scoped
      i : I
      Γ : List I
      ℓ ℓ₁ ℓ₂ : Level

  case⟶ : {A : Setoid zero zero} →
          (Eq.setoid (⟦ d1 ⟧ X i Γ) ⟶ A) →
          (Eq.setoid (⟦ d2 ⟧ X i Γ) ⟶ A) →
          (Eq.setoid (⟦ d1 `+ d2  ⟧ X i Γ) ⟶ A)
  case⟶ f g = →-to-⟶ (case (f ⟨$⟩_) (g ⟨$⟩_))

module _ {I : Set} {V C : I ─Scoped} where
  private variable d d1 d2 : Desc I

  _≅ₛ_ : Semantics d V C → Semantics d V C → Set
  S1 ≅ₛ S2 = Simulation _ S1 S2 Eqᴿ Eqᴿ

module _ {I : Set} where
  private variable d d1 d2 : Desc I
  open import Size
  open import Generic.Semantics.Syntactic

  morph-to-sem : (∀ {V C} → Semantics d1 V C → Semantics d2 V C) → Semantics d2 (Tm d1 ∞) (Tm d1 ∞)
  morph-to-sem m = m Sub

module _ {I : Set} {V : I ─Scoped} where
  TransitiveRel : Rel V V → Set
  TransitiveRel R = ∀ {σ Γ} →  Transitive (rel R σ {Γ})

module _ {I : Set} where

  private variable d1 d2 d3 : Desc I

  _∘ₘ_ : DescMorphism d2 d3 → DescMorphism d1 d2 → DescMorphism d1 d3
  m1 ∘ₘ m2 = MkDescMorphism (DescMorphism.apply m1 ∘′ DescMorphism.apply m2)

  open import Data.Bool

  minjₗ : DescMorphism d1 (d1 `+ d2)
  minjₗ .DescMorphism.apply e = true , e

  minjᵣ : DescMorphism d2 (d1 `+ d2)
  minjᵣ .DescMorphism.apply e = false , e

-- relation tools
module _ {I : Set} where

  private variable A B : I ─Scoped

  -- TODO: move to descutils
  _⇒ᴿ_ : Rel A B → Rel A B → Set
  R1 ⇒ᴿ R2 = ∀{i Γ e1 e2} → rel R1 i {Γ} e1 e2 → rel R2 i e1 e2

  open import Data.Sum

  infixr 8 _⊎ᴿ_

  _⊎ᴿ_ : Rel A B → Rel A B → Rel A B
  (R1 ⊎ᴿ R2) .rel i e1 e2 = rel R1 i e1 e2 ⊎ rel R2 i e1 e2
