{-# OPTIONS --sized-types --safe #-}

-- This module is for utilities and standard features
-- based on the generic syntax library
module DescUtils where

open import Level

open import Data.Empty
open import Data.List using (List)

open import Relation.Binary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; →-to-⟶)
open import Function.Inverse
open import Function.Equality using (_⟨$⟩_; _⟶_)

open import Data.Var
open import Generic.Syntax

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


