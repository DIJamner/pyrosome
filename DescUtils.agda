-- This module is for utilities and standard features
-- based on the generic syntax library
module DescUtils where

open import Data.Empty

open import Generic.Syntax

module _ {I : Set} where

  -- the empty description
  ⓪ : Desc I
  ⓪ = `σ ⊥ λ ()
           
  -- proof that the description is indeed empty
  ⓪-empty : ∀{X i Γ} → ⟦ ⓪ ⟧ X i Γ → ⊥
  ⓪-empty ()
