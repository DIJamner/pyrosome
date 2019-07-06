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

{- probably requires some sort of parametricity
open import Size
module _ {I : Set} { X Y : List I → I ─Scoped} {Γ Δ : List I} where
  fmap-shuffle : {d1 d2 : Desc I} →
                 {m : ∀ {X i Γ} → ⟦ d1 ⟧ X i Γ → ⟦ d2 ⟧ X i Γ} →
                {f : (Θ : List I) (i : I) → X Θ i Γ → Y Θ i Δ} →
                ∀{i e} → m {Y} {i} (fmap d1 f e) ≡ fmap d2 f (m {X} e)
  fmap-shuffle {`σ A x} {d2} {m} {f} {e = fst , snd} = {!!}
  fmap-shuffle {`X x x₁ d1} {d2} {m} {f} {e = fst , snd} = {!fst!}
  fmap-shuffle {`∎ x} {d2} {m} {f} {e = refl} = {!!}
-}
