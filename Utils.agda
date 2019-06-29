{-# OPTIONS --safe #-}
-- This module is for utilities that do not directly pertain
-- to the generic syntax library
module Utils where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

open import Relation.Binary
open import Algebra.Structures
open import Level


-- when combining multiple languages, we want to be able to merge shared components
-- TODO: add level for equivalence
record Pushout {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {_≈_ : A → A → Set ℓ₂} {_≤_ : A → A → Set ℓ₃}
  (P : IsPreorder _≈_ _≤_) (s a1 a2 r : A) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  module P = IsPreorder P
  field 1ltr : a1 ≤ r
        2ltr : a2 ≤ r
        slt1 : s ≤ a1
        slt2 : s ≤ a2
        sides-commute : P.trans slt1 1ltr ≡ P.trans slt2 2ltr
