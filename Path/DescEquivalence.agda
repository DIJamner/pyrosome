{-# OPTIONS --sized-types --safe #-}
module Path.DescEquivalence {I : Set} where

open import Data.Bool
open import Data.Product
open import Data.List using (List)
open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; →-to-⟶)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Algebra.Structures
open import Algebra.FunctionProperties

import Function

open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence hiding (id; _∘_)

open import Data.Relation
open import Data.Var hiding (_<$>_)
open import Generic.Syntax

open import Utils
open import DescUtils
open import Path.Path {I} as Path hiding (commute; idempotent)

private
  variable
    d d1 d2 d3 : Desc I
    X : List I → I ─Scoped
    i : I
    Γ : List I

record _≈_ (d1 d2 : Desc I) : Set₁ where
  field
    to : Path d1 d2
    from : Path d2 d1

  to$ : ⟦ d1 ⟧ X i Γ → ⟦ d2 ⟧ X i Γ
  to$ = ⟦ to ⟧$
  
  from$ : ⟦ d2 ⟧ X i Γ → ⟦ d1 ⟧ X i Γ
  from$ = ⟦ from ⟧$

  equiv : ⟦ d1 ⟧ X i Γ ⇔ ⟦ d2 ⟧ X i Γ
  equiv = equivalence to$ from$

{- ====================================
Properties derived from path properties
==================================== -}

isEquivalence : IsEquivalence _≈_
isEquivalence = record {
  refl = record { to = id ; from = id } ;
  sym = λ x → record { to = _≈_.from x ; from = _≈_.to x } ;
  trans = λ x y → record {
    to = (_≈_.to y) ∘ₚ (_≈_.to x) ;
    from = (_≈_.from x) ∘ₚ (_≈_.from y) } }

_`+̰_ : Congruent₂ _≈_ _`+_
e1 `+̰ e2 = record {
  to = _≈_.to e1 `+ₚ _≈_.to e2 ;
  from = (_≈_.from e1) `+ₚ (_≈_.from e2) }

commute : Commutative _≈_ _`+_
commute d1 d2 = record {
  to = Path.commute d1 d2 ;
  from = Path.commute d2 d1 }

-- we use the left injection here arbitrarily
idempotent : Idempotent _≈_ _`+_
idempotent x = record {
  to = Path.idempotent x ;
  from = injₗ }

