{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --sized-types --safe #-}
module Path.Semantics {I : Set} where

open import Size

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List using (List)
open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; →-to-⟶)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Algebra.Structures
open import Algebra.FunctionProperties

open import Function using (_∘_)

open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence hiding (id; _∘_)

open import Data.Relation
open import Data.Environment
open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike

open import Generic.Relator as Relator
open import Generic.Syntax

open import Generic.Semantics
open import Generic.Simulation

open import Utils
open import DescUtils
open import Path.Path {I} hiding (commute; idempotent)
open import Path.DescEquivalence {I}
open import Path.Equality {I}


-- TODO: should these be in a separate file?
{- ================
Semantic properties
================= -}


private
  variable
    d d1 d2 d3 : Desc I
    X : List I → I ─Scoped
    σ : I
    Γ Δ : List I
    V C : I ─Scoped

S⟦_⟧$ : Path d1 d2 → Semantics d2 V C → Semantics d1 V C
S⟦ p ⟧$ S = record {
    th^𝓥 = S.th^𝓥 ;
    var = S.var ;
    alg = S.alg ∘ ⟦ p ⟧$ } where
    module S = Semantics S

{-
sem-distribute : (p1 : Path d2 d3) → (p2 : Path d1 d2) → (S : Semantics d3 V C) →
                 S⟦ p1 ∘ₚ p2 ⟧$ S ≅ₛ (S⟦ p2 ⟧$ ∘ S⟦ p1 ⟧$) S
sem-distribute p1 p2 S = record {
  thᴿ = λ { ρ refl → refl} ;
  varᴿ = λ { refl → refl} ;
  algᴿ =  λ _ _ →
    cong (Semantics.alg S) ∘
    interp-distributes' p1 p2 ∘
    {!!} }
    -}
--interp-distributes p1 p2

{-

 λ {b x x₁ → cong (Semantics.alg S)
    (interp-distributes' p1 p2
    (Eq.cong₂ (fmap _) {!!} refl))}

-}
