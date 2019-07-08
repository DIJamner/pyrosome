{-# OPTIONS --sized-types --safe #-}
module Path.Equality {I : Set} where

open import Data.Bool
open import Data.Empty
open import Data.Product as Prod
open import Data.List hiding ([_])

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; cong; refl; isEquivalence)
open import Relation.Binary hiding (Rel)
open import Algebra.FunctionProperties

open import Function using (_∘_)

open import Data.Var using (_─Scoped)
open import Generic.Syntax

open import DescUtils
open import Path.Path {I}



-- TODO: I want to include things like IsSemigroupMorphism
-- This relies on the definition of description isomorphism,
-- but that definition relies on this one.
-- What to include where?
{- ==============
Path Equality
================ -}

open import Algebra.Morphism
                       
private
  variable
    d d1 d2 d3 : Desc I
    X : List I → I ─Scoped
    i : I
    Γ : List I

-- TODO: might I want to parameterize this over e-equality?
_≅₂_ : Path d1 d2 → Path d1 d2 → Set₁
_≅₂_ {d1} p1 p2 = ∀ {X i Γ} → (e : ⟦ d1 ⟧ X i Γ) → ⟦ p1 ⟧$ e ≡ ⟦ p2 ⟧$ e

{- ==========================
Properties of path operations
========================== -}

id-identity : (e : ⟦ d ⟧ X i Γ) → ⟦ id ⟧$ e ≡ e
id-identity {`σ A x} (fst , snd) = cong (fst ,_) (id-identity snd)
id-identity {`X Δ j d} (fst , snd) = cong (fst ,_) (id-identity snd)
id-identity {`∎ i} refl = refl

interp-distributes : (p1 : Path d2 d3) → (p2 : Path d1 d2) → (e : ⟦ d1 ⟧ X i Γ) →
                     ⟦ p1 ∘ₚ p2 ⟧$ e ≡ (⟦ p1 ⟧$ ∘ ⟦ p2 ⟧$) e
interp-distributes p1 (`σL A x) (fst , snd) = interp-distributes (p1) (x fst) snd
interp-distributes (`σL .A p1) (`σR A s p2) e = interp-distributes (p1 s) p2 e
interp-distributes (`σR A₁ s₁ p1) (`σR A s p2) e =
  cong (s₁ ,_) (interp-distributes p1 (`σR A s p2) e)
interp-distributes (`σR A s p1) (`XP Γ i p2) (fst , snd) =
  cong (s ,_) (interp-distributes p1 (`XP Γ i p2) ((fst , snd)))
interp-distributes (`XP .Γ .i p1) (`XP Γ i p2) (fst , snd) =
  cong (fst ,_) (interp-distributes p1 p2 snd)
interp-distributes (`σR A s p1) (`∎P i) e = cong (s ,_) (interp-distributes p1 (`∎P i) e)
interp-distributes (`∎P .i) (`∎P i) e = refl
