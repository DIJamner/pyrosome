{-# OPTIONS --sized-types --safe #-}
module Path.Path {I : Set} where

open import Data.Bool hiding (T)
open import Data.Empty
open import Data.Product as Prod
open import Data.List hiding ([_]; lookup)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; cong; refl; isEquivalence)
open import Relation.Binary hiding (Rel)
open import Algebra.FunctionProperties

open import Function using (_∘_)

open import Data.Var using (_─Scoped)
open import Generic.Syntax

open import DescUtils

--TODO: I want a path from (A × B) to (B × A)
data Path : Desc I → Desc I → Set₁ where
  `σL : (A : Set) → ∀ {d d2} → ((s : A) → Path (d s) d2) → Path (`σ A d) d2
  `σR : (A : Set) → ∀ {d1 d} → (s : A) → Path d1 (d s) → Path d1 (`σ A d)
  `XP : (Γ : List I) → (i : I) → ∀ {d1 d2} → Path d1 d2 → Path (`X Γ i d1) (`X Γ i d2)
  `∎P : (i : I) → Path (`∎ i) (`∎ i)

private
  variable
    d d1 d2 d3 : Desc I
    X : List I → I ─Scoped
    i : I
    Γ : List I

⟦_⟧$ : Path d1 d2 → ∀ {X i Γ} → ⟦ d1 ⟧ X i Γ → ⟦ d2 ⟧ X i Γ
⟦ `σL A x ⟧$ (fst , snd) = ⟦ x fst ⟧$ snd
⟦ `σR A s p ⟧$ e = s , ⟦ p ⟧$ e
⟦ `XP Γ i p ⟧$ (fst , snd) = fst , ⟦ p ⟧$ snd
⟦ `∎P i ⟧$ e = e

morph : Path d1 d2 → DescMorphism d1 d2
morph p = MkDescMorphism ⟦ p ⟧$

id : Path d d
id {`σ A x} = `σL A (λ s → `σR A s id)
id {`X Γ i d} = `XP Γ i id
id {`∎ i} = `∎P i

-- note : there are 2 choices for sequencing L and R σs
-- they should produce paths with the same interpretations
_∘ₚ_ : Path d2 d3 → Path d1 d2 → Path d1 d3
`σR A s p1 ∘ₚ p2 = `σR A s (p1 ∘ₚ p2)
`σL A x ∘ₚ `σR .A s p2 = x s ∘ₚ p2
`XP Γ i p1 ∘ₚ `XP .Γ .i p2 = `XP Γ i (p1 ∘ₚ p2)
`∎P i ∘ₚ `∎P .i = `∎P i
-- this clause could match anything, but σR is already handled
p1@(`σL A x) ∘ₚ `σL A₁ x₁ = `σL A₁ (λ s → p1 ∘ₚ x₁ s)
p1@(`XP Γ i p) ∘ₚ `σL A₁ x₁ = `σL A₁ (λ s → p1 ∘ₚ x₁ s)
p1@(`∎P i) ∘ₚ `σL A₁ x₁ = `σL A₁ (λ s → p1 ∘ₚ x₁ s)

-- TODO: Prove that the order of cases above doesn't matter
-- wrt the functions generated

isPreorder : IsPreorder _≡_ Path
IsPreorder.isEquivalence isPreorder = isEquivalence
IsPreorder.reflexive isPreorder refl = id
IsPreorder.trans isPreorder p1 p2 = p2 ∘ₚ p1

{- =================================
Properties of Description coproducts
================================= -}

-- `+ is a coproduct with paths as morphisms
_`+L_ : Path d1 d3 → Path d2 d3 → Path (d1 `+ d2) d3
p1 `+L p2 = `σL Bool λ { false → p2 ; true → p1}

-- ⓪ is initial with paths as morphisms
⓪-initial : Path ⓪ d
⓪-initial = `σL ⊥ (λ { ()})

-- an example of what can be shown from these axioms
⓪`+-path : Path (⓪ `+ d) d
⓪`+-path = ⓪-initial `+L id

injₗ : Path d1 (d1 `+ d2)
injₗ = `σR Bool true id

injᵣ : Path d2 (d1 `+ d2)
injᵣ = `σR Bool false id

-- adding the inputs and outputs of two paths
_`+ₚ_ : Congruent₂ Path _`+_
p1 `+ₚ p2 = (injₗ ∘ₚ p1) `+L (injᵣ ∘ₚ p2)

commute : Commutative Path _`+_
commute d1 d2 = `σL Bool λ { true → injᵣ ; false → injₗ }

idempotent : Idempotent Path _`+_
idempotent x = id `+L id

{- ======================
fmap shuffle property:
This shows that paths behave parametrically wrt the next level down (X)
====================== -}

fmap-shuffle : (p : Path d1 d2) → {X Y : List I → I ─Scoped} → {i : I} → {Γ Δ : List I} →
               (e :  ⟦ d1 ⟧ X i Γ) →
               (f : ∀ Φ i → X Φ i Γ → Y Φ i Δ) →
               ⟦ p ⟧$ {Y} (fmap d1 f e) ≡ (fmap d2 f (⟦ p ⟧$ e))
fmap-shuffle {`σ A x} {d2} (`σL .A x₁) (fst , snd) f = fmap-shuffle (x₁ fst) snd f
fmap-shuffle {`σ A x} {.(`σ A₁ _)} (`σR A₁ s p) e f = cong (s ,_) (fmap-shuffle p e f)
fmap-shuffle {`X x x₁ d1} {.(`σ A _)} (`σR A s p) e f =
  cong (s ,_) (fmap-shuffle p e f)
fmap-shuffle {`X x x₁ d1} {.(`X x x₁ _)} (`XP .x .x₁ p) (fst , snd) f =
  cong (f x x₁ fst ,_) (fmap-shuffle p snd f)
fmap-shuffle {`∎ x} {.(`σ A _)} (`σR A s p) refl f = cong (s ,_) (fmap-shuffle p refl f)
fmap-shuffle {`∎ x} {.(`∎ x)} (`∎P .x) e f = refl

