{-# OPTIONS --sized-types --safe #-}
-- We build a preorder on descriptions via injective morphisms
-- This lets us define description isomorphism as ordered in both directions
module DescPreorder {I : Set} where

open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Data.Product
open import Data.Bool
open import Function using (_∋_; id;_∘_)

open import Data.Var hiding (_<$>_)
open import Generic.Syntax

open import DescUtils

{-
  -- Description morphisms form a preorder wrt to equivalence
  desc-morph-preorder : IsPreorder _≡_ (DescMorphism {I})
  desc-morph-preorder = record {
    isEquivalence = Eq.isEquivalence ;
    reflexive = λ {i j} x →  MkDescMorphism (tmp i j x) ;
    trans = λ x x₁ → MkDescMorphism (λ x₂ → DescMorphism.apply x₁ (DescMorphism.apply x x₂)) }

  However, this is not an interesting preorder since it just partitions descriptions into inhabited
  and uninhabited ones
-}

infix 4 _⊑_

_⊑_ : (d1 d2 : Desc I) → Set₁
d1 ⊑ d2 = ∀ {X i Δ} → ⟦ d1 ⟧ X i Δ → ⟦ d2 ⟧ X i Δ


                       
⊑-is-preorder : IsPreorder _≡_ _⊑_
⊑-is-preorder = record {
  isEquivalence = Eq.isEquivalence ;
  reflexive = λ {refl → id } ;
  trans = λ g f → f ∘ g }


{- Properties relating to coproducts of descriptions -}

plus-⓪-no-increaseL : {d : Desc I} → ⓪ `+ d ⊑ d
plus-⓪-no-increaseL (false , snd) = snd

plus-⓪-no-increaseR : {d : Desc I} → d `+ ⓪ ⊑ d
plus-⓪-no-increaseR (true , snd) = snd

plus-nondecreasingL : {d1 d2 : Desc I} → d1 ⊑ d1 `+ d2
plus-nondecreasingL = true ,_

plus-nondecreasingR : {d1 d2 : Desc I} → d2 ⊑ d1 `+ d2
plus-nondecreasingR = false ,_

⓪-right-identity : RightIdentity _⊑_ ⓪ _`+_
⓪-right-identity d (true , snd) = snd

⓪-left-identity : LeftIdentity _⊑_ ⓪ _`+_
⓪-left-identity d (false , snd) = snd

⓪-identity : Identity _⊑_ ⓪ _`+_
⓪-identity = ⓪-left-identity , ⓪-right-identity

`+-congruence : Congruent₂ _⊑_ _`+_
`+-congruence f g (false , snd) = false , g snd
`+-congruence f g (true , snd) = true , f snd

`+-commutes : {d1 d2 : Desc I} → d1 `+ d2 ⊑ d2 `+ d1
`+-commutes (false , snd) = true , snd
`+-commutes (true , snd) = false , snd

`+-coproduct : {d1 d2 d3 : Desc I} → d1 ⊑ d3 → d2 ⊑ d3 → d1 `+ d2 ⊑ d3
`+-coproduct f g (false , snd) = g snd
`+-coproduct f g (true , snd) = f snd

{- TODO: what is the product of two descriptions? might be interesting -}
