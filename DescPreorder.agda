-- We build a preorder on descriptions via injective morphisms
-- This lets us define description isomorphism as ordered in both directions
module DescPreorder {I : Set} where

open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Algebra.Structures

open import Data.Var hiding (_<$>_)
open import Generic.Syntax

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

-- Injective description morphisms form a more interesting preorder
record _⊑_ (d1 d2 : Desc I) : Set₁ where
  field
    morph : DescMorphism d1 d2
    injective : ∀{X i Δ} → Injective (DescMorphism.apply morph {X} {i} {Δ})
    
  -- convenience accessor
  oapply : ∀ {X i Δ} → ⟦ d1 ⟧ X i Δ → ⟦ d2 ⟧ X i Δ
  oapply = DescMorphism.apply morph
                              
  -- convenience accessor
  oinj : ∀ {X i Δ i₁ i₂} → oapply {X} {i} {Δ} i₁ ≡ oapply i₂ → i₁ ≡ i₂
  oinj = Injective.inj injective
                       
⊑-is-preorder : IsPreorder _≡_ _⊑_
⊑-is-preorder = record {
  isEquivalence = Eq.isEquivalence ;
  reflexive = λ {refl → record {
    morph = MkDescMorphism (λ {X} {i} {Δ} z₁ → z₁) ;
    injective = λ {X} {i} {Δ} → mkInjective (λ {i₁} {i₂} z₁ → z₁) }} ;
  trans = λ x x₁ → record {
    morph = MkDescMorphism (λ x₂ → _⊑_.oapply x₁ (_⊑_.oapply x x₂)) ;
    injective = mkInjective λ x₂ →  _⊑_.oinj x (_⊑_.oinj x₁ x₂) } }
