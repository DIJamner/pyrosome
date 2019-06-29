{-# OPTIONS --sized-types --safe #-}
-- We define appropriate notations of equivalence between preorders/isomorphisms
-- so that we can establish properties about them
module DescHigherEquiv {I} where

open import Generic.Syntax
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Algebra.FunctionProperties
open import Relation.Binary hiding (Rel)

open import Utils
open import DescPreorder {I}
open import DescIsomorphism {I}

module _ {d1 d2 : Desc I} where
  -- We define equivalence between morphisms by extensional equivalence
  _≅₂_ : d1 ⊑ d2 → d1 ⊑ d2 → Set₁
  m1 ≅₂ m2 = ∀{X i Γ} → {e : ⟦ d1 ⟧ X i Γ} → _⊑_.oapply m1 e ≡ _⊑_.oapply m2 e

  ≅₂-is-equivalence : IsEquivalence _≅₂_
  ≅₂-is-equivalence = record {
    refl = refl ;
    sym = λ x → sym x ;
    trans = λ x x₁ → trans x x₁ }

module _ {d1 d2 : Desc I} where
  record _≅̂₂_ (m1 m2 : d1 ≅ d2) : Set₁ where
    module M1 = _≅_ m1
    module M2 = _≅_ m2
    field eq-l : M1.⊑L ≅₂ M2.⊑L
          eq-r : M1.⊑R ≅₂ M2.⊑R

  module Eq12 = IsEquivalence (≅₂-is-equivalence {d1} {d2})
  module Eq21 = IsEquivalence (≅₂-is-equivalence {d2} {d1})
  
  ≅̂₂-is-equivalence : IsEquivalence _≅̂₂_
  ≅̂₂-is-equivalence = record {
    refl = record { eq-l = refl ; eq-r = refl } ;
    sym = λ x → record {
      eq-l = sym (_≅̂₂_.eq-l x) ;
      eq-r = sym (_≅̂₂_.eq-r x) } ;
    trans = λ x x₁ → record {
      eq-l = trans (_≅̂₂_.eq-l x) (_≅̂₂_.eq-l x₁) ;
      eq-r =  trans (_≅̂₂_.eq-r x) (_≅̂₂_.eq-r x₁) } }




-- TODO: should probably have ⊑ be a preorder for isomorphism as well, use that here?
-- general goal: do everything up to isomorphism of descriptions
-- this allows for commutativity of `+, among other flexibilities, and generally makes sense
sum-pushout : {ds d1 d2 : Desc I} → Pushout ds (d1 `+ ds) (d2 `+ ds) (d1 `+ d2 `+ ds)
sum-pushout = record {
  morph-rel-eq = ≅₂-is-equivalence ;
  P =  ⊑-is-preorder ;
  1ltr = plus-congruence (IsPreorder.refl ⊑-is-preorder) plus-nondecreasingR ;
  2ltr = plus-nondecreasingR ;
  slt1 = plus-nondecreasingR ;
  slt2 = plus-nondecreasingR ;
  sides-commute = refl }
