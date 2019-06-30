{-# OPTIONS --sized-types --safe #-}
-- We care more about isomorphism of descriptions that equivalence
-- since we can transport semantics across description morphisms
module DescIsomorphism {I} where

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

open import Function.Inverse renaming (_∘_ to _∘ᴵ_)
open import Function.Equality using (_⟨$⟩_;_∘_)

open import Data.Var hiding (_<$>_)
open import Generic.Syntax

open import DescUtils
open import DescPreorder using(_⊑_)
import DescPreorder {I} as Pre

--private module Pre = IsPreorder ⊑-is-preorder

desc-≡ : Setoid _ _
desc-≡ = Eq.setoid (Desc I)

private
  variable
    d1 d2 : Desc I


infix 4 _≅_

-- We use inverses/isomorphism as our equivalence for descriptions
-- since we want commutativity of `+ and other sensible
-- (but not syntactically equal) relationships between descriptions

_≅_ : Desc I → Desc I → Set₁
d1 ≅ d2 = ∀ {X i Γ} → ⟦ d1 ⟧ X i Γ ↔ ⟦ d2 ⟧ X i Γ

right : d1 ≅ d2 → d1 ⊑ d2
right eq = Inverse.to eq ⟨$⟩_

left : d1 ≅ d2 → d2 ⊑ d1
left eq = Inverse.from eq ⟨$⟩_

isEquivalence : IsEquivalence _≅_
isEquivalence  = record {
  refl = id ;
  sym = λ x → sym x ;
  trans = λ f g → g ∘ᴵ f }


⓪-identity : Identity _≅_ ⓪ _`+_
⓪-identity =
  (λ x → record {
    to = →-to-⟶ Pre.plus-⓪-no-increaseL ;
    from = →-to-⟶ Pre.plus-nondecreasingR ;
    inverse-of = record {
      left-inverse-of = λ { (false , snd) → refl} ;
      right-inverse-of = λ x → refl } }) ,
  (λ x → record {
    to = →-to-⟶ Pre.plus-⓪-no-increaseR ;
    from = →-to-⟶ Pre.plus-nondecreasingL ;
    inverse-of = record {
      left-inverse-of = λ { (true , snd) → refl } ;
      right-inverse-of = λ x₁ → refl } })

`+-cong : Congruent₂ _≅_ _`+_
`+-cong iso1 iso2 = record {
  to = case⟶ (→-to-⟶ (true ,_ ) ∘ Inverse.to iso1) (→-to-⟶ (false ,_ ) ∘ Inverse.to iso2) ;
  from = case⟶ ((→-to-⟶ (true ,_ ) ∘ Inverse.from iso1)) ((→-to-⟶ (false ,_ ) ∘ Inverse.from iso2)) ;
  inverse-of = record {
    left-inverse-of = λ {
      (false , snd) → cong (false ,_ ) (Inverse.left-inverse-of iso2 snd)  ;
      (true , snd) → cong (true ,_ ) (Inverse.left-inverse-of iso1 snd) } ;
    right-inverse-of = λ {
      (false , snd) → cong (false ,_) (Inverse.right-inverse-of iso2 snd) ;
      (true , snd) → cong (true ,_) (Inverse.right-inverse-of iso1 snd)} } }

`+-assoc : Associative _≅_ _`+_
`+-assoc d1 d2 d3 =  record {
  to = case⟶
    (→-to-⟶ λ { (false , snd) → false , true , snd ;
                (true , snd) → true , snd})
    (→-to-⟶ (λ x → false , false , x)) ;
  from = case⟶
    (→-to-⟶ λ x → true , true , x)
    (→-to-⟶ (λ { (false , snd) → false , snd ;
                 (true , snd) → true , false , snd})) ;
  inverse-of = record {
    left-inverse-of = λ {
      (false , snd) → refl ;
      (true , false , snd) → refl ;
      (true , true , snd) → refl} ;
    right-inverse-of =  λ {
      (false , false , snd) → refl ;
      (false , true , snd) → refl ;
      (true , snd) → refl} } }

-- Descriptions form a commutative monoid under isomorphism with ⓪ and `+
desc-monoid : IsCommutativeMonoid _≅_ _`+_ ⓪
desc-monoid = record {
  isSemigroup = record {
    isMagma = record {
      isEquivalence = isEquivalence ;
      ∙-cong = `+-cong } ;
    assoc = `+-assoc } ;
  identityˡ = proj₁ ⓪-identity ;
  comm = λ x y → record {
    to = →-to-⟶ λ { (false , snd) → true , snd ; (true , snd) → false , snd} ;
    from = →-to-⟶ λ { (false , snd) → true , snd ; (true , snd) → false , snd} ;
    inverse-of = record {
      left-inverse-of = λ { (false , snd) → refl ; (true , snd) → refl} ;
      right-inverse-of = λ { (false , snd) → refl ; (true , snd) → refl} } } }

-- morphisms form a preorder under isomorphism as well as equivalence
⊑-isPreorder : IsPreorder _≅_ _⊑_
⊑-isPreorder = record {
  isEquivalence = isEquivalence ;
  reflexive = right ;
  trans = λ f g → g Function.∘ f }

{-
-- of course, injective morphisms also form a preorder up to isomorphism
⊑-is-≅-preorder : IsPreorder _≅_ _⊑_
⊑-is-≅-preorder = record {
  isEquivalence = ≅-is-equivalence ;
  reflexive = λ x → _≅_.⊑R x ;
  trans = λ x x₁ → IsPreorder.trans ⊑-is-preorder x x₁ }


desc-setoid : Setoid _ _
desc-setoid = record { Carrier = Desc I ; _≈_ = _≅_ ; isEquivalence = ≅-is-equivalence }
-}
