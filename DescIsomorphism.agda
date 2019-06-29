{-# OPTIONS --sized-types --safe #-}
-- We care more about isomorphism of descriptions that equivalence
-- since we can transport semantics across description morphisms
module DescIsomorphism {I} where

open import Data.Bool
open import Data.Product
open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Algebra.Structures
open import Algebra.FunctionProperties

open import Data.Var hiding (_<$>_)
open import Generic.Syntax

open import DescUtils
open import DescPreorder {I}

private module Pre = IsPreorder ⊑-is-preorder

infix 4 _≅_

-- We define isomorphism by a pair of injective functions
-- TODO: is this definition bad? I want the functions to compose to be inverses
-- Note: maybe the right definition is d1 ⊑ d2 = DescMorphism
-- and isomorphism is d1 ⊑ d2, d2 ⊑ d1 such that they are inverses
-- only reason to expect this definition is if ⊑ were a partial order and it's not
-- in this case, the two side of the isomorphism are provably injective I think

record _≅_ (d1 d2 : Desc I) : Set₁ where
  field
    ⊑R : d1 ⊑ d2
    ⊑L : d2 ⊑ d1

-- isomorphism is an equivalence relation
≅-is-equivalence : IsEquivalence _≅_
≅-is-equivalence = record {
  refl = record {
    ⊑R = Pre.reflexive refl ;
    ⊑L = Pre.reflexive refl }  ;
  sym = λ x → record { ⊑R = _≅_.⊑L x ; ⊑L = _≅_.⊑R x } ;
  trans = λ isoIJ isoJK → record {
    ⊑R = Pre.trans (_≅_.⊑R isoIJ) (_≅_.⊑R isoJK) ;
    ⊑L = Pre.trans (_≅_.⊑L isoJK) (_≅_.⊑L isoIJ) } }

⓪-≅-identity : Identity _≅_ ⓪ _`+_
⓪-≅-identity =
  (λ x → record {
    ⊑R = plus-⓪-no-increaseL ;
    ⊑L = plus-nondecreasingR }) ,
  λ x → record {
    ⊑R = plus-⓪-no-increaseR ;
    ⊑L = plus-nondecreasingL }

-- Descriptions form a monoid under isomorphism with ⓪ and `+
desc-monoid : IsMonoid _≅_ _`+_ ⓪
desc-monoid = record {
  isSemigroup = record {
    isMagma = record {
      isEquivalence = ≅-is-equivalence ;
      ∙-cong = λ iso1 iso2 → record {
        ⊑R = plus-congruence (_≅_.⊑R iso1) (_≅_.⊑R iso2) ;
        ⊑L = plus-congruence (_≅_.⊑L iso1) (_≅_.⊑L iso2) } } ;
    assoc = λ d1 d2 d3 → record {
      ⊑R = record {
         morph = MkDescMorphism (λ {
           (false , snd) → false , false , snd ;
           (true , false , snd) → false , true , snd ;
           (true , true , snd) → true ,  snd}) ;
         injective = mkInjective (λ {
           {false , snd} {false , .snd} refl → refl ;
           {false , snd} {true , false , snd₁} () ;
           {false , snd} {true , true , snd₁} () ;
           {true , false , snd} {false , snd₁} () ;
           {true , true , snd} {false , snd₁} () ;
           {true , false , snd} {true , false , .snd} refl → cong (true ,_) refl ;
           {true , true , snd} {true , true , .snd} refl → cong (true ,_) refl}) } ;
      ⊑L = record {
         morph = MkDescMorphism (λ{
           (false , false , snd) → false , snd ;
           (false , true , snd) → true , false , snd ;
           (true , snd) → true , true , snd}) ;
         injective = mkInjective (λ {
           {false , false , snd} {false , false , .snd} refl → refl ;
           {false , true , snd} {false , true , .snd} refl → refl ;
           {false , false , snd} {true , snd₁} () ;
           {false , true , snd} {true , snd₁} () ;
           {true , snd} {false , false , snd₁} () ;
           {true , snd} {false , true , snd₁} () ;
           {true , snd} {true , .snd} refl → cong (true ,_) refl }) } } } ;
  identity = ⓪-≅-identity }

-- TODO: clean up above by using this to show a monoid? (shorter proof)
desc-commutative-monoid : IsCommutativeMonoid _≅_ _`+_ ⓪
desc-commutative-monoid = record {
  isSemigroup = IsMonoid.isSemigroup desc-monoid ;
  identityˡ = proj₁ ⓪-≅-identity ;
  comm = λ x y → record {
    ⊑R = ⊑-commute ;
    ⊑L = ⊑-commute } }

-- of course, injective morphisms also form a preorder up to isomorphism
⊑-is-≅-preorder : IsPreorder _≅_ _⊑_
⊑-is-≅-preorder = record {
  isEquivalence = ≅-is-equivalence ;
  reflexive = λ x → _≅_.⊑R x ;
  trans = λ x x₁ → IsPreorder.trans ⊑-is-preorder x x₁ }


desc-setoid : Setoid _ _
desc-setoid = record { Carrier = Desc I ; _≈_ = _≅_ ; isEquivalence = ≅-is-equivalence }
