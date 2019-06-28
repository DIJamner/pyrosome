-- We care more about isomorphism of descriptions that equivalence
-- since we can transport semantics across description morphisms
module DescIsomorphism {I} where

open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Algebra.Structures

open import Data.Var hiding (_<$>_)
open import Generic.Syntax

open import DescPreorder {I}
module Pre = IsPreorder ⊑-is-preorder

infix 4 _≅_

-- We define isomorphism by a pair of injective functions

record _≅_ (d1 d2 : Desc I) : Set₁ where
  field
    ⊑R : d1 ⊑ d2
    ⊑L : d2 ⊑ d1

≅-refl : Reflexive _≅_
≅-refl = record {
    ⊑R = Pre.reflexive refl ;
    ⊑L = Pre.reflexive refl } 


-- isomorphism is an equivalence relation
≅-is-equivalence : IsEquivalence _≅_
≅-is-equivalence = record {
  refl = ≅-refl ;
  sym = λ x → record { ⊑R = _≅_.⊑L x ; ⊑L = _≅_.⊑R x } ;
  trans = λ isoIJ isoJK → record {
    ⊑R = Pre.trans (_≅_.⊑R isoIJ) (_≅_.⊑R isoJK) ;
    ⊑L = Pre.trans (_≅_.⊑L isoJK) (_≅_.⊑L isoIJ) } }
      
