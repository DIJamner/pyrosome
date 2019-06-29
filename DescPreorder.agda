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
open import Function using (_∋_)

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


plus-⓪-no-increaseL : {d : Desc I} → ⓪ `+ d ⊑ d
plus-⓪-no-increaseL {d} = record {
  morph = MkDescMorphism λ x → case (λ ()) (λ y → y) ((proj₁ x) , proj₂ x) ;
  injective = λ {X i Γ} → mkInjective (λ { {false , snd} {false , .snd} refl → refl} )}
  
plus-⓪-no-increaseR : {d : Desc I} → d `+ ⓪ ⊑ d
plus-⓪-no-increaseR {d} = record {
  morph = MkDescMorphism λ x → case (λ y → y) (λ ()) ((proj₁ x) , proj₂ x) ;
  injective = λ {X i Γ} → mkInjective (λ { {true , snd} {true , .snd} refl → refl} )}
                                                                                   
plus-nondecreasingL : {d1 d2 : Desc I} → d1 ⊑ d1 `+ d2
plus-nondecreasingL {d1} {d2} = record {
  morph = MkDescMorphism (λ {X} {i} {Δ} → _,_ true) ;
  injective =  mkInjective (λ { {i1} {.i1} refl → refl})}
                                                  
plus-nondecreasingR : {d1 d2 : Desc I} → d2 ⊑ d1 `+ d2
plus-nondecreasingR {d1} {d2} = record {
  morph = MkDescMorphism (λ {X} {i} {Δ} → _,_ false) ;
  injective =  mkInjective (λ { {i1} {.i1} refl → refl})}

-- TODO: change name and handle overlap via namespacing?
⓪-⊑-identity : Identity _⊑_ ⓪ _`+_
⓪-⊑-identity = ((λ x → plus-⓪-no-increaseL) , λ x → plus-⓪-no-increaseR)


-- TODO: find the right way to inline
tmp : {B : Bool → Set} → ∀ {b} → {a1 a2 : B b} → (Σ Bool B ∋ b , a1) ≡ (b , a2) → a1 ≡ a2
tmp refl = refl

plus-congruence : Congruent₂ _⊑_ _`+_
plus-congruence = λ leq1 leq2 → record {
  morph = MkDescMorphism (λ {
    (false , snd) → false , _⊑_.oapply leq2 snd ;
    (true , snd) → true , _⊑_.oapply leq1 snd} ) ;
  injective = mkInjective (λ {
    {false , snd} {false , snd₁} x₁ → cong ( false ,_) (_⊑_.oinj leq2 (tmp x₁)) ;
    {true , snd} {true , snd₁} x₁ → cong (true ,_) (_⊑_.oinj leq1 (tmp x₁))} ) }

-- under isomorphism, descriptions commute
⊑-commute : {d1 d2 : Desc I} → d1 `+ d2 ⊑ d2 `+ d1
⊑-commute = record {
  morph = MkDescMorphism (λ {
    (false , snd) → true , snd ;
    (true , snd) → false , snd}) ;
  injective = mkInjective (λ {
    {false , snd} {false , .snd} refl → refl ;
    {true , snd} {true , .snd} refl → refl}) }
