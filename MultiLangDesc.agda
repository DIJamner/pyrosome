module MultiLangDesc {I : Set} where

open import Generic.Syntax

open import Data.Bool
open import Data.Product
open import Data.List.Base as L hiding ([_])
open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; →-to-⟶)

open import Algebra.Structures

open import Function

open import Data.Var

open import Utils
open import DescUtils


open import DescPreorder {I}
                         
--open import DescIsomorphism {I}
                            
open import Algebra.FunctionProperties
            
open import DescHigherEquiv {I}
                            
                            

                            
-- we describe multilanguages via summing the descriptions of their subcomponents
-- note that for two components to be compatible, they must have the same syntactic
-- elements (I)
ml-desc : List (Desc I) → Desc I
ml-desc l = foldr _`+_ ⓪ l
                         
--open import Relation.Binary.SetoidReasoning
              
              
module Iso = IsCommutativeMonoid desc-monoid
open import Relation.Binary.Reasoning.Setoid desc-setoid
                                             
-- sums distribute over multilanguage descriptions up to isomorphism
ml-desc-distribute : {l1 l2 : List (Desc I)} → (ml-desc l1) `+ (ml-desc l2) ≅ ml-desc (l1 ++ l2)
ml-desc-distribute {[]} {l2} = IsCommutativeMonoid.identityˡ desc-monoid (ml-desc l2)
ml-desc-distribute {x ∷ l1} {l2} =
  begin
    (x `+ ml-desc l1) `+ (ml-desc l2)
    ≈⟨ Iso.assoc x (ml-desc l1) (ml-desc l2) ⟩
    x `+ (ml-desc l1) `+ (ml-desc l2)
    ≈⟨ Iso.∙-cong Iso.refl (ml-desc-distribute {l1} {l2}) ⟩
    ml-desc (x ∷ l1 ++ l2) ∎
                           
                           
select : (d : Desc I) → ∀ {l1 l2} → ml-desc (l1 ++ d ∷ l2) ≅ ml-desc (d ∷ (l1 ++ l2))
select d {[]} {l2} = Iso.refl {ml-desc (d ∷ l2)}
select d {x ∷ l1} {l2} =
  begin
    (x `+ ml-desc (l1 ++ d ∷ l2))
    ≈⟨ Iso.∙-cong Iso.refl (select d {l1} {l2}) ⟩
    x `+ ml-desc (d ∷ (l1 ++ l2))
    ≈˘⟨ (Iso.assoc x d (ml-desc (l1 ++ l2))) ⟩
    (x `+ d) `+ ml-desc (l1 ++ l2)
    ≈⟨ Iso.∙-cong (Iso.comm x d) Iso.refl ⟩
    (d `+ x) `+ ml-desc (l1 ++ l2)
    ≈⟨ Iso.assoc d x (ml-desc (l1 ++ l2)) ⟩
    ml-desc (d ∷ x ∷ l1 ++ l2) ∎
                               
                               


