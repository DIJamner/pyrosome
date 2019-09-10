open import Generic.Syntax

open import Data.Bool
open import Data.Product
open import Data.List.Base as L hiding ([_])
open import Data.List.All hiding (mapA; sequenceA)
open import Function hiding (case_of_)

data IdxPair (I J : Set) : Set where
    LeftTm : I -> IdxPair I J
    PairTm : I -> J -> IdxPair I J
    RightTm : J -> IdxPair I J

descPair : {I J : Set} → Desc I → Desc J → Desc (IdxPair I J)
descPair {I} {J} dl dr = (reindex LeftTm dl) `+ (reindex RightTm dr) `+
         (`σ I $ λ i →
           `σ J $ λ j → `X [] (LeftTm i) $ `X [] (RightTm j) $ `∎ (PairTm i j))



injPairL : {I J : Set} → (dl : Desc I) → (dr : Desc J) →
  DescMorphism (reindex LeftTm dl) (descPair dl dr)
injPairL dl dr = MkDescMorphism (λ e → true , e)


injPairR : {I J : Set} → (dl : Desc I) → (dr : Desc J) →
  DescMorphism (reindex RightTm dr) (descPair dl dr)
injPairR dl dr = MkDescMorphism (λ e → false , true , e)

open import Data.Sum

descEither : {I : Set} → Desc I → {J : Set} → Desc J → Desc (I ⊎ J)
descEither dl dr = (reindex inj₁ dl) `+ (reindex inj₂ dr)


descInj₁ : {I J : Set} → (dl : Desc I) → (dr : Desc J) →
  DescMorphism (reindex inj₁ dl) (descEither dl dr)
descInj₁ dl dr = MkDescMorphism (λ e → true , e)

descInj₂ : {I J : Set} → (dl : Desc I) → (dr : Desc J) →
  DescMorphism (reindex inj₂ dr) (descEither dl dr)
descInj₂ dl dr = MkDescMorphism (λ e → false , e)

data _+Ctx' (I : Set) : Set where
  Term : I → I +Ctx'
  Context : List I → I → I +Ctx'

_-Ctx : {I : Set} → Desc I → Desc (I +Ctx')
(`σ A df)-Ctx = {!!}
(`X Δ j d)-Ctx = {!!}
(`∎ i)-Ctx = {!!}

_+Ctx : {I : Set} → Desc I → Desc (I +Ctx')
_+Ctx {I} d = (d -Ctx) `+ (`σ I $ λ i → `∎(Context {!!} i)) `+ (reindex Term d)

  
ml-desc : {I : Set} → List (Desc I) → Desc I → Desc I
ml-desc l d = foldr _`+_ d l

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

multi-lang-id : {I : Set} → (d : Desc I) → ml-desc [] d ≡ d
multi-lang-id d = refl

multi-lang-app : {I : Set} → (l1 l2 : List (Desc I)) → (d : Desc I) →
  ml-desc l1 (ml-desc l2 d) ≡ ml-desc (l1 ++ l2) d
multi-lang-app [] l2 d = refl
multi-lang-app (x ∷ l1) l2 d = begin
      ml-desc (x ∷ l1) (ml-desc l2 d)
  ≡⟨⟩ x `+ ( ml-desc l1 (ml-desc l2 d))
  ≡⟨⟩ cong (x `+_) (multi-lang-app l1 l2 d)


--multi-lang-tl : {I : Set} → (l1 l2 : List (Desc I)) → (d1 d2 : Desc I) →
--  (ml-desc l1 d1) `+ (ml-desc l2 d2) ≅ 

module MultiLang {I : Set} where

  open import Data.Empty
  
  ⓪ : Desc I
  ⓪ = `σ ⊥ λ ()

  -- TODO: prove isomorphisms of descs involving sum and 0

  record MultiDesc : Set₂ where
    field descs : List (Desc I)
    as-desc : Desc I
    as-desc = foldr _`+_ ⓪ descs


--record Typed {I : Set} {tm ty jdg : I} (d : Desc I) where
--  field get-term : ⟦d⟧ X jdg Δ → ⟦d⟧ X tm Δ

module PropDesc where

  record Injection 
