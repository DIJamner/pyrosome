-- We consider languages where the terms and types are each
-- given by a description, but we have a single unified kind
-- across all types.
-- This could be generalized, but for now 2 levels suffices
module Typed where

open import Size

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List using (List)

open import Generic.Syntax

open import Path.Path
open import DescUtils

-- (open) types are pairs of type context and type syntax
AsIdx : {I : Set} → Desc I → I → Set
AsIdx d i = Σ[ Γ ∈ List _ ] Tm d ∞ i Γ


-- here we have our two-level syntax
record TypedDesc : Set₁ where
  field
    types : Desc ⊤
    terms : Desc (AsIdx types tt)

open TypedDesc

Ty⟦_⟧$ : ∀{I} {d1 d2 : Desc I} → Path d1 d2 → ∀{i} → AsIdx d1 i → AsIdx d2 i
Ty⟦ p ⟧$ = map₂ (map^Tm (morph p))

inj₁+ : ∀{d1 d2} → AsIdx (types d1) tt → AsIdx (types d1 `+ types d2) tt
inj₁+ = Ty⟦ injₗ ⟧$

inj₂+ : ∀{d1 d2} → AsIdx (types d2) tt → AsIdx (types d1 `+ types d2) tt
inj₂+ = Ty⟦ injᵣ ⟧$

_:+_ : TypedDesc → TypedDesc → TypedDesc
types (d1 :+ d2) = (types d1) `+ (types d2)
terms (d1 :+ d2) = (reindex (inj₁+ {d1} {d2}) (terms d1)) `+ (reindex (inj₂+ {d1} {d2}) (terms d2))

:⓪ : TypedDesc
types :⓪ = ⓪
terms :⓪ = ⓪

record TypedPath (d1 d2 : TypedDesc) : Set₁ where
  field
    ty-path : Path (types d1) (types d2)
    tm-path : Path (reindex Ty⟦ ty-path ⟧$ (terms d1)) (terms d2)
-- TODO: replicate for typed descs all things from paths/equivalence
