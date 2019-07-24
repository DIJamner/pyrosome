module ExpLang where

import Level as L

open import Size

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Maybe
open import Data.Maybe.Categorical as MC
open import Category.Monad
open import Data.List hiding (tabulate)
open import Data.List.Properties
open import Data.List.Relation.Unary.All using (tabulate)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Function

open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic using (th^Tm; vl^Tm)

open import Path.Path renaming (id to path-id)

--TODO: move to utils
_∘₂_ : ∀ {a1 a2 b c} {A₁ : Set a1} {A₂ : Set a2} {B : Set b} {C : Set c} →
         (B → C) → (A₁ → A₂ → B) → (A₁ → A₂ → C)
_∘₂_ = _∘′_ ∘ _∘′_

module _ {a b} {A : Set a} {B : Set b} where

  infix 10 IUniversal2
  IUniversal2 : ∀ {ℓ} → (A → B → Set ℓ) → Set _
  IUniversal2 P = ∀ {x y} → P x y
  
  syntax IUniversal2 P = ∀²[ P ]
  
  infixr 8 _⇒²_
  
  _⇒²_ : ∀ {ℓ₁ ℓ₂} → (A → B → Set ℓ₁) → (A → B → Set ℓ₂) → A → B → Set _
  P ⇒² Q = λ x y → P x y → Q x y

cast : ∀{ℓ₁ ℓ₂} → ∀ {A : Set ℓ₁} → ∀ {a b : A} → a ≡ b → (P : A → Set ℓ₂) → P a → P b
cast refl P = id


cong-app' : ∀ {a b} {A : Set a} {B : Set b} → {x y : A} → x ≡ y → {f g : (x : A) → B} →
           f ≡ g  → f x ≡ g y
cong-app' refl refl = refl

Tm⟦_⟧$ : ∀{I} → {d1 d2 : Desc I} → Path d1 d2 → ∀²[ Tm d1 ∞ ⇒² Tm d2 ∞ ]
Tm⟦ p ⟧$ = map^Tm (morph p)

id-ext-tm : ∀{I} → {d : Desc I} → ∀{i Γ} → (e : Tm d ∞ i Γ) → Tm⟦ path-id ⟧$ e ≡ e
id-ext-tm = {!!}

record Path² {t1 t2 : Desc ⊤} (d1 : Desc (TM t1 tt)) (d2 : Desc (TM t2 tt)) : Set₁ where
  field
    type-path : Path t1 t2
    term-path : Path (reindex Tm⟦ type-path ⟧$ d1) d2

open Path²

path-id² : ∀{t d} → Path² {t} d d
path-id² .type-path = path-id
path-id² {d = `σ A x} .term-path = {!!}
path-id² {d = `X x x₁ d} .term-path = {!`XP!}
path-id² {d = `∎ x} .term-path = cast (sym (id-ext-tm x)) (λ y → Path (`∎ y) (`∎ x)) (`∎P x)

-- TODO: this currently only works for simple types
-- get the indexing right in Poly/Syntax and it should work
-- for more interesting types though
record Lang : Set₁ where
  field
    type : Desc ⊤
    desc : Desc (TM type tt)
    -- Mendler semantics; represents one step of the precision derivation
    precision : ∀{t'} → {d' : Desc (TM t' tt)} → Path² desc d' →
                Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞)

  -- TODO: build in transitivity
  precⁿ : ℕ → Rel (Tm desc ∞) (Tm desc ∞)
  precⁿ zero = Eqᴿ
  precⁿ (suc n) = precision path-id² (precⁿ n)

  -- two terms are related if they are related by a finite precision derivation
  -- TODO: possible to write using size types? (probably not)
  prec : Rel (Tm desc ∞) (Tm desc ∞)
  prec .rel i e1 e2 = ∃[ n ] rel (precⁿ n) i e1 e2

  -- We use the precision relation to simultaneously define well-typed terms
  -- Issue: this would work for an intrinsically typed language,
  -- but if we want type-based reasoning (and we really do)
  -- this is insufficient for a syntax with types on top
  -- TODO: is this solvable with an addl syntax for types
  -- WITHOUT indexing desc by that syntax?
  -- to give precision enough info, it needs the typing of Γ
  -- Question: would that be enough?
  well-typed : ∀{i Γ} → Pred (Tm desc ∞ i Γ) L.0ℓ
  well-typed e = rel prec _ e e

open Lang public hiding (precⁿ)


open import DescUtils

private
  variable
    I : Set

--TODO: should be in path
path-projₗ : {d1 d2 d3 : Desc I} → Path (d1 `+ d2) d3 → Path d1 d3
path-projₗ (`σL .Bool x) = x true
path-projₗ (`σR A s₁ p) = `σR A s₁ (path-projₗ p)

path-projᵣ : {d1 d2 d3 : Desc I} → Path (d1 `+ d2) d3 → Path d2 d3
path-projᵣ (`σL .Bool x) = x false
path-projᵣ (`σR A s₁ p) = `σR A s₁ (path-projᵣ p)

{-
--TODO: issue: precision does not take types of vars into account
_+ᴸ_ : Lang → Lang → Lang
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .precision p R .rel i e1 e2 =
  rel (precision L1 (path-projₗ p) R) i e1 e2
  ⊎ rel (precision L2 (path-projᵣ p) R) i e1 e2


-- This language makes i into the unit type
-- i.e. with a trival element and all elements equal
-- issue: what if i is shared? this works on the intrinsic typing model
UnitLang : {!!} → Lang
UnitLang i .desc = `∎ i
UnitLang i .precision p R .rel j _ _ = i ≡ j


_ : {i : I} → ∀{Γ e1 e2} →  rel (prec (UnitLang i)) i {Γ} e1 e2
_ = (suc zero) , refl
-}
