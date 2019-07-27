module ExpLang where

import Level as L

open import Size

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
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

Extensible : ∀{ℓ I} → Desc I → (Desc I → Set ℓ) → Set _
Extensible d f = ∀{d'} → Path d d' → f d'

infix 10 Extensible
syntax Extensible d (λ d' → e) = Ex⟨ d ↑ d' ⟩ e

Tp : ∀{I} → (I → I) → Desc I → I ─Scoped
Tp f d = Tm d ∞ ∘ f

TEnv : ∀{I} → (I → I) → Desc I → List I → Set
TEnv f d Γ = (Γ ─Env) (Tp f d) Γ  --TODO: this last Γ is wrong; I want to order the env

TTm : ∀{I} → (I → I) → Desc I → I ─Scoped
TTm f d i Γ = TEnv f d Γ × Tm d ∞ i Γ × Tp f d i Γ

DescUnfix : ∀{I ℓ} → Desc I → (P : Desc I → Set ℓ) → Set _
DescUnfix d P = Ex⟨ d ↑ d' ⟩ (P d' → P d')

infix 10 DescUnfix
syntax DescUnfix d (λ d' → T) = Exᶠ⟨ d ↑ d' ⟩ T

record Lang (I : Set) (tp : I → I) : Set₁ where
  field
    desc : Desc I
    -- TODO: how do I want to handle this?
    -- not every syntactic term has a type, so it should be partial
    -- should be total on well-typed terms though
    -- also, types of well-typed terms should be well-typed
    -- should be "unfixed" in the same way as precision
    {-
    typeof : ∀{i} → Ex⟨ desc ↑ d' ⟩
      (∀[ TEnv tp d' ⇒ Tm d' ∞ i ⇒ Maybe ∘ Tp tp d' i ] →
        ∀[ TEnv tp d' ⇒ Tm d' ∞ i ⇒ Maybe ∘ Tp tp d' i ])
        -}
    --TODO: consistent type information
      -- envs for Γ mapping to types
        -- should be related if mapping give related types
        -- right now this allows for anything
      -- types should be related if type precision relates their terms
      --what's the best way to guarantee these properties? (may want typeof to be monotonic)
    -- Mendler semantics; represents one step of the precision derivation
    precision : Exᶠ⟨ desc ↑ d' ⟩ (Rel (TTm tp d') (TTm tp d'))
  
  -- TODO: build in transitivity, reflexivity or prove admissible ?
  -- TODO: Γ should be related by precision in base case
  -- and x should be mapped to type in Γ
  precⁿ : ℕ → Rel (TTm tp desc) (TTm tp desc)
  precⁿ zero .rel i (Γt1 , `var x , _) (Γt2 , `var x₁ , _) = x ≡ x₁
  precⁿ zero .rel i (Γt1 , `var _ , _) (Γt2 , `con _ , _) = ⊥
  precⁿ zero .rel i (Γt1 , `con _ , _) (Γt2 , `var _ , _) = ⊥
  precⁿ zero .rel i (Γt1 , `con _ , _) (Γt2 , `con _ , _) = ⊥
  precⁿ (suc n) = precision path-id (precⁿ n)
  
  -- two terms are related if they are related by a finite precision derivation
  -- TODO: possible to write using size types? (probably not)
  prec : Rel (TTm tp desc) (TTm tp desc)
  prec .rel i e1 e2 = ∀ n → rel (precⁿ n) i e1 e2

  -- We use the precision relation to simultaneously define well-typed terms
  well-typed : ∀{i Γ} → Pred (TTm tp desc i Γ) L.0ℓ
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


--TODO: issue: precision does not take types of vars into account
_+ᴸ_ : ∀[ Lang I ⇒ Lang I ⇒ Lang I ]
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .precision p R .rel i e1 e2 =
  rel (precision L1 (path-projₗ p) R) i e1 e2
  ⊎ rel (precision L2 (path-projᵣ p) R) i e1 e2


-- If we have a fixed point of tp,
-- we can establish an element that is its own type
-- termination issues here suggest that it may be better
-- to just use finite stratification for now.
-- It certainly captures more languages than I need
module _ {e : I} {tp : I → I} (fixed : tp e ≡ e) where
  TypeInType : Lang I tp
  TypeInType .desc = `∎ e
  -- TODO: this doesn't account for types properly, should use prec rather than equiv
  TypeInType .precision p R .rel i (_ , _ , t1) (_ , _ , t2) =
    Σ (i ≡ e) λ { refl → (t1 ≡ `con (⟦ p ⟧$ fixed)) × t2 ≡ `con (⟦ p ⟧$ fixed)}
