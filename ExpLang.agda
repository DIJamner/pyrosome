module ExpLang where

import Level as L

open import Size

open import Data.Nat hiding (pred)
open import Data.Fin hiding (cast)
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Data.Maybe.Categorical as MC
open import Category.Monad
open import Data.List hiding (tabulate; lookup)
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

-- everything at level 0 has the same type
Tp : ∀ {n} → Desc (Fin n) → (Fin n) ─Scoped
Tp .{suc _} d zero Γ = ⊤
Tp .{suc _} d (suc i) Γ = Tm d ∞ (inject₁ i) Γ

{-
  ordered environments do not fit this library too well
  TODO: figure out the right way to do it; is it as below?:
-}
data EnvTyping {n : ℕ} : Desc (Fin n) → List (Fin n) → Set where
  · : ∀{d} → EnvTyping d []
  _,ₜ_ : ∀ {d i Γ} → Tp d i Γ → EnvTyping d Γ → EnvTyping d (i ∷ Γ)

-- A convenience definition for use with ─Scoped
TEnv : ∀ {n} → Desc (Fin n) → (Fin n) ─Scoped
TEnv d _ Γ = EnvTyping d Γ
--TEnv d _ Γ = (Γ ─Env) (Tp d) Γ  --TODO: this last Γ is wrong; I want to order the env

TTm : ∀ {n} → Desc (Fin n) → (Fin n) ─Scoped
TTm d i Γ = TEnv d i Γ × Tm d ∞ i Γ

TTp : ∀ {n} → Desc (Fin n) → (Fin n) ─Scoped
TTp d i Γ = TEnv d i Γ × Tp d i Γ

DescUnfix : ∀{I ℓ} → Desc I → (P : Desc I → Set ℓ) → Set _
DescUnfix d P = Ex⟨ d ↑ d' ⟩ (P d' → P d')

infix 10 DescUnfix
syntax DescUnfix d (λ d' → T) = Exᶠ⟨ d ↑ d' ⟩ T

-- TODO: better placement of ⊤/naming here and elsewhere
-- probably makes sense to include "top" in the description
-- makes signatures much easier to work with
-- question: should it be up to the user then or should we add to the description?
⟦_⟧' : ∀{n} → Desc (Fin n) → (List (Fin n) → (Fin n) ─Scoped) → (Fin n) ─Scoped
⟦_⟧' {zero} _ _ _ _ = ⊤
⟦_⟧' {suc n} d X i Γ = ⟦ d ⟧ X (pred i) Γ

-- We deal with n-level languages only for now
record Lang (n : ℕ) : Set₁ where
  field
    desc : Desc (Fin n)
    -- TODO: how do I want to handle this?
    -- not every syntactic term has a type, so it should be partial
    -- should be total on well-typed terms though
    -- also, types of well-typed terms should be well-typed
    -- should be "unfixed" in the same way as precision
    typeof : ∀{X i} → ∀[ EnvTyping desc ⇒ ⟦ desc ⟧ X i ⇒ Maybe ∘ ⟦ desc ⟧' X (pred i) ]
    --TODO: consistent type information
      -- envs for Γ mapping to types
        -- should be related if mapping give related types
        -- right now this allows for anything
      -- types should be related if type precision relates their terms
      --what's the best way to guarantee these properties? (may want typeof to be monotonic)
    -- Mendler semantics; represents one step of the precision derivation
    precision : Ex⟨ desc ↑ d' ⟩ (Rel (TTm d') (TTm d') → Rel (TTm d') (TTm d'))

  -- TODO: how to guarantee termination?
  --  I want some way to partition d' and shrink it
  -- does that help here?
  -- should probably look back at Delaware's stuff
  type : ∀{i} → ∀[ EnvTyping desc ⇒ Tm desc ∞ i ⇒ Maybe ∘ Tp desc i ]
  type Γt (`var x) = {!lookup in Γt!}
  type {zero} Γt (`con x) = {!handle top; make part of desc???!}
  type {suc i} Γt (`con x) = Data.Maybe.map `con (Data.Maybe.map {!typeof!} {!!})

  -- TODO: build in transitivity, reflexivity or prove admissible ?
  -- TODO: Γ should be related by precision in base case
  -- and x should be mapped to type in Γ
  precⁿ : ℕ → Rel (TTm desc) (TTm desc)
  precⁿ zero .rel i (Γt1 , `var x) (Γt2 , `var x₁) = x ≡ x₁
  precⁿ zero .rel i (Γt1 , `var _) (Γt2 , `con _) = ⊥
  precⁿ zero .rel i (Γt1 , `con _) (Γt2 , `var _) = ⊥
  precⁿ zero .rel i (Γt1 , `con _) (Γt2 , `con _) = ⊥
  precⁿ (suc n) = precision path-id (precⁿ n)


  
  -- two terms are related if they are related by a finite precision derivation
  -- TODO: remove t1,t2 from TTm? (use typeof) since terms in 0 don't have types
  -- environment relation ignores the output type
  prec-env : Rel (TEnv desc) (TEnv desc)
  prec-type : Rel (TTp desc) (TTp desc)
  prec : Rel (TTm desc) (TTm desc)

  prec-env .rel _ {[]} · · = ⊤
  prec-env .rel i {x ∷ Γ} (x₁ ,ₜ Γ1) (x₂ ,ₜ Γ2) =
         rel prec-type x (Γ1 , x₁) (Γ2 , x₂)
         × rel prec-env i Γ1 Γ2

  -- rel prec-env zero Γ1 Γ2
  -- TODO: where best to enforce that the environment is well-formed?
  -- does this suffice? also, make user prove that rules preserve well-formedness
  prec-type .rel zero (Γ1 , tt) (Γ2 , tt) = rel prec-env zero Γ1 Γ2
  prec-type .rel (suc i) = rel prec (inject₁ i)
  
  prec .rel i e1 e2 = ∀ n → rel (precⁿ n) i e1 e2

{-
  -- We use the precision relation to simultaneously define well-typed terms
  well-typed : ∀{i Γ} → Pred (TTm tp desc i Γ) L.0ℓ
  well-typed e = rel prec _ e e

open Lang public hiding (precⁿ)


open import DescUtils

private
  variable
    I : Set


--TODO: issue: precision does not take types of vars into account
_+ᴸ_ : ∀[ Lang I ⇒ Lang I ⇒ Lang I ]
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .precision p R .rel i e1 e2 =
  rel (precision L1 (path-projₗ p) R) i e1 e2
  ⊎ rel (precision L2 (path-projᵣ p) R) i e1 e2
-}
