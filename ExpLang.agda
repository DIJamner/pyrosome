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

private
  variable
    I : Set

Tm⟦_⟧$ : {d1 d2 : Desc I} → Path d1 d2 → ∀²[ Tm d1 ∞ ⇒² Tm d2 ∞ ]
Tm⟦ p ⟧$ = map^Tm (morph p)

Extensible : ∀{ℓ} → Desc I → (Desc I → Set ℓ) → Set _
Extensible d f = ∀{d'} → Path d d' → f d'

infix 10 Extensible
syntax Extensible d (λ d' → e) = Ex⟨ d ↑ d' ⟩ e

-- Level 0 folds back on itself (think type in type)
-- TODO: this is sub-optimal, but may be what we have for now
Tp : (I → I) → Desc I → I ─Scoped
Tp tp d i Γ = Tm d ∞ (tp i) Γ

{-
  ordered environments do not fit this library too well,
  but this should work
TODO: pick correct things between this and other env typing
-}
data EnvTyping' (tp : I → I) (d : Desc I) : List I → Set where
  · : EnvTyping' tp d []
  _,ₜ_ : ∀ {i Γ} → Tp tp d i Γ → EnvTyping' tp d Γ → EnvTyping' tp d (i ∷ Γ)

-- A convenience definition for use with ─Scoped
TEnv : (I → I) → Desc I → I ─Scoped
TEnv tp d _ Γ = EnvTyping' tp d Γ

TTm : (I → I) → Desc I → I ─Scoped
TTm tp d i Γ = TEnv tp d i Γ × Tm d ∞ i Γ

TTp : (I → I) → Desc I → I ─Scoped
TTp tp d i Γ = TEnv tp d i Γ × Tp tp d i Γ

DescUnfix : ∀{I ℓ} → Desc I → (P : Desc I → Set ℓ) → Set _
DescUnfix d P = Ex⟨ d ↑ d' ⟩ (P d' → P d')

infix 10 DescUnfix
syntax DescUnfix d (λ d' → T) = Exᶠ⟨ d ↑ d' ⟩ T

-- We deal with n-level languages only for now
record Lang (tp : I → I) : Set₁ where
  field
    desc : Desc I
    -- TODO: how do I want to handle this?
    -- not every syntactic term has a type, so it should be partial
    -- should be total on well-typed terms though
    -- also, types of well-typed terms should be well-typed
    -- should be "unfixed" in the same way as precision
    typeof : ∀{X i} → ∀[ EnvTyping' tp desc ⇒ ⟦ desc ⟧⟨ tp ⟩ X i ⇒ Maybe ∘ ⟦ desc ⟧⟨ tp ⟩ X (tp i) ]
    --TODO: consistent type information
      -- envs for Γ mapping to types
        -- should be related if mapping give related types
        -- right now this allows for anything
      -- types should be related if type precision relates their terms
      --what's the best way to guarantee these properties? (may want typeof to be monotonic)
    -- Mendler semantics; represents one step of the precision derivation
    precision : Ex⟨ desc ↑ d' ⟩ (Rel (TTm tp d') (TTm tp d') → Rel (TTm tp d') (TTm tp d'))

  -- TODO: how to guarantee termination?
  --  I want some way to partition d' and shrink it
  -- does that help here?
  -- should probably look back at Delaware's stuff
  type : ∀{i} → ∀[ EnvTyping' tp desc ⇒ Tm desc ∞ i ⇒ Maybe ∘ Tp tp desc i ]
  type Γt (`var x) = {!lookup in Γt!}
  -- TODO: this seems wrong, since it doesn't go into the subterms
  -- TODO: how to do types for bound variables?
     --- I believe this is tied to the scope issue?
     -- the question is how best to come up with the types for bound variables
     -- this requires some additional information from the user
     -- seems like it's sort of recreating library functionality
     -- can I create a description type that is implicitly sort of self-indexed?
     -- still index by syntactic forms i but annotated with terms of type (Tp tp d i)
  type Γt (`con x) = Data.Maybe.map `con (typeof Γt (fmap desc (λ Θ i₁ → {!type Γt!}) {!!}))

  -- TODO: build in transitivity, reflexivity or prove admissible ?
  -- TODO: Γ should be related by precision in base case
  -- and x should be mapped to type in Γ
  precⁿ : ℕ → Rel (TTm tp desc) (TTm tp desc)
  precⁿ zero .rel i (Γt1 , `var x) (Γt2 , `var x₁) = x ≡ x₁
  precⁿ zero .rel i (Γt1 , `var _) (Γt2 , `con _) = ⊥
  precⁿ zero .rel i (Γt1 , `con _) (Γt2 , `var _) = ⊥
  precⁿ zero .rel i (Γt1 , `con _) (Γt2 , `con _) = ⊥
  precⁿ (suc n) = precision path-id (precⁿ n)

  
  -- two terms are related if they are related by a finite precision derivation
  -- TODO: remove t1,t2 from TTm? (use typeof) since terms in 0 don't have types
  -- environment relation ignores the output type
  prec-env : Rel (TEnv tp desc) (TEnv tp desc)
  prec-type : Rel (TTp tp desc) (TTp tp desc)
  prec : Rel (TTm tp desc) (TTm tp desc)

  prec-env .rel _ {[]} · · = ⊤
  prec-env .rel i {x ∷ Γ} (x₁ ,ₜ Γ1) (x₂ ,ₜ Γ2) =
         rel prec-type x (Γ1 , x₁) (Γ2 , x₂)
         × rel prec-env i Γ1 Γ2

  -- rel prec-env zero Γ1 Γ2
  -- TODO: where best to enforce that the environment is well-formed?
  -- does this suffice? also, make user prove that rules preserve well-formedness
  --prec-type .rel zero (Γ1 , _) (Γ2 , _) = rel prec-env zero Γ1 Γ2
  prec-type .rel i = rel prec (tp i)
  
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
