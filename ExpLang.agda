module ExpLang where

import Level as L

open import Size

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Maybe.Categorical as MC
open import Category.Monad
open import Data.List using (List; [_])
open import Relation.Unary
open import Agda.Builtin.Equality

open import Function

open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax renaming (Desc to IDesc)
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

{-=============
TODO!!!! nothing so far depends on this
it would be better to abstract it out if that continues to be the case
this may change, however, when we consider typing
==============-}
data SynClass : Set where
  Term : SynClass
  Type : SynClass

Desc : Set₁
Desc = IDesc SynClass

Scoped : Set₁
Scoped = SynClass ─Scoped

ValSet : Set₁
ValSet = List SynClass → Set

private
  variable
    i : SynClass
    Γ : List SynClass

--Type of partial terms (stuck/error, term, or value)
data PTm (d : Desc) (V : Scoped) : Scoped where
  Stuck : PTm d V i Γ
  Comp : Tm d ∞ i Γ → PTm d V i Γ
  Val : V i Γ → PTm d V i Γ

-- for sequential evaluation/interpretation
-- enables do notation
_>>=_ : ∀{d V} → ∀²[ (PTm d V ⇒² (Tm d ∞ ⇒² PTm d V) ⇒² PTm d V) ]
Stuck >>= f = Stuck
Comp x >>= f = f x
Val x >>= f = Val x

record Denotation : Set₁ where
  field
    val : Scoped
    th : ∀{i} → Thinnable (val i)
    vl : VarLike val

open Denotation

SynD : Desc → Denotation
SynD d .val = Tm d ∞
SynD d .th = th^Tm
SynD d .vl = vl^Tm

-- TODO: move away from Desc.
record Lang (I : Set) : Set₁ where
  field
    desc : IDesc I
    -- Mendler semantics; represents one step of the precision derivation
    precision : ∀{d'} → Path desc d' → Rel (Tm d' ∞) (Tm d' ∞) → Rel (Tm d' ∞) (Tm d' ∞)
    -- should be transitive and reflexive (TODO)
    -- precision-trans
    -- precision-refl

  precⁿ : ℕ → Rel (Tm desc ∞) (Tm desc ∞)
  precⁿ zero = Eqᴿ
  precⁿ (suc n) = precision path-id (precⁿ n)

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

path-projₗ : {d1 d2 d3 : IDesc I} → Path (d1 `+ d2) d3 → Path d1 d3
path-projₗ (`σL .Bool x) = x true
path-projₗ (`σR A s₁ p) = `σR A s₁ (path-projₗ p)

path-projᵣ : {d1 d2 d3 : IDesc I} → Path (d1 `+ d2) d3 → Path d2 d3
path-projᵣ (`σL .Bool x) = x false
path-projᵣ (`σR A s₁ p) = `σR A s₁ (path-projᵣ p)

--TODO: issue: precision does not take types of vars into account
_+ᴸ_ : Lang I → Lang I → Lang I
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .precision p R .rel i e1 e2 =
  rel (precision L1 (path-projₗ p) R) i e1 e2
  ⊎ rel (precision L2 (path-projᵣ p) R) i e1 e2


-- This language makes i into the unit type
-- i.e. with a trival element and all elements equal
-- issue: what if i is shared? this works on the intrinsic typing model
UnitLang : I → Lang I
UnitLang i .desc = `∎ i
UnitLang i .precision p R .rel j _ _ = i ≡ j


_ : {i : I} → ∀{Γ e1 e2} →  rel (prec (UnitLang i)) i {Γ} e1 e2
_ = (suc zero) , refl
