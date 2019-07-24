module ExpLang where

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

open import Function

open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
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

record Lang (V : Denotation) : Set₁ where
  module V = Denotation V
  field
    desc : Desc
    -- Mendler semantics
    alg   : ∀{d'} → Path desc d'  →
            -- TODO: makesure right things are patial
            ∀[ ⟦ desc ⟧ (Kripke V.val (PTm d' V.val)) i ⇒ PTm d' V.val i ]
    --TODO: typing : ~⟦ desc ⟧ Exp → ⟦ desc ⟧ Type
    -- TODO: equivalence: go with original axiomatic approach?
     {-
       this would replace the algebra in a lang def
       using the same injection trick to cover language extensions
    -}

  
  sem : ∀{d'} → Path desc d' → Semantics desc V.val (PTm d' V.val)
  sem m .Semantics.th^𝓥 = th V
  sem m .Semantics.var = Val
  sem m .Semantics.alg = alg m

  module S = Semantics (sem path-id)
  open S

  evalN : ℕ → ∀[ Tm desc ∞ i ⇒ PTm desc V.val i ]
  evalN zero = Comp
  evalN (suc n) e = do
    r ← eval V.vl e
    evalN n r

  -- TODO: gammas?
--  ctx-approx : (e1 e2 : Tm desc ∞ Exp ) → (C : Ctx desc) → {!!}
--  ctx-approx e1 e2 C = {!!}

open Lang public

open import DescUtils

private
  variable
    V : Denotation

_+ᴸ_ : Lang V → Lang V → Lang V
(L1 +ᴸ L2) .desc  = desc L1 `+ desc L2
(L1 +ᴸ L2) .alg p  = case
  (alg L1 (p ∘ₚ injₗ))
  (alg L2 (p ∘ₚ injᵣ))
