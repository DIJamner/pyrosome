{-# OPTIONS --safe --sized-types #-}
module V2.Semantics where

open import Data.List
open import Data.Product

open import Function using (id;_∘_)
open import Relation.Unary
open import Agda.Builtin.Equality

open import Data.Var hiding (s;_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation

open import Generic.Syntax
open import Generic.Semantics.Syntactic using (vl^Tm; th^Tm)
import Generic.Semantics as Sem'


private
  variable
    I : Set
    σ : I
    Γ Δ : List I
    d : Desc I

record Model (I : Set) : Set₁ where
  field
    Val : I ─Scoped
    Comp : I ─Scoped

    th^𝓥 : Thinnable (Val σ)

    var : ∀[ Val σ ⇒ Comp σ ]

open Model public
{- TODO: move this to separate semantics v2 file? -}

Semantics : Desc I → Model I → Set
Semantics d M = ∀{σ} → ∀[ ⟦ d ⟧ (Kripke M.Val M.Comp) σ ⇒ M.Comp σ ] where
  module M = Model M

-- a model + a semantics = an old semantics
to-sem' : {d : Desc I} → (M : Model I) → Semantics d M → Sem'.Semantics d (Val M) (Comp M)
to-sem' M S = record { th^𝓥 = th^𝓥 M ; var = var M ; alg = S }
to-sem : {d : Desc I} → ∀ {V C} → Sem'.Semantics d V C → Σ[ M ∈ Model I ] (Semantics d M)
to-sem {V = V} {C = C} S =
  (record { Val = V ; Comp = C ; th^𝓥 = S.th^𝓥 ; var = S.var }) ,
  Sem'.Semantics.alg S
  where module S = Sem'.Semantics S

-- TODO: prove inverses

module _  {d : Desc I} where


  _─Comp : List I → I ─Scoped → List I → Set
  (Γ ─Comp) 𝓒 Δ = ∀ {s σ} → Tm d s σ Γ → 𝓒 σ Δ

  semantics : (M : Model I) → Semantics d M → ∀ {Γ Δ} → (Γ ─Env) (Val M) Δ → (Γ ─Comp) (Comp M) Δ
  semantics M S = Sem'.Semantics.semantics (to-sem' M S)

  body : (M : Model I) → Semantics d M → ∀ {Γ Δ s} → (Γ ─Env) (Val M) Δ → ∀ Θ σ →
             Scope (Tm d s) Θ σ Γ → Kripke (Val M) (Comp M) Θ σ Δ
  body M S = Sem'.Semantics.body (to-sem' M S)


  eval : (M : Model I) → Semantics d M → ∀ {s σ} → VarLike (Val M) → ∀[ Tm d s σ ⇒ Comp M σ ]
  eval M S =  Sem'.Semantics.eval (to-sem' M S)

value-model : Model I → Model I
value-model M .Val = Val M
value-model M .Comp = Val M
value-model M .th^𝓥 = th^𝓥 M
value-model M .var = id

-- TODO: what's the best place for this?
VCᴿ : (M : Model I) → Rel (Val M) (Comp M)
VCᴿ M = mkRel λ σ v c → var M v ≡ c

open import Size
open import Path.Path renaming (id to id-path)

{- TODO: include in path? -}
Tm⟦_⟧$ : {d1 d2 : Desc I} → ∀ {s i Γ} → Path d1 d2 → (Tm d1 s i ⇒ Tm d2 s i) Γ
Tm⟦ p ⟧$ = map^Tm (morph p)

--TODO: rename
syn-model : (vd cd : Desc I) → Path vd cd → Model I
syn-model vd cd p .Val = Tm vd ∞
syn-model vd cd p .Comp = Tm cd ∞
syn-model vd cd p .th^𝓥 = th^Tm
syn-model vd cd p .var = Tm⟦ p ⟧$

syn-sem : (vd cd : Desc I) → (p : Path vd cd) → Semantics cd (syn-model vd cd p)
syn-sem vd cd p = `con ∘ fmap cd (reify vl^Tm)

-- TODO: this works for value syntaxes, do I need one for comps?
syn-val-model : (d : Desc I) → Model I
syn-val-model d = syn-model d d id-path

syn-val-sem : (d : Desc I) → Semantics d (syn-val-model d)
syn-val-sem d = syn-sem d d id-path
