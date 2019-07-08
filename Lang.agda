--{-# OPTIONS --safe --sized-types #-}
module Lang where

open import Size

open import Data.List

open import Data.Var hiding (s)
open import Data.Var.Varlike
open import Data.Environment
open import Relation.Unary

open import Data.Relation

open import Generic.Syntax
import Generic.Semantics as Sem'
open import Generic.Semantics.Syntactic
import Generic.Simulation as Sim'
open import Generic.Relator

open import Function as Fun using (_∘_)

open import Path.Path
open import Path.Semantics

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

open Model
{- TODO: move this to separate semantics v2 file? -}

Semantics : Desc I → Model I → Set
Semantics d M = ∀{σ} → ∀[ ⟦ d ⟧ (Kripke M.Val M.Comp) σ ⇒ M.Comp σ ] where
  module M = Model M


sem'-compat : {d : Desc I} → {M : Model I} → Semantics d M → Sem'.Semantics d (Val M) (Comp M)
sem'-compat {M = M} S = record {
  th^𝓥 = th^𝓥 M ; var = var M ; alg = S }
private
  variable
    s : Size

body : {d : Desc I} → (M : Model I) → Semantics d M → (Γ ─Env) (Val M) Δ → ∀ Θ σ →
             Scope (Tm d s) Θ σ Γ → Kripke (Val M) (Comp M) Θ σ Δ
body M S = (Sem'.Semantics.body ∘ (sem'-compat {M = M})) S

{- TODO: separate simulation file? -}

record Simulation (d : Desc I) (MA MB : Model I)
                  (SA : Semantics d MA) (SB : Semantics d MB)
                  (VR : Rel (Val MA) (Val MB)) (CR : Rel (Comp MA) (Comp MB)) : Set where
       module MA = Model MA
       module MB = Model MB
           
       field
          thᴿ   : ∀{σ vᴬ vᴮ} → (ρ : Thinning Γ Δ) → rel VR σ vᴬ vᴮ →
                   rel VR σ (MA.th^𝓥 vᴬ ρ) (MB.th^𝓥 vᴮ ρ)

          varᴿ  : ∀{σ Γ vᴬ vᴮ} → rel VR σ {Γ} vᴬ vᴮ → rel CR σ (MA.var vᴬ) (MB.var vᴮ)

          algᴿ  : {ρᴬ : (Γ ─Env) MA.Val Δ} → {ρᴮ : (Γ ─Env) MB.Val Δ} →
                  (b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ) → All VR Γ ρᴬ ρᴮ →
                let  vᴬ = fmap d (body MA SA ρᴬ) b
                     vᴮ = fmap d (body MB SB ρᴮ) b
                in ⟦ d ⟧ᴿ (Kripkeᴿ VR CR) vᴬ vᴮ → rel CR σ (SA vᴬ) (SB vᴮ)

{- TODO: include in path? -}
Tm⟦_⟧$ : {d1 d2 : Desc I} → ∀ {s i Γ} → Path d1 d2 → (Tm d1 s i ⇒ Tm d2 s i) Γ
Tm⟦ p ⟧$ = map^Tm (morph p)


value-model : Model I → Model I
value-model M .Val = Val M
value-model M .Comp = Val M
value-model M .th^𝓥 = th^𝓥 M
value-model M .var = Fun.id

{-
A language has two syntaxes, one for values and one for computations,
with a path embedding the value syntax into the computation one.
It also has a model and a denotational semantics of values as model values
and computations as model computations.
These semantics should agree.

A laguage's syntax model can be used as the target of another's
semantics to implement a language by elaboration
-}
record Language (vd : Desc I) (cd : Desc I) (M : Model I) : Set₁ where
  field
    vd-embed : Path vd cd
    val-sem : Semantics vd (value-model M)
    comp-sem : Semantics cd M
    sem-cong : Simulation vd (value-model M) M val-sem (comp-sem ∘ ⟦ vd-embed ⟧$) Eqᴿ {!!}
    
  syntax-model : Model I
  syntax-model .Val = Tm vd ∞
  syntax-model .Comp = Tm cd ∞
  syntax-model .th^𝓥 = th^Tm
  syntax-model .var = Tm⟦ vd-embed ⟧$

