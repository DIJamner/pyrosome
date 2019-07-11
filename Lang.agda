{-# OPTIONS --safe --sized-types #-}
module Lang where

open import Size

open import Data.List

open import Data.Var hiding (s;_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Relation.Unary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Data.Relation

open import Generic.Syntax
import Generic.Semantics as Sem'
open import Generic.Semantics.Syntactic
import Generic.Simulation as Sim'
open import Generic.Relator

open import Function as Fun using (_∘_)

open import Path.Path
--open import Path.Semantics

open import V2.Semantics
open import V2.Fusion

private
  variable
    I : Set
    σ : I
    Γ Δ : List I
    d : Desc I

private
  variable
    s : Size

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
    vd-embed : Path vd cd --TODO: should this be abstracted out like for model? might be too small
    val-sem : Semantics vd (value-model M)
    comp-sem : Semantics cd M
    sem-cong : Simulation vd (value-model M) M val-sem (comp-sem ∘ ⟦ vd-embed ⟧$) Eqᴿ (VCᴿ M)
    
  syntax-model : Model I
  syntax-model .Val = Tm vd ∞
  syntax-model .Comp = Tm cd ∞
  syntax-model .th^𝓥 = th^Tm
  syntax-model .var = Tm⟦ vd-embed ⟧$

  value-syntax-model : Model I
  value-syntax-model = value-model syntax-model

  val-sem' : Sem'.Semantics vd (Val M) (Val M)
  val-sem' = to-sem' (value-model M) val-sem
  
  comp-sem' : Sem'.Semantics cd (Val M) (Comp M)
  comp-sem' = to-sem' M comp-sem

open Language


module _ {I : Set} {vd1 vd2 cd1 cd2 : Desc I} {M1 M2 : Model I} where

  record Compiler (L1 : Language vd1 cd1 M1)
                  (L2 : Language vd2 cd2 M2)
                  (VR : Rel (Val M2) (Val M1))
                  (VC : Rel (Comp M2) (Comp M1)) : Set₁ where
    module L1 = Language L1
    module L2 = Language L2
    field
      translation : Language vd1 cd1 L2.syntax-model
      correctⱽ : Fusion L2.value-syntax-model (value-model M2) (value-model M1)
                        vd1 vd2
                        (val-sem translation)
                        L2.val-sem
                        L1.val-sem
                        (λ Γ Δ ρ1 ρ2 → All VR Γ (Sem'.Semantics.semantics L2.val-sem' ρ2 <$> ρ1))
                        VR
                        VR
      correctᶜ : Fusion L2.syntax-model M2 M1
                        cd1 cd2
                        (comp-sem translation)
                        L2.comp-sem
                        L1.comp-sem
                        (λ Γ Δ ρ1 ρ2 → All VR Γ (Sem'.Semantics.semantics L2.val-sem' ρ2 <$> ρ1))
                        VR
                        VC
