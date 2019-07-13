{-# OPTIONS --safe --sized-types #-}

{-
Regular fusion doesn't work for me since the B semantics is not for the same language.
This module generalizes the definition of fusion to work in such a setting.
It also makes use of the model/semantics split introduced in V2.Semantics (TODO)
-}

open import V2.Semantics renaming (body to Sbody)

module V2.Fusion {I : Set} (Mᴬ Mᴮ Mᴬᴮ : Model I) where

open import Size
open import Data.List hiding ([_] ; zip ; lookup)
open import Function renaming (_∘′_ to _∘_) hiding (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Data.Relation hiding (_>>ᴿ_)
open import Data.Var hiding (z; s; _<$>_)
open import Data.Var.Varlike
open import Data.Environment

open import Generic.Syntax
open import Generic.Relator

private module Mᴬ = Model Mᴬ
private module Mᴮ = Model Mᴮ
private module Mᴬᴮ = Model Mᴬᴮ


private
  variable
    s : Size
    σ τ : I
    Γ Δ Θ Ω : List I
    ρᴬ : (Γ ─Env) Mᴬ.Val Δ
    ρᴮ : (Δ ─Env) Mᴮ.Val Θ
    ρᴬᴮ : (Γ ─Env) Mᴬᴮ.Val Θ
    vsᴬᴮ : (Δ ─Env) Mᴬᴮ.Val Γ
    vsᴮ : (Δ ─Env) Mᴮ.Val Γ

{--
TODO: Should this be split up the same way semantics are?
i.e. Modelᴿ, Fusion?
--}
record Fusion (d1 : Desc I) (d2 : Desc I)
  (𝓢ᴬ : Semantics d1 Mᴬ) (𝓢ᴮ : Semantics d2 Mᴮ)
  (𝓢ᴬᴮ : Semantics d1 Mᴬᴮ)
  (𝓔ᴿ : ∀ Γ Δ {Θ} → (Γ ─Env) Mᴬ.Val Δ → (Δ ─Env) Mᴮ.Val Θ → (Γ ─Env) Mᴬᴮ.Val Θ → Set)
  (𝓥ᴿ : Rel Mᴮ.Val Mᴬᴮ.Val) (𝓒ᴿ : Rel Mᴮ.Comp Mᴬᴮ.Comp) : Set where

  --module 𝓢ᴬ = Semantics 𝓢ᴬ
  --module 𝓢ᴮ = Semantics 𝓢ᴮ
  --module 𝓢ᴬᴮ = Semantics 𝓢ᴬᴮ
  evalᴬ = semantics Mᴬ 𝓢ᴬ
  evalᴮ = semantics Mᴮ 𝓢ᴮ
  evalᴬᴮ = semantics Mᴬᴮ 𝓢ᴬᴮ
  field

    reifyᴬ  :  ∀ σ → ∀[ Mᴬ.Comp σ ⇒ Tm d2 ∞ σ ]

    vl^𝓥ᴬ :  VarLike Mᴬ.Val

  quoteᴬ : ∀ Δ i → Kripke Mᴬ.Val Mᴬ.Comp Δ i Γ → Tm d2 ∞ i (Δ ++ Γ)
  quoteᴬ Δ i k = reifyᴬ i (reify vl^𝓥ᴬ Δ i k)

  field

    _>>ᴿ_  :  𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → All 𝓥ᴿ Θ vsᴮ vsᴬᴮ →
              let id>>ρᴬ = freshˡ vl^𝓥ᴬ Δ >> th^Env Mᴬ.th^𝓥 ρᴬ (freshʳ vl^Var Θ)
              in 𝓔ᴿ (Θ ++ Γ) (Θ ++ Δ) id>>ρᴬ (vsᴮ >> ρᴮ) (vsᴬᴮ >> ρᴬᴮ)

    th^𝓔ᴿ  : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ  → (ρ : Thinning Θ Ω) →
             𝓔ᴿ Γ Δ ρᴬ (th^Env Mᴮ.th^𝓥 ρᴮ ρ) (th^Env Mᴬᴮ.th^𝓥 ρᴬᴮ ρ)

  𝓡 :  ∀ σ → (Γ ─Env) Mᴬ.Val Δ → (Δ ─Env) Mᴮ.Val Θ → (Γ ─Env) Mᴬᴮ.Val Θ →
       Tm d1 s σ Γ → Set
  𝓡 σ ρᴬ ρᴮ ρᴬᴮ t = rel 𝓒ᴿ σ (evalᴮ ρᴮ (reifyᴬ σ (evalᴬ ρᴬ t))) (evalᴬᴮ ρᴬᴮ t)

  field

    varᴿ : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → ∀ v → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`var v)

    algᴿ : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → (b : ⟦ d1 ⟧ (Scope (Tm d1 s)) σ Γ) →
           let  bᴬ :  ⟦ d1 ⟧ (Kripke Mᴬ.Val Mᴬ.Comp) _ _
                bᴬ   = fmap d1 (Sbody Mᴬ 𝓢ᴬ ρᴬ) b
                bᴮ   = fmap d1 (λ Δ i → Sbody Mᴮ 𝓢ᴮ ρᴮ Δ i ∘ quoteᴬ Δ i) bᴬ
                bᴬᴮ  = fmap d1 (Sbody Mᴬᴮ 𝓢ᴬᴮ ρᴬᴮ) b
           in ⟦ d1 ⟧ᴿ (Kripkeᴿ 𝓥ᴿ 𝓒ᴿ) bᴮ bᴬᴮ → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`con b)

  fusion : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → (t : Tm d1 s σ Γ) → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t

  body   : 𝓔ᴿ Γ Δ ρᴬ ρᴮ ρᴬᴮ → ∀ Δ σ → (b : Scope (Tm d1 s) Δ σ Γ) →
           let vᴮ   = Sbody Mᴮ 𝓢ᴮ ρᴮ Δ σ (quoteᴬ Δ σ (Sbody Mᴬ 𝓢ᴬ ρᴬ Δ σ b))
               vᴬᴮ  = Sbody Mᴬᴮ 𝓢ᴬᴮ ρᴬᴮ Δ σ b
           in Kripkeᴿ 𝓥ᴿ 𝓒ᴿ Δ σ vᴮ vᴬᴮ

  fusion ρᴿ (`var v) = varᴿ ρᴿ v
  fusion ρᴿ (`con t) = algᴿ ρᴿ t (rew (liftᴿ d1 (body ρᴿ) t)) where

     eq  = fmap² d1 (Sbody Mᴬ 𝓢ᴬ _) (λ Δ i t → Sbody Mᴮ 𝓢ᴮ _ Δ i (quoteᴬ Δ i t)) t
     rew = subst (λ v → ⟦ d1 ⟧ᴿ (Kripkeᴿ 𝓥ᴿ 𝓒ᴿ) v _) (sym eq)

  body ρᴿ []       i b = fusion ρᴿ b
  body ρᴿ (σ ∷ Δ)  i b = λ ρ vsᴿ → fusion (th^𝓔ᴿ ρᴿ ρ >>ᴿ vsᴿ) b
