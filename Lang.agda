{-# OPTIONS --safe --sized-types #-}
module Lang where

open import Size

open import Data.List as L hiding ([_]; lookup)
open import Data.Product
open import Data.Bool
open import Data.Maybe

open import Data.Var hiding (s;_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Relation.Unary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Function as Fun using (_∘_)
open import Generic.Syntax


module _ {I : Set} where
  
  private
    variable
      i σ : I
      Γ₁ Γ₂ : List I
      s : Size
      X Y : List I → I ─Scoped

  _─TpEnv : List I → (I → I) → (List I → I ─Scoped) → List I → Set
  (Δ ─TpEnv) tp X Γ = ((L.map tp Δ) ─Env) (X []) Γ

  ⟦_⟧⟨_⟩ : Desc I → (I → I) → (List I → I ─Scoped) → (List I → I ─Scoped) → I ─Scoped
  ⟦ `σ A d    ⟧⟨ tp ⟩ X Xt i Γ = Σ[ a ∈ A ] (⟦ d a ⟧⟨ tp ⟩ X Xt i Γ)
  --TODO: should the argument to X be [] or Δ or something else?
  ⟦ `X Δ j d  ⟧⟨ tp ⟩ X Xt i Γ = (Δ ─TpEnv) tp Xt Γ × X Δ j Γ × ⟦ d ⟧⟨ tp ⟩ X Xt i Γ
  ⟦ `∎ j      ⟧⟨ tp ⟩ X Xt i Γ = i ≡ j × Xt [] (tp i) Γ

  data Tm⟨_⟩ (tp : I → I) (d : Desc I) : Size → I ─Scoped where
   `var  : ∀[ Var i                     ⇒ Tm⟨ tp ⟩ d (↑ s) i ]
   `con  : ∀[ ⟦ d ⟧⟨ tp ⟩ (Scope (Tm⟨ tp ⟩ d s)) (Scope (Tm d s)) i  ⇒ Tm⟨ tp ⟩ d (↑ s) i ]

  _─TmTpEnv : List I → Desc I → (I → I) → List I → Set
  (Δ ─TmTpEnv) d tp Γ = (Δ ─Env) (Tm⟨ tp ⟩ d ∞) Γ

  --TODO: this env is wrong; should be a stack of envs
  Inference : (d : Desc I) → (tp : I → I) → Set
  Inference d tp =  ∀{i Γ} → (Γ ─TmTpEnv) d tp Γ → Tm d ∞ i Γ → Maybe (Tm⟨ tp ⟩ d ∞ i Γ)

module TEST where
  data Kind : Set where
    KTm : Kind
    KTp : Kind
    KTop : Kind

  typeof : Kind → Kind
  typeof KTm = KTp
  typeof KTp = KTop
  typeof KTop = KTop

  Lam : Desc Kind
  Lam = `X [] KTp (`X (KTm ∷ []) KTm (`∎ KTm))
      `+ `X [] KTm (`X [] KTm (`∎ KTm))
      `+ `X [] KTp (`X [] KTp (`∎ KTp))

  Unit : Desc Kind
  Unit = `∎ KTp `+ `∎ KTm

  TypeInType : Desc Kind
  TypeInType = `∎ KTop

  ttInf : Inference TypeInType typeof
  ttInf Γt (`var x) = just (lookup Γt x)
  ttInf Γt (`con refl) = just (`con (refl , `con refl))

  ttUnit : Inference (Unit `+ TypeInType) typeof
  ttUnit Γt (`var x) = just (lookup Γt x)
  ttUnit Γt (`con (false , refl)) = just (`con (false , (refl , (`con (false , refl)))))
  ttUnit Γt (`con (true , false , refl)) =
    just (`con (true , (false , (refl , `con (true , (true , refl))))))
  ttUnit Γt (`con (true , true , refl)) = just (`con (false , ({!!} , {!!})))

