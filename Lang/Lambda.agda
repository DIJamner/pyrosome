
module Lang.Lambda where

open import Data.Product
open import Data.List hiding (lookup)
open import Data.Bool
open import Relation.Unary

open import Function
open import Agda.Builtin.Equality

--open import Lang
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Generic.Syntax renaming (Desc to IDesc)
open import Generic.Semantics.Syntactic

open import ExpLang
open import Path.Path renaming (id to path-id)


Lambda : IDesc SynClass
Lambda = `X [] Term (`X [] Term (`∎ Term))
       `+ `X [] Type (`X [ Term ] Term (`∎ Term))
       `+ `X [] Type (`X [] Type (`∎ Type))
{-
typeof : {X : List Kind → Kind ─Scoped} → ∀ {Δ} →
         ∀[ ⟦ Lambda ⟧ X Term ⇒ (X Δ Term ⇒ X Δ Type) ⇒ X Δ Type ]
typeof e f = {!!}
-}

open import Size

--TODO: move to descutils or somewhere similar
private variable I : Set

-- TODO: should be in environent/descutils
extendΔ : {Δ' Δ : List I} → Thinning Δ (Δ' ++ Δ)
extendΔ {Δ' = []} = identity
lookup (extendΔ  {Δ' = x ∷ Δ'}) v = lookup extend (lookup extendΔ v)


extendΔ2 : {Δ' Δ : List I} → Thinning Δ (Δ ++ Δ')
extendΔ2 {Δ = []} = ε
lookup (extendΔ2 {Δ = x ∷ Δ}) Var.z = Var.z
lookup (extendΔ2 {Δ = x ∷ Δ}) (Var.s v) = Var.s (lookup extendΔ2 v)

th^App : {Δ'' Δ' Δ : List I} → Thinning Δ Δ' → Thinning (Δ'' ++ Δ) (Δ'' ++ Δ')
th^App th = extendΔ2 >> ((λ x → lookup extendΔ x) <$> th)

-- TODO: level ─Scoped
↑⟨_⟩ : (IDesc I → I ─Scoped) → IDesc I → I → List I → Set₁
↑⟨ X ⟩ d i Γ = ∀{d'} → Path d d' → X d' i Γ

{-
module _ {d : IDesc I} {i : I} {Γ : List I} where
  ↑⟨_⟩Tm : Tm d ∞ i Γ → ∀{d'} → Path d d' → Tm d' ∞ i Γ
  ↑⟨ e ⟩Tm p = map^Tm (morph p) e
-}

EnvFn : List I → IDesc I → I → List I → Set
EnvFn [] d = Tm d ∞
EnvFn (x ∷ Γ) d i Δ = Tm d ∞ x (Γ ++ Δ) → EnvFn Γ d i Δ

{-
EnvFn' : IDesc I → I → List I → Set
EnvFn'  d i [] = Tm d ∞ i []
EnvFn' d i (x ∷ Γ) = Tm d ∞ x Γ → EnvFn' d i Γ
-}

module _ {d : IDesc I} {i : I} where
{-
  asConstr' : {Γ : List I} → Tm d ∞ i Γ → EnvFn' d i Γ
  asConstr' {[]} e = e
  asConstr' {x ∷ Γ} e = λ x → asConstr' (e [ x /0])
-}
  
  asConstr : {Γ : List I} → ∀[ (Γ ++_) ⊢ Tm d ∞ i ⇒ EnvFn Γ d i ]
  asConstr {[]} e = e
  asConstr {x ∷ Γ} e = λ x → asConstr {Γ} (e [ x /0])


module _ {I : Set} {d : IDesc I} {i : I} {Γ : List I} where
  ↑⟨_⟩c :  Tm d ∞ i Γ → ∀[ ↑⟨ EnvFn Γ ⟩ d i ]
  ↑⟨ e ⟩c {Δ} p = asConstr (map^Tm (morph p) (th^Tm e extendΔ2))


FunTy : Tm Lambda ∞ Type ( Type ∷ Type ∷ [])
FunTy = `con (false , false , `var z , ( `var (s z) , refl))

⟨_⟩_→t_ : ∀[ ↑⟨ EnvFn ( Type ∷ Type ∷ []) ⟩ Lambda Type ]
⟨_⟩_→t_ = ↑⟨ FunTy ⟩c


SLam : Lang (SynD Lambda)
SLam .desc = Lambda
SLam .alg m = case
  {!!}
  (case
    {!!}
    λ { (lp , rp , refl) → do
      l ← lp
      r ← rp
      --TODO: I shouldn't use/need a path here
      -- TODO: issue: contravariance problems;
        -- need the quantification on alg to be outside SynD somehow
      Val (⟨ path-id ⟩ {!l!} →t {!r!})})

