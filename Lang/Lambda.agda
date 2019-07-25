
module Lang.Lambda where

open import Data.Product
open import Data.List hiding (lookup)
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Nat
open import Data.Empty
open import Relation.Unary

open import Function
open import Agda.Builtin.Equality

--open import Lang
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.Relation
open import Generic.Syntax renaming (Desc to IDesc)
open import Generic.Semantics.Syntactic

open import ExpLang
open import Path.Path renaming (id to path-id)

{-
Lambda : IDesc SynClass
Lambda = `X [] Term (`X [] Term (`∎ Term))
       `+ `X [] Type (`X [ Term ] Term (`∎ Term))
       `+ `X [] Type (`X [] Type (`∎ Type))

typeof : {X : List Kind → Kind ─Scoped} → ∀ {Δ} →
         ∀[ ⟦ Lambda ⟧ X Term ⇒ (X Δ Term ⇒ X Δ Type) ⇒ X Δ Type ]
typeof e f = {!!}
-}

open import Size hiding (↑_)

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



⑴ : {i : I} → ∀[ Tm (`∎ i) ∞ i ]
⑴ = `con refl

⑴⟨_⟩ : {i : I} → Ex⟨ `∎ i ↑ d' ⟩ ∀[ Tm d' ∞ i ]
⑴⟨ p ⟩ = ↑⟨ `con refl ⟩c p

-- This language makes i into the unit type
-- i.e. with a trival element and all elements equal
-- issue: what if i is shared? this works on the intrinsic typing model
UnitLang : I → Lang I
UnitLang i .type = `∎ i
UnitLang i .desc = `∎ i
-- Reflexivity is automatic and we don't want to relate additional types
UnitLang i .type-precision _ _ .rel _ _ _ = ⊥
-- two terms are related if their types are both unit
-- TODO: also need Γ-relatedness (should be built in to Lang, but isn't yet
UnitLang i .precision pt pd R .rel j (_ , i1 , Γt1) (_ , i2 , Γt2) =
  Σ (j ≡ i) λ { refl → i1 ≡ ⑴⟨ pt ⟩ × i2 ≡ ⑴⟨ pt ⟩ }


-- Proof that all terms are related at unit type
_ : {i : I} → ∀{Γ Γt1 Γt2 e1 e2} →
    rel (prec (UnitLang i)) i {Γ} (e1 , ⑴ , Γt1) (e2 , ⑴ , Γt2)
_ = suc zero , refl , refl , refl



LamDesc : I → I → IDesc I
LamDesc t e = `X [] t (`X [ e ] e (`∎ e)) -- λ:a.b
            `+ `X [] e (`X [] e (`∎ e)) -- a b
            `+ `X [] t (`X [] t (`∎ t)) -- a -> b
            -- TODO: I'm repeating myself here
            -- In addition, I need UnitLang, etc to follow the same convention
            -- how to fix?
            -- idea: instead of separate types, I -> I function
            -- that maps class i to class j of types for those terms

FunTy : (t e : I) → Tm (LamDesc t e) ∞ t ( t ∷ t ∷ [])
FunTy t e = `con (false , false , `var z , ( `var (s z) , refl))

⟨_⟩_→t_ : {t e : I} → ∀[ ↑⟨ EnvFn ( t ∷ t ∷ []) ⟩ (LamDesc t e) t ]
⟨_⟩_→t_ {t = t} {e = e} = ↑⟨ FunTy t e ⟩c

LambdaLang : I → I → Lang I
LambdaLang t e .type = `X [] e (`X [] e (`∎ e)) -- a -> b
LambdaLang t e .desc = LamDesc t e
LambdaLang t e .type-precision _ _ .rel _ _ _ = ⊥
LambdaLang t e .precision pt {d''} pd R .rel j (e1 , i1 , Γt1) (e2 , i2 , Γt2) =
  (Σ (j ≡ t) λ { refl →
  Σ (TM d'' t × TM d'' t × TM d'' t × TM d'' t) λ { (i11 , i12 , i21 , i22) →
  {!i1 ≡ ⟨ pd ⟩ i11 →t i12!}}})
  ⊎ {!!}

{-
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

-}
