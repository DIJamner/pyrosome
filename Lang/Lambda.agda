
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


UnitDesc : I → (I → I) → IDesc I
UnitDesc e tp = `∎ e `+ `∎ (tp e)

module _ {e : I} {tp : I → I} where
  -- the unit type
  -- TODO: what's the type (kind) of the unit type?
     -- the most obvious thing right now is just to build an infinite tower, tp^n
     -- however, if tp is idempotent, for example, this does bad things
     -- one option is to find a fixpoint of tp and stop there
     -- another option is to pass in a kind for the unit type
        -- this seems not in the spirit of things? the unit language
        -- should describe its interactions with the kind of types
  -- need to establish a system of kinds
  -- also, language extensions that depend on the other parts
  ⑴ : ∀[ Tm (UnitDesc e tp) ∞ (tp e) ]
  ⑴ = `con (false , refl)

  ⑴⟨_⟩ : Ex⟨ UnitDesc e tp ↑ d' ⟩ ∀[ Tm d' ∞ (tp e) ]
  ⑴⟨ p ⟩ = ↑⟨ ⑴ ⟩c p

  UnitLang : Lang I tp
  UnitLang .desc = UnitDesc e tp
  -- two terms are related if their types are both unit
  -- TODO: also need Γ-relatedness (should be built in to Lang, but isn't yet
  UnitLang .precision p R .rel j (_ , i1 , Γt1) (_ , i2 , Γt2) =
    -- TODO: equivalences on types are bad; this should
    -- be using precision on the types
    Σ (j ≡ e) λ { refl → i1 ≡ ⑴⟨ p ⟩ × i2 ≡ ⑴⟨ p ⟩ }


  -- Proof that all terms are related at unit type
  _ : ∀{Γ Γt1 Γt2 e1 e2} →
      rel (prec UnitLang) e {Γ} (e1 , ⑴ , Γt1) (e2 , ⑴ , Γt2)
  _ = suc zero , refl , refl , refl

{-

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
-}

--oplang: give operational semantics via function f
--precision is defined as rel x (f x)
