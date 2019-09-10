module Adromeda where

open import Data.Unit
open import Data.List

open import Relation.Unary
open import Function

open import Data.Var hiding (s)
open import Data.Var.Varlike
open import Data.Environment


--open import Generic.Syntax renaming (Desc to $Desc)

{-
-- For now, focus on systems with a single kind
TDesc : Set₁
TDesc = $Desc ⊤

--TODO: dependent desc;
-- It's sufficient for my needs (using codes to get e.g. system F as per Andrej Bauer)
-- is it necessary?
-- Fundamentally, substitution should change I, shouldn't it...

{-
--TODO: should I allow term/type derivations to depend on equality/approximation?
-- long term it's desirable, but would require a new, more complex Desc datatype
-- this trick with td' might allow me to do proper simple types at least
-- (avoiding the contravariance issue)
EDesc : TDesc → Set₁
EDesc td = ∀{td'} → DescMorphism td td' → $Desc (Tm 
-}
-}

-- a closed, simply-typed language
record Lang : Set₁ where
  field
    type : Set
    term : type ─Scoped
    _=ₜ_ : type → type → Set
    _=ₑ_ : ∀ i → ∀[ term i ⇒ term i ⇒ const Set ]

-- a closed, polymorphically-typed language
record PLang : Set₁ where
  field
    type : ⊤ ─Scoped
    term : (Δ : List ⊤) → (type tt Δ) ─Scoped
    _=ₜ_ : ∀[ type tt ⇒ type tt ⇒ const Set ]
    _=ₑ_ : ∀{Δ} → (i : type tt Δ) → ∀[ term Δ i ⇒ term Δ i ⇒ const Set ]


th^Cons : {A : Set} (a : A) → ∀ {x1 x2} → Thinning x1 x2 → Thinning (a ∷ x1) (a ∷ x2)
_─Env.lookup (th^Cons a th) z = z
_─Env.lookup (th^Cons a (pack lookup)) (Var.s v) = Var.s (lookup v)

module SYSTEMF where
  data FType : ⊤ ─Scoped where
    tyvar : ∀[ Var tt ⇒ FType tt ]
    tyfn : ∀[ FType tt ⇒ FType tt ⇒ FType tt ]
    tyforall : ∀[ (tt ∷_) ⊢ FType tt ⇒ FType tt ]

  private
    variable
      Δ : List ⊤
      i j : FType tt Δ

  th^Ty : Thinnable (FType tt)
  th^Ty (tyvar x) th = tyvar (_─Env.lookup th x)
  th^Ty (tyfn t t₁) th = tyfn (th^Ty t th) (th^Ty t₁ th)
  th^Ty (tyforall t) th = tyforall (th^Ty t (th^Cons tt th))

  ty↑ : FType tt Δ → FType tt (tt ∷ Δ)
  ty↑ t = th^Ty t extend

  vl^Ty : VarLike FType
  new vl^Ty = tyvar z
  th^𝓥 vl^Ty = th^Ty

  infix 5 _[_
  infix 6 _/0]

  _/0] : FType tt Δ → (tt ∷ Δ ─Env) FType Δ
  _/0] = singleton vl^Ty

  _[_ : FType tt (tt ∷ Δ) → (tt ∷ Δ ─Env) FType Δ → FType tt Δ
  t [ ρ = ? -- th^Ty t {!ρ!}

  data FTerm : (Δ : List ⊤) → (FType tt Δ) ─Scoped where
    tmvar : ∀[ Var i ⇒ FTerm Δ i ]
    tmfn : ∀[ (j ∷_) ⊢ FTerm Δ i ⇒ FTerm Δ i ]
    tmapp : ∀[ FTerm Δ (tyfn j i) ⇒ FTerm Δ j ⇒ FTerm Δ i ]
    tmforall : ∀[ map ty↑ ⊢ FTerm (tt ∷ Δ) i ⇒ FTerm Δ (tyforall i) ]
    --TODO: substitution
    tminst : ∀[ FTerm Δ (tyforall i) ⇒ FTerm Δ (i [ j /0]) ]

{-
data _─DScoped : (T : T ─DScoped → Set) → Set₁ where
  []ᴰ : ∀{T} → T ─DScoped
  _,ᴰ_ : ∀{T} → (Γ : T ─DScoped) → T Γ → T ─DScoped
-}
