--{-# OPTIONS --safe --sized-types #-}

module Lang.SystemF where

open import Size

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.List.Properties as LP
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; _≗_; refl ; sym ; cong)

open import Poly.Syntax
open import Data.Var
open import Data.Environment
open import Generic.Semantics.Syntactic

open import Function

private
  variable
    J : Set
    I : DescTy J
    j : J
    Δ : List J

--TODO: move to utils/somewhere general
AsTypes : Desc I Δ → DescTy (DescTy.Tp I Δ)
DescTy.type (AsTypes d) = Tm d ∞ []
--TODO: needs semantics (including ren) ported to Poly.Desc
DescTy.th^Ty (AsTypes d) = {!th^Tm!}

TopTy : DescTy ⊤
TopTy = record { type = λ _ _ → ⊤ ; th^Ty = λ {j} {x} a {_} _ → a }

--TODO: get Tm
FtyDesc : SDesc ⊤
FtyDesc = `SX [] tt (`SX [] tt (`S∎ tt)) -- arrow
        `+ `SX [ tt ] tt (`S∎ tt) -- forall
      -- variables will be handled by Tm

Fty : DescTy (DescTy.Tp TopTy [])
Fty = AsTypes FtyDesc

kd : ⊤ × ⊤
kd = tt , tt


--TODO: should this be over arbitrary Δ?
∀t : DescTy.type Fty kd (kd ∷ Δ) → DescTy.type Fty kd Δ
∀t {Δ = Δ} b = `con (false , (cast (cong (kd ∷_) ((sym ∘ map-id) Δ)) (DescTy.type Fty kd) b , refl))


_→t_ :  DescTy.type Fty kd Δ → DescTy.type Fty kd Δ → DescTy.type Fty kd Δ
_→t_ {Δ = Δ} a b = `con (true ,
     ((cast ((sym ∘ map-id) Δ) (DescTy.type Fty kd) a) ,
     (cast ((sym ∘ map-id) Δ) (DescTy.type Fty kd) b , refl)))

empty : DescTy.type Fty kd Δ
empty = ∀t (`var z)

ident : DescTy.type Fty kd Δ
ident = ∀t ((`var z) →t (`var z))

-- issue: how do I specify the type of the input to FDesc?
-- It should work for any type that starts with a forall
-- but this requires storing a type with an open variable
-- that is not free in the rest of the term
-- (this might be okay if the T constructor were to bind type variables)
FDesc : Desc Fty []
FDesc = `T [ kd ] kd (`X [] [] (kd , ∀t (`var (s z))) {!!})
