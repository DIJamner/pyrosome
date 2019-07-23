--{-# OPTIONS --safe --sized-types #-}

module Lang.SystemF where

open import Size

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List
open import Agda.Builtin.Equality

open import Poly.Syntax
open import Data.Var
open import Data.Environment
open import Generic.Semantics.Syntactic

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


--TODO: get Tm
FtyDesc : SDesc ⊤
FtyDesc = `SX [] tt (`SX [] tt (`S∎ tt)) -- arrow
        `+ `SX [ tt ] tt (`S∎ tt) -- forall
      -- variables will be handled by Tm

Fty : DescTy _
Fty = AsTypes FtyDesc

kd : ⊤ × ⊤
kd = tt , tt

--TODO: should this be over arbitrary Δ?
∀t : DescTy.type Fty kd [ kd ] → DescTy.type Fty kd []
∀t b = `con (false , (b , refl))

_→t_ :  DescTy.type Fty kd Δ → DescTy.type Fty kd Δ → DescTy.type Fty kd Δ
a →t b = `con (true , ({!a!} , ({!!} , refl)))

empty : DescTy.type Fty kd []
empty = ∀t (`var z)

ident : DescTy.type Fty kd []
ident = ∀t {!!}

-- issue: how do I specify the type of the input to FDesc?
-- It should work for any type that starts with a forall
-- but this requires storing a type with an open variable
-- that is not free in the rest of the term
-- (this might be okay if the T constructor were to bind type variables)
-- TODO: X constructor wrong???? Should its Δ be exposed to the rest of the desc?
FDesc : Desc Fty []
FDesc = `X [] [] {!!} {!!}
