{-# OPTIONS --safe --sized-types #-}
-- Can you use size types to define a description indexed by itself?
-- if Desc is generalized to take an i-level set to a (suc i)-level set,
-- can you use levels to get an n-approximation of Desc (d ∞)?
module DepDesc where

open import Size

open import Level

open import Data.Bool
open import Data.Product
open import Data.List
open import Data.Unit
-- open import Data.Nat
open import Data.Empty

open import Agda.Builtin.Equality

open import V2.Var
open import V2.Syntax

--open import DescUtils

private variable ℓ : Level

⑴ : Desc ⊤
⑴ = `∎ tt

dep0 : Desc ⊤
dep0 = ⑴

-- closed types only
depSucC : {I : Set ℓ} → Desc I → I → Set (suc ℓ)
depSucC d i = Desc (TM d i)

-- open types V1. issue: all types open in the same way
DepSuc1 : {I : Set ℓ} → Desc I → I → List I → Set (suc ℓ)
DepSuc1 d i Γ = Desc (Tm d ∞ i Γ)

-- types are pairs of type context and type syntax
DepSuc : {I : Set ℓ} → Desc I → I → Set (suc ℓ)
DepSuc d i = Desc (Σ[ Γ ∈ List _ ] Tm d ∞ i Γ)

{-
So far we have n finitary levels of typing
this should be enough for now, but can't do universes (not too surprising)
-}

-- types are pairs of type context and type syntax
AsIdx : {I : Set ℓ} → Desc I → I → Set ℓ
AsIdx d i = Σ[ Γ ∈ List _ ] Tm d ∞ i Γ

record TypedDesc : Set₁ where
  field
    td : Desc ⊤
    ed : Desc (AsIdx td tt)

record KindDesc : Set₁ where
  field
    kd : Desc ⊤
    td : Desc (AsIdx kd tt)
    tp : TM kd tt
    ed : Desc (AsIdx td ([] , tp))


record SortDesc : Set₁ where
  field
    sd : Desc ⊤
    kd : Desc (AsIdx sd tt)
    kind : TM sd tt
    td : Desc (AsIdx kd ([] , kind))
    type : TM kd ([] , kind)
    ed : Desc (AsIdx td ([] , type))


private variable I : Set

TDesc : Desc I → I → Set₁
TDesc td i = Desc (AsIdx td i)

record TypeDesc (I : Set) : Set₁ where
  field
    desc : Desc I
    kind : I

⑴-td : TypeDesc ⊤
TypeDesc.desc ⑴-td = ⑴
TypeDesc.kind ⑴-td = tt

WithType : TypeDesc I → TypeDesc I
TypeDesc.desc (WithType record { desc = desc ; kind = kind }) = desc `+ `∎ kind
TypeDesc.kind (WithType record { desc = desc ; kind = kind }) = kind

Type : {td : TypeDesc I} →
       let module WTD = TypeDesc (WithType td) in
       TM WTD.desc WTD.kind
Type {td = td} = `con (false , refl)

record KDesc (I : Set) : Set₁ where
  field
    Kind : I
    td : TypeDesc I
    desc : let module WTD = TypeDesc (WithType td) in
           Desc (AsIdx WTD.desc Kind)

data DescChain : (I : Set) → Desc I → I → Set₁ where
  `⑴ : DescChain ⊤ ⑴ tt
  _`∋[_]_ : ∀{I d i} → DescChain I d i → (d' : Desc (AsIdx d i)) →
          (tp : TM d i) → DescChain (AsIdx d i) d' ([] , tp)

--TODO: when adding chains, I want to join them at some point
-- I guess the question is: how to describe subchains/add subchains
-- can't just go one level up since that keeps adding levels
_C+_ : DescChain {!!} {!!} {!!} → DescChain {!!} {!!} {!!} → DescChain {!!} {!!} {!!}
`⑴ C+ `⑴ = {!`⑴ ∋[ tt!}
c1 C+ c2 = {!!}

{-
NDesc : ℕ → Σ[ I ∈ Set ] TypeDesc I
NDesc zero = ⊤ , ⑴-td
NDesc (suc n) with NDesc n
...              | K , td = AsIdx TD.desc TD.kind  , record { desc = {!!} ; kind = [] , Type }
                 where module TD = TypeDesc (WithType td)
-}


{-=====================================================
Conclusion: this stuff is possible, but hard in general
For now, stick to terms with types, types all have kind tt
-}
