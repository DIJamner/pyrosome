{-# OPTIONS --sized-types --safe #-}
-- TODO: remove unsolved metas by splitting this file a little
-- We care more about isomorphism of descriptions that equivalence
-- since we can transport semantics across description morphisms
module Path.DescIsomorphism {I} where

open import Data.Bool
open import Data.Product
open import Data.List using (List)
open import Relation.Binary hiding (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; →-to-⟶)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Algebra.Structures
open import Algebra.FunctionProperties

import Function

open import Function.Inverse renaming (_∘_ to _∘ᴵ_)
open import Function.Equality using (_⟨$⟩_;_∘_)

open import Data.Relation
open import Data.Var hiding (_<$>_)
open import Generic.Syntax

open import Utils
open import DescUtils
open import Path.Path {I}

--private module Pre = IsPreorder ⊑-is-preorder

desc-≡ : Setoid _ _
desc-≡ = Eq.setoid (Desc I)

private
  variable
    d1 d2 : Desc I


infix 4 _≅_

-- We use inverses/isomorphism as our equivalence for descriptions
-- since we want commutativity of `+ and other sensible
-- (but not syntactically equal) relationships between descriptions

record _≅_ (d1 d2 : Desc I) : Set₁ where
  field
    right : Path d1 d2
    left : Path d2 d1
    inverses : ∀ {X i Γ} → ⟦ right ⟧$ {X} {i} {Γ} InverseOfᶠ ⟦ left ⟧$

  left-inverse-of : ∀ {X i Γ} → ∀ e → ⟦ right ⟧$ {X} {i} {Γ} ( ⟦ left ⟧$ e) ≡ e
  left-inverse-of = {!!}


  right-morph : DescMorphism d1 d2
  right-morph = MkDescMorphism ⟦ right ⟧$
  
  left-morph : DescMorphism d2 d1
  left-morph = MkDescMorphism ⟦ left ⟧$

                                     
  Tm-right : ∀{s i Γ} → Tm d1 s i Γ → Tm d2 s i Γ
  Tm-right = map^Tm right-morph

  Tm-left : ∀{s i Γ} → Tm d2 s i Γ → Tm d1 s i Γ
  Tm-left = map^Tm left-morph


open _≅_ public

  
Tm-roundtrip : (iso : d1 ≅ d2) → ∀{s i Γ} → (e : Tm d1 s i Γ) → Tm-left iso (Tm-right iso e) ≡ e
Tm-roundtrip iso (`var x) = refl
Tm-roundtrip {`σ A x₁} {d2} iso (`con x) = {!!}
Tm-roundtrip {`X x₁ x₂ d1} {d2} iso (`con x) = {!!}
Tm-roundtrip {`∎ x₁} {`σ A x₂} iso (`con x) = cong `con {!!}
Tm-roundtrip {`∎ x₁} {`∎ x₂} iso (`con x) = cong `con {!inverses!} 


{-
{-
-}

isEquivalence : IsEquivalence _≅_
isEquivalence  = record {
  refl = id ;
  sym = λ x → sym x ;
  trans = λ f g → g ∘ᴵ f }


⓪-identity : Identity _≅_ ⓪ _`+_
⓪-identity =
  (λ x → record {
    to = →-to-⟶ Pre.plus-⓪-no-increaseL ;
    from = →-to-⟶ Pre.plus-nondecreasingR ;
    inverse-of = record {
      left-inverse-of = λ { (false , snd) → refl} ;
      right-inverse-of = λ x → refl } }) ,
  (λ x → record {
    to = →-to-⟶ Pre.plus-⓪-no-increaseR ;
    from = →-to-⟶ Pre.plus-nondecreasingL ;
    inverse-of = record {
      left-inverse-of = λ { (true , snd) → refl } ;
      right-inverse-of = λ x₁ → refl } })

`+-cong : Congruent₂ _≅_ _`+_
`+-cong iso1 iso2 = record {
  to = case⟶ (→-to-⟶ (true ,_ ) ∘ Inverse.to iso1) (→-to-⟶ (false ,_ ) ∘ Inverse.to iso2) ;
  from = case⟶ ((→-to-⟶ (true ,_ ) ∘ Inverse.from iso1)) ((→-to-⟶ (false ,_ ) ∘ Inverse.from iso2)) ;
  inverse-of = record {
    left-inverse-of = λ {
      (false , snd) → cong (false ,_ ) (Inverse.left-inverse-of iso2 snd)  ;
      (true , snd) → cong (true ,_ ) (Inverse.left-inverse-of iso1 snd) } ;
    right-inverse-of = λ {
      (false , snd) → cong (false ,_) (Inverse.right-inverse-of iso2 snd) ;
      (true , snd) → cong (true ,_) (Inverse.right-inverse-of iso1 snd)} } }

`+-assoc : Associative _≅_ _`+_
`+-assoc d1 d2 d3 =  record {
  to = case⟶
    (→-to-⟶ λ { (false , snd) → false , true , snd ;
                (true , snd) → true , snd})
    (→-to-⟶ (λ x → false , false , x)) ;
  from = case⟶
    (→-to-⟶ λ x → true , true , x)
    (→-to-⟶ (λ { (false , snd) → false , snd ;
                 (true , snd) → true , false , snd})) ;
  inverse-of = record {
    left-inverse-of = λ {
      (false , snd) → refl ;
      (true , false , snd) → refl ;
      (true , true , snd) → refl} ;
    right-inverse-of =  λ {
      (false , false , snd) → refl ;
      (false , true , snd) → refl ;
      (true , snd) → refl} } }

-- Descriptions form a commutative monoid under isomorphism with ⓪ and `+
desc-monoid : IsCommutativeMonoid _≅_ _`+_ ⓪
desc-monoid = record {
  isSemigroup = record {
    isMagma = record {
      isEquivalence = isEquivalence ;
      ∙-cong = `+-cong } ;
    assoc = `+-assoc } ;
  identityˡ = proj₁ ⓪-identity ;
  comm = λ x y → record {
    to = →-to-⟶ λ { (false , snd) → true , snd ; (true , snd) → false , snd} ;
    from = →-to-⟶ λ { (false , snd) → true , snd ; (true , snd) → false , snd} ;
    inverse-of = record {
      left-inverse-of = λ { (false , snd) → refl ; (true , snd) → refl} ;
      right-inverse-of = λ { (false , snd) → refl ; (true , snd) → refl} } } }

-- morphisms form a preorder under isomorphism as well as equivalence
⊑-isPreorder : IsPreorder _≅_ _⊑_
⊑-isPreorder = record {
  isEquivalence = isEquivalence ;
  reflexive = right ;
  trans = λ f g → g Function.∘ f }

open import Level
desc-setoid : Setoid (suc zero) (suc zero)
desc-setoid = record {
  Carrier = Desc I ;
  _≈_ = _≅_ ;
  isEquivalence = isEquivalence }


-- Semantics and description isomorphisms
-- Like morphisms, we can transport semantics along isomorphisms
private variable V C : I ─Scoped

open import Generic.Semantics

sem-right : d1 ≅ d2 → Semantics d2 V C → Semantics d1 V C
sem-right iso = DescPreorder.sem-transport (right iso)

sem-left : d1 ≅ d2 → Semantics d1 V C → Semantics d2 V C
sem-left iso = DescPreorder.sem-transport (left iso)


{- TODO: everything below is experimental -}

{-
Issue with all variations on the shuffle lemma: they seem to rely on parametric reasoning
-}

open import Data.Environment
open import Size

private
  variable X : List I → I ─Scoped
           i : I
           Γ Δ : List I

_≅[_]_ : ⟦ d1 ⟧ X i Γ → (iso : d1 ≅ d2) → ⟦ d2 ⟧ X i Γ → Set
e1 ≅[ iso ] e2 = right iso e1 ≡ e2 

fmap-shuffle : (iso : d1 ≅ d2) → {X Y : List I → I ─Scoped} → {i : I} → {Γ Δ : List I} →
               (e :  ⟦ d1 ⟧ X i Γ) →
               (f : ∀ Φ i → X Φ i Γ → Y Φ i Δ) →
               _≅[_]_ {X = Y} (fmap d1 f e) iso (fmap d2 f (right iso e))
fmap-shuffle {d1} {`σ A x} iso e f = {!!}
fmap-shuffle {d1} {`X x x₁ d2} iso e f = {!!}
fmap-shuffle {`σ A x₁} {`∎ x} iso e f = cong (right iso) refl
fmap-shuffle {`X x₁ x₂ d1} {`∎ x} iso e f = cong (right iso) refl
fmap-shuffle {`∎ x₁} {`∎ x} iso e f = cong (right iso) refl

sem-identity : (iso : d1 ≅ d2) → (S : Semantics d2 V C) → {ρ : (Γ ─Env) V Δ} →
  {e : Tm d1 ∞ i Γ} → 
  Semantics.semantics (sem-right iso S) ρ e
  ≡ Semantics.semantics S ρ (map^Tm (MkDescMorphism (right iso)) e)
sem-identity iso S {pack lookup} {`var x} = cong (Semantics.var S) refl
sem-identity {d1 = d1} iso S {pack lookup} {`con x} = cong (Semantics.alg S) {!!}
{-
  (begin
    Inverse.to iso ⟨$⟩ fmap d1
         (Semantics.body (Pre.sem-transport
           (λ {X} {i} {Δ} → (Inverse.to iso)⟨$⟩_) S) (pack lookup)) x
    ≡⟨ cong (Inverse.to iso ⟨$⟩_) {!sem-identity iso S!} ⟩
    Inverse.to iso ⟨$⟩ {!!}
    ≡⟨ {!!} ⟩ {!!}) where
  module S = Semantics S
-}

{-
(Inverse.to iso ⟨$⟩ fmap d1 (Semantics.body
            (Pre.sem-transport (λ {X} {i} {Δ} → _⟨$⟩ (Inverse.to iso)) S)
            (pack lookup)) x)
-}

open import Generic.Simulation

sim-right : (iso : d1 ≅ d2) → {V1 V2 C1 C2 : I ─Scoped} →
            {S1 : Semantics d2 V1 C1} → {S2 : Semantics d2 V2 C2} → ∀{VR CR} →
            Simulation d2 S1 S2 VR CR → Simulation d1 (sem-right iso S1) (sem-right iso S2) VR CR
sim-right iso sim = record {
  thᴿ = Sim.thᴿ ;
  varᴿ = Sim.varᴿ ;
  algᴿ = λ b x x₁ → {!sem-identity!} } where
  module Sim = Simulation sim

{-
open import MultiFusion {I}

iso-fusion : (iso : d1 ≅ d2) →
             (S : Semantics d1 V C) →
             Fusion d1 d2 (morph-to-sem (sem-right iso)) (sem-left iso S) S {!!} Eqᴿ Eqᴿ
iso-fusion iso S = record {
  reifyᴬ = λ σ x → x ;
  vl^𝓥ᴬ = record { th^𝓥 = λ x x₁ → {!!} ; new = {!!} } ;
  _>>ᴿ_ = {!!} ;
  th^𝓔ᴿ = {!!} ;
  varᴿ = {!!} ;
  algᴿ = {!!} }
  -}



{-

  roundtrip : d1 ≅ d2 → Semantics d2 V C → Semantics d2 V C
  roundtrip iso S = sem-transport (sym iso) (sem-transport iso S)

  strans-th : (iso : d1 ≅ d2) → (S : Semantics d2 V C) →
              ∀{σ Γ} → Semantics.th^𝓥 S {σ} {Γ} ≡ Semantics.th^𝓥 (roundtrip iso S)
  strans-th iso S = refl

  tmp : (iso : d1 ≅ d2) → (S : Semantics d2 V C) →
                     sem-transport (sym iso) (sem-transport iso S) ≡ S
  tmp iso S with sem-transport (sym iso) (sem-transport iso S) | strans-th iso S
  tmp iso record { th^𝓥 = th^𝓥₁ ; var = var₁ ; alg = alg₁ }
          | record { th^𝓥 = th^𝓥 ; var = var ; alg = alg } | refl = {!!}

  sem-transport-id : (iso : d1 ≅ d2) → (S : Semantics d2 V C) →
                     sem-transport (sym iso) (sem-transport iso S) ≅ₛ S
  sem-transport-id {d1} {d2} iso S = record {
    thᴿ = λ { ρ refl → refl} ;
    varᴿ = λ { refl → refl} ;
    algᴿ = λ { e (All.packᴿ lookupᴿ) r → {!!}}
    -- Eq.cong₂ (λ x x₁ → Semantics.alg x x₁) {!!} {!!}
    --cong {!!} (Eq.cong₂ (fmap d2) {!!} refl)
    {-λ  a b → cong S.alg Function.∘ λ x →
      begin
        {!!} ≡⟨ Iso.right-inverse-of {!!} ⟩ Eq.cong₂ (fmap d2) (cong {!!} {!!}) refl-}
        } where
    module Iso {X i Γ} = Inverse (iso {X} {i} {Γ})
    --module S = Semantics S
-}

-}
