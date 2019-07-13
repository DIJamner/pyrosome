{-# OPTIONS --safe --sized-types #-}
module Lang where

open import Size

open import Data.List

open import Data.Var hiding (s;_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Relation.Unary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Data.Relation hiding (_>>ᴿ_)

open import Generic.Syntax
import Generic.Semantics as Sem'
open import Generic.Semantics.Syntactic
import Generic.Simulation as Sim'
open import Generic.Relator

open import Function as Fun using (_∘_)

open import Path.Path
--open import Path.Semantics

open import V2.Semantics
open import V2.Fusion

private
  variable
    I : Set
    σ : I
    Γ Δ : List I
    d : Desc I

private
  variable
    s : Size

{- TODO: separate simulation file? -}

record Simulation (d : Desc I) (MA MB : Model I)
                  (SA : Semantics d MA) (SB : Semantics d MB)
                  (VR : Rel (Val MA) (Val MB)) (CR : Rel (Comp MA) (Comp MB)) : Set where
       module MA = Model MA
       module MB = Model MB
           
       field
          thᴿ   : ∀{σ vᴬ vᴮ} → (ρ : Thinning Γ Δ) → rel VR σ vᴬ vᴮ →
                   rel VR σ (MA.th^𝓥 vᴬ ρ) (MB.th^𝓥 vᴮ ρ)

          varᴿ  : ∀{σ Γ vᴬ vᴮ} → rel VR σ {Γ} vᴬ vᴮ → rel CR σ (MA.var vᴬ) (MB.var vᴮ)

          algᴿ  : {ρᴬ : (Γ ─Env) MA.Val Δ} → {ρᴮ : (Γ ─Env) MB.Val Δ} →
                  (b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ) → All VR Γ ρᴬ ρᴮ →
                let  vᴬ = fmap d (body MA SA ρᴬ) b
                     vᴮ = fmap d (body MB SB ρᴮ) b
                in ⟦ d ⟧ᴿ (Kripkeᴿ VR CR) vᴬ vᴮ → rel CR σ (SA vᴬ) (SB vᴮ)

{-
A language has two syntaxes, one for values and one for computations,
with a path embedding the value syntax into the computation one.
It also has a model and a denotational semantics of values as model values
and computations as model computations.
These semantics should agree.

A laguage's syntax model can be used as the target of another's
semantics to implement a language by elaboration

TODO: shoudl vd/cd be arguments? fields prob. suit them better
-}
record Language (vd : Desc I) (cd : Desc I) (M : Model I) : Set₁ where
  field
    vd-embed : Path vd cd --TODO: should this be abstracted out like for model? might be too small
    val-sem : Semantics vd (value-model M)
    comp-sem : Semantics cd M
    sem-cong : Simulation vd (value-model M) M val-sem (comp-sem ∘ ⟦ vd-embed ⟧$) Eqᴿ (VCᴿ M)
    
  syntax-model : Model I
  syntax-model .Val = Tm vd ∞
  syntax-model .Comp = Tm cd ∞
  syntax-model .th^𝓥 = th^Tm
  syntax-model .var = Tm⟦ vd-embed ⟧$

  value-syntax-model : Model I
  value-syntax-model = value-model syntax-model

  val-sem' : Sem'.Semantics vd (Val M) (Val M)
  val-sem' = to-sem' (value-model M) val-sem
  
  comp-sem' : Sem'.Semantics cd (Val M) (Comp M)
  comp-sem' = to-sem' M comp-sem

open Language


module _ {I : Set} {vd1 vd2 cd1 cd2 : Desc I} {M1 M2 : Model I} where

  record Compiler (L1 : Language vd1 cd1 M1)
                  (L2 : Language vd2 cd2 M2)
                  (VR : Rel (Val M2) (Val M1))
                  (VC : Rel (Comp M2) (Comp M1)) : Set₁ where
    module L1 = Language L1
    module L2 = Language L2
    field
      translation : Language vd1 cd1 L2.syntax-model
      correctⱽ : Fusion L2.value-syntax-model (value-model M2) (value-model M1)
                        vd1 vd2
                        (val-sem translation)
                        L2.val-sem
                        L1.val-sem
                        (λ Γ Δ ρ1 ρ2 → All VR Γ (Sem'.Semantics.semantics L2.val-sem' ρ2 <$> ρ1))
                        VR
                        VR
      correctᶜ : Fusion L2.syntax-model M2 M1
                        cd1 cd2
                        (comp-sem translation)
                        L2.comp-sem
                        L1.comp-sem
                        (λ Γ Δ ρ1 ρ2 → All VR Γ (Sem'.Semantics.semantics L2.val-sem' ρ2 <$> ρ1))
                        VR
                        VC
    compile : ∀ {i} → VarLike (Tm vd2 ∞) → ∀[ Tm cd1 ∞ i ⇒ Tm cd2 ∞ i ]
    compile = eval L2.syntax-model (comp-sem translation)

open Compiler


lang-id : {vd cd : Desc I} → (M : Model I) → (L : Language vd cd M) → Language vd cd (syntax-model L)
lang-id {vd = vd} {cd = cd} M L = record {
  vd-embed = vd-embed L ;
  val-sem = syn-val-sem vd ;
  comp-sem = syn-sem vd cd (vd-embed L) ;
  sem-cong = record {
    thᴿ = λ { ρ refl → refl} ;
    varᴿ = λ { refl → refl} ;
    -- TODO: would be simple if VR was Eq (just path distributivity wrt fmap)
    -- need to figure out how to use assumptions
    algᴿ = λ b ρᴿ vᴿ → {!Eq.cong (rel (VCᴿ (syntax-model L)) _)!} } }

open Fusion
open import Generic.Fusion.Utils

comp-id : {vd cd : Desc I} → (M : Model I) → (L : Language vd cd M) → Compiler L L Eqᴿ Eqᴿ
comp-id M L .translation = lang-id M L
comp-id M L .correctⱽ .reifyᴬ σ = Fun.id
comp-id M L .correctⱽ .vl^𝓥ᴬ = vl^Tm
comp-id M L .correctⱽ ._>>ᴿ_ = subBodyEnv (to-sem' (value-model M) (val-sem L)) {!!} {!!} {!!}
comp-id M L .correctⱽ .th^𝓔ᴿ = {!!}
comp-id M L .correctⱽ .varᴿ ρeq x = lookupᴿ ρeq x
comp-id M L .correctⱽ .algᴿ = {!!}
comp-id M L .correctᶜ .reifyᴬ σ = Fun.id
comp-id M L .correctᶜ .vl^𝓥ᴬ = vl^Tm
comp-id M L .correctᶜ ._>>ᴿ_ ρeq veq = thBodyEnv {!!} {!!}
comp-id M L .correctᶜ .th^𝓔ᴿ = {!!}
comp-id M L .correctᶜ .varᴿ ρeq x = lookupᴿ {!ρeq!} x
comp-id M L .correctᶜ .algᴿ = {!!}

-- TODO: generalize beyond Eq and to multiple models
_∘ᶜ_ :  {vd1 cd1 vd2 cd2 vd3 cd3 : Desc I} →
        {M : Model I} →
        {L1 : Language vd1 cd1 M} → {L2 : Language vd2 cd2 M} → {L3 : Language vd3 cd3 M} →
        Compiler L2 L3 Eqᴿ Eqᴿ → Compiler L1 L2 Eqᴿ Eqᴿ → Compiler L1 L3 Eqᴿ Eqᴿ
_∘ᶜ_ {L1 = L1} C1 C2 .translation .vd-embed = vd-embed L1
(C1 ∘ᶜ C2) .translation .val-sem v = val-sem (translation C1) {!val-sem (translation C2) v!}
(C1 ∘ᶜ C2) .translation .comp-sem e = comp-sem (translation C1) {!comp-sem (translation C2)!}
(C1 ∘ᶜ C2) .translation .sem-cong = {!!}
(C1 ∘ᶜ C2) .correctⱽ .reifyᴬ σ = Fun.id
(C1 ∘ᶜ C2) .correctⱽ .vl^𝓥ᴬ = vl^Tm
(C1 ∘ᶜ C2) .correctⱽ ._>>ᴿ_ ρeq veq = {!!}
(C1 ∘ᶜ C2) .correctⱽ .th^𝓔ᴿ = {!!}
(C1 ∘ᶜ C2) .correctⱽ .varᴿ = {!!}
(C1 ∘ᶜ C2) .correctⱽ .algᴿ = {!!}
(C1 ∘ᶜ C2) .correctᶜ .reifyᴬ σ = Fun.id
(C1 ∘ᶜ C2) .correctᶜ .vl^𝓥ᴬ = vl^Tm
(C1 ∘ᶜ C2) .correctᶜ ._>>ᴿ_ ρeq veq = {!!}
(C1 ∘ᶜ C2) .correctᶜ .th^𝓔ᴿ = {!!}
(C1 ∘ᶜ C2) .correctᶜ .varᴿ = {!!}
(C1 ∘ᶜ C2) .correctᶜ .algᴿ = {!!}
