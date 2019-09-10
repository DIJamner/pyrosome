{-# OPTIONS --safe --sized-types #-}

module ShiftedSyntax where

open import Size
open import Data.Bool
open import Data.List.Base as L hiding ([_])
open import Data.List.All hiding (mapA; sequenceA)
open import Data.Product as Prod
open import Function hiding (case_of_)
open import Relation.Binary.PropositionalEquality hiding ([_])

data Desc (I : Set) : Set₁ where
