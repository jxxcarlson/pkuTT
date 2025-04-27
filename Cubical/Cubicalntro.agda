{-# OPTIONS --cubical #-}

module Cubicalntro where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_)
open import Data.Nat using (ℕ; zero; suc)

-- Path composition using primitive operations
composeManual : {A : Type} {x y z : A}
              → Path A x y → Path A y z → Path A x z
composeManual p q = p ∙ q