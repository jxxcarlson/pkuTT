{-# OPTIONS --cubical #-}

module CircleM where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_)
open import Data.Nat using (ℕ; zero; suc)

-- Define the circle as a HIT
data S¹ : Set where
  base : S¹
  loop : Path S¹ base base

ΩS¹ : Set
ΩS¹ = Path S¹ base base

double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

-- Define a type-level path that corresponds to the successor function on ℤ
helix : S¹ → Set
helix base = ℤ
helix (loop i) = ℤ




     