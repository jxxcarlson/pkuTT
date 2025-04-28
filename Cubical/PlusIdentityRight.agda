{-# OPTIONS --cubical #-}

module Cubical.PlusIdentityRight where

open import Cubical.Foundations.Prelude

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

+-identityʳ : (n : ℕ) → PathP (λ i → ℕ) (n + zero) n
+-identityʳ zero = λ i → zero
+-identityʳ (suc n) = cong suc (+-identityʳ n)


