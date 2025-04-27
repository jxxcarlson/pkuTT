{-# OPTIONS --cubical #-}

module CirclePi1 where

open import Agda.Primitive                  using (Level; lzero)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base           using (ℕ; zero; suc)
open import Cubical.Data.Int.Base           using (ℤ; pos; negsuc)
open import Cubical.HITs.S1.Base            using (S¹; base; loop)
open import Cubical.HITs.S1.Properties      using (elim)

-- The loop space at the basepoint
ΩS¹ : Type lzero
ΩS¹ = base ≡ base

-- Code family via circle elimination
code : S¹ → Type lzero
code = elim (λ _ → Type lzero) ℤ (λ _ → pos zero)

-- Loop exponentiation: repeat a loop n times
_^_ : ∀ {ℓ} {A : Type ℓ} {a : A} → a ≡ a → ℕ → a ≡ a
p ^ zero    = refl
p ^ suc n   = p ∙ (p ^ n)

-- Inverse loop iteration for negative integers
invLoop : ℕ → ΩS¹
invLoop zero    = refl
invLoop (suc n) = sym loop ∙ invLoop n

-- Decode an integer to a loop
decode : ℤ → ΩS¹
decode (pos n)    = loop ^ n
decode (negsuc n) = invLoop (suc n)

-- Encode a loop to an integer
encode : ΩS¹ → ℤ
encode p = transport code p (pos zero)

-- TODO: prove encode ∘ decode ≡ id and decode ∘ encode ≡ id
-- showing ΩS¹ ≃ ℤ