{-# OPTIONS --cubical #-}

module HIT.CirclePi1EqZ1 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (refl; _≡_; _∙_; sym; Path; transport; cong)
open import Cubical.Data.Int 
open import Cubical.Data.Nat using (ℕ; zero; suc)

-- Define the circle as a HIT
data S¹ : Set where
  base : S¹
  loop : Path S¹ base base

-- Loops in the circle (paths from base to base)
ΩS¹ : Set
ΩS¹ = Path S¹ base base

-- The helix fibration over the circle
helix : S¹ → Set
helix base = ℤ
helix (loop i) = sucPathℤ i

-- Compute the winding number of a loop
winding : ΩS¹ → ℤ  
winding p = transport (λ i → helix (p i)) (pos 0)

-- Apply a function n times (for natural numbers)
applyN : {A : Set} → ℕ → (A → A) → A → A
applyN zero    f x = x
applyN (suc n) f x = f (applyN n f x)

-- Apply a function n times (for integers)
applyZ : {A : Set} → ℤ → (A → A) → (A → A) → A → A
applyZ (pos n)    f g x = applyN n f x
applyZ (negsuc n) f g x = applyN (suc n) g x

-- Create a path that goes around the loop n times (for integers)
loopZ : ℤ → ΩS¹
loopZ n = applyZ n (λ p → p ∙ loop) (λ p → p ∙ sym loop) refl