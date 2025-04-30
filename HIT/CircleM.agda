{-# OPTIONS --cubical #-}

module HIT.CircleM where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (assoc; lUnit; rUnit)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Int 
open import Cubical.Data.Int.Properties
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_)

-- Define the circle as a HIT
data S¹ : Set where
  base : S¹
  loop : Path S¹ base base

ΩS¹ : Set
ΩS¹ = Path S¹ base base

double : S¹ → S¹ 
double base = base
double (loop i) = (loop ∙ loop) i


helix : S¹ → Set
helix base = ℤ
helix (loop i) = sucPathℤ i

winding : ΩS¹  → ℤ  
winding p = transport (λ i → helix (p i)) (pos 0)

ex1 : winding loop ≡ pos 1
ex1 = refl

ex2 : winding (loop ∙ loop) ≡ pos 2
ex2 = refl

ex3 : winding (sym loop) ≡ negsuc 0
ex3 = refl

-- 2. Going around the loop twice (corresponds to +2)
loopTwice : ΩS¹
loopTwice = loop ∙ loop

-- 3. Going around the loop in the opposite direction (corresponds to -1)
loopBackwards : ΩS¹
loopBackwards = sym loop

-- 4. Let's compute what happens to an integer when we go around the loop
-- Starting with 0 and going around once should give us 1
computeOnce : transport (λ i → helix (loop i)) (pos 0) ≡ pos 1
computeOnce = refl

-- Going around twice should give us 2
computeTwice : transport (λ i → helix (loopTwice i)) (pos 0) ≡ pos 2
computeTwice = refl

-- Going backwards should give us -1
computeBackwards : transport (λ i → helix (loopBackwards i)) (pos 0) ≡ negsuc 0
computeBackwards = refl

-- Examples with more complex path compositions
loopThreeTimes : ΩS¹
loopThreeTimes = loop ∙ loop ∙ loop

_ : winding loopThreeTimes ≡ pos 3
_ = refl

-- Going forward then backward
forwardThenBack : ΩS¹
forwardThenBack = loop ∙ sym loop

_ : winding forwardThenBack ≡ pos 0
_ = refl

-- Going backward then forward
backThenForward : ΩS¹
backThenForward = sym loop ∙ loop

_ : winding backThenForward ≡ pos 0
_ = refl

-- Using transport to show the same
_ : transport (λ i → helix (forwardThenBack i)) (pos 0) ≡ pos 0
_ = refl

_ : transport (λ i → helix (backThenForward i)) (pos 0) ≡ pos 0
_ = refl

-- Apply a function n times (for natural numbers)
applyN : {A : Set} → ℕ → (A → A) → A → A
applyN zero    f x = x
applyN (suc n) f x = f (applyN n f x)

-- Apply a function n times (for integers)
applyZ : {A : Set} → ℤ → (A → A) → (A → A) → A → A
applyZ (pos n)    f g x = applyN n f x
applyZ (negsuc n) f g x = applyN (suc n) g x

-- Examples of using applyZ
_ : applyZ (pos 3) suc (λ x → x ∸ 1) 0 ≡ 3
_ = refl


-- Create a path that goes around the loop n times (for natural numbers)
loopN : ℕ → ΩS¹
loopN n = applyN n (λ p → p ∙ loop) refl

-- Create a path that goes around the loop n times (for integers)
loopZ : ℤ → ΩS¹
loopZ n = applyZ n (λ p → p ∙ loop) (λ p → p ∙ sym loop) refl

-- Verify winding numbers for loopZ
winding-pos : (n : ℕ) → winding (loopZ (pos n)) ≡ pos n
winding-pos zero = refl
winding-pos (suc n) = cong sucℤ (winding-pos n)

winding-neg : (n : ℕ) → winding (loopZ (negsuc n)) ≡ negsuc n
winding-neg zero = refl
winding-neg (suc n) = cong predℤ (winding-neg n)