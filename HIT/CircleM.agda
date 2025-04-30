{-# OPTIONS --cubical #-}

module HIT.CircleM where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
--open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_)
open import Cubical.Data.Int 
open import Cubical.Data.Int.Properties
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






     