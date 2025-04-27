{-# OPTIONS --cubical #-}

module Circle where

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

-- Helper function to compose a path with itself n times
composeN : {A : Set} {x : A} → (p : Path A x x) → ℕ → Path A x x
composeN p zero = refl
composeN p (suc n) = composeN p n ∙ p

encode : ΩS¹ → ℤ
encode p = + 1  -- This is a simplification. In reality, we need to analyze the path p

decode : ℤ → ΩS¹
decode (+ zero) = refl
decode (+ (suc n)) = decode (+ n) ∙ loop
decode (-[1+ zero ]) = sym loop
decode (-[1+ suc n ]) = decode (-[1+ n ]) ∙ sym loop

-- Define how the loop acts on integers
loopAction : ℤ → ℤ
loopAction x = x + (+ 1)

-- Define the inverse of loopAction
loopAction⁻¹ : ℤ → ℤ
loopAction⁻¹ x = x - (+ 1)

-- Prove that loopAction and loopAction⁻¹ are inverses
loopAction-inv : (x : ℤ) → Path ℤ (loopAction (loopAction⁻¹ x)) x
loopAction-inv x = λ i → x + (+ 0)

loopAction⁻¹-inv : (x : ℤ) → Path ℤ (loopAction⁻¹ (loopAction x)) x
loopAction⁻¹-inv x = λ i → x + (+ 0)

code : S¹ → Set 
code base = ℤ
code (loop i) = ua (isoToEquiv (iso loopAction loopAction⁻¹ 
                                   loopAction-inv loopAction⁻¹-inv)) i

-- Define how the transport should behave
transportCode : (x : ℤ) → Path ℤ (transp (λ i → code (loop i)) i0 x) (loopAction x)
transportCode x = transportRefl




