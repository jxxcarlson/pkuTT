{-# OPTIONS --cubical #-}
module Cubical.FunExt where

open import Cubical.Foundations.Prelude hiding (funExt)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties

-- Given two functions f and g
funExt : {A : Type} {B : A → Type} {f g : (x : A) → B x}
       → (∀ x → f x ≡ g x)  -- Pointwise equality
       → f ≡ g               -- Function equality
funExt p = λ i → λ x → p x i


f : ℕ → ℕ
f x = x + 1

g : ℕ → ℕ
g x = 1 + x

-- Proof that f ≡ g
f≡g : f ≡ g
f≡g = funExt λ x → +-comm x 1

-- Normal form:: (λ x → x + 1) ≡ (λ x → suc x)
test1 : Set
test1 = f ≡ g



      