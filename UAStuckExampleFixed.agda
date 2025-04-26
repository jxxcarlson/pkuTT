{-# OPTIONS --without-K #-}

module UAStuckExampleFixed where

open import Agda.Primitive
open import Data.Bool
open import Relation.Binary.PropositionalEquality

record Equiv (A B : Set) : Set where
  constructor equiv
  field
    to     : A → B
    from   : B → A
    left   : ∀ b → to (from b) ≡ b
    right  : ∀ a → from (to a) ≡ a

postulate
  ua : {A B : Set} → Equiv A B → A ≡ B

transport : {A B : Set} → (p : A ≡ B) → A → B
transport refl x = x

notNotId : (b : Bool) → not (not b) ≡ b
notNotId true  = refl
notNotId false = refl

example-equiv : Equiv Bool Bool
example-equiv = equiv not not notNotId notNotId

example-transport : Bool → Bool
example-transport b = transport (ua example-equiv) b