{-# OPTIONS --without-K #-}

module TransportAlongUA where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat

-- Proper Equivalence
record Equiv (A B : Set) : Set where
  constructor equiv
  field
    to    : A → B
    from  : B → A
    left  : (b : B) → to (from b) ≡ b
    right : (a : A) → from (to a) ≡ a

postulate
  ua : {A B : Set} → Equiv A B → A ≡ B

transport : {A B : Set} → (p : A ≡ B) → A → B
transport refl x = x

postulate
  transport-ua : {A B : Set} (e : Equiv A B) (a : A) → transport (ua e) a ≡ Equiv.to e a

notNot : (b : Bool) → not (not b) ≡ b
notNot true = refl
notNot false = refl

boolEquiv : Equiv Bool Bool
boolEquiv = equiv not not notNot notNot

-- Map from Bool to Nat
boolToNat : Bool → ℕ
boolToNat true  = 1
boolToNat false = 0

-- Example usage
example : Bool
example = transport (ua boolEquiv) true

badNat : ℕ
badNat = boolToNat (transport (ua boolEquiv) true)

expected : badNat ≡ 0
expected = cong boolToNat (transport-ua boolEquiv true)