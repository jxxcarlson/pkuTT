{-# OPTIONS --without-K #-}

module UA.TransportAlongUA where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool.Base
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism


-- Proper Equivalence


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