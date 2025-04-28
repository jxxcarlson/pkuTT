{-# OPTIONS --without-K #-}

module Axiom.UAStuck where

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

isInvolution : (b : Bool) → not (not b) ≡ b
isInvolution true  = refl
isInvolution false = refl

ourEquiv : Equiv Bool Bool
ourEquiv = equiv not not isInvolution isInvolution

ourTransport : Bool → Bool
ourTransport b = transport (ua ourEquiv) b  