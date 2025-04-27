{-# OPTIONS --without-K #-}

module UnivalenceCanonicityFailure where

open import Agda.Primitive
open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality

-- Define equivalences manually (very simply)

record Equiv (A B : Set) : Set where
  constructor equiv
  field
    to     : A → B
    from   : B → A
    

-- Postulate Univalence
postulate
  ua : {A B : Set} → Equiv A B → A ≡ B

-- Transport along equality
transport : {A B : Set} → (p : A ≡ B) → A → B
transport refl x = x

-- An explicit equivalence between Bool and Bool
bool-equiv : Equiv Bool Bool
bool-equiv = equiv not not

-- A map from Bool to ℕ
boolToNat : Bool → ℕ
boolToNat true = 1
boolToNat false = 0

-- Now, define a term of type ℕ
badNat : ℕ
badNat = boolToNat (transport (ua bool-equiv) true)