{-# OPTIONS --without-K #-}

module IsSetNat where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)

-- A type A is a set if all identity proofs between any two points coincide
isSet : ∀ {A : Set} → Set
isSet {A} = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

-- ℕ is a set
isSetℕ : isSet {ℕ}
isSetℕ zero     zero     refl refl = refl
isSetℕ (suc m) (suc n) refl refl = refl
isSetℕ zero     (suc _)   ()
isSetℕ (suc _)   zero     ()

-- And hence UIP for ℕ
UIPℕ : ∀ (m : ℕ) (p : m ≡ m) → p ≡ refl
UIPℕ m p = isSetℕ m m p refl