{-# OPTIONS --without-K #-}

module Hedberg where

open import Level                              using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)                            -- only propositional equality
open import Data.Sum                          using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                  using (¬_)
open import Data.Empty                        using (⊥; ⊥-elim)

-- A “set” is a type whose identity‑proofs are unique:
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ {x y : A} (p q : x ≡ y) → p ≡ q

-- Hedberg’s theorem: decidable equality ⇒ isSet
hedberg
  : ∀ {ℓ} {A : Set ℓ}
  → (dec : ∀ x y → (x ≡ y) ⊎ ¬ (x ≡ y))
  → isSet A
hedberg dec {x}{y} p q with dec x y
... | inj₂ not      = ⊥-elim (not p)
... | inj₁ e   with p | q
...   | refl | refl rewrite e = refl