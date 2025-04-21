{-# OPTIONS --without-K #-}

module Hedberg where

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- Definition of isSet: the type has at most one proof of equality between any two terms
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ x y → ∀ (p q : x ≡ y) → p ≡ q

-- Normalize a proof of identity to a canonical representative (e.g., the one from dec x y)
normalize : ∀ {ℓ} {A : Set ℓ} →
            (dec : ∀ x y → (x ≡ y) ⊎ ¬ (x ≡ y)) →
            ∀ {x y : A} → (p : x ≡ y) → x ≡ y
normalize dec {x} {y} p with dec x y
... | inj₁ e = e
... | inj₂ not = ⊥-elim (not p)

-- Show that normalize always returns the same result, regardless of input proof
normalize-constant : ∀ {ℓ} {A : Set ℓ}
  (dec : ∀ x y → (x ≡ y) ⊎ ¬ (x ≡ y)) →
  ∀ {x y : A} (p q : x ≡ y) → normalize dec p ≡ normalize dec q
normalize-constant dec {x} {y} p q with dec x y
... | inj₁ e = refl
... | inj₂ not = ⊥-elim (not p)

-- Hedberg’s Theorem: decidable equality implies A is a set
hedberg : ∀ {ℓ} {A : Set ℓ} →
          (∀ x y → (x ≡ y) ⊎ ¬ (x ≡ y)) →
          isSet A
hedberg dec x y p q =
  trans (sym (normalize-constant dec p refl))
        (normalize-constant dec q refl)