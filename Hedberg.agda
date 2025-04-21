module Hedberg where

open import Level using (Level; zero)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- A type is a set if all equality proofs between any two values are equal
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

-- Helper: reduce all identity proofs to refl
normalize : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → (r : x ≡ y) → (s : x ≡ y) → s ≡ r
normalize refl refl = refl

-- Hedberg’s Theorem: decidable equality implies uniqueness of identity proofs
hedberg : ∀ {ℓ} {A : Set ℓ} →
  (dec : ∀ x y → Dec (x ≡ y)) →
  isSet A
hedberg dec x y p q with dec x y
... | yes r = trans (normalize r p) (sym (normalize r q))
... | no ¬r = ⊥-elim (¬r p)

-- Injectivity of suc
cong-from-suc : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
cong-from-suc refl = refl

-- Decidable equality for ℕ
decEqℕ : ∀ (m n : ℕ) → Dec (m ≡ n)
decEqℕ zero zero = yes refl
decEqℕ zero (suc n) = no (λ ())
decEqℕ (suc m) zero = no (λ ())
decEqℕ (suc m) (suc n) with decEqℕ m n
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (cong-from-suc q))

-- Finally: ℕ is a set
isSetℕ : isSet ℕ
isSetℕ = hedberg decEqℕ


