{-# OPTIONS --cubical-compatible --safe #-}

module Hedberg where

open import Level using (Level)
open import Relation.Nullary.Decidable.Core
  using (recompute)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions
  using (Sym; Irrelevant; DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; sym; cong)
open import Relation.Binary.PropositionalEquality.Properties

private
  variable
    a : Level
    A : Set a
    x y : A
  
UIP : (A : Set a) → Set a
UIP A = Irrelevant {A = A} _≡_



module Constant⇒UIP
  (f : _≡_ {A = A} ⇒ _≡_)
  (f-constant : ∀ {x y} (p q : x ≡ y) → f p ≡ f q)
  where

  ≡-canonical : (p : x ≡ y) → trans (sym (f refl)) (f p) ≡ p
  ≡-canonical refl = trans-symˡ (f refl)

  ≡-irrelevant : UIP A
  ≡-irrelevant p q = begin
    p                          ≡⟨ sym (≡-canonical p) ⟩
    trans (sym (f refl)) (f p) ≡⟨ cong (trans _) (f-constant p q) ⟩
    trans (sym (f refl)) (f q) ≡⟨ ≡-canonical q ⟩
    q                          ∎
    where open ≡-Reasoning



module Decidable⇒UIP (_≟_ : DecidableEquality A)
  where
 
  -- This function takes a proof x≡y of equality between 
  -- elements x and y of type A, and returns a canonical 
  -- proof of x ≡ y by recomputing it using the decision 
  -- procedure x ≟ y.
  ≡-normalise : _≡_ {A = A} ⇒ _≡_
  ≡-normalise {x} {y} x≡y = recompute (x ≟ y) x≡y
  
  -- This function asserts that for any two proofs 
  -- p and q of equality between elements x and y of 
  -- type A, their normalized forms obtained via 
  -- ≡-normalise are equal. In other words, ≡-normalise 
  -- is a function that maps all proofs of x ≡ y to 
  -- a unique, canonical proof. This is where it is 
  -- shown that a type satisfying decidable equality 
  -- also satisfies compressible identity.
  --
  -- ≡-normalise-constant holds 
  -- because of the properties of the recompute function. 
  -- According to the Agda standard library documentation, 
  -- recompute ensures that for any two proofs p and q 
  -- of a decidable proposition, 
  --
  --   recompute a? p ≡ recompute a? q holds, 
  -- 
  -- where a? is the decision procedure for the 
  -- proposition. This property is formalized in the 
  -- lemma recompute-constant in 
  -- the Relation.Nullary.Decidable.Core module.
  --
  ≡-normalise-constant : (p q : x ≡ y) → ≡-normalise p ≡ ≡-normalise q
  ≡-normalise-constant {x} {y} p q = refl

  ≡-irrelevant : UIP A
  ≡-irrelevant = Constant⇒UIP.≡-irrelevant ≡-normalise ≡-normalise-constant