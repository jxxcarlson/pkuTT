{-# OPTIONS --without-K #-}

module HedbergUnit where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes)
open import Hedberg

-- Define decidable equality for ⊤
_≟_ : (x y : ⊤) → Dec (x ≡ y)
tt ≟ tt = yes refl

-- Get UIP for free using Hedberg's theorem
unitUIP : UIP ⊤
unitUIP = Decidable⇒UIP.≡-irrelevant _≟_ 