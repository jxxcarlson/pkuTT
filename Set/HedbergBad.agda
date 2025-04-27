module HedbergBad where

open import Relation.Binary.PropositionalEquality
open import Hedberg

bad : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
bad p q = normalize p q

-- I you try to compile this file, you get this error:

-- ErrorAgda v2.8.0-47e7dcb
-- Error
-- /Users/carlson/dev/agda/agda-course/pkuTT/HedbergBad.agda:7.11-24: error: [UnequalTerms]
-- q != p of type x ≡ y
-- when checking that the expression normalize p q has type p ≡ q