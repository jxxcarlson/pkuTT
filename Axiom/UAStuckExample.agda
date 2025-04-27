{-# OPTIONS --without-K #-}

module UAStuckExample where

open import Agda.Primitive
open import Data.Bool
open import Relation.Binary.PropositionalEquality

-- Define a simple equivalence between Bool and Bool   
record Equiv (A B : Set) : Set where
  constructor equiv
  field
    to     : A → B
    from   : B → A
    -- left   : ∀ b → to (from b) ≡ b
    -- right  : ∀ a → from (to a) ≡ a
    -- /Users/carlson/dev/agda/agda-course/pkuTT/UAStuckExample.agda:28.17-30: error: [UnequalTerms]
    -- (left : (b : Bool) → not (not b) ≡ b)
    -- (right : (a : Bool) → not (not a) ≡ a) →
    -- Equiv Bool Bool
    -- !=< Equiv Bool Bool
    -- when checking that the expression equiv not not has type
    -- Equiv Bool Bool

    
-- Postulate Univalence (no computational content)
postulate
  ua : {A B : Set} → Equiv A B → A ≡ B

-- Define transport along an equality
transport : {A B : Set} → (p : A ≡ B) → A → B
transport refl x = x

-- Build an explicit equivalence: negation is its own inverse
example-equiv : Equiv Bool Bool
example-equiv = equiv not not

-- Attempt to transport along ua
example-transport : Bool → Bool
example-transport b = transport (ua example-equiv) b

-- 
-- Explanation:
-- - "transport" works by pattern matching on "refl".
-- - But "ua example-equiv" does not compute to "refl".
-- - Thus, "transport (ua example-equiv) b" is stuck.
-- 
-- Attempting to evaluate "example-transport true" will not simplify.
-- Computation is blocked because "ua" is a postulate.
--
