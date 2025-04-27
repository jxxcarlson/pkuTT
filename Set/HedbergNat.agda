{-# OPTIONS --without-K #-}

module HedbergNat where

open import Data.Nat using (ℕ; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Hedberg

-- Natural numbers have decidable equality built-in via _≟_
-- We can use this to get UIP for free:

natUIP : UIP ℕ
natUIP = Decidable⇒UIP.≡-irrelevant _≟_