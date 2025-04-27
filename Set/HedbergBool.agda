{-# OPTIONS --without-K #-}

module HedbergBool where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Hedberg

-- First define decidable equality for Bool
_≟_ : (x y : Bool) → Dec (x ≡ y)
true ≟ true = yes refl
true ≟ false = no λ()
false ≟ true = no λ()
false ≟ false = yes refl

-- Then get UIP for free using Hedberg's theorem
boolUIP : UIP Bool
boolUIP = Decidable⇒UIP.≡-irrelevant _≟_ 