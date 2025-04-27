{-# OPTIONS --without-K #-}
module DecidableEqualityNat where


open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

decEqNat : (m n : ℕ) → Dec (m ≡ n)
decEqNat zero    zero    = yes refl
decEqNat zero    (suc n) = no (λ ())
decEqNat (suc m) zero    = no (λ ())
decEqNat (suc m) (suc n) with decEqNat m n
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (cong pred q))