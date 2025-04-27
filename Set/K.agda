{-# OPTIONS --without-K #-}


module K where

open import Data.Bool
open import Agda.Primitive using (Level; _⊔_)
open import Data.Nat using (ℕ)
open import Agda.Builtin.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; J)




-- postulate K 
postulate
  K : ∀ {A : Set} (x : A) (p : x ≡ x) → p ≡ refl

-- derive uip from K
uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip {A} {x} {x} refl q = sym (K x q)



-- A simple proof that 2 ≡ 2 using refl
example1 : 2 ≡ 2
example1 = refl

-- Another "proof" that 2 ≡ 2 using refl again
example2 : 2 ≡ 2
example2 = refl

-- Try to use UIP to show that example1 and example2 are equal
equality-of-equalities : example1 ≡ example2
equality-of-equalities = uip example1 example2

