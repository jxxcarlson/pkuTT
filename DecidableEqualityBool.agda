module DecidableEqualityBool where

-- Define the empty type
data ⊥ : Set where

-- Define negation
¬_ : Set → Set
¬ A = A → ⊥

-- Define decidable propositions
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

-- Define equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Define Bool type
data Bool : Set where
  true  : Bool
  false : Bool

-- Prove that Bool has decidable equality
_≟_ : (x y : Bool) → Dec (x ≡ y)
true ≟ true = yes refl
true ≟ false = no λ()
false ≟ true = no λ()
false ≟ false = yes refl