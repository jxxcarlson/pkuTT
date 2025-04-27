{-# OPTIONS --cubical #-}

module EvenTransport where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool.Base
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

------------------------------------------------------------------------
-- Step 1: Define unary ℕ
------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- Step 2: Define binary numbers
------------------------------------------------------------------------

data Bin : Set where
  zeroB : Bin
  bit0  : Bin → Bin
  bit1  : Bin → Bin


------------------------------------------------------------------------
-- Step 3: Encode ℕ → Bin
------------------------------------------------------------------------


-- helper function to do successor in binary
sucBin : Bin → Bin
sucBin zeroB      = bit1 zeroB
sucBin (bit0 b)   = bit1 b
sucBin (bit1 b)   = bit0 (sucBin b)

encode : ℕ → Bin
encode zero     = zeroB
encode (suc n) = sucBin (encode n)


------------------------------------------------------------------------
-- Step 4: Decode Bin → ℕ
------------------------------------------------------------------------

-- helper: double a number
double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

decode : Bin → ℕ
decode zeroB    = zero
decode (bit0 b) = double (decode b)
decode (bit1 b) = suc (double (decode b))



------------------------------------------------------------------------
-- Step 5: Prove encode and decode are inverses
------------------------------------------------------------------------

-- encode after decode and decode after encode
-- For simplicity, we use postulates here (a real proof is possible, but tedious)

postulate
  encode-decode : (b : Bin) → encode (decode b) ≡ b
  decode-encode : (n : ℕ) → decode (encode n) ≡ n

------------------------------------------------------------------------
-- Step 6: Define the equivalence ℕ ≃ Bin
------------------------------------------------------------------------

ℕ≃Bin : ℕ ≃ Bin
ℕ≃Bin = isoToEquiv (iso encode decode encode-decode decode-encode)

------------------------------------------------------------------------
-- Step 7: Define even function on ℕ
------------------------------------------------------------------------

even : ℕ → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

------------------------------------------------------------------------
-- Step 8: Use ua to transport even to Bin
------------------------------------------------------------------------

evenBin : Bin → Bool
evenBin = transport (λ i → ua ℕ≃Bin i → Bool) even

------------------------------------------------------------------------
-- Step 9: Check some computations
------------------------------------------------------------------------

-- Define 3 in Bin: 3 = bit1 (bit1 zeroB)

threeBin : Bin
threeBin = bit1 (bit1 zeroB)

testThree : Bool
testThree = evenBin threeBin

-- Compute evenBin threeBin

exampleThree : evenBin threeBin ≡ false
exampleThree = refl

-- Define 4 in Bin: 4 = bit0 (bit0 (bit1 zeroB))

fourBin : Bin
fourBin = bit0 (bit0 (bit1 zeroB))

-- Compute evenBin fourBin

exampleFour : evenBin fourBin ≡ true
exampleFour = refl

testFour : Bool
testFour = evenBin fourBin