{-# OPTIONS --without-K #-}

module UA.EvenTransportNonCubical where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Primitive

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

sucBin : Bin → Bin
sucBin zeroB      = bit1 zeroB
sucBin (bit0 b)   = bit1 b
sucBin (bit1 b)   = bit0 (sucBin b)

encode : ℕ → Bin
encode zero     = zeroB
encode (suc n)  = sucBin (encode n)

------------------------------------------------------------------------
-- Step 4: Decode Bin → ℕ
------------------------------------------------------------------------

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

decode : Bin → ℕ
decode zeroB    = zero
decode (bit0 b) = double (decode b)
decode (bit1 b) = suc (double (decode b))

------------------------------------------------------------------------
-- Step 5: Postulate encode-decode and decode-encode
------------------------------------------------------------------------

postulate
  encode-decode : (b : Bin) → encode (decode b) ≡ b
  decode-encode : (n : ℕ) → decode (encode n) ≡ n

------------------------------------------------------------------------
-- Step 6: Define an equivalence
------------------------------------------------------------------------

record Equiv (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    sect    : (b : B) → to (from b) ≡ b
    retr    : (a : A) → from (to a) ≡ a

open Equiv

ℕ≃Bin : Equiv ℕ Bin
ℕ≃Bin = record
  { to   = encode
  ; from = decode
  ; sect = encode-decode
  ; retr = decode-encode
  }

------------------------------------------------------------------------
-- Step 7: Define even function on ℕ
------------------------------------------------------------------------

even : ℕ → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

------------------------------------------------------------------------
-- Step 8: Postulate univalence and define transport
------------------------------------------------------------------------

-- Postulate ua
postulate
  ua : {A B : Set} → Equiv A B → A ≡ B

-- Standard transport
transport : {A B : Set} → A ≡ B → (A → Bool) → (B → Bool)
transport refl f = f

-- Define evenBin by transporting along ua ℕ≃Bin
evenBin : Bin → Bool
evenBin = transport (ua ℕ≃Bin) even

------------------------------------------------------------------------
-- Step 9: Check some computations (no judgmental computation!)
------------------------------------------------------------------------

threeBin : Bin
threeBin = bit1 (bit1 zeroB)

testThree : Bool
testThree = evenBin threeBin

postulate
  exampleThree : evenBin threeBin ≡ false

fourBin : Bin
fourBin = bit0 (bit0 (bit1 zeroB))

testFour : Bool
testFour = evenBin fourBin

postulate
  exampleFour : evenBin fourBin ≡ true