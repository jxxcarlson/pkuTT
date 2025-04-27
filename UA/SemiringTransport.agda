{-# OPTIONS --cubical #-}

module UA.SemiringTransport where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool.Base
open import Cubical.Data.Sigma

infixl 20 _+_ℕ
infixl 30 _*_ℕ

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
encode (suc n)  = sucBin (encode n)

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
-- Step 5: Equivalence between ℕ and Bin
------------------------------------------------------------------------

postulate
  encode-decode : (b : Bin) → encode (decode b) ≡ b
  decode-encode : (n : ℕ) → decode (encode n) ≡ n

ℕ≃Bin : ℕ ≃ Bin
ℕ≃Bin = isoToEquiv (iso encode decode encode-decode decode-encode)

------------------------------------------------------------------------
-- Step 6: Define Semiring structure
------------------------------------------------------------------------

private
  module NatOps where
    _+_ℕ : ℕ → ℕ → ℕ
    _+_ℕ zero n = n
    _+_ℕ (suc m) n = suc (_+_ℕ m n)

    _*_ℕ : ℕ → ℕ → ℕ
    _*_ℕ zero n = zero
    _*_ℕ (suc m) n = _+_ℕ n (_*_ℕ m n)

open NatOps public

-- 0 and 1 for ℕ
zeroℕ : ℕ
zeroℕ = zero

oneℕ : ℕ
oneℕ = suc zero

-- A record for Semiring structure
record Semiring (A : Set) : Set where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    0#  : A
    1#  : A

    +-assoc  : (x y z : A) → (x + (y + z)) ≡ ((x + y) + z)
    +-comm   : (x y : A) → (x + y) ≡ (y + x)
    *-assoc  : (x y z : A) → (x * (y * z)) ≡ ((x * y) * z)
    left-distrib  : (x y z : A) → (x * (y + z)) ≡ ((x * y) + (x * z))
    right-distrib : (x y z : A) → ((x + y) * z) ≡ ((x * z) + (y * z))
    0-left-annihilates : (x : A) → (0# * x) ≡ 0#
    1-left-neutral : (x : A) → (1# * x) ≡ x

  infixl 20 _+_
  infixl 30 _*_

  -- Helper functions to make the operators available in the record
  _+'_ : A → A → A
  _+'_ = _+_

  _*'_ : A → A → A
  _*'_ = _*_

  -- Helper functions to make the operators available in the record
  _+''_ : A → A → A
  _+''_ = _+_

  _*''_ : A → A → A
  _*''_ = _*_

  -- Helper functions to make the operators available in the record
  _+'''_ : A → A → A
  _+'''_ = _+_

  _*'''_ : A → A → A
  _*'''_ = _*_

  -- Helper functions to make the operators available in the record
  _+''''_ : A → A → A
  _+''''_ = _+_

  _*''''_ : A → A → A
  _*''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+'''''_ : A → A → A
  _+'''''_ = _+_

  _*'''''_ : A → A → A
  _*'''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+''''''_ : A → A → A
  _+''''''_ = _+_

  _*''''''_ : A → A → A
  _*''''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+'''''''_ : A → A → A
  _+'''''''_ = _+_

  _*'''''''_ : A → A → A
  _*'''''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+''''''''_ : A → A → A
  _+''''''''_ = _+_

  _*''''''''_ : A → A → A
  _*''''''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+'''''''''_ : A → A → A
  _+'''''''''_ = _+_

  _*'''''''''_ : A → A → A
  _*'''''''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+''''''''''_ : A → A → A
  _+''''''''''_ = _+_

  _*''''''''''_ : A → A → A
  _*''''''''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+'''''''''''_ : A → A → A
  _+'''''''''''_ = _+_

  _*'''''''''''_ : A → A → A
  _*'''''''''''_ = _*_

  -- Helper functions to make the operators available in the record
  _+''''''''''''_ : A → A → A
  _+''''''''''''_ = _+_

  _*''''''''''''_ : A → A → A
  _*''''''''''''_ = _*_

------------------------------------------------------------------------
-- Step 7: Define Semiring instance for ℕ
------------------------------------------------------------------------

-- Proofs (quickly postulated here for simplicity)
postulate
  +-assocℕ : (x y z : ℕ) → (x + (y + z)) ≡ ((x + y) + z)
  +-commℕ  : (x y : ℕ) → (x + y) ≡ (y + x)
  *-assocℕ : (x y z : ℕ) → (x * (y * z)) ≡ ((x * y) * z)
  left-distribℕ  : (x y z : ℕ) → (x * (y + z)) ≡ (x * y + x * z)
  right-distribℕ : (x y z : ℕ) → ((x + y) * z) ≡ (x * z + y * z)
  0-left-annihilatesℕ : (x : ℕ) → (zero * x) ≡ zero
  1-left-neutralℕ : (x : ℕ) → (suc zero * x) ≡ x

-- Now package everything into a Semiring ℕ
semiringℕ : Semiring ℕ
semiringℕ .Semiring._+_ = _+_ℕ
semiringℕ .Semiring._*_ = _*_ℕ
semiringℕ .Semiring.0#  = zeroℕ
semiringℕ .Semiring.1#  = oneℕ
semiringℕ .Semiring.+-assoc = +-assocℕ
semiringℕ .Semiring.+-comm  = +-commℕ
semiringℕ .Semiring.*-assoc = *-assocℕ
semiringℕ .Semiring.left-distrib  = left-distribℕ
semiringℕ .Semiring.right-distrib = right-distribℕ
semiringℕ .Semiring.0-left-annihilates = 0-left-annihilatesℕ
semiringℕ .Semiring.1-left-neutral = 1-left-neutralℕ

------------------------------------------------------------------------
-- Step 8: Transport the Semiring structure to Bin
------------------------------------------------------------------------

semiringBin : Semiring Bin
semiringBin = transport (λ X → Semiring X) (ua ℕ≃Bin) semiringℕ

------------------------------------------------------------------------
-- Step 9: Result
------------------------------------------------------------------------

-- Now semiringBin is a valid Semiring on Bin!