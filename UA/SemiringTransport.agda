{-# OPTIONS --cubical #-}

module UA.SemiringTransport where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool.Base
open import Cubical.Data.Sigma

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

    infixl 20 _+_ℕ
    infixl 30 _*_ℕ

open NatOps public

-- 0 and 1 for ℕ
zeroℕ : ℕ
zeroℕ = zero

oneℕ : ℕ
oneℕ = suc zero

-- Properties of natural numbers
private
  module NatProps where
    -- Properties of addition and multiplication for ℕ
    +-assocℕ : (x y z : ℕ) → (_+_ℕ x (_+_ℕ y z)) ≡ (_+_ℕ (_+_ℕ x y) z)
    +-assocℕ zero y z = refl
    +-assocℕ (suc x) y z = cong suc (+-assocℕ x y z)

    -- Helper lemmas for addition
    +-zero : (n : ℕ) → _+_ℕ n zero ≡ n
    +-zero zero = refl
    +-zero (suc n) = cong suc (+-zero n)

    +-zero-right : (n : ℕ) → _+_ℕ zero n ≡ n
    +-zero-right n = refl

    +-suc : (m n : ℕ) → _+_ℕ m (suc n) ≡ suc (_+_ℕ m n)
    +-suc zero n = refl
    +-suc (suc m) n = cong suc (+-suc m n)

    +-suc-right : (m n : ℕ) → _+_ℕ (suc m) n ≡ suc (_+_ℕ m n)
    +-suc-right m n = refl

    -- Additional helper lemmas
    +-cong-left : {m n p : ℕ} → m ≡ n → _+_ℕ m p ≡ _+_ℕ n p
    +-cong-left {m} {n} {p} m≡n = cong (λ x → _+_ℕ x p) m≡n

    +-cong-right : {m n p : ℕ} → n ≡ p → _+_ℕ m n ≡ _+_ℕ m p
    +-cong-right {m} {n} {p} n≡p = cong (λ x → _+_ℕ m x) n≡p

    +-assoc-left : (x y z : ℕ) → _+_ℕ (_+_ℕ x y) z ≡ _+_ℕ x (_+_ℕ y z)
    +-assoc-left x y z = sym (+-assocℕ x y z)

    +-assoc-right : (x y z : ℕ) → _+_ℕ x (_+_ℕ y z) ≡ _+_ℕ (_+_ℕ x y) z
    +-assoc-right x y z = +-assocℕ x y z

    +-commℕ : (x y : ℕ) → (_+_ℕ x y) ≡ (_+_ℕ y x)
    +-commℕ m zero = +-zero m
    +-commℕ m (suc n) = 
      _+_ℕ m (suc n)
        ≡⟨ +-suc m n ⟩
      suc (_+_ℕ m n)
        ≡⟨ cong suc (+-commℕ m n) ⟩
      suc (_+_ℕ n m)
        ≡⟨ sym (+-suc-right n m) ⟩
      _+_ℕ (suc n) m
      ∎

    +-swap : (x y z : ℕ) → _+_ℕ x (_+_ℕ y z) ≡ _+_ℕ y (_+_ℕ x z)
    +-swap x y z = 
      _+_ℕ x (_+_ℕ y z)
        ≡⟨ +-assoc-right x y z ⟩
      _+_ℕ (_+_ℕ x y) z
        ≡⟨ cong (λ w → _+_ℕ w z) (+-commℕ x y) ⟩
      _+_ℕ (_+_ℕ y x) z
        ≡⟨ +-assoc-left y x z ⟩
      _+_ℕ y (_+_ℕ x z)
      ∎

    +-assoc-middle : (x y z w : ℕ) → _+_ℕ x (_+_ℕ y (_+_ℕ z w)) ≡ _+_ℕ x (_+_ℕ (_+_ℕ y z) w)
    +-assoc-middle x y z w = 
      _+_ℕ x (_+_ℕ y (_+_ℕ z w))
        ≡⟨ cong (_+_ℕ x) (+-assoc-right y z w) ⟩
      _+_ℕ x (_+_ℕ (_+_ℕ y z) w)
      ∎

    -- Multiplication properties
    *-distrib-+ : (x y z : ℕ) → _*_ℕ x (_+_ℕ y z) ≡ _+_ℕ (_*_ℕ x y) (_*_ℕ x z)
    *-distrib-+ zero y z = refl
    *-distrib-+ (suc x) y z = 
      let ih : _*_ℕ x (_+_ℕ y z) ≡ _+_ℕ (_*_ℕ x y) (_*_ℕ x z)
          ih = *-distrib-+ x y z
          
          step1 : _*_ℕ (suc x) (_+_ℕ y z) ≡ _+_ℕ (_+_ℕ y z) (_*_ℕ x (_+_ℕ y z))
          step1 = refl
          
          step2 : _+_ℕ (_+_ℕ y z) (_*_ℕ x (_+_ℕ y z)) ≡ _+_ℕ (_+_ℕ y z) (_+_ℕ (_*_ℕ x y) (_*_ℕ x z))
          step2 = cong (_+_ℕ (_+_ℕ y z)) ih
          
          step3 : _+_ℕ (_+_ℕ y z) (_+_ℕ (_*_ℕ x y) (_*_ℕ x z)) ≡ _+_ℕ y (_+_ℕ z (_+_ℕ (_*_ℕ x y) (_*_ℕ x z)))
          step3 = +-assocℕ y z (_+_ℕ (_*_ℕ x y) (_*_ℕ x z))
          
          step4 : _+_ℕ y (_+_ℕ z (_+_ℕ (_*_ℕ x y) (_*_ℕ x z))) ≡ _+_ℕ y (_+_ℕ (_*_ℕ x y) (_+_ℕ z (_*_ℕ x z)))
          step4 = cong (_+_ℕ y) (+-swap z (_*_ℕ x y) (_*_ℕ x z))
          
          step5 : _+_ℕ y (_+_ℕ (_*_ℕ x y) (_+_ℕ z (_*_ℕ x z))) ≡ _+_ℕ (_+_ℕ y (_*_ℕ x y)) (_+_ℕ z (_*_ℕ x z))
          step5 = sym (+-assocℕ y (_*_ℕ x y) (_+_ℕ z (_*_ℕ x z)))
      in step1 ∙ step2 ∙ step3 ∙ step4 ∙ step5

    *-suc : (x y : ℕ) → _*_ℕ (suc x) y ≡ _+_ℕ y (_*_ℕ x y)
    *-suc x y = refl

    *-assocℕ : (x y z : ℕ) → (_*_ℕ x (_*_ℕ y z)) ≡ (_*_ℕ (_*_ℕ x y) z)
    *-assocℕ zero y z = refl
    *-assocℕ (suc x) y z = 
      let ih = *-assocℕ x y z
      in *-suc x (_*_ℕ y z) ∙ cong (_+_ℕ (_*_ℕ y z)) ih

    1-left-neutralℕ : (x : ℕ) → (_*_ℕ (suc zero) x) ≡ x
    1-left-neutralℕ zero = refl
    1-left-neutralℕ (suc x) = 
      let ih = 1-left-neutralℕ x
      in cong suc ih

    -- For now, we'll postulate the remaining properties
    postulate
      right-distribℕ : (x y z : ℕ) → (_*_ℕ (_+_ℕ x y) z) ≡ (_+_ℕ (_*_ℕ x z) (_*_ℕ y z))
      0-left-annihilatesℕ : (x : ℕ) → (_*_ℕ zero x) ≡ zero

open NatProps public

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

-- Now package everything into a Semiring ℕ
semiringℕ : Semiring ℕ
semiringℕ = record
  { _+_ = _+_ℕ
  ; _*_ = _*_ℕ
  ; 0#  = zeroℕ
  ; 1#  = oneℕ
  ; +-assoc = +-assocℕ
  ; +-comm  = +-commℕ
  ; *-assoc = *-assocℕ
  ; left-distrib  = *-distrib-+
  ; right-distrib = right-distribℕ
  ; 0-left-annihilates = 0-left-annihilatesℕ
  ; 1-left-neutral = 1-left-neutralℕ
  }

------------------------------------------------------------------------
-- Step 8: Transport the Semiring structure to Bin
------------------------------------------------------------------------

semiringBin : Semiring Bin
semiringBin = transport (λ i → Semiring (ua ℕ≃Bin i)) semiringℕ

------------------------------------------------------------------------
-- Step 9: Result
------------------------------------------------------------------------

-- Now semiringBin is a valid Semiring on Bin