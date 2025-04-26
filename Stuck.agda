module Stuck where

open import Data.Nat

inc : ℕ → ℕ
inc n = n + 1

double : ℕ → ℕ
double n = n + n

postulate
    foo : ℕ → ℕ

t1 : ℕ
t1 = foo (inc 0)

t2 : ℕ
t2 = inc (foo 0)



