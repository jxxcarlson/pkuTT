module Axiom.Stuck where

open import Data.Nat

inc : ℕ → ℕ
inc n = n + 1

double : ℕ → ℕ
double n = n + n

postulate
    foo : ℕ → ℕ


-- Try normalizing the following terms (c-C, c-N).  Some will fully
evaluate, others are "stuck."

t0 : ℕ
t0 = inc 0

t1 : ℕ
t1 = foo (inc 0)

t2 : ℕ
t2 = double 3

t3 : ℕ
t3 = foo (double 3)

t4 : ℕ
t4 = double (foo 3)



 