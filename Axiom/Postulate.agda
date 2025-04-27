module Postulate where

open import Data.Nat

foo : ℕ → ℕ
foo n = suc n

postulate
    bar : ℕ → ℕ

foobar : ℕ → ℕ
foobar n = foo (bar n)

barfoo : ℕ → ℕ
barfoo n = bar (foo n)

 
