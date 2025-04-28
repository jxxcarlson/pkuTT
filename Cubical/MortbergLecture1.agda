{-# OPTIONS --cubical #-}

module Cubical.MortbergLecture1 where

open import Cubical.Foundations.Prelude hiding (refl; funExt; sym)
open import Cubical.Data.Bool

variable
    ℓ : Level
    A B : Set ℓ

apply0 : (A : Set) → (p : I → A) → A 
apply0  A p = p i0

apply1 : (A : Set) → (p : I → A) → A 
apply1  A p = p i1

ex1 : Bool
ex1 = apply0 Bool (λ i → true)

-- A non-constant path from true to false
nonConstPath : I → Bool
nonConstPath i = transp (λ j → Bool) i true

-- Example using the non-constant path
ex2 : Bool
ex2 = apply0 Bool nonConstPath  -- This will be true

ex3 : Bool
ex3 = apply1 Bool nonConstPath  -- This will be false



myPath : { A : Set } (x : A) → x ≡ x
myPath x = λ i → x

refl : { A : Set } { x : A } → x ≡ x
refl { x = x } = λ i → x

-- ap = cong in the library
ap : (f : A → B) { x y : A } → x ≡ y → f x ≡ f y
ap f p i = f (p i)

--funExt (function extensionality) from scratch
funExt : { f g : A → B } → (p : (x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

sym : { x y : A } → x ≡ y → y ≡ x
sym p i = p (~ i)

-- A simple path from true to true
truePath : true ≡ true
truePath = λ i → true

-- Path concatenation example
-- Concatenating a path with its symmetric path
pathConcatExample : true ≡ true
pathConcatExample = truePath ∙ sym truePath

-- This creates a path that goes from true to true by going through true and back










 