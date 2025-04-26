{-# OPTIONS --cubical #-}

module MortbergLecture1 where

open import Cubical.Foundations.Prelude hiding (refl; funExt)

variable
    ℓ : Level
    A B : Set ℓ

apply0 : (A : Set) → (p : I → A) → A 
apply0  A p = p i0

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






