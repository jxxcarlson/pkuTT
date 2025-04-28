{-# OPTIONS --cubical #-}

-- /Users/carlson/dev/agda/cubical/Cubical/Foundations/Prelude.agda

module Cubical.Basic where


open import Cubical.Foundations.Prelude hiding (funExt)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Relation.Binary.PropositionalEquality hiding(_≡_; refl; cong)
open import Data.Bool hiding(not)
open import Data.Empty
open import Relation.Nullary

variable 
    A B : Set

-- A path from a to b in A
pathExample : (A : Set) → (a b : A) → Path A a b → A
pathExample A a b p = p i0  -- evaluates to `a`

-- The identity path, i.e. the constantpath from a to a
pathId : ∀ {A : Set} (a : A) → Path A a a
pathId a i = a

-- Function extensionality is a library function,
-- but we can hide it and implement it ourselves:
funExt : ∀ {A B : Set} (f g : A → B) →
         (∀ x → Path B (f x) (g x)) →
         Path (A → B) f g
funExt f g p i x = p x i


-- The univalence axiom is provable (defined in Cubical.Foundations.Univalence)
univalenceExample :
  ∀ {A B : Set} → (e : A ≃ B) → Path (Set) A B
univalenceExample = ua

-- The not equivalence on Bool
notEquiv : Bool ≃ Bool
notEquiv = isoToEquiv (iso not not not-involutive not-involutive)
  where
    not : Bool → Bool
    not true = false
    not false = true
    
    not-involutive : (b : Bool) → not (not b) ≡ b
    not-involutive true = refl
    not-involutive false = refl

-- Two different paths between Bool and itself
path1 : Path (Set) Bool Bool
path1 = refl

path2 : Path (Set) Bool Bool
path2 = ua notEquiv

-- Proof that Set is not a set (see HoTT book page 142)
Set-is-not-set : ¬ (∀ (A B : Set) (p q : Path (Set) A B) → p ≡ q)
Set-is-not-set isSet = false≢true (transport-path-eq path-eq)
  where
    -- Extract the value at i0 from a path in Set
    f : Path (Set) Bool Bool → Bool
    f p = transport (λ i → p i) true
    
    -- If path1 ≡ path2, then their transported values must be equal
    path-eq : path1 ≡ path2
    path-eq = isSet Bool Bool path1 path2
    
    -- Helper function to get the path between transported values
    transport-path-eq : path1 ≡ path2 → Path Bool (transport (λ i → path1 i) true) (transport (λ i → path2 i) true)
    transport-path-eq p i = transport (λ j → p i j) true
    
    -- But path1 transports true to true, while path2 transports true to false
    false≢true : Path Bool true false → ⊥
    false≢true p = transport (λ i → if p i then Bool else ⊥) false



-- HITs Set-is-not-set

open import Cubical.HITs.S1

-- base : S¹
-- loop : PathP (λ _ → S¹) base base

loopTwice : Path S¹ base base
loopTwice = loop ∙ loop