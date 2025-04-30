# Introduction



- Annotated list of Agda programs, all which sucessfully type-check using Agda version 2.8.0-47e7dcb.  Many composed with AI assistance (ChatGPT, Claude 3.7 Sonnet)

# PDF Files

## hoffman-streicher-sketch.pdf

Sketch of Hoffman-Strieicher's construction of a groupoid model for MLTT proving independence of UIP and Univalence relative to MILTT.

# Agda Files

## Axiom

- Stuck: 
- UAStuck:

## Cubical

- Basic: `Set-is-not-set` shows that the universe `Set` is not a set.
- PlusIdentityRight: show that n + 0 = n for all n : N
- FunExt

## HIT

- CirclePi1EqZ1: construct `winding : ΩS¹ → ℤ` and `loopZ : ℤ → ΩS¹`
- CirclePi1EqZ2: show that `winding : ΩS¹ → ℤ` and `loopZ : ℤ → ΩS¹` are mutually inverse, then show that `π₁S¹≡ℤ : ΩS¹ ≡ ℤ`

## UA

- *EvenTransport*: transports `even : ℕ → Bool` using univalence
and the equivalence `ℕ≃Bin` to produce a function `evenBin : Bin → Bool`.  The functions `encode-decode` and `decode-encode` which show that the `encode`-`decode` pair form an equivalence for `ℕ` and `Bin` are postulated but could be proved. Normaling `testThree` and `testFour` yields the expected values `false` and `true`.
- *EvenTransportNonCubical* does the same work but does not use cubical, instead postulating univalence.  As a result, normalizing `testThree` and `testFour` produce normal but (uninformative) non-canonical forms.
- *SemiRingTransport*: `ℕ` is a semiring, meaning





### CubicalBasics.agda

- Examples of paths
- Define funext from scratch
- Show that the universe of small types is not a Set

## Sets and related matters

### K

Use `{-# OPTIONS --without-K -#}` to disable K, then
postulate K and give a proof of UIP.

### Hedberg

A proof of Hedberg's theorem: a type which satisfies decidable
equality also satisfies uniqueness of identity proofs

### HedbergBad

A demonstration of the fact that the function `normalize` fails
to compile outside of the context of decidable equality.

### HedbergNat, HedbergBool, HedbergBool

Proof that the type of natural numbers and the type booleans
of booleans satisfy UIP.  Same for the unit type.  All these
refer to Hedberg.agda

### DecideableEqualityBool, DecideableEqualtyNat

Show that Bool and the natural numbers satisfy Dec Bool, Dec N.


