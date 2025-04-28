# Introduction



- Annotated list of Agda programs, all which sucessfully type-check using Agda version 2.8.0-47e7dcb.

# PDF Files

## hoffman-streicher-sketch.pdf

Sketch of Hoffman-Strieicher's construction of a groupoid model for MLTT proving independence of UIP and Univalence relative to MILTT.

# Agda Files

## Cubical

- Basic: 
- PlusIdentityRight: show that n + 0 = n for all n : N

## UA

- EvenTransport: transports `even : ℕ → Bool` using univalence
and the equivalence `ℕ≃Bin` to produce a function `evenBin : Bin → Bool`.  The functions `encode-decode` and `decode-encode` which show that the `encode`-`decode` pair form an equivalence for `ℕ` and `Bin` are postulated but could be proved. Normaling `testThree` and `testFour` yields the expected values `false` and `true`.
- EvenTransportNonCubical does the same work but does not use cubical, instead postulating univalence.  As a result, normalizing `testThree` and `testFour` produce normal but (uninformative) non-canonical forms.


## Postulate

### Stuck.agda

Examples of stuck computations for N.

### UAStuckExampleFixed.agda

Using ua (univalence) to transport a Boolean value along a path fails to compute.



# Agda Files



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


