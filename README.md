# Introduction

Annotated list of Agda programs, all which sucessfully type-check using Agda version 2.8.0-47e7dcb.

# Postulate.agda

We can work with postulated functions, but computation with them may be "stuck."

# Sets and related matters

## K

Use `{-# OPTIONS --without-K -#}` to disable K, then
postulate K and give a proof of UIP.

## Hedberg

A proof of Hedberg's theorem: a type which satisfies decidable
equality also satisfies uniqueness of identity proofs

## HedbergBad

A demonstration of the fact that the function `normalize` fails
to compile outside of the context of decidable equality.

## HedbergNat, HedbergBool, HedbergBool

Proof that the type of natural numbers and the type booleans
of booleans satisfy UIP.  Same for the unit type.  All these
refer to Hedberg.agda

## DecideableEqualityBool, DecideableEqualtyNat

Show that Bool and the natural numbers satisfy Dec Bool, Dec N.


