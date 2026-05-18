MANIFEST
========

## `basics/`
    * defines the basic theory of nominal sets (principally, the notion of a
      permutation acting on a type).

    * establishes a type of lambda-calculus terms, including a notion of
      substitution.

    * provides some ML support for working in the nominal environment.

## `barendregt/`
    * mechanisation of chapter 2 from Hankin, and chapters 3 and (most of)
      11 from Barendregt's book.

    * mechanisation of chapter 8.3, 10, 11, 15.1 from Barendregt's book.

## `cl/`
    * abstraction elimination (aka bracket abstraction) in Combinatory Logic

## `fsub/`
    * System F with subtyping

## `other-models/`
    * lots of different models of the lambda-calculus. Most are related back to
      the term type in basics, and the notion of beta reduction that is defined
      in `barendregt/chap3Theory`.

## `typing/`
    * type systems for the  lambda calculus, focussing on simple type theory.

## `wcbv-reasonable/`
    * "The Weak Call-by-Value 𝜆-Calculus Is Reasonable for Both Time and Space"
      (translated from Coq formalisation by Zhuo Zhen)

## `cbpv-reasonable/`
    * "A Verified Cost Model for Call-By-Push-Value (𝜆-Calculus)" (by Zhuo Zhen et al.)
