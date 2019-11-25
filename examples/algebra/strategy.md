# Strategy for Algebraic Package

This is a document explaining how the algebraic types inter-relate, and the way in which we expect to reason about them.  This is with particular reference to HOL’s simplification and rewriting.

## Algebraic Structures

### Types

Strictly, there are only two types: monoids and rings.  An `α monoid` is

      <| carrier : α set;
         op      : α → α → α;
         id      : α |>

An `α ring` is

      <| carrier : α set;
         sum     : α monoid;
         prod    : α monoid |>

All “algebraic types” are identified as subsets of the above, with predicates constraining the structures.

### Predicates

Predicates are used to describe algebraic types with various conditions on the components.

An `α monoid` structure is denoted by a generic symbol `g`, with these predicates:

* `Monoid g` with closure for a binary operation, with associativity and an identity.
* `Group g` is a `Monoid g` with all elements invertible.

An `α ring` structure is denoted by a generic symbol `r`, with these predicates:

* `Ring r` consists of an Abelian Group `r.sum` and an Abelian Monoid `r.prod`, both sharing the same carrier as the Ring.
* `IntegralDomain r` is a non-trivial `Ring r` with no zero divisors.
* `Field r` is a `Ring r` with the Abelian Monoid being a Group when the additive identity is excluded.

### Notions

#### Basic

We use overloading in HOL to simplify the description of algebraic structures, so that parameters like `g` or `r` are implicit.

For an `α monoid` type structure `g`:

* The carrier set `g.carrier` is denoted by `G`, *e.g.* element `x` ∈ `G`.
* The binary operation `g.op` is denoted by `*`, and the identity `g.id` is denoted by `#e`.

A *trivial* monoid has only one element: `#e`.

For an `α ring` type structure `r`:

* The carrier set `r.carrier` is denoted by `R`, *e.g.* element `x` ∈ `R`.
* The additive group `r.sum` has binary operation `r.sum.op` denoted by `+`, its identity `r.sum.id` denoted by `#0`.
* The multiplicative monoid `r.prod` has binary operation `r.prod.op` denoted by `*`, its identity `r.prod.id` denoted by `#1`.

A *trivial* ring has only one element: `#0 = #1`.

A *non-trivial* ring has `#0 ≠ #1`. A ring has *no zero divisors* if for all `x ≠ #0` and `y ≠ #0` with `x * y ≠ #0`.

#### Exponents

For `α monoid` structures, we define exponentiation to be a repetition of the monoid operation `g.op`, or `*`, and write this as `x ** n`, for element `x` and natural number `n`. This exponentiation is also parsed as a record field, `g.exp`.

This parsing of exponentiation is extended to `α ring` structures:

* `r.sum.exp` is the iteration of `r.sum.op`, or `+`, and write `##`*n* to be `r.sum.exp #1` *n*.
* `r.prod.exp` is the iteration of `r.prod.op`, or `*`, and write `x **`*n* to be `r.prod.exp x` *n*.

Thus in `α ring` structures, `##0 = #0` and `##1 = #1`.

#### Inverses

For an `α monoid` structure `g`, an *invertible* element is one that has an inverse. The set of all invertibles elements is a subset of `G`, denoted by `G*`. For a `Group g`, `G* = G` by definition.

The inverse of an invertible element has its existence asserted as an axiom, and then Skolemisation is used to derive HOL functions corresponding to the inverse. The parser is also extended so that record field selection can be used to access these function, so, *e.g.* for an element `x` we can write its inverse as `g.inv x`, or abbreviated as `x ⁻¹` in unicode, or `|/ x` (resembles `1/x`) in non-unicode code.

These ideas are extended to an `α ring` structure `r`:

* the set of nonzero elements in `R` is denoted by `R+`.
* the set of multiplicative *invertible* elements in `R` (called *units*), is denoted by R*, a subset of `R+`.
* the additive inverse `r.sum.inv x` is denoted by `- x`
* the multiplicative inverse `r.prod.inv x` is denoted by `|/ x`.

A `Field r` is equivalent to a `Ring r` with `<G,+>` and `<G*,*>` both Abelian groups, and the distribution law holds.

## Polynomials

### Representation

Polynomials are represented as a list of coefficients taken from an `α ring` structure, with constant term first and leading term last. 

For example, x^3 - 2x + 3  treated as a polynomial from the ring `Z 7` is represented internally as:

    [3;5;0;1]     for 3 + 5x + 0x^2 + x^3,   as 5 = -2 (mod 7).
    
Note that all coefficients are elements in the `α ring` structure, and all terms up to the leading term are explicit.

### Type

The polynomial type `α poly` is just a synonym for `α list`.

### Notions

The empty list `[]` represents a polynomial with no coefficients, the *zero polynomial*. This will eventually be identified with `|0|`, the additiive identity for polynomials.

The list `[#1]` represents the *unit polynomial* `1`, a constant. In a *non-trivial* Ring (with #1 distinct from #0), this will eventually be identified with `|1|`, the multiplicative identity for polynomials.

Since the generic symbol for an `α ring` structure is `r`, we avoid using `r` for polynomials. Instead, we shall use `p`, `q`, `s`, `t` for polynomials, *i.e.* elements of type `α poly`.

### Normalisation

All polynomials are **normalized**, *i.e.* the leading coefficient is nonzero.

This is trivially true for `[]`, but `[#1]` is normalized if the coefficients are from a `Ring r` that is *non-trivial*, where `#1 ≠ #0` (*e.g.* a `Field r`).

Therefore, elements of type `α poly` are generally *not* normalized, called ``weak polynomials``. The normalization operator to convert a weak one to a normalized one is `chop`, which removes all leading zero coefficients, *e.g.* `chop [#0] = |0|. Therefore `chop p` is always a normalized polynomial for any `p:α poly`.

Note that the *trivial* Ring has only one element: `#1 = #0`. Thus `chop [#1] = |0|`, and the only polynomial from such a ring is `|0|`.

Of course, for *non-trivial* Rings, (e.g. a `Field r`), `chop [#1] = |1|`.

Although weak polynomials are implemented in HOL, they are supposed to be internal. We shall briefly say that `(p || q)` and `(p o q)` denote addition and multiplication for weak polynomials. Their full documentation is included in the implementation scripts. 

This document hereafter will describe polynomials that are *normalized* -- they form interesting algebraic structures.

### Polynomial Rings

The primary aim of the polynomial package in HOL is to establish the following:

* **R[x]**, the polynomials with coefficients from `Ring r`, is itself a Ring.
* **F[x]**, the polynomials with coefficients from `Field r`, is not only a Ring, but also an Integral Domain.

With this in mind, the polynomials are embedded in an `α poly ring` structure:

    val ring_of_poly_def = Define`
        ring_of_poly (r:'a ring):α poly ring =
            <| carrier := { p:α poly | poly p };
                   sum := <| carrier := { p:α poly | poly p };
                                  op := (\p q. chop (p || q));
                                  id := []
                           |>;
                  prod := <| carrier := { p:α poly | poly p };
                                  op := (\p q. chop (p o q));
                                  id := chop [#1]
                           |>       
             |>
    `;

We shall use HOL overloading to simplify the description of operations on polynomials, starting with:

* `|0|` to denote `(ring_of_poly r).sum.id`,
* `|1|` to denote `(ring_of_poly r).prod.id`.

### Operations

The sum of two polynomials `p + q` will actually expand to

      (ring_of_poly r).sum.op p q

The negation of a polynomial `-p` will expand to:

      (ring_of_poly r).sum.inv p

The subtraction of two polynomials `p - q`, defined as `p + (-q)`, will expand to:

      (ring_of_poly r).sum.op p ((ring_of_poly r).sum.inv q)

The product of two polynomials `p * q` will expand to:

      (ring_of_poly r).prod.op p q

Similar to the inverse for invertible elements of Monoid, the *quotient* and *remainder* of polynomial division are Skolemisation functions derived from a proof of their existence:

* `poly_div r` is the quotient function, denoted by `/`, an infix operator.
* `poly_mod r` is the remainder function, denoted by `%`, an infix operator.

Thus the Division Algorithm for two polynomials `p` and `q`, with `q <> |0|`, is:

      p = (p / q) * q + (p % q)
      
which underneath is:

      p = (ring_of_poly r).sum.op ((ring_of_poly r).prod.op (poly_div r p q) q) (poly_mod r p q)
      
The additive identity, denoted by `|0|`, is actually

      (ring_of_poly r).sum.id

which is shown by definition to be the same as zero polynomial `[]`.

The multiplicative identity, denoted by `|1|`, is actually

      (ring_of_poly r).prod.id

which is shown by definition to be the same as normalized unit polynomial `chop [#1]`.

In order to be able to apply the standard monoid rewrite

      Monoid g ∧ x ∈ G ⇒ g.op x g.id = x

we will have to keep `|0|` in that form.  Then,

      p + |0|

can be successfully rewritten (assuming `Poly p`) because that term will actually be

      (ring_of_poly r).sum.op p (ring_of_poly r).sum.id

which matches the LHS of the rewrite above, as long as `(ring_of_poly r).sum` can be shown to be a `Monoid`, which will follow because `ring_of_poly r` is a ring, and we will have that

      Ring r ⇒ Monoid r.sum

With division, we might have assumptions

      Field r
      Poly r p
      Poly r q
      Poly r t

and a term in the goal looking like `p + q / t` which would really expand to

      (ring_of_poly r).sum.op p (poly_div r q t)
