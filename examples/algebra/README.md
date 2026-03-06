
# Abstract Algebra

These theories of abstract algebra form a useful collection of libraries,
to support in particular the mechanisation of AKS algorithm.

This library is being re-structured,
see comments in pull requests [#1224](https://github.com/HOL-Theorem-Prover/HOL/pull/1224) and  [#1235](https://github.com/HOL-Theorem-Prover/HOL/pull/1235).

## Helper Theories
* __lib__ is the extension of existing HOL libraries.
    * Most scripts are now incorporated into HOL4 theories, the rest are moved to `src/algebra/base`.

## Basic Theories
* __monoid__ is an algebraic structure with a useful binary operation.
* __group__ is a monoid with all its elements invertible.
* __ring__ is an algebraic structure with two related binary operations.
    * These theories have been relocated to `src/algebra/construction`.
    * The `ring` theory here is a port from HOL-light, as a place-holder.

* __field__ is a nontrivial ring with all nonzero elements invertible.
    * `field/field`, properties of a field, as an invertible (zero excluded) ring.
    * `field/fieldInstances`, examples of fields, mainly arithmetic in prime modulus.
    * `field/fieldIdeal`, extends the ringIdeal and quotientRing to fields.
    * `field/fieldBinomial`, extends the ring binomial theorem to fields.
    * `field/fieldUnit`, properties of nonzero elements in a field (all invertible).
    * `field/fieldOrder`, multiplicative order of elements in a field.
    * `field/fieldMap`, homomorphism and isomorphism between fields.
    * `field/fieldProduct`, product of a set of field elements.

* __polynomial__ is made up of coefficients taken from a ring or a field.
    * `polynomial/polyWeak`, properties of un-normalized polynomials.
    * `polynomial/polynomial`, properties of normalized polynomials.
    * `polynomial/polyRing`, theorems for polynomials with coefficients from a ring.
    * `polynomial/polyField`, theorems for polynomials with coefficients from a field.
    * `polynomial/polyDivision`, theorems for polynomial division in general.
    * `polynomial/polyFieldDivision`, theorems for field polynomial division.
    * `polynomial/polyRingModulo`, theorems for ring polynomial division remainders.
    * `polynomial/polyFieldModulo`, theorems for field polynomial division remainders.
    * `polynomial/polyRoot`, properties of polynomial roots and factors.
    * `polynomial/polyMonic`, properties of monic polynomials.
    * `polynomial/polyEval`, polynomial evaluation, acting as a function.
    * `polynomial/polyBinomial`, binomial theorem for polynomials.
    * `polynomial/polyDivides`, divisibility of polynomials.
    * `polynomial/polyIrreducible`, properties of irreducible polynomials.
    * `polynomial/polyDerivative`,formal derivative for polynomials, symbolic term by term.
    * `polynomial/polyProduct`, product of polynomials, properties, evaluation, and divisibility.
    * `polynomial/polyCyclic`, properties of the quotient of (x^n - 1) by (x - 1).
    * `polynomial/polyGCD`, greatest common divisor of polynomials.
    * `polynomial/polyMultiplicity`, multiplicity of polynomial factors and roots.
    * `polynomial/polyMap`, maps between polynomials, under homomorphism or isomorphism of their coefficient rings or fields.

## Advanced Theories
* __linear__ is the study of linear spaces.
    * `linear/VectorSpace`, properties of vector space from its scalars and vectors.
    * `linear/SpanSpace`, represents elements by linear combination of basis vectors.
    * `linear/LinearIndep`, theorems for change of basis and linear independence.
    * `linear/FiniteVSpace`, dimension over subspace and linear independent basis.

* __finitefield__ has an intricate structural theory due to its finite nature.
    * `finitefield/ffBasic`, properties of the prime subfield of a finite field.
    * `finitefield/ffAdvanced`, extend a finite field by an irreducible polynomial.
    * `finitefield/ffInstances`, examples of finite field construction, e.g. GF<sub>4</sub>.
    * `finitefield/ffPoly`, subring polynomials, common polynomials, roots of subfield polynomials.
    * `finitefield/ffMaster`, master polynomials, relationship with irreducible polynomials of a subfield.
    * `finitefield/ffCyclo`, cyclotomic polynomials, the order of its roots.
    * `finitefield/ffUnity`, roots of unity and the number of elements of each field order.
    * `finitefield/ffMinimal`, minimal polynomials, its existence by linear independence, and its properties.
    * `finitefield/ffConjugate`, conjugates of field elements, their order and product of conjugate factors.
    * `finitefield/ffExist`, the classification of finite fields: existence and uniqueness.
    * `finitefield/ffExtend`, field extension by isomorphic subfield.
    * `finitefield/ffSplit`, splitting field of a field polynomial.
