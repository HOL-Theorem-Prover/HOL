
# Abstract Algebra

These theories of abstract algebra form a useful collection of libraries,
to support in particular the mechanisation of AKS algorithm.

## Helper Theories
* __lib__ is the extension of existing HOL libraries.
    * `lib/helperNum`, more theorems on `arithmeticTheory`, `dividesTheory`, and `gcdTheory`.
    * `lib/helperSet`, more theorems about sets and mappings, extends `pred_setTheory`.
    * `lib/helperList`, more theorems about list manipulations, extends `listTheory`.
    * `lib/helperFunction`, theorems on function equivalence.
    * `lib/binomial`, properties of Pascal's triangle, for binomial coefficients.
    * `lib/triangle`, properties of Leibniz's Denominator triangle, for consecutive LCM.
    * `lib/Euler`, properties of number-theoretic sets, and Euler's φ function.
    * `lib/Gauss`, more theorems about coprimes, &phi; function, and Gauss' Little Theorem.
    * `lib/primes`, properties of two-factors, and a primality test.
    * `lib/primePower`, properties of prime powers and divisors, study for consecutive LCM.
    * `lib/logPower`, properties of perfect power, power free, and upper logarithm.
    * `lib/sublist`, order-preserving sublist and properties.

## Basic Theories
* __monoid__ is an algebraic structure with a useful binary operation.
    * `monoid/monoid`, properties of a monoid with identity.
    * `monoid/monoidInstances`, examples of monoids, in particular modulo numbers.
    * `monoid/monoidOrder`, order of element in a monoid and its properties.
    * `monoid/monoidMap`, homomorphism and isomorphism between monoids.
    * `monoid/submonoid`, properties of submonoids of a monoid.

* __group__ is a monoid with all its elements invertible.
    * `group/group`, properties of group, as an invertible monoid.
    * `group/groupInstances`, examples of groups, in particular prime modulo systems.
    * `group/groupOrder`, extends monoidOrder to groupOrder.
    * `group/groupCyclic`, theorems on cyclic group and generators.
    * `group/subgroup`, theorems on subgroups, including cosets.
    * `group/quotientGroup`, theorems of a group partitioned by a normal subgroup.
    * `group/groupMap`, homomorphism and isomorphism between groups.
    * `group/congruences`, application to number theory, mainly Fermat's Little Theorem.
    * `group/corres`, the Correspondence Theorem for group theory.
    * `group/finiteGroup`, properties of a finite group.
    * `group/groupAction`, action of a group on a target.

* __ring__ is an algebraic structure with two related binary operations.
    * `ring/ring`, properties of a ring, made up of a group and a monoid.
    * `ring/ringInstances`, examples of rings, in particular modulo arithmetic systems.
    * `ring/ringUnit`, properties of invertible elements in a ring (they form a group).
    * `ring/ringDivides`, theorems of division for invertible elements in a ring.
    * `ring/ringIdeal`, the concept of a well-behaved sub-structure, like the normal subgroup.
    * `ring/quotientRing`, theorems of a ring partitioned by an ideal.
    * `ring/ringMap`, homomorphism and isomorphism between rings.
    * `ring/ringInteger`, the similarity of the multiples of ring unity and the integers.
    * `ring/ringBinomial`, the binomial theorem in terms of ring integers.
    * `ring/integralDomain`, properties of integral domain, a non-trivial ring without zero divisors.
    * `ring/integralDomainInstances`, examples of integral domains, e.g. arithmetic in modulo prime.

* __field__ is a nontrivial ring with all nonzero elements invertible.
    * `field/field`, properties of a field, as an invertible (zero excluded) ring.
    * `field/fieldInstances`, examples of fields, mainly arithmetic in prime modulus.
    * `field/fieldIdeal`, extends the ringIdeal and quotientRing to fields.
    * `field/fieldBinomial`, extends the ring binomial theorem to fields.
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
