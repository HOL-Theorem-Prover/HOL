## `declare_ring`

``` hol4
ringLib.declare_ring :
  { Name : string, Theory : thm, Const : term->bool, Rewrites : thm list } ->
  { NormConv : conv, EqConv : conv,
    Reify : term list -> {Metamap : term, Poly : term list} }
```

------------------------------------------------------------------------

Simplification and conversion in an arbitrary ring or semi-ring theory.

Given a record gathering information about a ring structure,
`declare_ring` returns two conversions `NormConv` and `EqConv`. The
former does simplifications on any ring expression. Ring expressions are
HOL terms built on the ring operations and the constants (or values) of
that ring. Other subterms are abstracted and considered as variables.

The simplification of the expression (that can be seen as a polynomial)
consists in developing, reordering monomials and grouping terms of same
degree. `EqConv` solves an equality by simplifying both sides, and then
using reflexivity. This cannot exactly be achieved by applying
`NormConv` on both hand sides, since the variable ordering is not
necessarily the same for both sides, and then applying reflexivity may
not be enough.

The input structure contains various information about the ring: field
`Name` is a prefix that will be used when declaring new constants for
internal use of the conversions. `Theory` is a proof that a given
structure is a ring or a semi-ring. `Const` is a predicate on HOL terms
that defines the constants of the ring. `Rewrites` is a bunch of
rewrites that should allow to compute the ring operations and also
decide equality upon constants. If (Const c1) and (Const c2) then (c1 +
c2) and (c1 \* c2) should simplify to terms c and c' such that (Const c)
and (Const c'), and also (c1 = c2) should simplify to either T or F.

### Example

Assuming we have proved that the integers form a ring, and gathered all
required information in `int_ring_infos`, we can build the conversions
and simplify or solve symbolic equations on integers:

``` hol4
- val {EqConv=INT_RING_CONV, NormConv=INT_NORM_CONV,...} =
    ringLib.declare_ring int_ring_infos
> val INT_RING_CONV = fn : Term.term -> Thm.thm
  val INT_NORM_CONV = fn : Term.term -> Thm.thm
- INT_NORM_CONV “(a+b)*(a+b):int”;
> val it = |- (a + b) * (a + b) = a * a + (2 * (a * b) + b * b) : Thm.thm
- INT_RING_CONV “(a+b)*(a+b) = (b+a)*(b+a):int”;
> val it = |- ((a + b) * (a + b) = (b + a) * (b + a)) = T : Thm.thm
```

These conversions can also be used like reduceLib, but will evaluate
only sums, products and unary negation:

``` hol4
- INT_NORM_CONV “ ~(3 * (9 + ~7)) ”;
> val it = |- ~(3 * (9 + ~7)) = ~6 : Thm.thm
- INT_NORM_CONV “ ~(3 * (10 - 1 + ~7)) ”;
> val it = |- ~(3 * (10 - 1 + ~7)) = 21 + ~3 * (10 - 1) : Thm.thm
```

### Failure

If the Theory theorem is not of the form \|- is_ring r or \|-
is_semi_ring r or if Name is not allowed to start a constant identifier.

The returned conversions fail on terms that do not belong to the type of
the ring, but does not fail if no rewrite has been done.
