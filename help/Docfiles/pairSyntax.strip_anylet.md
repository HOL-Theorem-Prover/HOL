## `strip_anylet`

``` hol4
pairSyntax.strip_anylet : term -> (term * term) list list * term
```

------------------------------------------------------------------------

Repeatedly destructs arbitrary `let` terms.

The invocation `strip_anylet M` where `M` has the form of a
let-abstraction, i.e., `LET P Q`, returns a pair
`([[(a1,b1),...,(an,bn)], ... [(u1,v1),...,(uk,vk)]],body)`, where the
first element of the pair is a list of lists of bindings, and the second
is the body of the let. The binding lists are required since let terms
can, in general, be of the form (using surface syntax)
`let a1 = b1 and ... and an = bn in body`.

### Failure

Never fails.

### Example

``` hol4
- strip_anylet ``let g x = A in
                 let v = g x y in
                 let f x y (a,b) = g a
                 and foo = M
                 in
                  f x foo v``;
> val it =
    ([[(`g x`, `A`)],
      [(`v`, `g x y`)],
      [(`f x y (a,b)`, `g a`), (`foo`, `M`)]], `f x foo v`)
```

Programming that involves manipulation of term syntax.

### See also

[`boolSyntax.dest_let`](#boolSyntax.dest_let),
[`pairSyntax.mk_anylet`](#pairSyntax.mk_anylet),
[`pairSyntax.list_mk_anylet`](#pairSyntax.list_mk_anylet),
[`pairSyntax.dest_anylet`](#pairSyntax.dest_anylet)
