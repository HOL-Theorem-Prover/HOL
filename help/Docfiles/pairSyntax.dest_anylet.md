## `dest_anylet`

``` hol4
pairSyntax.dest_anylet : term -> (term * term) list * term
```

------------------------------------------------------------------------

Destructs arbitrary `let` terms.

The invocation `dest_anylet M` where `M` has the form of a
let-abstraction, i.e., `LET P Q`, returns a pair
`([(a1,b1),...,(an,bn)],body)`, where the first argument is a list of
bindings, and the second is the body of the let. The list of bindings is
required since let terms can, in general, be of the form (using surface
syntax) `let a1 = b1 and ... and an = bn in body`.

Each `ai` can be a varstruct (a single variable or a tuple of
variables), or a function variable applied to a sequence of varstructs.

### Failure

Fails if `M` is not a let abstraction.

### Example

``` hol4
- dest_anylet ``let f (x,y) = M and g z = N in g (f (a,b))``;
> val it = ([(`f (x,y)`, `M`), (`g z`, `N`)], `g (f (a,b))`) :

- dest_anylet ``let f (x,y) = M in
                let g z = N
                in g (f (a,b))``;
> val it = ([(`f (x,y)`, `M`)], `let g z = N in g (f (a,b))`)
```

Programming that involves manipulation of term syntax.

### See also

[`boolSyntax.dest_let`](#boolSyntax.dest_let),
[`pairSyntax.mk_anylet`](#pairSyntax.mk_anylet),
[`pairSyntax.list_mk_anylet`](#pairSyntax.list_mk_anylet),
[`pairSyntax.strip_anylet`](#pairSyntax.strip_anylet)
