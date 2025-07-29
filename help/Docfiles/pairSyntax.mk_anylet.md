## `mk_anylet`

``` hol4
pairSyntax.mk_anylet : (term * term) list * term -> term
```

------------------------------------------------------------------------

Constructs arbitrary `let` terms.

The invocation `mk_anylet ([(a1,b1),...,(an,bn)],N)` returns a term of
the form `` `LET P Q` ``, which will prettyprint as
`let a1 = b1 and ... and an = bn in N`. The internal representation is
equal to

``` hol4
    LET (...(LET (\an ...\a1. N) bn) ...) b1
```

Each `ai` can be a varstruct (a single variable or a tuple of
variables), or a function variable applied to a sequence of varstructs.
In the usual case, only a single binding is made, i.e.,
`mk_anylet ([(a,b)],N)`, and the result is equal to `LET (\a. N) b`.

### Failure

Fails if the type of any `ai` is not equal to the type of the
corresponding `bi`.

### Example

``` hol4
- strip_comb (mk_anylet ([(Term`x`, Term`M`)], Term`N x`));
> val it = (`LET`, [`\x. N x`, `M`]) : term * term list

- mk_anylet ([(``f (x:'a,y:'b):'c``, ``M:'c``), (``g (z:'c) :'d``, ``N:'d``)],
             ``g (f (a:'a,b:'b):'c):'d`);
> val it = ``let f (x,y) = M and g z = N in g (f (a,b))`` : term
```

Programming that involves manipulation of term syntax.

### See also

[`boolSyntax.mk_let`](#boolSyntax.mk_let),
[`boolSyntax.dest_let`](#boolSyntax.dest_let),
[`boolSyntax.is_let`](#boolSyntax.is_let),
[`pairSyntax.list_mk_anylet`](#pairSyntax.list_mk_anylet),
[`pairSyntax.dest_anylet`](#pairSyntax.dest_anylet)
