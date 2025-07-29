## `list_mk_anylet`

``` hol4
pairSyntax.list_mk_anylet : (term * term) list list * term -> term
```

------------------------------------------------------------------------

Construct arbitrary `let` terms.

The invocation
`list_mk_anylet ([[(a1,b1),...,(an,bn)], ... [(u1,v1),...,(uk,vk)]],body)`
returns a term with surface syntax

``` hol4
let a1 = b1 and ... an = bn in
   ...                      in
let u1 = v1 and ... and uk = vk
 in body
```

### Failure

If any binding pair `(x,y)` is such that `x` and `y` have different
types.

### Example

``` hol4
list_mk_anylet
  ([[(``x:'a``, ``P:'a``)],
    [(``(y:'a, z:ind)``, ``M:'a#ind``)],
    [(``f (x:'a):bool``, ``N:bool``),
     (``g:bool->'a``,    ``K (v:'a):bool->'a``)]], ``g (f (x:'a):bool):'a``);
> val it = `let x = P in
            let (y,z) = M in
            let f x = N
            and g = K v
            in g (f x)`
```

Programming that involves manipulation of term syntax.

### See also

[`boolSyntax.dest_let`](#boolSyntax.dest_let),
[`pairSyntax.mk_anylet`](#pairSyntax.mk_anylet),
[`pairSyntax.strip_anylet`](#pairSyntax.strip_anylet),
[`pairSyntax.dest_anylet`](#pairSyntax.dest_anylet)
