## `dest_strip_comb`

``` hol4
boolSyntax.dest_strip_comb : term -> string * term list
```

------------------------------------------------------------------------

Strips a function application, and breaks head constant.

If `t` is a term of the form `c t1 t2 .. tn`, with `c` a constant, then
a call to `dest_strip_comb t` returns a pair `(s,[t1,...,tn])`, where
`s` is a string of the form `thy$name`. The `thy` prefix identifies the
theory where the constant was defined, and the `name` suffix is the
constant's name.

### Failure

Fails if the term is not a constant applied to zero or more arguments.

### Example

``` hol4
> dest_strip_comb ``SUC 2``;
val it = ("num$SUC", [``2``]) : string * term list
```

### Comments

Useful for pattern-matching at the ML level, where doing a `case` on
`Lib.total dest_strip_comb t` allows patterns of interest to be
idiomatically identified. In the absence of view-patterns in SML, one
has to use custom destructors.

### See also

[`HolKernel.dest_term`](#HolKernel.dest_term)
