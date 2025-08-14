## `dest_pselect`

``` hol4
pairSyntax.dest_pselect : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a paired choice-term into the selected pair and the body.

`dest_pselect` is a term destructor for paired choice terms. The
application of `dest_select` to `@pair. t` returns `(pair,t)`.

### Failure

Fails with `dest_pselect` if term is not a paired choice-term.

### See also

[`boolSyntax.dest_select`](#boolSyntax.dest_select),
[`pairSyntax.is_pselect`](#pairSyntax.is_pselect)
