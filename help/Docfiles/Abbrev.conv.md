## `conv`

``` hol4
Abbrev.conv = term -> thm
```

------------------------------------------------------------------------

The type of a function which finds an equal term and returns a theorem
stating the equality

If the function `c` is not only of the right type, but is actually what
we call a conversion, then `(c : conv) (t : term)` returns a theorem of
the form

``` hol4
   |- t = t'
```

If (roughly speaking) `t` is of the right form to be passed to `c`, but
`c` doesn't find a desired equal term `t'` then `c t` may raise the
exception `UNCHANGED` in preference to returning `|- t = t`, as it can
be dealt with more efficiently.

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED)
