## `pvariant`

``` hol4
PairRules.pvariant : (term list -> term -> term)
```

------------------------------------------------------------------------

Modifies variable and constant names in a paired structure to avoid
clashes.

When applied to a list of (possibly paired structures of) variables to
avoid clashing with, and a pair to modify, `pvariant` returns a variant
of the pair. That is, it changes the names of variables and constants in
the pair as intuitively as possible to make them distinct from any
variables in the list, or any (non-hidden) constants. This is normally
done by adding primes to the names.

The exact form of the altered names should not be relied on, except that
the original variables will be unmodified unless they are in the list to
avoid clashing with. Also note that if the same variable occurs more
that one in the pair, then each instance of the variable will be
modified in the same way.

### Failure

`pvariant l p` fails if any term in the list `l` is not a paired
structure of variables, or if `p` is not a paired structure of variables
and constants.

### Example

The following shows a case that exhibits most possible behaviours:

``` hol4
   - pvariant [Term `b:'a`, Term `(c:'a,c':'a)`]
              (Term `((a:'a,b:'a),(c:'a,b':'a,T,b:'a))`);
   val it = `(a,b''),c'',b',T',b''` : term
```

The function `pvariant` is extremely useful for complicated derived
rules which need to rename pairs variable to avoid free variable capture
while still making the role of the pair obvious to the user.

### See also

[`Term.variant`](#Term.variant), [`Term.genvar`](#Term.genvar)
