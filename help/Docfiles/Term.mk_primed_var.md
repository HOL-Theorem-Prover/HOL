## `mk_primed_var`

``` hol4
Term.mk_primed_var : string * hol_type -> term
```

------------------------------------------------------------------------

Primes a variable name sufficiently to make it distinct from all
constants.

When applied to a record made from a string `v` and a type `ty`, the
function `mk_primed_var` constructs a variable whose name consists of
`v` followed by however many primes are necessary to make it distinct
from any constants in the current theory.

### Failure

Never fails.

### Example

``` hol4
- new_theory "wombat";
> val it = () : unit

- mk_primed_var("x", bool);
> val it = “x” : term

- new_constant("x", alpha);
> val it = () : unit

- mk_primed_var("x", bool);
> val it = “x'” : term
```

### See also

[`Term.genvar`](#Term.genvar), [`Term.variant`](#Term.variant)
