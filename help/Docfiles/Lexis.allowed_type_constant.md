## `allowed_type_constant`

``` hol4
Lexis.allowed_type_constant : string -> bool
```

------------------------------------------------------------------------

Tests if a string has a permissible name for a type constant.

When applied to a string, `allowed_type_constant` returns `true` if the
string is a permissible constant name for a type operator, and `false`
otherwise.

### Failure

Never fails.

### Example

The following gives a sample of some allowed and disallowed names for
type operators:

``` hol4
   - map Lexis.allowed_type_constant ["list", "'a", "fun", "->", "#", "fun2"];
   > val it = [true, false, true, false, false, true] : bool list
```

### Comments

Note that this function only performs a lexical test; it does not check
whether there is already a type operator of that name in the current
theory.

This function is not currently enforced by the system, as it was found
that more flexibilty in naming was preferable.

### See also

[`Lexis.allowed_term_constant`](#Lexis.allowed_term_constant)
