## `allowed_term_constant`

``` hol4
Lexis.allowed_term_constant : string -> bool
```

------------------------------------------------------------------------

Tests if a string has a permissible name for a term constant.

When applied to a string, `allowed_term_constant` returns `true` if the
string is a permissible constant name for a term, that is, if it is an
identifier (see the DESCRIPTION for more details), and `false`
otherwise.

### Failure

Never fails.

### Example

The following gives a sample of some allowed and disallowed constant
names:

``` hol4
   - map Lexis.allowed_term_constant ["pi", "@", "a name", "+++++", "10"];
   > val it = [true, true, false, true, false] : bool list
```

### Comments

Note that this function only performs a lexical test; it does not check
whether there is already a constant of that name in the current theory.

### See also

[`Theory.constants`](#Theory.constants),
[`Lexis.allowed_type_constant`](#Lexis.allowed_type_constant)
