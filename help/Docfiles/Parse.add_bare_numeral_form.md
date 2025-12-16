## `add_bare_numeral_form`

``` hol4
Parse.add_bare_numeral_form : (char * string option) -> unit
```

------------------------------------------------------------------------

Adds support for annotated numerals to the parser/pretty-printer.

The function `add_bare_numeral_form` allows the user to give special
meaning to strings of digits that are suffixed with single characters. A
call to this function with pair argument `(c, s)` adds `c` as a possible
suffix. Subsequently, if a sequence of digits is parsed, and it has the
character `c` directly after the digits, then the natural number
corresponding to these digits is made the argument of the "map function"
corresponding to `s`.

This map function is computed as follows: if the `s` option value is
`NONE`, then the function is considered to be the identity and never
really appears; the digits denote a natural number. If the value of `s`
is `SOME s'`, then the parser translates the string to an application of
`s'` to the natural number denoted by the digits.

### Failure

Fails if the suffix character is not a letter.

### Example

The following function, `binary_of`, defined with equations:

``` hol4
   val bthm =
     |- binary_of n = if n = 0 then 0
                      else n MOD 10 + 2 * binary_of (n DIV 10) : thm
```

can be used to convert numbers whose decimal notation is `x`, to numbers
whose binary notation is `x` (as long as `x` only involves zeroes and
ones).

The following call to `add_bare_numeral_form` then sets up a numeral
form that could be used by users wanting to deal with binary numbers:

``` hol4
   - add_bare_numeral_form(#"b", SOME "binary_of");
   > val it = () : unit

   - Term`1011b`;
   > val it = `1011b` : term

   - dest_comb it;
   > val it = (`binary_of`, `1011`) : term * term
```

### Comments

It is highly recommended that users avoid using suffixes that might be
interpreted as hexadecimal digits A to F, in either upper or lower case.
Further, HOL convention has it that suffix character should be lower
case.

If one has a range of values that are usefully indexed by natural
numbers, the function `add_bare_numeral_form` provides a syntactically
convenient way of reading and writing these values. If there are other
functions in the range type such that the mapping function is a
homomorphism from the natural numbers, then `add_numeral_form` could be
used, and the appropriate operators (`+`, `*` etc) overloaded.

### See also

[`Parse.add_numeral_form`](#Parse.add_numeral_form)
