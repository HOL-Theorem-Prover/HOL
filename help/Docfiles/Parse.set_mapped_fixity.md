## `set_mapped_fixity`

``` hol4
Parse.set_mapped_fixity :
  {tok : string, term_name : string, fixity : fixity} -> unit
```

------------------------------------------------------------------------

Allows the fixity of tokens to be updated.

The `set_mapped_fixity` function is used to change the fixity of a
single token, simultaneously mapping forms using that token name to a
different name. Apart from the additional `term_name` field, the
behaviour is similar to that of `set_fixity`.

### Failure

This function fails if the new fixity causes a clash with existing
rules, as happens if the precedence level of the specified fixity is
already taken by rules using a fixity of a different type. Even if the
application of `set_mapped_fixity` succeeds, it may cause the next
subsequent application of the `Term` parsing function to complain about
precedence conflicts in the operator precedence matrix. These problems
may cause the parser to behave oddly on terms involving the token whose
fixity was set. Excessive parentheses will usually cure even these
problems.

### Comments

This function is of no use if multiple-token rules (such as those for
conditional expressions) are desired.

As with other functions in the `Parse` structure, there is a companion
`temp_set_mapped_fixity` function, which has the same effect on the
global grammar, but which does not cause this effect to persist when the
current theory is exported.

### See also

[`Parse.add_rule`](#Parse.add_rule),
[`Parse.set_fixity`](#Parse.set_fixity)
