## `thytype_abbrev`

``` hol4
Parse.thytype_abbrev : {Name:string,Thy:string} * hol_type * bool -> unit
```

------------------------------------------------------------------------

Abbreviates a type to a specific theory-qualified name.

A call to `thytype_abbrev({Name=n,Thy=t}, ty, prp)` establishes the
"kernel" name `t$n` as an abbreviation for the type `ty`, as happens
with `type_abbrev`. The boolean flag `prp` indicates whether or not this
abbreviation will also be used when the printer comes to print the given
type. In other words, after the call it becomes possible to write
`“:args t$n”` to stand for type `ty`. If there are type variables in
`ty` they become the parameters to the new abbreviated type operator.
These parameters need to be filled in in the `args` position above. If
there are no type variables in `ty` then abbreviation is of a whole
type, and `args` must be blank.

If there was an existing abbreviation for `t$n`, then this will be
replaced by the call.

In addition, after the given call, this abbreviation will become the
preferred binding for the bare name `n`. Other abbreviations in
different theories will need to use the form with fully-qualified names
(`thy1$n`, `thy2$n` etc).

If the boolean flag is false, this invocation is comparable to the
behaviour after `intputonly_type_abbrev`: the abbreviation can be used
to input types of the desired pattern, but such types will print as they
did previously.

### Failure

Fails if `ty` is a variable type.

### Comments

As with other parsing and pretty-printing functions, there is a
companion function, `temp_thytype_abbrev`, which has the same effect on
the global grammar but does not cause the change to persist when the
theory is exported.

It is legitimate to use a string for the theory component of the record
that does not correspond to the current theory. Indeed, it is perfectly
reasonable to do this, if one wants to give priority to a particular
ancestral abbreviation.

### See also

[`Parse.type_abbrev`](#Parse.type_abbrev)
