## `dest_term`

``` hol4
Term.dest_term : term -> lambda
```

------------------------------------------------------------------------

Breaks terms into a type with SML constructors for pattern-matching.

A call to `dest_term t` returns a value of type `lambda`, which has SML
definition

``` hol4
   datatype lambda =
      VAR of string * hol_type
    | CONST of {Name:string, Thy:string, Ty:hol_type}
    | COMB of term * term
    | LAMB of term * term
```

This type encodes all possible forms of `term`.

### Failure

Never fails.

### Example

``` hol4
> dest_term ``SUC 2``;
val it = COMB (``SUC``, ``2``) : lambda
```

### See also

[`Term.dest_abs`](#Term.dest_abs), [`Term.dest_comb`](#Term.dest_comb),
[`Term.dest_const`](#Term.dest_const),
[`boolSyntax.dest_strip_comb`](#boolSyntax.dest_strip_comb),
[`Term.dest_thy_const`](#Term.dest_thy_const),
[`Term.dest_var`](#Term.dest_var)
