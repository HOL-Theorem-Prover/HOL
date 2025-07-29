## `datatype_thm_to_string`

``` hol4
EmitTeX.datatype_thm_to_string : thm -> string
```

------------------------------------------------------------------------

Converts a datatype theorem to a string.

An invocation of `datatype_thm_to_string thm`, where `thm` is a datatype
theorem produced by `Hol_datatype`, will return a string that
corresponds with the orginal datatype declaration.

### Failure

Will fail if the supplied theorem is not a datatype theorem, as created
by `Hol_datatype`.

### Example

``` hol4
- new_theory "example";
<<HOL message: Created theory "example">>
> val it = () : unit
- val _ = Hol_datatype `example = First | Second`;
<<HOL message: Defined type: "example">>
- EmitTeX.datatype_thm_to_string (theorem "datatype_example");
> val it = "example = First | Second" : string
```

### See also

[`bossLib.Hol_datatype`](#bossLib.Hol_datatype)
