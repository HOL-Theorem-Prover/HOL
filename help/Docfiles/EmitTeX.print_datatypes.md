## `print_datatypes`

``` hol4
EmitTeX.print_datatypes : string -> unit
```

------------------------------------------------------------------------

Prints datatype declarations for the named theory to the screeen
(standard out).

An invocation of `print_datatypes thy`, where `thy` is the name of a
currently loaded theory segment, will print the datatype declarations
made in that theory.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment then no output will be produced.

### Example

``` hol4
- new_theory "example";
<<HOL message: Created theory "example">>
> val it = () : unit
- val _ = Hol_datatype `example = First | Second`;
<<HOL message: Defined type: "example">>
- EmitTeX.print_datatypes "example";
example = First | Second
> val it = () : unit
```

### See also

[`EmitTeX.datatype_thm_to_string`](#EmitTeX.datatype_thm_to_string),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype)
