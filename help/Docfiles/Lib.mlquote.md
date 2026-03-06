## `mlquote`

``` hol4
Lib.mlquote : string -> string
```

------------------------------------------------------------------------

Put quotation marks around a string.

Like `quote`, `mlquote s` puts quotation marks around a string. However,
it also transforms the characters in a string so that, when printed, it
would be a valid ML lexeme.

### Failure

Never fails

### Example

``` hol4
- print (quote "foo\nbar" ^ "\n");
"foo
bar"
> val it = () : unit

- print (mlquote "foo\nbar" ^ "\n");
"foo\nbar"
> val it = () : unit
```

### See also

[`Lib.quote`](#Lib.quote)
