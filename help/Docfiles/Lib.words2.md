## `words2`

``` hol4
Lib.words2 : string -> string -> string list
```

------------------------------------------------------------------------

Splits a string into a list of substrings, breaking at occurrences of a
specified character.

`words2 char s` splits the string `s` into a list of substrings.
Splitting occurs at each occurrence of a sequence of the character
`char`. The `char` characters do not appear in the list of substrings.
Leading and trailing occurrences of `char` are also thrown away. If
`char` is not a single-character string (its length is not 1), then `s`
will not be split and so the result will be the list `[s]`.

### Failure

Never fails.

### Example

``` hol4
- words2  "/"  "/the/cat//sat/on//the/mat/";
> val it = ["the", "cat", "sat", "on", "the", "mat"] : string list

- words2  "//"  "/the/cat//sat/on//the/mat/";
> val it = ["/the/cat//sat/on//the/mat/"] : string list
```

### Comments

The SML Library functions `String.tokens` and `String.fields` offer
similar functionality.
