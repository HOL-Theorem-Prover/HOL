## `commafy`

``` hol4
Lib.commafy : string list -> string list
```

------------------------------------------------------------------------

Add commas into a list of strings.

An application `commafy [s1,...,sn]` yields `[s1, ",", ..., ",", sn]`.

### Failure

Never fails.

### Example

``` hol4
- commafy ["donkey", "mule", "horse", "camel", "llama"];
> val it =
    ["donkey", ", ", "mule", ", ", "horse", ", ", "camel", ", ", "llama"] :
  string list

- print (String.concat it ^ "\n");
donkey, mule, horse, camel, llama
> val it = () : unit

- commafy ["foo"];
> val it = ["foo"] : string list
```
