## `mk_word_size`

``` hol4
wordsLib.mk_word_size : int -> unit
```

------------------------------------------------------------------------

Adds a type abbreviation and theorems for a given word length.

An invocation of `mk_word_size n` introduces a type abbreviation for
words of length `n`. Theorems for `dimindex(:n)`, `dimword(:n)` and
`INT_MIN(:n)` are generated and stored.

### Example

``` hol4
- mk_word_size 128
> val it = () : unit
- “:word128”
> val it = “:bool[128]” : hol_type
- theorem "dimword_128"
> val it = |- dimword (:128) = 340282366920938463463374607431768211456 : thm
```

### Comments

The type abbreviation will only print when `type_pp.pp_array_types` is
set to `false`.

### See also

[`Parse.type_abbrev`](#Parse.type_abbrev),
[`wordsLib.SIZES_CONV`](#wordsLib.SIZES_CONV),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss)
