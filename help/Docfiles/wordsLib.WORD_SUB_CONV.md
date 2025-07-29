## `WORD_SUB_CONV`

``` hol4
wordsLib.WORD_SUB_CONV : conv
```

------------------------------------------------------------------------

The conversion `WORD_SUB_CONV` is designed to eliminate occurrences of
multiplication by a negative coefficient, introducing unary-minus (2's
complement) and subtraction wherever possible.

### Example

``` hol4
> wordsLib.WORD_SUB_CONV “a + -3w * b + -1w * c = -1w * d + e: 'a word”;
val it =
   |- (a + -3w * b + -1w * c = -1w * d + e) <=> (a - 3w * b - c = e - d):
   thm

> wordsLib.WORD_SUB_CONV “-1w * a: 'a word”;
val it = |- -1w * a = -a: thm

wordsLib.WORD_SUB_CONV “-1w * a + -2w * b: 'a word”;
val it =
   |- -1w * a + -2w * b = -(2w * b + a):
   thm
```

### Comments

This conversion forms the basis of `wordsLib.WORD_SUB_ss`. Care should
be taken when using this conversion in combination with other bit-vector
tools. For example, `wordsLib.WORD_ARITH_CONV` will undo all of the work
of `WORD_SUB_CONV`.

### See also

[`wordsLib.WORD_SUB_ss`](#wordsLib.WORD_SUB_ss)
