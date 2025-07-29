## `EXPAND_REDUCE_CONV`

``` hol4
wordsLib.EXPAND_REDUCE_CONV : conv
```

------------------------------------------------------------------------

The conversion `EXPAND_REDUCE_CONV` expands out applications of
`reduce_and`, `reduce_or`, `reduce_xor`, `reduce_nand`, `reduce_nor` and
`reduce_xnor`.

### Example

``` hol4
> wordsLib.EXPAND_REDUCE_CONV “reduce_and (w: word4)”;
val it =
   |- reduce_and w =
   (((3 >< 3) w && (2 >< 2) w) && (1 >< 1) w) && (0 >< 0) w:
   thm
```

### See also

[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)
