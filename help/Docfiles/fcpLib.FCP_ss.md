## `FCP_ss`

``` hol4
fcpLib.FCP_ss : ssfrag
```

------------------------------------------------------------------------

A simpset fragment for simplifying finite Cartesian product expressions.

### Example

``` hol4
  simpLib.SSFRAG{ac = [], congs = [], convs = [], dprocs = [], filter = NONE,
                 rewrs =
                   [|- !i. i < dimindex (:'b) ==> ($FCP g ' i = g i),
                    |- !g. (FCP i. g ' i) = g,
                    |- !x y. (x = y) = !i. i < dimindex (:'b) ==> (x ' i = y ' i)]}
   : ssfrag
```

### See also

[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss)
