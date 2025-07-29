## `PALPHA`

``` hol4
PairRules.PALPHA : term -> term -> thm
```

------------------------------------------------------------------------

Proves equality of paired alpha-equivalent terms.

When applied to a pair of terms `t1` and `t1'` which are
alpha-equivalent, `ALPHA` returns the theorem `|- t1 = t1'`.

``` hol4
   -------------  PALPHA "t1" "t1'"
    |- t1 = t1'
```

The difference between `PALPHA` and `ALPHA` is that `PALPHA` is prepared
to consider pair structures of different structure to be
alpha-equivalent. In its most trivial case this means that `PALPHA` can
consider a variable and a pair to alpha-equivalent.

### Failure

Fails unless the terms provided are alpha-equivalent.

### Example

``` hol4
- PALPHA (Term `\(x:'a,y:'a). (x,y)`) (Term`\xy:'a#'a. xy`);
> val it = |- (\(x,y). (x,y)) = (\xy. xy) : thm
```

### Comments

Alpha-converting a paired abstraction to a nonpaired abstraction can
introduce instances of the terms `FST` and `SND`. A paired abstraction
and a nonpaired abstraction will be considered equivalent by `PALPHA` if
the nonpaired abstraction contains all those instances of `FST` and
`SND` present in the paired abstraction, plus the minimum additional
instances of `FST` and `SND`. For example:

``` hol4
   - PALPHA
      (Term `\(x:'a,y:'b). (f x y (x,y)):'c`)
      (Term `\xy:'a#'b. (f (FST xy) (SND xy) xy):'c`);
   > val it = |- (\(x,y). f x y (x,y)) = (\xy. f (FST xy) (SND xy) xy) : thm

   - PALPHA
      (Term `\(x:'a,y:'b). (f x y (x,y)):'c`)
      (Term `\xy:'a#'b. (f (FST xy) (SND xy) (FST xy, SND xy)):'c`)
     handle e => Raise e;

   Exception raised at ??.failwith:
   PALPHA
   ! Uncaught exception:
   ! HOL_ERR
```

### See also

[`Thm.ALPHA`](#Thm.ALPHA), [`Term.aconv`](#Term.aconv),
[`PairRules.PALPHA_CONV`](#PairRules.PALPHA_CONV),
[`PairRules.GEN_PALPHA_CONV`](#PairRules.GEN_PALPHA_CONV)
