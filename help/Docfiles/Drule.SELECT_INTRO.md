## `SELECT_INTRO`

``` hol4
Drule.SELECT_INTRO : (thm -> thm)
```

------------------------------------------------------------------------

Introduces an epsilon term.

`SELECT_INTRO` takes a theorem with an applicative conclusion, say
`P x`, and returns a theorem with the epsilon term `$@ P` in place of
the original operand `x`.

``` hol4
     A |- P x
   --------------  SELECT_INTRO
    A |- P($@ P)
```

The returned theorem asserts that `$@ P` denotes some value at which `P`
holds.

### Failure

Fails if the conclusion of the theorem is not an application.

### Example

Given the theorem

``` hol4
   th1 = |- (\n. m = n)m
```

applying `SELECT_INTRO` replaces the second occurrence of `m` with the
epsilon abstraction of the operator:

``` hol4
   - val th2 = SELECT_INTRO th1;
   val th2 = |- (\n. m = n)(@n. m = n) : thm
```

This theorem could now be used to derive a further result:

``` hol4
   - EQ_MP (BETA_CONV(concl th2)) th2;
   val it = |- m = (@n. m = n) : thm
```

### See also

[`Thm.EXISTS`](#Thm.EXISTS), [`Conv.SELECT_CONV`](#Conv.SELECT_CONV),
[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM),
[`Drule.SELECT_RULE`](#Drule.SELECT_RULE)
