## `dest_thm`

``` hol4
Thm.dest_thm : thm -> term list * term
```

------------------------------------------------------------------------

Breaks a theorem into assumption list and conclusion.

`dest_thm ([t1,...,tn] |- t)` returns `([t1,...,tn],t)`.

### Failure

Never fails.

### Example

``` hol4
- dest_thm (ASSUME (Term `p=T`));
> val it = ([`p = T`], `p = T`) : term list * term
```

### See also

[`Thm.concl`](#Thm.concl), [`Thm.hyp`](#Thm.hyp)
