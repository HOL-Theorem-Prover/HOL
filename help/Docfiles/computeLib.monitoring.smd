## `monitoring`

``` hol4
computeLib.monitoring : (term -> bool) option ref
```

------------------------------------------------------------------------

Monitoring support for evaluation.

The reference variable `monitoring` provides a simple way to view the
operation of `EVAL`, `EVAL_RULE`, and `EVAL_TAC`. The initial value of
`monitoring` is `NONE`. If one wants to monitor the expansion of a
function, defined with constant `c`, then setting `monitoring` to
`SOME (same_const c)` will tell the system to print out the expansion of
`c` by the evaluation entrypoints. To monitor the expansions of a
collection of functions, defined with `c1`,...,`cn`, then `monitoring`
can be set to

``` hol4
   SOME (fn x => same_const c1 x orelse ... orelse same_const cn x)
```

### Failure

Never fails.

### Example

``` hol4
- val [FACT] = decls "FACT";
> val FACT = `FACT` : term

- computeLib.monitoring := SOME (same_const FACT);

- EVAL (Term `FACT 4`);
FACT 4 = (if 4 = 0 then 1 else 4 * FACT (PRE 4))
FACT 3 = (if 3 = 0 then 1 else 3 * FACT (PRE 3))
FACT 2 = (if 2 = 0 then 1 else 2 * FACT (PRE 2))
FACT 1 = (if 1 = 0 then 1 else 1 * FACT (PRE 1))
FACT 0 = (if 0 = 0 then 1 else 0 * FACT (PRE 0))
> val it = |- FACT 4 = 24 : thm
```

### See also

[`computeLib.RESTR_EVAL_CONV`](#computeLib.RESTR_EVAL_CONV),
[`Term.decls`](#Term.decls)
