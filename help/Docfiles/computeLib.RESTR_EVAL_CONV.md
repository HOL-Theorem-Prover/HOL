## `RESTR_EVAL_CONV`

``` hol4
computeLib.RESTR_EVAL_CONV : term list -> conv
```

------------------------------------------------------------------------

Symbolically evaluate a term, except for specified constants.

An application `RESTR_EVAL_CONV [c1, ..., cn] M` evaluates the term `M`
in the call-by-value style of `EVAL`. When a type instance `c` of any
element in `c1`,...,`cn` is encountered, `c` is not expanded by
`RESTR_EVAL_CONV`. The effect is that evaluation stops at `c` (even
though any arguments to `c` may be evaluated). This facility can be used
to control `EVAL_CONV` to some extent.

### Failure

Never fails, but may diverge.

### Example

In the following, we first attempt to map the factorial function `FACT`
over a list of variables. This attempt goes into a loop, because the
conditional statement in the evaluation rule for `FACT` is never
determine when the argument is equal to zero. However, if we suppress
the evaluation of `FACT`, then we can return a useful answer.

``` hol4
   - EVAL (Term `MAP FACT [x; y; z]`);   (* loops! *)
   > Interrupted.

   - val [FACT] = decls "FACT";   (* find FACT constant *)
   > val FACT = `FACT` : term

   - RESTR_EVAL_CONV [FACT] (Term `MAP FACT [x; y; z]`);

   > val it = |- MAP FACT [x; y; z] = [FACT x; FACT y; FACT z] : thm
```

Controlling symbolic evaluation when it loops or becomes exponential.

### See also

[`bossLib.EVAL`](#bossLib.EVAL),
[`computeLib.RESTR_EVAL_TAC`](#computeLib.RESTR_EVAL_TAC),
[`computeLib.RESTR_EVAL_RULE`](#computeLib.RESTR_EVAL_RULE),
[`Term.decls`](#Term.decls)
