## `REWR_CONV`

``` hol4
Conv.REWR_CONV : (thm -> conv)
```

------------------------------------------------------------------------

Uses an instance of a given equation to rewrite a term.

`REWR_CONV` is one of the basic building blocks for the implementation
of rewriting in the HOL system. In particular, the term replacement or
rewriting done by all the built-in rewriting rules and tactics is
ultimately done by applications of `REWR_CONV` to appropriate subterms.
The description given here for `REWR_CONV` may therefore be taken as a
specification of the atomic action of replacing equals by equals that is
used in all these higher level rewriting tools.

The first argument to `REWR_CONV` is expected to be an equational
theorem which is to be used as a left-to-right rewrite rule. The general
form of this theorem is:

``` hol4
   A |- t[x1,...,xn] = u[x1,...,xn]
```

where `x1`, ..., `xn` are all the variables that occur free in the
left-hand side of the conclusion of the theorem but do not occur free in
the assumptions. Any of these variables may also be universally
quantified at the outermost level of the equation, as for example in:

``` hol4
   A |- !x1...xn. t[x1,...,xn] = u[x1,...,xn]
```

Note that `REWR_CONV` will also work, but will give a generally
undesirable result (see below), if the right-hand side of the equation
contains free variables that do not also occur free on the left-hand
side, as for example in:

``` hol4
   A |- t[x1,...,xn] = u[x1,...,xn,y1,...,ym]
```

where the variables `y1`, ..., `ym` do not occur free in `t[x1,...,xn]`.

If `th` is an equational theorem of the kind shown above, then
`REWR_CONV th` returns a conversion that maps terms of the form
`t[e1,...,en/x1,...,xn]`, in which the terms `e1`, ..., `en` are free
for `x1`, ..., `xn` in `t`, to theorems of the form:

``` hol4
   A |- t[e1,...,en/x1,...,xn] = u[e1,...,en/x1,...,xn]
```

That is, `REWR_CONV th tm` attempts to match the left-hand side of the
rewrite rule `th` to the term `tm`. If such a match is possible, then
`REWR_CONV` returns the corresponding substitution instance of `th`.

If `REWR_CONV` is given a theorem `th`:

``` hol4
   A |- t[x1,...,xn] = u[x1,...,xn,y1,...,ym]
```

where the variables `y1`, ..., `ym` do not occur free in the left-hand
side, then the result of applying the conversion `REWR_CONV th` to a
term `t[e1,...,en/x1,...,xn]` will be:

``` hol4
   A |- t[e1,...,en/x1,...,xn] = u[e1,...,en,v1,...,vm/x1,...,xn,y1,...,ym]
```

where `v1`, ..., `vm` are variables chosen so as to be free nowhere in
`th` or in the input term. The user has no control over the choice of
the variables `v1`, ..., `vm`, and the variables actually chosen may
well be inconvenient for other purposes. This situation is, however,
relatively rare; in most equations the free variables on the right-hand
side are a subset of the free variables on the left-hand side.

In addition to doing substitution for free variables in the supplied
equational theorem (or 'rewrite rule'), `REWR_CONV th tm` also does type
instantiation, if this is necessary in order to match the left-hand side
of the given rewrite rule `th` to the term argument `tm`. If, for
example, `th` is the theorem:

``` hol4
   A |- t[x1,...,xn] = u[x1,...,xn]
```

and the input term `tm` is (a substitution instance of) an instance of
`t[x1,...,xn]` in which the types `ty1`, ..., `tyi` are substituted for
the type variables `vty1`, ..., `vtyi`, that is if:

``` hol4
   tm = t[ty1,...,tyn/vty1,...,vtyn][e1,...,en/x1,...,xn]
```

then `REWR_CONV th tm` returns:

``` hol4
   A |- (t = u)[ty1,...,tyn/vty1,...,vtyn][e1,...,en/x1,...,xn]
```

Note that, in this case, the type variables `vty1`, ..., `vtyi` must not
occur anywhere in the hypotheses `A`. Otherwise, the conversion will
fail.

### Failure

`REWR_CONV th` fails if `th` is not an equation or an equation
universally quantified at the outermost level. If `th` is such an
equation:

``` hol4
  th = A |- !v1....vi. t[x1,...,xn] = u[x1,...,xn,y1,...,yn]
```

then `REWR_CONV th tm` fails unless the term `tm` is alpha-equivalent to
an instance of the left-hand side `t[x1,...,xn]` which can be obtained
by instantiation of free type variables (i.e. type variables not
occurring in the assumptions `A`) and substitution for the free
variables `x1`, ..., `xn`.

As noted, `REWR_CONV th` will fail rather than substitute for variables
or type variables which appear in the hypotheses `A`. To allow
substitution in the hypotheses, use `REWR_CONV_A th`.

### Example

The following example illustrates a straightforward use of `REWR_CONV`.
The supplied rewrite rule is polymorphic, and both substitution for free
variables and type instantiation may take place. `EQ_SYM_EQ` is the
theorem:

``` hol4
   |- !x:'a. !y. (x = y) = (y = x)
```

and `REWR_CONV EQ_SYM_EQ` behaves as follows:

``` hol4
   - REWR_CONV EQ_SYM_EQ (Term `1 = 2`);
   > val it = |- (1 = 2) = (2 = 1) : thm

   - REWR_CONV EQ_SYM_EQ (Term `1 < 2`);
   ! Uncaught exception:
   ! HOL_ERR
```

The second application fails because the left-hand side `x = y` of the
rewrite rule does not match the term to be rewritten, namely `1 < 2`.

In the following example, one might expect the result to be the theorem
`A |- f 2 = 2`, where `A` is the assumption of the supplied rewrite
rule:

``` hol4
   - REWR_CONV (ASSUME (Term `!x:'a. f x = x`)) (Term `f 2:num`);
   ! Uncaught exception:
   ! HOL_ERR
```

The application fails, however, because the type variable `'a` appears
in the assumption of the theorem returned by
`` ASSUME (Term `!x:'a. f x = x`) ``.

Failure will also occur in situations like:

``` hol4
   - REWR_CONV (ASSUME (Term `f (n:num) = n`)) (Term `f 2:num`);
   ! Uncaught exception:
   ! HOL_ERR
```

where the left-hand side of the supplied equation contains a free
variable (in this case `n`) which is also free in the assumptions, but
which must be instantiated in order to match the input term.

### See also

[`Conv.REWR_CONV_A`](#Conv.REWR_CONV_A),
[`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV)
