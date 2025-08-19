## `COND_REWR_CONV`

``` hol4
Cond_rewrite.COND_REWR_CONV : ((term -> term ->
 ((term # term) list # (type # type) list) list) -> thm -> conv)
```

------------------------------------------------------------------------

A lower level conversion implementing simple conditional rewriting.

`COND_REWR_CONV` is one of the basic building blocks for the
implementation of the simple conditional rewriting conversions in the
HOL system. In particular, the conditional term replacement or rewriting
done by all the conditional rewriting conversions in this library is
ultimately done by applications of `COND_REWR_CONV`. The description
given here for `COND_REWR_CONV` may therefore be taken as a
specification of the atomic action of replacing equals by equals in a
term under certain conditions that are used in all these higher level
conditional rewriting conversions.

The first argument to `COND_REWR_CONV` is expected to be a function
which returns a list of matches. Each of these matches is in the form of
the value returned by the built-in function `match`. It is used to
search the input term for instances which may be rewritten.

The second argument to `COND_REWR_CONV` is expected to be an implicative
theorem in the following form:

``` hol4
   A |- !x1 ... xn. P1 ==> ... Pm ==> (Q[x1,...,xn] = R[x1,...,xn])
```

where `x1`, ..., `xn` are all the variables that occur free in the left
hand side of the conclusion of the theorem but do not occur free in the
assumptions.

The last argument to `COND_REWR_CONV` is the term to be rewritten.

If `fn` is a function and `th` is an implicative theorem of the kind
shown above, then `COND_REWR_CONV fn th` will be a conversion. When
applying to a term `tm`, it will return a theorem

``` hol4
   P1', ..., Pm' |- tm = tm[R'/Q']
```

if evaluating `fn Q[x1,...,xn] tm` returns a non-empty list of matches.
The assumptions of the resulting theorem are instances of the
antecedents of the input theorem `th`. The right hand side of the
equation is obtained by rewriting the input term `tm` with instances of
the conclusion of the input theorem.

### Failure

`COND_REWR_CONV fn th` fails if `th` is not an implication of the form
described above. If `th` is such an equation, but the function `fn`
returns a null list of matches, or the function `fn` returns a non-empty
list of matches, but the term or type instantiation fails.

### Example

The following example illustrates a straightforward use of
`COND_REWR_CONV`. We use the built-in theorem `LESS_MOD` as the input
theorem, and the function `search_top_down` as the search function.

``` hol4
   #LESS_MOD;;
   Theorem LESS_MOD autoloading from theory `arithmetic` ...
   LESS_MOD = |- !n k. k < n ==> (k MOD n = k)

   |- !n k. k < n ==> (k MOD n = k)

   #search_top_down;;
   - : (term -> term -> ((term # term) list # (type # type) list) list)

   #COND_REWR_CONV search_top_down LESS_MOD "2 MOD 3";;
   2 < 3 |- 2 MOD 3 = 2
```

### See also

[`Cond_rewrite.COND_REWR_TAC`](#Cond_rewrite.COND_REWR_TAC),
[`Cond_rewrite.COND_REWRITE1_TAC`](#Cond_rewrite.COND_REWRITE1_TAC),
[`Cond_rewrite.COND_REWRITE1_CONV`](#Cond_rewrite.COND_REWRITE1_CONV),
[`Cond_rewrite.COND_REWR_CANON`](#Cond_rewrite.COND_REWR_CANON),
[`Cond_rewrite.search_top_down`](#Cond_rewrite.search_top_down)
