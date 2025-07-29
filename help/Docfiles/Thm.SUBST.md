## `SUBST`

``` hol4
Thm.SUBST : (term,thm) subst -> term -> thm -> thm
```

------------------------------------------------------------------------

Makes a set of parallel substitutions in a theorem.

Implements the following rule of simultaneous substitution

``` hol4
    A1 |- t1 = u1 ,  ... , An |- tn = un ,    A |- t[t1,...,tn]
   -------------------------------------------------------------
        A u A1 u ... u An |- t[u1,...,un]
```

Evaluating

``` hol4
   SUBST [x1 |-> (A1 |- t1=u1) ,..., xn |-> (An |- tn=un)]
         t[x1,...,xn]
         (A |- t[t1,...,tn])
```

returns the theorem `A u A1 u ... u An |- t[u1,...,un]` (perhaps with
fewer assumptions, see paragraph below). The term argument
`t[x1,...,xn]` is a template which should match the conclusion of the
theorem being substituted into, with the variables `x1`, ... , `xn`
marking those places where occurrences of `t1`, ... , `tn` are to be
replaced by the terms `u1`, ... , `un`, respectively. The occurrence of
`ti` at the places marked by `xi` must be free (i.e. `ti` must not
contain any bound variables). `SUBST` automatically renames bound
variables to prevent free variables in `ui` becoming bound after
substitution.

The assumptions of the returned theorem may not contain all the
assumptions `A1 u ... u An` if some of them are not required. In
particular, if the theorem `Ak |- tk = uk` is unnecessary because `xk`
does not appear in the template, then `Ak` is not be added to the
assumptions of the returned theorem.

### Failure

If the template does not match the conclusion of the hypothesis, or the
terms in the conclusion marked by the variables `x1`, ... , `xn` in the
template are not identical to the left hand sides of the supplied
equations (i.e. the terms `t1`, ... , `tn`).

### Example

``` hol4
- val x = “x:num”
  and y = “y:num”
  and th0 = SPEC “0” arithmeticTheory.ADD1
  and th1 = SPEC “1” arithmeticTheory.ADD1;

(*    x = `x`
      y = `y`
    th0 = |- SUC 0 = 0 + 1
    th1 = |- SUC 1 = 1 + 1     *)

- SUBST [x |-> th0, y |-> th1]
        “(x+y) > SUC 0”
        (ASSUME “(SUC 0 + SUC 1) > SUC 0”);

> val it = [.] |- (0 + 1) + 1 + 1 > SUC 0 : thm


- SUBST [x |-> th0, y |-> th1]
        “(SUC 0 + y) > SUC 0”
        (ASSUME “(SUC 0 + SUC 1) > SUC 0”);

> val it = [.] |- SUC 0 + 1 + 1 > SUC 0 : thm


- SUBST [x |-> th0, y |-> th1]
        “(x+y) > x”
        (ASSUME “(SUC 0 + SUC 1) > SUC 0”);

> val it = [.] |- (0 + 1) + 1 + 1 > 0 + 1 : thm
```

### Comments

`SUBST` is perhaps overly complex for a primitive rule of inference.

For substituting at selected occurrences. Often useful for writing
special purpose derived inference rules.

### See also

[`Thm.INST`](#Thm.INST), [`Drule.SUBS`](#Drule.SUBS),
[`Drule.SUBST_CONV`](#Drule.SUBST_CONV), [`Lib.|->`](#Lib..GZKQ4)
