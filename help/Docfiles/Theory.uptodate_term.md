## `uptodate_term`

``` hol4
Theory.uptodate_term : term -> bool
```

------------------------------------------------------------------------

Tells if a term is out of date.

Operations in the current theory segment of HOL allow one to redefine
types and constants. This can cause theorems to become invalid. As a
result, HOL has a rudimentary consistency maintenance system built
around the notion of whether type operators and term constants are
"up-to-date".

An invocation `uptodate_term M` checks `M` to see if it has been built
from any out-of-date components. The definition of `out-of-date` is
mutually recursive among types, terms, and theorems. If `M` is a
variable, it is out-of-date if its type is out-of-date. If `M` is a
constant, it is out-of-date if it has been redeclared, or if its type is
out-of-date, or if the witness theorem used to justify its existence is
out-of-date. If `M` is a combination, it is out-of-date if either of its
components are out-of-date. If `M` is an abstraction, it is out-of-date
if either the bound variable or the body is out-of-date.

All items from ancestor theories are fixed, and unable to be
overwritten, thus are always up-to-date.

### Failure

Never fails.

### Example

``` hol4
- Define `fact x = if x=0 then 1 else x * fact (x-1)`;
Equations stored under "fact_def".
Induction stored under "fact_ind".
> val it = |- fact x = (if x = 0 then 1 else x * fact (x - 1)) : thm

- val M = Term `!x. 0 < fact x`;
> val M = `!x. 0 < fact x` : term

- uptodate_term M;
> val it = true : bool

- delete_const "fact";
> val it = () : unit

- uptodate_term M;
> val it = false : bool
```

### See also

[`Theory.uptodate_type`](#Theory.uptodate_type),
[`Theory.uptodate_thm`](#Theory.uptodate_thm)
