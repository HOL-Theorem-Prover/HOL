## `tgoal`

``` hol4
Defn.tgoal : defn -> proofs
```

------------------------------------------------------------------------

Set up a termination proof.

`tgoal defn` sets up a termination proof for the function represented by
`defn`. It creates a new goalstack and makes it the focus of subsequent
goalstack operations.

### Failure

`tgoal defn` fails if `defn` represents a non-recursive or primitive
recursive function.

### Example

``` hol4
- val qsort_defn =
    Hol_defn "qsort"
       `(qsort ___ [] = []) /\
        (qsort ord (x::rst) =
            APPEND (qsort ord (FILTER ($~ o ord x) rst))
              (x :: qsort ord (FILTER (ord x) rst)))`;

- tgoal qsort_defn;
> val it =
   Proof manager status: 1 proof.
   1. Incomplete:
       Initial goal:
       ?R. WF R /\
           (!rst x ord. R (ord,FILTER ($~ o ord x) rst) (ord,x::rst)) /\
            !rst x ord. R (ord,FILTER (ord x) rst) (ord,x::rst)
```

### See also

[`TotalDefn.WF_REL_TAC`](#TotalDefn.WF_REL_TAC),
[`Defn.tprove`](#Defn.tprove), [`Defn.Hol_defn`](#Defn.Hol_defn)
