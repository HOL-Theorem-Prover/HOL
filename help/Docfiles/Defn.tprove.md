## `tprove` {#Defn.tprove}


```
tprove : defn * tactic -> thm * thm
```



Prove termination of a `defn`.


`tprove` takes a `defn` and a `tactic`, and uses the tactic to prove the
termination constraints of the `defn`. A pair of theorems `(eqns,ind)`
is returned: `eqns` is the unconstrained recursion equations of the
`defn`, and `ind` is the corresponding induction theorem for the
equations, also unconstrained.

`tprove` and `tgoal` can be seen as analogues of `prove` and `set_goal`
in the specialized domain of proving termination of recursive functions.

It is up to the user to store the results of `tprove` in the current
theory segment.



### Failure

`tprove (defn,tac)` fails if `tac` fails to prove the termination
conditions of `defn`.

`tprove (defn,tac)` fails if `defn` represents a non-recursive or
primitive recursive function.

### Example

Suppose that we have defined a version of Quicksort as follows:
    
       - val qsort_defn =
           Hol_defn "qsort"
              `(qsort ___ [] = []) /\
               (qsort ord (x::rst) =
                   APPEND (qsort ord (FILTER ($~ o ord x) rst))
                     (x :: qsort ord (FILTER (ord x) rst)))`
    
Also suppose that a tactic `tac` proves termination of
`qsort`. (This tactic has probably been built by interactive proof
after starting a goalstack with `tgoal qsort_defn`.) Then
    
       - val (qsort_eqns, qsort_ind) = tprove(qsort_defn, tac);
    
       > val qsort_eqns =
           |- (qsort v0 [] = []) /\
              (qsort ord (x::rst) =
                 APPEND (qsort ord (FILTER ($~ o ord x) rst))
                     (x::qsort ord (FILTER (ord x) rst))) : thm
    
         val qsort_ind =
           |- !P.
                (!v0. P v0 []) /\
                (!ord x rst.
                   P ord (FILTER ($~ o ord x) rst) /\
                   P ord (FILTER (ord x) rst) ==> P ord (x::rst))
                ==>
               !v v1. P v v1 : thm
    



### Comments

The recursion equations returned by a successful invocation of `tprove`
are automatically added to the global `compset` accessed by `EVAL`.

### See also

[`Defn.tgoal`](#Defn.tgoal), [`Defn.Hol_defn`](#Defn.Hol_defn), [`bossLib.EVAL`](#bossLib.EVAL)

