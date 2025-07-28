## `MATCH_ASMSUB_RENAME_TAC` {#Q.MATCH_ASMSUB_RENAME_TAC}


```
MATCH_ASMSUB_RENAME_TAC : term quotation -> string list -> tactic
```



Finds a match for a pattern in assumptions; instantiates goal to rename or abbreviate.


When applied to the goal `(asl,w)`, the tactic
`Q.MATCH_ASMSUB_RENAME_TAC q` parses the quotation `q` in the context
of the goal, producing a term `pat` to use as a pattern. The tactic
then attempts a (first order) match of `pat` against each term in
`asl`, stopping when it finds an assumption that either matches `pat`
in its entirety, or has a sub-term that matches `pat` (holding
existing free variables from the goal constant).

In either case, the match will return an instantiation mapping the
fresh free variables of `pat` to terms occurring in the goal. This
instantiation drops its bindings for variables whose names begin with
an underscore, is next reversed, and is finally applied to the goal.
This will both cause free variables in the goal to be renamed, and for
larger terms to be replaced by variables (similar to what happens with
the use of `SPEC_TAC`).

### Failure

Fails if there is no valid match for the pattern among the assumptions
and their sub-terms. A valid match will not bind variables that are
bound in the assumption being searched.

### Example

In the following example, the variable `x` is treated as if a
constant, so the search for a match with the pattern does not succeed
on the first assumption (featuring `P`). Instead the second assumption
provides the instantiation, and so the variable `z` in the original is
renamed to `n`.
    
       > Q.MATCH_ASMSUB_RENAME_TAC `x < n`
           ([``P(y < m):bool``, ``Q(x < z) : bool``], ``x + z < 10``);
       val it = ([([``P (y < m)``, ``Q (x < n)``], ``x + n < 10``)],
                 fn): goal list * validation
    

### See also

[`Q.MATCH_ASSUM_RENAME_TAC`](#Q.MATCH_ASSUM_RENAME_TAC), [`Q.MATCH_GOALSUB_RENAME_TAC`](#Q.MATCH_GOALSUB_RENAME_TAC)

