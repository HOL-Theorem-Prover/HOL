## `FVL`

``` hol4
Term.FVL : term list -> term set -> term set
```

------------------------------------------------------------------------

Efficient computation of the set of free variables in a list of terms.

An invocation `FVL [t1,...,tn] V` adds the set of free variables found
in `t1,...,tn` to the accumulator `V`.

### Failure

Never fails.

### Example

``` hol4
- FVL [Term `v1 /\ v2 ==> v2 \/ v3`] empty_varset;
> val it = <set> : term set

- HOLset.listItems it;
> val it = [`v1`, `v2`, `v3`] : term list
```

### Comments

Preferable to `free_varsl` when the number of free variables becomes
large.

### See also

[`HOLset`](#HOLset), [`Term.empty_varset`](#Term.empty_varset),
[`Term.free_varsl`](#Term.free_varsl),
[`Term.free_vars`](#Term.free_vars)
