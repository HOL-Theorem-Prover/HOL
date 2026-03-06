## `PART_MATCH_A`

``` hol4
Drule.PART_MATCH_A : (term -> term) -> thm -> term -> thm
```

------------------------------------------------------------------------

Instantiates a theorem by matching part of its conclusion to a term.

`PART_MATCH_A` behaves as `PART_MATCH` except that it permits
instantiating variables which appear in the assumptions of the given
theorem.

### See also

[`Drule.PART_MATCH`](#Drule.PART_MATCH),
[`Conv.REWR_CONV_A`](#Conv.REWR_CONV_A)
