## `hh`

``` hol4
holyHammer.hh : tactic
```

------------------------------------------------------------------------

General purpose tactic relying on a automatic selection of theorems in
the library. It returns a automatically generated call to `METIS_TAC`
that solves the goal. A good practice is to replace the call of
`holyhammer.hh` by the generated tactic.

Select relevant theorems for proving a goal using the k-nearest neighbor
premise selection algorithm, translate the theorems together with the
goal from higher-order to first-order, call external provers (ATP) and
reconstruct the final proof inside HOL4 by calling `METIS_TAC` with the
theorems appearing in the proof of the prover.

### Failure

Fails if the supplied goal does not contain boolean terms only. Or if no
ATP is installed. Or if no proof is found by the installed ATPs in less
than a 15 seconds (default). This timeout can be modifed by
`holyHammer.set_timeout`. Or if `METIS_TAC` cannot reconstruct the proof
from the selected theorems in less than one second.

### Example

``` hol4
- load "holyHammer"; open holyHammer;
(* output omitted *)
> val it = () : unit

- hh ([],``1+1=2``);
Loading 3091 theorems 
proof found by eprover:
  metisTools.METIS_TAC [arithmeticTheory.ALT_ZERO , arithmeticTheory.SUC_ONE_ADD , arithmeticTheory.TWO , numeralTheory.numeral_distrib , numeralTheory.numeral_suc]
minimized proof:  
  METIS_TAC [arithmeticTheory.SUC_ONE_ADD, numeralTheory.numeral_distrib, numeralTheory.numeral_suc]
(* output omitted *)
> val it = ([], fn): goal list * validation
```

### Comments

See `src/holyhammer/README` for more information on how to install the
provers. See more examples in `src/holyhammer/examples`.

### See also

[`holyHammer.holyhammer`](#holyHammer.holyhammer),
[`tacticToe.ttt`](#tacticToe.ttt), [`DB.matchp`](#DB.matchp)
